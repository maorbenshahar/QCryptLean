import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.Basic
import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.OutputBlock
import QCryptLean.Quantum.Symmetry.AttackSymmetrization
import QCryptLean.InfoTheory.QuantumLHL.Main
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeySmoothing
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQStateCastTransport
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.PureCoreUncertainty

/-!
# Key-copy postprocess cast and CQ-state transport helpers

General key-copy-postprocess layer infrastructure: no declaration below mentions a BB84 or
QKD-protocol object. These are register-cast and Bochner-sum transport lemmas for the
LHL key-copy postprocess output and for seed-uniform / joint-density CQ states, kept separate
from the high-level protocol assembly.

## Main statements
- `partialTraceA_cast_one_mul_eq`: a trivial-dimension cast commutes with `partialTraceA`.
- `keyCopyPostprocessOutputBlock_sum_hash_smul_sum_ite_apply`,
  `keyCopyPostprocessOutputBlock_sum_smul_sum_ite_apply`: Bochner-sum transport through the
  key-copy postprocess output block, for a hashed and for a predicate-filtered reference sum.
- `seedUniformOutputState_fin_stateMap_toOp`: the seed-uniform output state's per-outcome block.
- `cqState_toJointDensity_castDim_toOp`: lifting a per-outcome state-map cast to the joint density.
- `cqStateCastOneLeft`: embedding a CQ state into a `1 * eveDim`-dimensioned reference.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.QuantumLHL
open Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.QuantumLHL

/-- Tracing out the dummy one-dimensional left factor introduced by the retained
branch postprocess cast recovers the original Eve operator. -/
lemma partialTraceA_cast_one_mul_eq
    (eveDim : ℕ) (A : Op eveDim) :
    partialTraceA (Op.castDim (Nat.one_mul eveDim).symm A) = A := by
  ext i j
  simp only [partialTraceA, Matrix.of_apply, Fin.sum_univ_one]
  rw [Op.castDim_apply]
  simp [finProdFinEquiv]

/-- Entry form for copied-key output blocks indexed by a hash constraint when
the payload is a retained reference block, rather than a partial trace. -/
lemma keyCopyPostprocessOutputBlock_sum_hash_smul_sum_ite_apply
    (keyDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    {S Ω : Type*} [Fintype S] [Fintype Ω]
    (passTranscript : S → Fin transcriptDim)
    (hash : S → Ω → Fin keyDim)
    (c : ℝ)
    (B : S → Ω → Op refDim)
    (p q : Fin ((keyDim * keyDim * transcriptDim) * refDim)) :
    (∑ sz : S × Fin keyDim,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim
        (passTranscript sz.1) sz.2
        (c • ∑ ω : Ω, if hash sz.1 ω = sz.2 then B sz.1 ω else 0)) p q =
      ∑ s : S, ∑ ω : Ω,
        (c : ℂ) * Matrix.single
          (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            (transcriptDim := transcriptDim) (passTranscript s) (hash s ω) p.modNat)
          (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            (transcriptDim := transcriptDim) (passTranscript s) (hash s ω) q.modNat)
          (B s ω p.modNat q.modNat)
          p q := by
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ (t : Fin transcriptDim) (z : Fin keyDim) (A : Op refDim),
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim t z (c • A) =
        (c : ℂ) • keyCopyPostprocessOutputBlock keyDim refDim transcriptDim t z A by
    intro t z A
    simp [keyCopyPostprocessOutputBlock, Finset.smul_sum]]
  simp_rw [keyCopyPostprocessOutputBlock_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_eq_single (hash s ω)]
  · simp [keyCopyPostprocessOutputBlock_apply]
  · intro z _ hz
    rw [ite_eq_right]
    · simp [keyCopyPostprocessOutputBlock]
    · exact hz.symm
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ (hash s ω)))

lemma keyCopyPostprocessOutputBlock_sum_smul_sum_ite_apply
    (keyDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    {S Ω : Type*} [Fintype S] [Fintype Ω]
    (passTranscript : S → Fin transcriptDim)
    (key : S → Fin keyDim)
    (c : ℂ)
    (P : Ω → Prop) [DecidablePred P]
    (B : Ω → Op refDim)
    (p q : Fin ((keyDim * keyDim * transcriptDim) * refDim)) :
    (∑ s : S,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim
        (passTranscript s) (key s)
        (c • ∑ ω : Ω, if P ω then B ω else 0)) p q =
      ∑ s : S,
        c * ∑ ω : Ω,
          if P ω then
            Matrix.single
              (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
                (transcriptDim := transcriptDim) (passTranscript s) (key s) p.modNat)
              (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
                (transcriptDim := transcriptDim) (passTranscript s) (key s) q.modNat)
              (B ω p.modNat q.modNat) p q
          else 0 := by
  simp_rw [keyCopyPostprocessOutputBlock_smul]
  simp_rw [keyCopyPostprocessOutputBlock_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω
  · simp [h, keyCopyPostprocessOutputBlock_apply]
  · simp [h, keyCopyPostprocessOutputBlock]

lemma seedUniformOutputState_fin_stateMap_toOp
    {seed : Type*} [Fintype seed] [Nonempty seed]
    {ℓ dim : ℕ} [NeZero (2 ^ ℓ)]
    (σ : SubDensityOp dim) (sz : seed × Fin (2 ^ ℓ)) :
    (((seedUniformOutputState σ : CQState (seed × Fin (2 ^ ℓ)) dim).stateMap sz).toOp) =
      (((2 ^ ℓ : ℂ) * Fintype.card seed)⁻¹) • σ.toOp := by
  simpa [seedUniformOutputState, uniformOutputState, Fintype.card_prod,
    Fintype.card_fin, one_div, mul_comm] using
    (@uniformOutput_stateMap_toOp (seed × Fin (2 ^ ℓ)) _ _ dim σ sz)

lemma cqState_toJointDensity_castDim_toOp
    {α : Type*} [Fintype α] [DecidableEq α]
    {d e : ℕ} (h : d = e)
    (ρ : CQState α d)
    (ρ' : CQState α e)
    (h_state : ∀ x : α, SubDensityOp.castDim h (ρ.stateMap x) = ρ'.stateMap x) :
    Op.castDim (congrArg (fun q => q * Fintype.card α) h) ρ.toJointDensity.toOp =
      ρ'.toJointDensity.toOp := by
  have hsub :=
    CQState.toJointDensity_castDim_eq_of_stateMap_castDim_eq
      h ρ ρ' h_state
  have hop :
      (SubDensityOp.castDim (congrArg (fun q => q * Fintype.card α) h)
        ρ.toJointDensity).toOp =
        ρ'.toJointDensity.toOp := by
    rw [hsub]
  simpa [InfoTheory.SmoothMinEntropy.SubDensityOp.castDim_toOp] using hop

/-- `ρ` recast along the dimension identity `eveDim = 1 * eveDim`, padding a trivial
`1`-dimensional factor on the left of the quantum register. -/
noncomputable def cqStateCastOneLeft
    {α : Type*} [Fintype α]
    (eveDim : ℕ) (ρ : CQState α eveDim) :
    CQState α (1 * eveDim) where
  stateMap := fun x => SubDensityOp.castDim (Nat.one_mul eveDim).symm (ρ.stateMap x)
  weight_le_one := by
    simpa [SubDensityOp.castDim_trace] using ρ.weight_le_one

end InfoTheory.QuantumLHL

end -- noncomputable section
