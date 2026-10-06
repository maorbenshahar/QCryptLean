import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.AnnounceCoarsenCommute
import QCryptLean.QKD.BB84.Engine.EntropyFloor.AnnouncePEFloorChain
import QCryptLean.QKD.BB84.Engine.EntropyFloor.IsometricInvariance
import QCryptLean.QKD.BB84.Engine.Budgets

/-!
# Tracing out the symmetric purifier register recovers the sifted de Finetti reference

Register-transport lemmas needed to adjoin the symmetric-purifier register `V`
(`BB84SymmetricPurifier`) to the sifted τ-conditioned de Finetti reference: tracing `V` back out of
the `Eⁿ ⊗ V`-registered construction recovers exactly the unpurified `Eⁿ`-only object, both at a
single outcome block and at the fail-closed local-PE-pass-filtered mixture `bb84EnVRhoEtilde`.

Every step is one of the register-generic trailing-partial-trace bridges (the σ-independent attack
channel, the sift conjugation, per-outcome submatrix extraction), applied with the BB84 sift
`bb84SiftedRotation`.

## Main results
- `bb84_EnV_siftedTauEveRefConditioned_partialTraceB_eq`: tracing out `V` from a single
  τ-conditioned outcome block of the EnV purification recovers the corresponding block of the
  unpurified sifted reference `pairedDeFinettiState`.
- `bb84_EnV_rhoEV_partialTraceB_eq_forCoarsen`: the same identity lifted to the fail-closed
  local-PE-pass-filtered mixture `bb84EnVRhoEtilde`.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) App. B,
`\label{eq:splittingoffV}` (main.tex:1393–:1396).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy
open InfoTheory.QuantumLHL
open Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## Register plumbing for the left-oriented announcement -/

/-- Casting a CQ state through a register-dimension equality transports each block's operator along
the matrix cast. -/
private lemma bb84CastCQState_stateMap_toOpEnV {Xc : Type*} [Fintype Xc] {a b : ℕ} (h : a = b)
    (ρ : CQState Xc a) (ω : Xc) :
    ((bb84CastCQState h ρ).stateMap ω).toOp = h ▸ ((ρ.stateMap ω).toOp) := by
  subst h; rfl

/-- The fail-closed local-PE pass filter reads only the classical outcome, so it commutes with a
register-dimension cast. -/
private lemma bb84CastCQState_SiftedLocalPEPassFilter {n a b : ℕ} [NeZero a] [NeZero b]
    (h : a = b) (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ρ : CQState (Fin n → Fin signalDim) a) :
    bb84CastCQState h (bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ ρ) =
      bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ (bb84CastCQState h ρ) := by
  subst h; rfl

/-! ## The trace-out-`V` blocks identity (Nahar et al. B13) -/

/-- **Nahar et al. B13 (spectator-`V` τ-conditioning commutation).**

Tracing out only the trailing symmetric-purifier register `V` from the reassociated sifted
τ-conditioned `Eⁿ ⊗ V` block of the EnV purification recovers the sifted τ-conditioned `Eⁿ` block
of the symmetric joint de Finetti state `pairedDeFinettiState`.

Every step is one of the three trailing bridges —
`partialTraceB_mapTensorId_trailing` (the σ-independent attack
channel), `partialTraceB_sandwich_tensor_one_trailing` (the sift
conjugation), `bb84Sifted_partialTraceB_trailing_submatrix_tauEmbedding`
(per-outcome extraction) — all of which are register-generic and read
no property of the rotation beyond its acting on the Alice–Bob register only.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `\label{eq:splittingoffV}`. -/
lemma bb84_EnV_siftedTauEveRefConditioned_partialTraceB_eq {n : ℕ} [NeZero n]
    [NeZero (4 ^ n)] (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (V : BB84SymmetricPurifier n)
    (ω : Fin n → Fin signalDim) :
    Quantum.TensorProducts.partialTraceB
        ((Nat.mul_assoc eveDim (signalDim ^ n) V.dV).symm ▸
          (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel (bb84EnVCKRPurification V)
              ω).toOp) =
      (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel
        (pairedDeFinettiState signalDim n) ω).toOp := by
  have hVdv : NeZero V.dV := V.dV_neZero
  have hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hR : NeZero (signalDim ^ n * V.dV) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hcancel : ∀ {p q : ℕ} (h : p = q) (x : Op p),
      (h.symm ▸ (h ▸ x : Op q) : Op p) = x := by
    intro p q h x; subst h; rfl
  have hCastToOp : ∀ {a b : ℕ} (h : a = b) (ρ : DensityOp a),
      (DensityOp.castDim h ρ).toOp = h ▸ ρ.toOp := by
    intro a b h ρ; subst h; rfl
  -- Step 5: the trailing-`V` marginal of the EnV purification is `pairedDeFinettiState`.
  have hbottom : Quantum.TensorProducts.partialTraceB
      ((Nat.mul_assoc (signalDim ^ n) (signalDim ^ n) V.dV).symm ▸
        (bb84EnVCKRPurification V).toOp) =
      (pairedDeFinettiState signalDim n).toOp := by
    have hcast : (Nat.mul_assoc (signalDim ^ n) (signalDim ^ n) V.dV).symm ▸
        (bb84EnVCKRPurification V).toOp = V.purifier.toOp := by
      simp only [bb84EnVCKRPurification, hCastToOp]
      exact hcancel _ _
    rw [hcast]
    exact congrArg (·.toOp) V.purifier_partialTraceB
  -- Step 4: the σ-independent attack channel acts as the identity on the reference.
  have hM : Quantum.TensorProducts.partialTraceB
      ((Nat.mul_assoc (4 ^ n * eveDim) (signalDim ^ n) V.dV).symm ▸
        (bb84TauOutputDensity eveDim pre hpre (bb84EnVCKRPurification V)).toOp) =
      (bb84TauOutputDensity eveDim pre hpre (pairedDeFinettiState signalDim n)).toOp := by
    rw [show (bb84TauOutputDensity eveDim pre hpre (bb84EnVCKRPurification V)).toOp =
          mapTensorId pre (bb84EnVCKRPurification V).toOp from rfl,
      partialTraceB_mapTensorId_trailing, hbottom,
      show mapTensorId pre (pairedDeFinettiState signalDim n).toOp =
          (bb84TauOutputDensity eveDim pre hpre (pairedDeFinettiState signalDim n)).toOp from rfl]
  -- Step 3: the sift conjugation acts as the identity on the reference.
  have hcore : Quantum.TensorProducts.partialTraceB
      ((Nat.mul_assoc (4 ^ n * eveDim) (signalDim ^ n) V.dV).symm ▸
        (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel (bb84EnVCKRPurification V)).toOp)
            =
      (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel
        (pairedDeFinettiState signalDim n)).toOp := by
    simp only [bb84SiftedTauPreOutputDensity, densityOpUnitaryConj_toOp,
      Op.tensor_conjTranspose, Matrix.conjTranspose_one]
    rw [partialTraceB_sandwich_tensor_one_trailing, hM]
  -- Steps 1-2: the conditioned block is a τ-embedding submatrix.
  rw [show
      (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel (bb84EnVCKRPurification V) ω).toOp
      =
        (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel
            (bb84EnVCKRPurification V)).toOp.submatrix
          (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
            (dimR := signalDim ^ n * V.dV) (bb84OutcomeIndex ω))
          (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
            (dimR := signalDim ^ n * V.dV) (bb84OutcomeIndex ω)) from rfl,
    bb84Sifted_partialTraceB_trailing_submatrix_tauEmbedding, hcore]
  rfl

/-- **Nahar et al. B13 — tracing out `V` from the EnV reference recovers `bb84EnVRhoEtilde`.**

Each local-PE-pass-filtered EnV block (register (eveDim·4ⁿ)·dV after reassociation, where dV
is the purifier's register dimension), partial-traced over the purifier register, equals the
corresponding block of the `Eⁿ`-marginal de Finetti reference `bb84EnVRhoEtilde`.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `\label{eq:splittingoffV}`. -/
theorem bb84_EnV_rhoEV_partialTraceB_eq_forCoarsen {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (V : BB84SymmetricPurifier n) :
    ∀ x : Fin n → Fin signalDim,
      Quantum.TensorProducts.partialTraceB
          (((bb84CastCQState (Nat.mul_assoc eveDim (signalDim ^ n) V.dV).symm
            (bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
              (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
                (bb84EnVCKRPurification V)).toCQState)).stateMap x).toOp) =
        ((bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ).stateMap x).toOp := by
  have hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hVdv : NeZero V.dV := V.dV_neZero
  have hEnDim : NeZero (eveDim * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  intro x
  rw [bb84CastCQState_SiftedLocalPEPassFilter
    (Nat.mul_assoc eveDim (signalDim ^ n) V.dV).symm peSel xSel Q δ
    (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
      (bb84EnVCKRPurification V)).toCQState]
  refine (bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq
    (dE := eveDim * (signalDim ^ n)) (dR := V.dV) peSel xSel Q δ
    (bb84CastCQState (Nat.mul_assoc eveDim (signalDim ^ n) V.dV).symm
      (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
        (bb84EnVCKRPurification V)).toCQState)
    (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
      (pairedDeFinettiState signalDim n)).toCQState ?_ x).trans rfl
  intro ω
  rw [bb84CastCQState_stateMap_toOpEnV]
  exact bb84_EnV_siftedTauEveRefConditioned_partialTraceB_eq eveDim pre hpre peSel xSel V ω

end QKD.BB84.Engine

end -- noncomputable section
