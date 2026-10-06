import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SmoothCompactness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import QCryptLean.InfoTheory.QuantumLHL.HashingError
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyDirect
import QCryptLean.InfoTheory.QuantumLHL.Smoothing

/-!
# Seed-visible smooth leftover hashing

A real floor `k` with `ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ` gives hashing error `(1/2) *
sqrt(|Z| * 2^(-k)) + 2 * ε` at every nonnegative radius. The positive-definite reference supplies
exact feasible witnesses for positive floors. Infinite entropy leaves only the smoothing charge.
The seed remains in both compared states.
-/

open Quantum.Operators Quantum.Metrics Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- An extended smooth floor has a hashing witness at the exact rate.
For a nonpositive floor the centre itself suffices, without a domination claim. -/
theorem quantum_seedKey_LHL_smooth_hashing_witness
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z) (hH : H.isUniversal)
    (ρ : CQState X n) (σ : SubDensityOp n) (hσ : σ.toOp.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε) (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    ∃ τ : CQState X n, CQState.purifiedDistance ρ τ ≤ ε ∧
      traceDistanceGen (seedKeyExtractorOutputState H τ).toJointDensity.toOp
        (seedUniformOutputState (S := S) (Z := Z) τ.quantumMarginal).toJointDensity.toOp ≤
        (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) := by
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  by_cases hkpos : 0 < k
  · obtain ⟨τ, hd, ht⟩ := smoothMinEntropy_exists_approx_le ε hε ρ σ hσ k hkpos hk
    exact ⟨τ, hd, traceDistanceGen_seedKeyExtractorOutput_uniformOutput_le_of_minEntropy
      H hH τ σ hσ k (ofReal_le_conditionalMinEntropy_of_isFeasible τ σ k ht)⟩
  · refine ⟨ρ, ?_, ?_⟩
    · simpa only [CQState.purifiedDistance_self_zero] using hε
    · apply traceDistanceGen_seedKeyExtractorOutput_uniformOutput_le_of_minEntropy
        H hH ρ σ hσ k
      simp [ENNReal.ofReal_of_nonpos (le_of_not_gt hkpos)]

/-- Smooth seed-visible leftover hashing from extended entropy at every nonnegative radius.
The real hashing term is unchanged and the smoothing charge is exactly `2 * ε`. -/
theorem quantum_seedKey_LHL_smooth
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedUniformOutputState (S := S) (Z := Z)
          ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) + 2 * ε := by
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  obtain ⟨ρ', hρ'_dist, hρ'_k⟩ :=
    quantum_seedKey_LHL_smooth_hashing_witness H hH ρ σ hσ_pd ε hε k hk
  have hT1 :
      Quantum.Metrics.traceDistanceGen
          (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
          (seedKeyExtractorOutputState H ρ').toJointDensity.toOp ≤ ε :=
    (traceDistanceGen_seedKeyExtractorOutput_le_purifiedDistance H
      ρ ρ').trans hρ'_dist
  have hT2 :
      Quantum.Metrics.traceDistanceGen
          (seedKeyExtractorOutputState H ρ').toJointDensity.toOp
          (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal :
            CQState (S × Z) n).toJointDensity.toOp ≤
        (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) :=
    hρ'_k
  have hT3 :
      Quantum.Metrics.traceDistanceGen
          (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal :
            CQState (S × Z) n).toJointDensity.toOp
          (seedUniformOutputState (S := S) (Z := Z)
            ρ.quantumMarginal :
            CQState (S × Z) n).toJointDensity.toOp ≤ ε := by
    have h := traceDistanceGen_uniformOutput_le_marginal_purifiedDistance
      (Z := S × Z) ρ' ρ
    refine h.trans ?_
    rw [CQState.purifiedDistance_symm]
    exact hρ'_dist
  have hTri1 :=
    Quantum.Metrics.traceDistanceGen_triangle
      (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
      (seedKeyExtractorOutputState H ρ').toJointDensity.toOp
      (seedUniformOutputState (S := S) (Z := Z)
        ρ.quantumMarginal :
        CQState (S × Z) n).toJointDensity.toOp
  have hTri2 :=
    Quantum.Metrics.traceDistanceGen_triangle
      (seedKeyExtractorOutputState H ρ').toJointDensity.toOp
      (seedUniformOutputState (S := S) (Z := Z) ρ'.quantumMarginal :
        CQState (S × Z) n).toJointDensity.toOp
      (seedUniformOutputState (S := S) (Z := Z)
        ρ.quantumMarginal :
        CQState (S × Z) n).toJointDensity.toOp
  change Quantum.Metrics.traceDistanceGen
      (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
      (seedUniformOutputState (S := S) (Z := Z)
        ρ.quantumMarginal :
        CQState (S × Z) n).toJointDensity.toOp ≤ _
  linarith

/-- Infinite entropy removes the hashing term, leaving only the smoothing charge. -/
lemma le_two_mul_of_forall_hashing_bound (d ε : ℝ) (z : ℕ)
    (h : ∀ k : ℝ, d ≤ (1 / 2) * Real.sqrt ((z : ℝ) * 2 ^ (-k)) + 2 * ε) :
    d ≤ 2 * ε := by
  have hp := (tendsto_rpow_atBot_of_base_gt_one 2 one_lt_two).comp
    Filter.tendsto_neg_atTop_atBot
  have hs := (Real.continuous_sqrt.tendsto 0).comp
    (show Filter.Tendsto (fun k : ℝ => (z : ℝ) * 2 ^ (-k)) Filter.atTop (nhds 0) by
      simpa only [Function.comp_def, mul_zero] using hp.const_mul (z : ℝ))
  have hf := (hs.const_mul (1 / 2 : ℝ)).add_const (2 * ε)
  simpa using ge_of_tendsto' hf h

/-- At infinite fixed-reference smooth entropy the seed-visible distance is at most `2 * ε`. -/
theorem quantum_seedKey_LHL_smooth_of_top
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hk : smoothMinEntropy ε ρ σ = ⊤) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedUniformOutputState (S := S) (Z := Z)
          ρ.quantumMarginal).toJointDensity.toOp ≤
      2 * ε := by
  apply le_two_mul_of_forall_hashing_bound _ ε (Fintype.card Z)
  intro k
  exact quantum_seedKey_LHL_smooth H hH ρ σ hσ_pd ε hε k (by rw [hk]; exact le_top)

/-- The seed-visible leftover-hashing bound evaluated at the extended smooth entropy itself.
Infinite entropy removes the hashing term, and finite entropy uses the usual exponential. -/
theorem quantum_seedKey_LHL_smooth_hashingError
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {r : ℕ} [NeZero r]
    (H : QuantumHashFamily S X Z) (hH : H.isUniversal)
    (ρ : CQState X r) (σ : SubDensityOp r) (hσ : σ.toOp.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε) (l : ℕ) (hcardZ : Fintype.card Z = 2 ^ l) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (r * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne r) Fintype.card_ne_zero⟩
    traceDistanceGen (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp ≤
      hashingError l (smoothMinEntropy ε ρ σ) + 2 * ε := by
  by_cases htop : smoothMinEntropy ε ρ σ = ⊤
  · rw [htop, hashingError_top, zero_add]
    exact quantum_seedKey_LHL_smooth_of_top H hH ρ σ hσ ε hε htop
  · rw [hashingError_of_ne_top l htop]
    set k := (smoothMinEntropy ε ρ σ).toReal
    have hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
      rw [ENNReal.ofReal_toReal htop]
    have h := quantum_seedKey_LHL_smooth H hH ρ σ hσ ε hε k hk
    refine h.trans_eq ?_
    have hcard : (Fintype.card Z : ℝ) = (2 : ℝ) ^ l := by
      rw [hcardZ]
      norm_cast
    rw [hcard, Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) l,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 3
    ring

end InfoTheory.QuantumLHL

end -- noncomputable section
