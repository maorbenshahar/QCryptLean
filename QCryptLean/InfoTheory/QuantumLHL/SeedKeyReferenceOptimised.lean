import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.ReferenceOptimisedFloor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeySmoothing

/-!
# Reference-optimized leftover hashing

Optimizing the reference gives seed-visible hashing bounds from `smoothMinEntropyOpt`.
Regularization supplies positive-definite references for positive floors. The infinite-entropy
case leaves only the smoothing charge.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- The seed-key smooth LHL bound is continuous in the entropy level. -/
lemma continuous_seedKey_smooth_LHL_bound (Zcard : ℕ) (ε : ℝ) :
    Continuous (fun t : ℝ => (1 / 2) * Real.sqrt ((Zcard : ℝ) * 2 ^ (-t)) + 2 * ε) := by
  refine Continuous.add (continuous_const.mul ?_) continuous_const
  refine Real.continuous_sqrt.comp (continuous_const.mul ?_)
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  exact (Real.continuous_const_rpow h2).comp continuous_neg

/-- Reference-optimized extended floors give the sharp real hashing bound at every radius. -/
theorem quantum_seedKey_LHL_smooth_of_refOptimisedFloor
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ)
    (hfloor : ∀ t : ℝ, t < k →
      ∃ σ : SubDensityOp n, σ.toOp.PosDef ∧ ENNReal.ofReal t ≤ smoothMinEntropy ε ρ σ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedUniformOutputState (S := S) (Z := Z)
          ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) + 2 * ε := by
  haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  set f : ℝ → ℝ := fun t =>
      (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-t)) + 2 * ε with hf_def
  have hf_cont : Continuous f := continuous_seedKey_smooth_LHL_bound (Fintype.card Z) ε
  set kseq : ℕ → ℝ := fun m => k - 1 / ((m : ℝ) + 1) with hkseq_def
  have hkseq_lt : ∀ m, kseq m < k := by
    intro m
    have hpos : 0 < 1 / ((m : ℝ) + 1) := by positivity
    simp only [hkseq_def]
    linarith
  have hbd : ∀ m, f (kseq m) ≥
      Quantum.Metrics.traceDistanceGen
          (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
          (seedUniformOutputState (S := S) (Z := Z)
            ρ.quantumMarginal).toJointDensity.toOp := by
    intro m
    obtain ⟨σ, hσ_pd, hσ_floor⟩ := hfloor (kseq m) (hkseq_lt m)
    exact quantum_seedKey_LHL_smooth H hH ρ σ hσ_pd ε hε (kseq m) hσ_floor
  have hk_tendsto : Filter.Tendsto kseq Filter.atTop (nhds k) := by
    have h1 : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [hkseq_def, neg_zero, zero_add, neg_add_eq_sub] using h1.neg.add_const k
  have hf_tendsto : Filter.Tendsto (fun m => f (kseq m)) Filter.atTop (nhds (f k)) :=
    (hf_cont.tendsto k).comp hk_tendsto
  exact ge_of_tendsto' hf_tendsto hbd

/-- Optimized extended smooth entropy gives seed-visible hashing with no reference guard. -/
theorem quantum_seedKey_LHL_smoothOpt
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropyOpt ε ρ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedUniformOutputState (S := S) (Z := Z)
          ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) + 2 * ε := by
  apply quantum_seedKey_LHL_smooth_of_refOptimisedFloor H hH ρ ε hε k
  intro t ht
  by_cases htpos : 0 < t
  · obtain ⟨u, htu, huk⟩ := exists_between ht
    have hu : ENNReal.ofReal u < smoothMinEntropyOpt ε ρ :=
      (ENNReal.ofReal_lt_ofReal_iff (lt_trans htpos ht) |>.mpr huk).trans_le hk
    obtain ⟨σ, hσ⟩ := lt_iSup_iff.mp hu
    exact exists_posDef_smoothMinEntropy_ge_of_lt ε ρ σ u hσ.le t htu
  · obtain ⟨σ, hσ, _⟩ := exists_posDef_reference_isFeasible_of_one_lt ρ 2 (by norm_num)
    exact ⟨σ, hσ, by simp [ENNReal.ofReal_of_nonpos (le_of_not_gt htpos)]⟩

/-- Infinite optimized entropy leaves only the `2 * ε` seed-visible smoothing charge. -/
theorem quantum_seedKey_LHL_smoothOpt_of_top
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hk : smoothMinEntropyOpt ε ρ = ⊤) :
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
  exact quantum_seedKey_LHL_smoothOpt H hH ρ ε hε k (by rw [hk]; exact le_top)

end InfoTheory.QuantumLHL

end -- noncomputable section
