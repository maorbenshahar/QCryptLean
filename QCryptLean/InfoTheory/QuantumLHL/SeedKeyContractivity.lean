import QCryptLean.InfoTheory.QuantumLHL.SeedKeyExtractor
import QCryptLean.InfoTheory.QuantumLHL.ExtractorContractivity
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized

/-!
# Contraction of the seed-visible extractor

The public-seed extractor preserves the input weight and contracts the joint trace norm and
its generalized trace distance. The purified-distance bound supplies the extractor leg of
smoothing arguments while keeping the seed in the output register.
-/

open Quantum.Operators Quantum.Metrics Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- Trace preservation for the seed-visible extractor output. -/
lemma seedKeyExtractorOutputState_joint_trace_eq_quantumMarginal_trace
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Fintype X]
    [Fintype Z] [DecidableEq Z]
    {n : ℕ} (H : QuantumHashFamily S X Z) (ρ : CQState X n) :
    ((seedKeyExtractorOutputState H ρ) : CQState (S × Z) n).toJointDensity.toOp.trace.re =
      ρ.quantumMarginal.trace := by
  change ((seedKeyExtractorOutputState H ρ) : CQState (S × Z) n).toJointDensity.trace = _
  rw [CQState.toJointDensity_trace_eq_sum]
  change ∑ sz : S × Z, (seedPerSeedWeightedOp H ρ sz.1 sz.2).trace.re = _
  rw [← Complex.re_sum, ← Matrix.trace_sum, sum_seedPerSeedWeightedOp_eq_quantumMarginalOp]
  rfl

/-- Trace preservation for the seed-visible uniform output. -/
lemma seedUniformOutputState_joint_trace_eq_quantumMarginal_trace
    {S Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} (σ : SubDensityOp n) :
    (seedUniformOutputState (S := S) (Z := Z) σ :
      CQState (S × Z) n).toJointDensity.toOp.trace.re = σ.trace := by
  change (uniformOutputState (Z := S × Z) σ :
    CQState (S × Z) n).toJointDensity.trace = σ.trace
  exact uniformCQState_toJointDensity_trace (X := S × Z) σ

/-- Linearity of seed-visible extractor blocks in the CQ input. -/
lemma seedPerSeedConditionedOp_sub_toOp_eq
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (H : QuantumHashFamily S X Z)
    (ρ ρ' : CQState X n) (s : S) (z : Z) :
    (seedPerSeedConditionedOp H ρ s z).toOp -
        (seedPerSeedConditionedOp H ρ' s z).toOp =
      (1 / (Fintype.card S : ℝ)) •
        ∑ x : X, if H.hash s x = z then
          (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp else 0 := by
  change seedPerSeedWeightedOp H ρ s z - seedPerSeedWeightedOp H ρ' s z = _
  unfold seedPerSeedWeightedOp
  rw [← smul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs
  · rfl
  · simp

/-- Per-block triangle bound for the seed-visible extractor. -/
lemma traceNorm_seedPerSeedConditionedOp_sub_le
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} [NeZero n] (H : QuantumHashFamily S X Z)
    (ρ ρ' : CQState X n) (s : S) (z : Z) :
    Quantum.Metrics.traceNorm
        ((seedPerSeedConditionedOp H ρ s z).toOp -
          (seedPerSeedConditionedOp H ρ' s z).toOp) ≤
      (1 / (Fintype.card S : ℝ)) *
        ∑ x : X, if H.hash s x = z then
          Quantum.Metrics.traceNorm
            ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
  have : Nonempty S := H.seedNonempty
  have hS_nn : (0 : ℝ) ≤ 1 / (Fintype.card S : ℝ) := by positivity
  rw [seedPerSeedConditionedOp_sub_toOp_eq H ρ ρ' s z, traceNorm_real_smul]
  rw [abs_of_nonneg hS_nn]
  refine mul_le_mul_of_nonneg_left ?_ hS_nn
  calc Quantum.Metrics.traceNorm
        (∑ x : X, if H.hash s x = z then
          (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp else 0)
      ≤ ∑ x : X, Quantum.Metrics.traceNorm
          (if H.hash s x = z then
            (ρ.stateMap x).toOp - (ρ'.stateMap x).toOp else 0) :=
        traceNorm_finset_sum_le _ _
    _ = ∑ x : X, if H.hash s x = z then
          Quantum.Metrics.traceNorm
            ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs
        · rfl
        · exact Quantum.Channels.traceNorm_zero (n := n)

/-- Summed trace-norm contraction for the seed-visible extractor. -/
lemma sum_traceNorm_seedPerSeedConditionedOp_sub_le
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} [NeZero n] (H : QuantumHashFamily S X Z)
    (ρ ρ' : CQState X n) :
    ∑ sz : S × Z, Quantum.Metrics.traceNorm
        ((seedPerSeedConditionedOp H ρ sz.1 sz.2).toOp -
          (seedPerSeedConditionedOp H ρ' sz.1 sz.2).toOp) ≤
      ∑ x : X, Quantum.Metrics.traceNorm
          ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
  have : Nonempty S := H.seedNonempty
  have hS_pos : (0 : ℝ) < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  calc
    ∑ sz : S × Z, Quantum.Metrics.traceNorm
        ((seedPerSeedConditionedOp H ρ sz.1 sz.2).toOp -
          (seedPerSeedConditionedOp H ρ' sz.1 sz.2).toOp)
      ≤ ∑ sz : S × Z, (1 / (Fintype.card S : ℝ)) *
          ∑ x : X, if H.hash sz.1 x = sz.2 then
            Quantum.Metrics.traceNorm
              ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
        exact Finset.sum_le_sum (fun sz _ =>
          traceNorm_seedPerSeedConditionedOp_sub_le H ρ ρ' sz.1 sz.2)
    _ = (1 / (Fintype.card S : ℝ)) *
          ∑ sz : S × Z, ∑ x : X, if H.hash sz.1 x = sz.2 then
            Quantum.Metrics.traceNorm
              ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
        rw [Finset.mul_sum]
    _ = (1 / (Fintype.card S : ℝ)) *
          ∑ s : S, ∑ z : Z, ∑ x : X, if H.hash s x = z then
            Quantum.Metrics.traceNorm
              ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
        congr 1
        rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = (1 / (Fintype.card S : ℝ)) *
          ∑ s : S, ∑ x : X, ∑ z : Z, if H.hash s x = z then
            Quantum.Metrics.traceNorm
              ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) else 0 := by
        congr 1
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.sum_comm]
    _ = (1 / (Fintype.card S : ℝ)) *
          ∑ s : S, ∑ x : X, Quantum.Metrics.traceNorm
            ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
        congr 1
        refine Finset.sum_congr rfl (fun s _ => ?_)
        refine Finset.sum_congr rfl (fun x _ => ?_)
        have := Finset.sum_ite_eq (Finset.univ : Finset Z) (H.hash s x)
          (fun _ => Quantum.Metrics.traceNorm
            ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp))
        rw [this]
        simp
    _ = (1 / (Fintype.card S : ℝ)) *
          ((Fintype.card S : ℝ) *
            ∑ x : X, Quantum.Metrics.traceNorm
              ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp)) := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ x : X, Quantum.Metrics.traceNorm
          ((ρ.stateMap x).toOp - (ρ'.stateMap x).toOp) := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ hS_ne, one_mul]

/-- Trace-norm contraction for the seed-visible extractor on joint densities. -/
lemma traceNorm_seedKeyExtractorOutput_sub_joint_le
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z) (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        ((seedKeyExtractorOutputState H ρ).toJointDensity.toOp -
          (seedKeyExtractorOutputState H ρ').toJointDensity.toOp) ≤
      Quantum.Metrics.traceNorm
        (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) := by
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [cqState_joint_traceNorm_eq_sum_blocks
        (seedKeyExtractorOutputState H ρ) (seedKeyExtractorOutputState H ρ'),
      cqState_joint_traceNorm_eq_sum_blocks ρ ρ']
  exact sum_traceNorm_seedPerSeedConditionedOp_sub_le H ρ ρ'

private lemma quantumMarginal_trace_eq_toJointDensity_trace
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} (ρ : CQState X n) :
    ρ.quantumMarginal.trace = ρ.toJointDensity.toOp.trace.re := by
  change ρ.quantumMarginal.trace = ρ.toJointDensity.trace
  rw [CQState.toJointDensity_trace_eq_sum]
  unfold CQState.quantumMarginal SubDensityOp.trace CQState.quantumMarginalOp
  rw [Matrix.trace_sum, Complex.re_sum]

/-- Generalized trace-distance contraction for the seed-visible extractor. -/
lemma traceDistanceGen_seedKeyExtractorOutput_le
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z) (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedKeyExtractorOutputState H ρ').toJointDensity.toOp ≤
      Quantum.Metrics.traceDistanceGen
        ρ.toJointDensity.toOp ρ'.toJointDensity.toOp := by
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  unfold Quantum.Metrics.traceDistanceGen
  have hnorm := traceNorm_seedKeyExtractorOutput_sub_joint_le H ρ ρ'
  have htrρ := seedKeyExtractorOutputState_joint_trace_eq_quantumMarginal_trace H ρ
  have htrρ' := seedKeyExtractorOutputState_joint_trace_eq_quantumMarginal_trace H ρ'
  have htrρ_in := quantumMarginal_trace_eq_toJointDensity_trace ρ
  have htrρ'_in := quantumMarginal_trace_eq_toJointDensity_trace ρ'
  have htr :
      (((seedKeyExtractorOutputState H ρ).toJointDensity.toOp.trace -
          (seedKeyExtractorOutputState H ρ').toJointDensity.toOp.trace).re) =
        (ρ.toJointDensity.toOp.trace - ρ'.toJointDensity.toOp.trace).re := by
    rw [Complex.sub_re, Complex.sub_re, htrρ, htrρ', htrρ_in, htrρ'_in]
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hnorm_half :
      (1 / 2) *
        Quantum.Metrics.traceNorm
          ((seedKeyExtractorOutputState H ρ).toJointDensity.toOp -
            (seedKeyExtractorOutputState H ρ').toJointDensity.toOp) ≤
      (1 / 2) *
        Quantum.Metrics.traceNorm
          (ρ.toJointDensity.toOp - ρ'.toJointDensity.toOp) :=
    mul_le_mul_of_nonneg_left hnorm hhalf
  have htrace_half :
      (1 / 2) *
          abs (((seedKeyExtractorOutputState H ρ).toJointDensity.toOp.trace -
            (seedKeyExtractorOutputState H ρ').toJointDensity.toOp.trace).re) =
        (1 / 2) *
          abs ((ρ.toJointDensity.toOp.trace - ρ'.toJointDensity.toOp.trace).re) := by
    rw [htr]
  linarith [hnorm_half, htrace_half]

/-- DPI step for the seed-visible extractor leg of the smooth LHL triangle. -/
lemma traceDistanceGen_seedKeyExtractorOutput_le_purifiedDistance
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (ρ ρ' : CQState X n) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedKeyExtractorOutputState H ρ').toJointDensity.toOp ≤
      CQState.purifiedDistance ρ ρ' := by
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  have hStep1 := traceDistanceGen_seedKeyExtractorOutput_le H ρ ρ'
  have hStep2 :=
    InfoTheory.SmoothMinEntropy.traceDistanceGen_le_purifiedDistance
      ρ.toJointDensity ρ'.toJointDensity
  exact hStep1.trans hStep2

end InfoTheory.QuantumLHL

end -- noncomputable section
