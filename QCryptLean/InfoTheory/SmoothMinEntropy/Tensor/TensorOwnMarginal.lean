import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.SmoothSuperadditivity
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.ChainRule.SmoothEntropyBridgeLemmas

/-!
# Tensoring an own-marginal state

Tensoring a CQ state with a state referenced to its own marginal preserves feasible
coefficients and purified-distance control. The resulting canonical smooth entropy
comparison allows singular own-marginal references.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- `1` is feasible for a CQ state against its own quantum marginal: each block is
dominated by the marginal, which equals the reference. -/
lemma isFeasible_one_quantumMarginal {Y : Type*} [Fintype Y] {m : ℕ}
    (tail : CQState Y m) :
    isFeasible tail tail.quantumMarginal 1 := by
  refine InfoTheory.SmoothMinEntropy.isFeasible_of_quantumMarginalOp_dominated tail
      tail.quantumMarginal
    (by norm_num) ?_
  rw [Complex.ofReal_one, one_smul]
  intro v
  exact le_refl _

/-- `1` is feasible for the tensor of two CQ states against the tensor of their own
quantum marginals: `block.stateMap x ⊗ tail.stateMap y ≼ block.quantumMarginal ⊗
tail.quantumMarginal` blockwise via `opLe_tensor_psd`. -/
lemma isFeasible_one_tensor_quantumMarginal {X Y : Type*} [Fintype X] [Fintype Y]
    {n m : ℕ} (block : CQState X n) (tail : CQState Y m) :
    isFeasible (CQState.tensor block tail)
      (SubDensityOp.tensor block.quantumMarginal tail.quantumMarginal) 1 := by
  refine ⟨zero_le_one, ?_⟩
  rintro ⟨x, y⟩
  rw [Complex.ofReal_one, one_smul]
  have h := Quantum.Operators.opLe_tensor_psd
    (block.stateMap x).isHermitian
    (posSemidefOp_implies_mathlib block.quantumMarginal.toPosSemidefOp)
    (posSemidefOp_implies_mathlib (tail.stateMap y).toPosSemidefOp)
    tail.quantumMarginal.isHermitian
    (InfoTheory.SmoothMinEntropy.stateMap_opLe_quantumMarginalOp block x)
    (InfoTheory.SmoothMinEntropy.stateMap_opLe_quantumMarginalOp tail y)
  exact h

/-- A `1`-feasible reference gives a nonnegative conditional min-entropy. -/
lemma conditionalMinEntropyReal_nonneg_of_isFeasible_one {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (h : isFeasible ρ σ 1) :
    0 ≤ conditionalMinEntropyReal ρ σ := by
  unfold conditionalMinEntropyReal
  have hle1 : minFeasibleLambda ρ σ ≤ 1 := minFeasibleLambda_le_of_isFeasible ρ σ h
  have hnn : 0 ≤ minFeasibleLambda ρ σ := minFeasibleLambda_nonneg ρ σ
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · rw [← h0, Real.log_zero, neg_zero, zero_div]
  · have hlog_nonpos : Real.log (minFeasibleLambda ρ σ) ≤ 0 :=
      Real.log_nonpos hpos.le hle1
    apply div_nonneg _ hlog2.le
    linarith

/-- **Pointwise own-marginal tensor-tail bound, feasible block.**

For a block-approximator `blockbar` that is feasible against `σ_block`, the conditional
min-entropy of `blockbar ⊗ tail` against `σ_block ⊗ tail.quantumMarginal` is at least
that of `blockbar` against `σ_block`.

htail_weight (the tail carries positive total weight) is what makes the inequality
nondegenerate: it forces the tensor optimum to be strictly positive whenever the block
optimum is, so that `Real.log` monotonicity applies on the nondegenerate branch. -/
lemma conditionalMinEntropyReal_le_tensor_own_marginal_of_feasible
    {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    {n m : ℕ}
    (blockbar : CQState X n) (tail : CQState Y m) (σ_block : SubDensityOp n)
    (htail_weight : 0 < ∑ y : Y, (tail.stateMap y).trace)
    (hfeas_block : hasFeasibleLambda blockbar σ_block) :
    conditionalMinEntropyReal blockbar σ_block ≤
      conditionalMinEntropyReal (CQState.tensor blockbar tail)
        (SubDensityOp.tensor σ_block tail.quantumMarginal) := by
  have feas_tail1 : isFeasible tail tail.quantumMarginal 1 := isFeasible_one_quantumMarginal tail
  have hfeas_tail : hasFeasibleLambda tail tail.quantumMarginal := ⟨1, feas_tail1⟩
  have hlamt_le1 : minFeasibleLambda tail tail.quantumMarginal ≤ 1 :=
    minFeasibleLambda_le_of_isFeasible tail tail.quantumMarginal feas_tail1
  have hlamb_nn : 0 ≤ minFeasibleLambda blockbar σ_block := minFeasibleLambda_nonneg _ _
  -- `λ_T ≤ λ_block · λ_tail ≤ λ_block`.
  have hT_le : minFeasibleLambda (CQState.tensor blockbar tail)
        (SubDensityOp.tensor σ_block tail.quantumMarginal) ≤
      minFeasibleLambda blockbar σ_block * minFeasibleLambda tail tail.quantumMarginal :=
    InfoTheory.SmoothMinEntropy.minFeasibleLambda_tensor_le blockbar tail σ_block
        tail.quantumMarginal
      hfeas_block hfeas_tail
  have hT_le_block : minFeasibleLambda (CQState.tensor blockbar tail)
        (SubDensityOp.tensor σ_block tail.quantumMarginal) ≤
      minFeasibleLambda blockbar σ_block :=
    le_trans hT_le (by
      calc minFeasibleLambda blockbar σ_block * minFeasibleLambda tail tail.quantumMarginal
          ≤ minFeasibleLambda blockbar σ_block * 1 :=
            mul_le_mul_of_nonneg_left hlamt_le1 hlamb_nn
        _ = minFeasibleLambda blockbar σ_block := mul_one _)
  unfold conditionalMinEntropyReal
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases eq_or_lt_of_le hlamb_nn with hlamb0 | hlambpos
  · -- `λ_block = 0` ⟹ `λ_T = 0`; both sides equal.
    have hlamb_eq : minFeasibleLambda blockbar σ_block = 0 := hlamb0.symm
    have hT0 : minFeasibleLambda (CQState.tensor blockbar tail)
        (SubDensityOp.tensor σ_block tail.quantumMarginal) = 0 :=
      le_antisymm (hlamb_eq ▸ hT_le_block) (minFeasibleLambda_nonneg _ _)
    rw [hlamb_eq, hT0]
  · -- `λ_block > 0`: derive positive block weight, hence positive tensor optimum.
    have hwblock : 0 < ∑ x : X, (blockbar.stateMap x).trace := by
      by_contra hw
      have hzero := CQState.stateMap_toOp_eq_zero_of_weight_nonpos blockbar hw
      have hfeas0 : isFeasible blockbar σ_block 0 := by
        refine ⟨le_refl 0, fun x => ?_⟩
        rw [hzero x, Complex.ofReal_zero, zero_smul]
        intro v
        exact le_refl _
      have hle0 : minFeasibleLambda blockbar σ_block ≤ 0 :=
        minFeasibleLambda_le_of_isFeasible blockbar σ_block hfeas0
      linarith
    have hwT : 0 < ∑ p : X × Y, ((CQState.tensor blockbar tail).stateMap p).trace := by
      rw [CQState.tensor_sum_trace]
      exact mul_pos hwblock htail_weight
    have hfeasT : hasFeasibleLambda (CQState.tensor blockbar tail)
        (SubDensityOp.tensor σ_block tail.quantumMarginal) := by
      obtain ⟨t, ht⟩ := hfeas_block
      exact ⟨t * 1, InfoTheory.SmoothMinEntropy.isFeasible_tensor ht feas_tail1⟩
    have hTpos : 0 < minFeasibleLambda (CQState.tensor blockbar tail)
        (SubDensityOp.tensor σ_block tail.quantumMarginal) :=
      minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos _ _ hwT hfeasT
    have hlog_le : Real.log (minFeasibleLambda (CQState.tensor blockbar tail)
        (SubDensityOp.tensor σ_block tail.quantumMarginal)) ≤
        Real.log (minFeasibleLambda blockbar σ_block) :=
      Real.log_le_log hTpos hT_le_block
    apply div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2.le

/-- Tensoring with a tail referenced to its own marginal increases extended smooth entropy,
including a zero tail and singular references. -/
theorem smoothMinEntropy_le_tensor_own_marginal
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {n m : ℕ} [NeZero n] [NeZero m] [NeZero (n * m)]
    (ε : ℝ) (block : CQState X n) (tail : CQState Y m) :
    smoothMinEntropy ε block block.quantumMarginal ≤
      smoothMinEntropy ε (CQState.tensor block tail)
        (SubDensityOp.tensor block.quantumMarginal tail.quantumMarginal) := by
  apply smoothMinEntropy_le_of_transport
  intro τ hd
  refine ⟨CQState.tensor τ tail, ?_, fun t ht => ?_⟩
  · have hdist := CQState.tensor_purifiedDistance_subadditive block τ tail tail
    rw [CQState.purifiedDistance_self_zero, add_zero] at hdist
    exact hdist.trans hd
  · simpa only [mul_one] using isFeasible_tensor ht (isFeasible_one_quantumMarginal tail)


/-- Tensoring with a positive-weight tail does not decrease signed smooth min-entropy at the
product of the marginal references when the target ball is bounded above. -/
theorem smoothMinEntropyReal_le_tensor_own_marginal
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {n m : ℕ} [NeZero n] [NeZero m] [NeZero (n * m)]
    (ε : ℝ) (hε : 0 ≤ ε)
    (block : CQState X n) (tail : CQState Y m)
    (htail_weight : 0 < ∑ y : Y, (tail.stateMap y).trace)
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε (CQState.tensor block tail)
      (SubDensityOp.tensor block.quantumMarginal tail.quantumMarginal)))) :
    smoothMinEntropyReal ε block block.quantumMarginal ≤
      smoothMinEntropyReal ε (CQState.tensor block tail)
        (SubDensityOp.tensor block.quantumMarginal tail.quantumMarginal) := by
  have key : ∀ a ∈ Set.ofPred (isInSmoothedSetReal ε block block.quantumMarginal),
      ∃ b ∈ Set.ofPred (isInSmoothedSetReal ε (CQState.tensor block tail)
        (SubDensityOp.tensor block.quantumMarginal tail.quantumMarginal)), a - 0 ≤ b := by
    intro a ha
    obtain ⟨blockbar, rfl, hd⟩ := ha
    by_cases hfeas : hasFeasibleLambda blockbar block.quantumMarginal
    · -- Feasible witness: map to `blockbar ⊗ tail`.
      refine ⟨conditionalMinEntropyReal (CQState.tensor blockbar tail)
        (SubDensityOp.tensor block.quantumMarginal tail.quantumMarginal),
        ⟨CQState.tensor blockbar tail, rfl, ?_⟩, ?_⟩
      · have hsub := InfoTheory.SmoothMinEntropy.CQState.tensor_purifiedDistance_subadditive block
          blockbar tail tail
        rw [CQState.purifiedDistance_self_zero, add_zero] at hsub
        exact le_trans hsub hd
      · rw [sub_zero]
        exact conditionalMinEntropyReal_le_tensor_own_marginal_of_feasible
          blockbar tail block.quantumMarginal htail_weight hfeas
    · -- Infeasible witness: sentinel `0`, covered by the `1`-feasible center witness.
      refine ⟨conditionalMinEntropyReal (CQState.tensor block tail)
        (SubDensityOp.tensor block.quantumMarginal tail.quantumMarginal),
        ⟨CQState.tensor block tail, rfl, by rw [CQState.purifiedDistance_self_zero]; exact hε⟩, ?_⟩
      rw [sub_zero]
      have ha0 : conditionalMinEntropyReal blockbar block.quantumMarginal = 0 := by
        unfold conditionalMinEntropyReal
        rw [minFeasibleLambda_eq_zero_of_not_hasFeasibleLambda blockbar block.quantumMarginal hfeas,
          Real.log_zero, neg_zero, zero_div]
      rw [ha0]
      exact conditionalMinEntropyReal_nonneg_of_isFeasible_one _ _
        (isFeasible_one_tensor_quantumMarginal block tail)
  have hmain := csSup_sub_le_csSup_of_forall_exists_sub_le _ _ 0
    (smoothedSetReal_nonempty hε block block.quantumMarginal) hbdd key
  simpa only [smoothMinEntropyReal, sub_zero] using hmain

end InfoTheory.SmoothMinEntropy

end
