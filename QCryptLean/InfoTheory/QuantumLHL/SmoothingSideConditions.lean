import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundCore
import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundSubNormalized
import QCryptLean.InfoTheory.QuantumLHL.ExtractorContractivity
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.Quantum.Operators.PSDTraceBound

/-!
# Subnormalized hashing estimates

The direct quantum leftover hash bound consumes an extended conditional entropy floor. Positive
floors give exponential feasible coefficients, while nonpositive floors use universal trace-
distance estimates. Auxiliary lemmas identify the traces of extractor and uniform outputs.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- **Sub-normalized analog of `extractorOutputState_joint_trace_eq_one_of_normalized`.**

For an arbitrary (sub-normalized) CQ state `ρ`, the joint trace of the extractor
output state equals the (real) trace of the input quantum marginal. Proof
mirrors the normalized case: collapse the joint trace to a sum over Z, apply
`sum_extractorWeightedOp_eq_quantumMarginalOp`, and unfold to
`ρ.quantumMarginal.trace`. -/
lemma extractorOutputState_joint_trace_eq_quantumMarginal_trace
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S X Z) (ρ : CQState X n) :
    ((extractorOutputState H ρ) : CQState Z n).toJointDensity.toOp.trace.re =
      ρ.quantumMarginal.trace := by
  change ((extractorOutputState H ρ) : CQState Z n).toJointDensity.trace = _
  rw [CQState.toJointDensity_trace_eq_sum]
  change ∑ z : Z, (extractorWeightedOp H ρ z).trace.re = _
  rw [← Complex.re_sum, ← Matrix.trace_sum, sum_extractorWeightedOp_eq_quantumMarginalOp]
  rfl

/-- **Sub-normalized analog of `toJointDensity_uniformOutputState_trace_eq_of_normalized`.**

For an arbitrary (sub-normalized) CQ state `ρ`, the joint trace of the
uniform-output state on register `Z` indexed by `ρ.quantumMarginal` equals
`ρ.quantumMarginal.trace`. -/
lemma uniformOutputState_joint_trace_eq_quantumMarginal_trace
    {Z X : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype X] {n : ℕ}
    (ρ : CQState X n) :
    (uniformOutputState ρ.quantumMarginal : CQState Z n).toJointDensity.toOp.trace.re =
      ρ.quantumMarginal.trace := by
  change (uniformOutputState ρ.quantumMarginal : CQState Z n).toJointDensity.trace = _
  exact uniformCQState_toJointDensity_trace (X := Z) ρ.quantumMarginal

/-- **Monotonicity helper: inflate `√|Z|` to `√(|Z|·2^{-k})` when `k ≤ 0`.**

When `k ≤ 0` we have `-k ≥ 0` and hence `1 ≤ 2^{-k}`. Multiplying by the
nonneg `|Z|` and taking square roots gives the desired inequality. -/
lemma sqrt_card_le_sqrt_card_mul_two_pow_neg_k
    {Z : Type*} [Fintype Z] {k : ℝ} (hk_nonpos : k ≤ 0) :
    Real.sqrt ((Fintype.card Z : ℝ)) ≤
      Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) := by
  apply Real.sqrt_le_sqrt
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (-k) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hcard_nn : (0 : ℝ) ≤ (Fintype.card Z : ℝ) := Nat.cast_nonneg _
  calc (Fintype.card Z : ℝ)
      = (Fintype.card Z : ℝ) * 1 := by ring
    _ ≤ (Fintype.card Z : ℝ) * (2 : ℝ) ^ (-k) :=
        mul_le_mul_of_nonneg_left h1 hcard_nn

/-- Direct seed-averaged hashing from an exponential or arbitrary feasible coefficient. -/
lemma quantum_LHL_of_isFeasible
    {S X Z : Type*} [Fintype S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (t : ℝ)
    (ht : isFeasible ρ σ t) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        ((extractorOutputState H ρ).toJointDensity.toOp -
          (uniformOutputState (Z := Z) ρ.quantumMarginal).toJointDensity.toOp) ≤
      Real.sqrt ((Fintype.card Z : ℝ) * t) := by
  haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [cqState_joint_traceNorm_eq_sum_blocks]
  exact (joint_traceNorm_sum_blocks_le_sqrt_card_mul_lambda_subNorm
    H hH ρ σ hσ_pd ⟨t, ht⟩).trans (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (minFeasibleLambda_le_of_isFeasible ρ σ ht)
        (Nat.cast_nonneg _)))

/-- Positive blocks differ from their uniform average by at most
`2 * (1 - 1 / |Z|)` times their total trace. This is sharp for a single nonzero block. -/
lemma sum_traceNorm_sub_uniform_le
    {Z : Type*} [Fintype Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (A : Z → Op n) (hA : ∀ z, (A z).PosSemidef) :
    ∑ z, Quantum.Metrics.traceNorm (A z - (1 / (Fintype.card Z : ℝ)) • ∑ w, A w) ≤
      2 * (1 - 1 / (Fintype.card Z : ℝ)) * ∑ z, (A z).trace.re := by
  classical
  let c : ℝ := 1 / Fintype.card Z
  have hm : (1 : ℝ) ≤ Fintype.card Z := by exact_mod_cast Fintype.card_pos (α := Z)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; simpa using one_div_le_one_div_of_le (by norm_num) hm
  have hcm : (Fintype.card Z : ℝ) * c = 1 := by
    dsimp [c]
    field_simp
  have hblock (z : Z) :
      Quantum.Metrics.traceNorm (A z - c • ∑ w, A w) ≤
        (1 - c) * (A z).trace.re + c * (∑ w, (A w).trace.re - (A z).trace.re) := by
    have heq : A z - c • ∑ w, A w =
        (1 - c) • A z - c • ∑ w ∈ Finset.univ.erase z, A w := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ z)]
      module
    rw [heq]
    have h := Quantum.Metrics.traceNorm_sub_le
      ((1 - c) • A z) (c • ∑ w ∈ Finset.univ.erase z, A w)
    rw [traceNorm_real_smul, traceNorm_real_smul, abs_of_nonneg (sub_nonneg.mpr hc1),
      abs_of_nonneg hc, Quantum.Channels.traceNorm_posSemidef_eq_trace _ (hA z)] at h
    have hs := traceNorm_finset_sum_le (Finset.univ.erase z) A
    simp only [Quantum.Channels.traceNorm_posSemidef_eq_trace _ (hA _)] at hs
    have herase : ∑ w ∈ Finset.univ.erase z, (A w).trace.re =
        ∑ w, (A w).trace.re - (A z).trace.re := by
      exact Finset.sum_erase_eq_sub (Finset.mem_univ z)
    rw [herase] at hs
    exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hc))
  calc
    _ ≤ ∑ z, ((1 - c) * (A z).trace.re +
        c * (∑ w, (A w).trace.re - (A z).trace.re)) :=
      Finset.sum_le_sum fun z _ => hblock z
    _ = 2 * (1 - c) * ∑ z, (A z).trace.re := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      nlinarith [congrArg (fun t : ℝ => t * ∑ z, (A z).trace.re) hcm]

/-- The sharp CQ-to-uniform factor is at most the square root of the alphabet size. -/
lemma two_mul_one_sub_inv_le_sqrt_card (m : ℕ) (hm : 0 < m) :
    2 * (1 - 1 / (m : ℝ)) ≤ Real.sqrt m := by
  by_cases h4 : 4 ≤ m
  · exact (show 2 * (1 - 1 / (m : ℝ)) ≤ 2 by
      have : 0 ≤ 1 / (m : ℝ) := by positivity
      linarith).trans
      (Real.le_sqrt_of_sq_le (by norm_num; exact h4))
  · interval_cases m <;> norm_num at hm ⊢
    apply Real.le_sqrt_of_sq_le
    norm_num

/-- Every hash family satisfies the zero-floor bound, without an entropy hypothesis. -/
lemma quantum_LHL_zero_floor
    {S X Z : Type*} [Fintype S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        ((extractorOutputState H ρ).toJointDensity.toOp -
          (uniformOutputState (Z := Z) ρ.quantumMarginal).toJointDensity.toOp) ≤
      Real.sqrt ((Fintype.card Z : ℝ)) := by
  haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [cqState_joint_traceNorm_eq_sum_blocks]
  have h := sum_traceNorm_sub_uniform_le
    (fun z => ((extractorOutputState H ρ).stateMap z).toOp)
    (fun z => posSemidefOp_implies_mathlib
      ((extractorOutputState H ρ).stateMap z).toPosSemidefOp)
  have hsum : ∑ z, ((extractorOutputState H ρ).stateMap z).toOp =
      ρ.quantumMarginal.toOp := sum_extractorWeightedOp_eq_quantumMarginalOp H ρ
  have htrace : ∑ z, ((extractorOutputState H ρ).stateMap z).toOp.trace.re =
      ρ.quantumMarginal.trace := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, hsum]
    rfl
  simp only [hsum, htrace] at h
  have hblocks : ∀ z : Z, ((uniformOutputState ρ.quantumMarginal).stateMap z).toOp =
      (1 / (Fintype.card Z : ℝ)) • ρ.quantumMarginal.toOp := fun z => by
    simpa only [← Complex.coe_smul] using uniformOutput_stateMap_toOp ρ.quantumMarginal z
  simp only [hblocks]
  have hm : (1 : ℝ) ≤ Fintype.card Z := by exact_mod_cast Fintype.card_pos (α := Z)
  have hc : 1 / (Fintype.card Z : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num) hm
  exact h.trans ((mul_le_mul_of_nonneg_left ρ.quantumMarginal.trace_le_one
    (mul_nonneg (by norm_num) (sub_nonneg.mpr hc))).trans
      (by simpa using two_mul_one_sub_inv_le_sqrt_card (Fintype.card Z) Fintype.card_pos))

/-- Direct seed-averaged hashing from a clipped extended entropy floor, including zero. -/
lemma quantum_LHL_subNormalized
    {S X Z : Type*} [Fintype S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ) :
    haveI : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card Z) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        ((extractorOutputState H ρ).toJointDensity.toOp -
          (uniformOutputState (Z := Z) ρ.quantumMarginal).toJointDensity.toOp) ≤
      Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) := by
  by_cases hkpos : 0 < k
  · exact quantum_LHL_of_isFeasible H hH ρ σ hσ_pd _
      (isFeasible_of_ofReal_le_conditionalMinEntropy ρ σ hkpos hk)
  · exact (quantum_LHL_zero_floor H ρ).trans
      (sqrt_card_le_sqrt_card_mul_two_pow_neg_k (le_of_not_gt hkpos))

end InfoTheory.QuantumLHL

end -- noncomputable section
