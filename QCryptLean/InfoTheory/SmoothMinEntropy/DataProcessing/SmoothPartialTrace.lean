import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.ProductReference
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.DimensionPenalty

/-!
# Signed smoothing at the zero-state boundary

The signed real smoothing set is unbounded when its ball reaches the zero state and the reference
is positive definite. These results supply the positive candidate-weight condition needed for
finite real entropy continuity and compactness arguments.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Local helpers (rebuilds of `private` lemmas from other files). -/

/-- A sub-density operator of trace zero has zero underlying matrix.  Local
replica of the `private` lemma in `ExtensionPenalty.lean`. -/
private lemma subDensityOp_toOp_eq_zero_of_trace_eq_zero
    {d : ℕ} (ρ : SubDensityOp d) (htrace : ρ.trace = 0) :
    ρ.toOp = 0 := by
  have hpsd : Matrix.PosSemidef ρ.toOp :=
    posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have htrace_complex : ρ.toOp.trace = 0 := by
    rw [SubDensityOp.trace_complex_eq, htrace]
    norm_num
  exact hpsd.trace_eq_zero_iff.mp htrace_complex

/-- A CQ state with non-positive total weight has zero stateMap (operator) at
every outcome.  Local replica of the `private` lemma in `ExtensionPenalty.lean`. -/
private lemma cqState_stateMap_toOp_eq_zero_of_weight_nonpos
    {X : Type*} [Fintype X] {d : ℕ}
    (ρ : CQState X d)
    (hweight : ¬ 0 < ∑ x : X, (ρ.stateMap x).trace) :
    ∀ x : X, (ρ.stateMap x).toOp = 0 := by
  classical
  have hsum_nonpos : (∑ x : X, (ρ.stateMap x).trace) ≤ 0 := le_of_not_gt hweight
  intro x
  have hx_nonneg : 0 ≤ (ρ.stateMap x).trace := (ρ.stateMap x).trace_nonneg
  have hx_le_sum :
      (ρ.stateMap x).trace ≤ ∑ y : X, (ρ.stateMap y).trace :=
    Finset.single_le_sum (fun y _ => (ρ.stateMap y).trace_nonneg) (Finset.mem_univ x)
  have hx_trace_zero : (ρ.stateMap x).trace = 0 :=
    le_antisymm (le_trans hx_le_sum hsum_nonpos) hx_nonneg
  exact subDensityOp_toOp_eq_zero_of_trace_eq_zero (ρ.stateMap x) hx_trace_zero

/-! ## Sufficient unboundedness construction under `2 · weight ≤ ε²`.

The original false linear statement is replaced first by a proved quadratic
sufficient condition.  The exact `weight ≤ ε²` boundary is stated below as the
residual theorem consumed by the equality-transfer lemma.
-/

/-- Blockwise scaling of a CQ state by a scalar `c ∈ [0,1]`.

This is the witness construction for Issue #165: `(c • ρ).stateMap x` is
`SubDensityOp.smul (ρ.stateMap x) c`, which scales each per-outcome block by
`c`.  The resulting CQ state has total weight `c · (∑ tr (ρ.stateMap x))` and
each block dominated by the corresponding block of `ρ`. -/
private noncomputable def smulCQ {X : Type*} [Fintype X] {n : ℕ}
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) : CQState X n where
  stateMap x := SubDensityOp.smul (ρ.stateMap x) c hc_nn hc_le
  weight_le_one := by
    have hweight :
        (∑ x : X, (SubDensityOp.smul (ρ.stateMap x) c hc_nn hc_le).trace)
          = c * ∑ x : X, (ρ.stateMap x).trace := by
      simp_rw [SubDensityOp.smul_trace (ρ.stateMap _) c hc_nn hc_le,
        ← Finset.mul_sum]
    rw [hweight]
    calc c * ∑ x : X, (ρ.stateMap x).trace
        ≤ c * 1 := mul_le_mul_of_nonneg_left ρ.weight_le_one hc_nn
      _ = c := mul_one c
      _ ≤ 1 := hc_le

private lemma smulCQ_stateMap_toOp {X : Type*} [Fintype X] {n : ℕ}
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) (x : X) :
    ((smulCQ c hc_nn hc_le ρ).stateMap x).toOp = (c : ℂ) • (ρ.stateMap x).toOp :=
  rfl

private lemma smulCQ_stateMap_trace {X : Type*} [Fintype X] {n : ℕ}
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) (x : X) :
    ((smulCQ c hc_nn hc_le ρ).stateMap x).trace = c * (ρ.stateMap x).trace :=
  SubDensityOp.smul_trace (ρ.stateMap x) c hc_nn hc_le

private lemma sum_smulCQ_stateMap_trace {X : Type*} [Fintype X] {n : ℕ}
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) :
    (∑ x : X, ((smulCQ c hc_nn hc_le ρ).stateMap x).trace) =
      c * ∑ x : X, (ρ.stateMap x).trace := by
  simp_rw [smulCQ_stateMap_trace c hc_nn hc_le ρ, ← Finset.mul_sum]

private lemma smulCQ_toJointDensity_toOp
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) :
    (smulCQ c hc_nn hc_le ρ).toJointDensity.toOp =
      (c : ℂ) • ρ.toJointDensity.toOp := by
  let e : Fin n × X ≃ Fin (n * Fintype.card X) :=
    (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin X)).trans
      finProdFinEquiv
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal,
    CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  change
    Matrix.reindex e e
        (Matrix.blockDiagonal
          (fun x : X => ((smulCQ c hc_nn hc_le ρ).stateMap x).toOp)) =
      (c : ℂ) •
        Matrix.reindex e e
          (Matrix.blockDiagonal (fun x : X => (ρ.stateMap x).toOp))
  simp_rw [smulCQ_stateMap_toOp c hc_nn hc_le ρ]
  exact reindex_blockDiagonal_smul e (c : ℂ) (fun x : X => (ρ.stateMap x).toOp)

private lemma smulCQ_toJointDensity_trace
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) :
    (smulCQ c hc_nn hc_le ρ).toJointDensity.trace =
      c * ρ.toJointDensity.trace := by
  rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum,
    sum_smulCQ_stateMap_trace c hc_nn hc_le ρ]

/-- `c • ρ` is blockwise dominated by `ρ` in the PSD (Löwner) order when
`c ∈ [0, 1]`.  This is `(1 - c) · ρ.stateMap x ≥ 0`. -/
private lemma smulCQ_stateMap_opLe {X : Type*} [Fintype X] {n : ℕ}
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) (x : X) :
    opLe ((smulCQ c hc_nn hc_le ρ).stateMap x).toOp (ρ.stateMap x).toOp := by
  -- Goal: opLe (c • A) A where A = (ρ.stateMap x).toOp is PSD.
  -- Equivalent: A - c • A = (1-c) • A is PSD.
  rw [smulCQ_stateMap_toOp]
  apply opLe_of_posSemidef_sub
  have hA_psd : (ρ.stateMap x).toOp.PosSemidef :=
    posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  have h_one_sub_nn : (0 : ℝ) ≤ 1 - c := by linarith
  have h_eq :
      (ρ.stateMap x).toOp - (c : ℂ) • (ρ.stateMap x).toOp =
        ((1 - c : ℝ) : ℂ) • (ρ.stateMap x).toOp := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  rw [h_eq]
  exact Quantum.Metrics.posSemidef_ofReal_smul
    (ρ.stateMap x).toOp hA_psd (1 - c) h_one_sub_nn

/-- Purified distance bound for blockwise scaling: `P(ρ, c • ρ) ≤ √(2 (1-c) · w)`
where `w` is the total CQ weight `∑_x tr(ρ.stateMap x)`.

This is a direct application of the sub-normalized trace-gap purified-distance
bound `purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe`
to the blockwise PSD domination `(c • ρ).stateMap x ≤ ρ.stateMap x`. -/
private lemma purifiedDistance_smulCQ_le_sqrt_two_mul_one_sub_c_mul_weight
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) :
    CQState.purifiedDistance ρ (smulCQ c hc_nn hc_le ρ) ≤
      Real.sqrt (2 * ((1 - c) * ∑ x : X, (ρ.stateMap x).trace)) := by
  have hgap_nn :
      (0 : ℝ) ≤ (1 - c) * ∑ x : X, (ρ.stateMap x).trace := by
    apply mul_nonneg (by linarith)
    exact Finset.sum_nonneg (fun x _ => (ρ.stateMap x).trace_nonneg)
  have hgap_eq :
      (∑ x : X, (ρ.stateMap x).trace) -
          (∑ x : X, ((smulCQ c hc_nn hc_le ρ).stateMap x).trace) =
        (1 - c) * ∑ x : X, (ρ.stateMap x).trace := by
    rw [sum_smulCQ_stateMap_trace c hc_nn hc_le ρ]
    ring
  exact
    CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      ρ (smulCQ c hc_nn hc_le ρ) hgap_nn
      (smulCQ_stateMap_opLe c hc_nn hc_le ρ)
      (le_of_eq hgap_eq)

private lemma one_sub_sq_scaling_bhattacharyya_le_weight
    {w c : ℝ} (hw_nn : 0 ≤ w) (hw_le : w ≤ 1)
    (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) :
    1 - (Real.sqrt c * w + Real.sqrt ((1 - w) * (1 - c * w))) ^ 2 ≤ w := by
  have hcw_nn : 0 ≤ c * w := mul_nonneg hc_nn hw_nn
  have hcw_le_one : c * w ≤ 1 := by
    have hcw_le_w : c * w ≤ 1 * w := mul_le_mul_of_nonneg_right hc_le hw_nn
    nlinarith only [hcw_le_w, hw_le]
  have h1w_nn : 0 ≤ 1 - w := sub_nonneg.mpr hw_le
  have h1w_le_one : 1 - w ≤ 1 := by linarith
  have h1cw_nn : 0 ≤ 1 - c * w := sub_nonneg.mpr hcw_le_one
  have h1cw_le_one : 1 - c * w ≤ 1 := by linarith
  have hsqrt1w_le_one : Real.sqrt (1 - w) ≤ 1 :=
    Real.sqrt_le_one.mpr h1w_le_one
  have hsqrt1cw_le_one : Real.sqrt (1 - c * w) ≤ 1 :=
    Real.sqrt_le_one.mpr h1cw_le_one
  have hgap_nn : 0 ≤ 1 - Real.sqrt (1 - c * w) := by linarith
  have hgap_le : 1 - Real.sqrt (1 - c * w) ≤ c * w := by
    have hle_sqrt : 1 - c * w ≤ Real.sqrt (1 - c * w) := by
      rw [Real.le_sqrt h1cw_nn h1cw_nn]
      nlinarith only [h1cw_nn, h1cw_le_one]
    linarith only [hle_sqrt]
  have hc_le_sqrt : c ≤ Real.sqrt c := by
    rw [Real.le_sqrt hc_nn hc_nn]
    nlinarith only [hc_nn, hc_le]
  have hgap_scaled :
      Real.sqrt (1 - w) * (1 - Real.sqrt (1 - c * w)) ≤ Real.sqrt c * w := by
    calc Real.sqrt (1 - w) * (1 - Real.sqrt (1 - c * w))
        ≤ 1 * (1 - Real.sqrt (1 - c * w)) :=
            mul_le_mul_of_nonneg_right hsqrt1w_le_one hgap_nn
      _ ≤ 1 * (c * w) := by
            exact mul_le_mul_of_nonneg_left hgap_le (by norm_num)
      _ = c * w := by ring
      _ ≤ Real.sqrt c * w := mul_le_mul_of_nonneg_right hc_le_sqrt hw_nn
  have hsqrt_mul :
      Real.sqrt ((1 - w) * (1 - c * w)) =
        Real.sqrt (1 - w) * Real.sqrt (1 - c * w) := by
    rw [Real.sqrt_mul h1w_nn]
  have hB_ge :
      Real.sqrt (1 - w) ≤
        Real.sqrt c * w + Real.sqrt ((1 - w) * (1 - c * w)) := by
    rw [hsqrt_mul]
    calc Real.sqrt (1 - w)
        = Real.sqrt (1 - w) * Real.sqrt (1 - c * w) +
            Real.sqrt (1 - w) * (1 - Real.sqrt (1 - c * w)) := by ring
      _ ≤ Real.sqrt (1 - w) * Real.sqrt (1 - c * w) + Real.sqrt c * w :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hgap_scaled
                  (Real.sqrt (1 - w) * Real.sqrt (1 - c * w))
      _ = Real.sqrt c * w + Real.sqrt (1 - w) * Real.sqrt (1 - c * w) := by ring
  have hB_nn :
      0 ≤ Real.sqrt c * w + Real.sqrt ((1 - w) * (1 - c * w)) := by
    apply add_nonneg
    · exact mul_nonneg (Real.sqrt_nonneg _) hw_nn
    · exact Real.sqrt_nonneg _
  have hsq :
      1 - w ≤ (Real.sqrt c * w + Real.sqrt ((1 - w) * (1 - c * w))) ^ 2 := by
    have hsq' :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hB_nn).mpr hB_ge
    rwa [Real.sq_sqrt h1w_nn] at hsq'
  linarith only [hsq]

private lemma fidelityGen_smulCQ_ge_scaling_bhattacharyya
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) :
    Real.sqrt c * (∑ x : X, (ρ.stateMap x).trace) +
        Real.sqrt
          ((1 - ∑ x : X, (ρ.stateMap x).trace) *
            (1 - c * ∑ x : X, (ρ.stateMap x).trace)) ≤
      letI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
      letI : NeZero (n * Fintype.card X) :=
        ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
      fidelityGen ρ.toJointDensity (smulCQ c hc_nn hc_le ρ).toJointDensity := by
  unfold fidelityGen
  let A := ρ.toJointDensity.toPosSemidefOp
  let τ : CQState X n := smulCQ c hc_nn hc_le ρ
  have hτ_op : ((c : ℂ) • A.toOp) = τ.toJointDensity.toPosSemidefOp.toOp := by
    simpa [A, τ] using (smulCQ_toJointDensity_toOp c hc_nn hc_le ρ).symm
  have h_scaling :=
    Quantum.Metrics.fidelity_smul_smul
      (α := (1 : ℝ)) (β := c) (by norm_num) hc_nn A A
  have h_fid_expand :
      Quantum.Metrics.fidelity A τ.toJointDensity.toPosSemidefOp =
        Real.sqrt c * ρ.toJointDensity.trace := by
    calc Quantum.Metrics.fidelity A τ.toJointDensity.toPosSemidefOp
        = Real.sqrt ((1 : ℝ) * c) * Quantum.Metrics.fidelity A A := by
            rw [← h_scaling, hτ_op]
            simp
            rfl
      _ = Real.sqrt c * ρ.toJointDensity.trace := by
            rw [one_mul, Quantum.Metrics.fidelity_self_posSemidefOp]
            rfl
  rw [h_fid_expand]
  rw [CQState.toJointDensity_trace_eq_sum, smulCQ_toJointDensity_trace c hc_nn hc_le ρ]
  rw [CQState.toJointDensity_trace_eq_sum]

/-- Sharp purified-distance bound for blockwise scaling.

For `0 ≤ c ≤ 1`, the purified distance between a CQ state and its blockwise
scaled copy is bounded by the square root of the original total CQ weight. -/
private lemma purifiedDistance_smulCQ_le_sqrt_weight
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n) :
    CQState.purifiedDistance ρ (smulCQ c hc_nn hc_le ρ) ≤
      Real.sqrt (∑ x : X, (ρ.stateMap x).trace) := by
  classical
  let τ : CQState X n := smulCQ c hc_nn hc_le ρ
  let w : ℝ := ∑ x : X, (ρ.stateMap x).trace
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have hw_nn : 0 ≤ w :=
    Finset.sum_nonneg (fun x _ => (ρ.stateMap x).trace_nonneg)
  have hw_le : w ≤ 1 := by
    simpa [w] using ρ.weight_le_one
  set B : ℝ :=
    Real.sqrt c * w + Real.sqrt ((1 - w) * (1 - c * w)) with hB_def
  have hB_nn : 0 ≤ B := by
    rw [hB_def]
    apply add_nonneg
    · exact mul_nonneg (Real.sqrt_nonneg _) hw_nn
    · exact Real.sqrt_nonneg _
  have hfg_lb : B ≤ fidelityGen ρ.toJointDensity τ.toJointDensity := by
    simpa [B, τ, w] using
      fidelityGen_smulCQ_ge_scaling_bhattacharyya c hc_nn hc_le ρ
  have hscalar : 1 - B ^ 2 ≤ w := by
    simpa [B, w] using
      one_sub_sq_scaling_bhattacharyya_le_weight
        (w := w) (c := c) hw_nn hw_le hc_nn hc_le
  have hP_sq : CQState.purifiedDistance ρ τ ^ 2 ≤ w := by
    unfold CQState.purifiedDistance
    have hfg_nn : 0 ≤ fidelityGen ρ.toJointDensity τ.toJointDensity :=
      fidelityGen_nonneg ρ.toJointDensity τ.toJointDensity
    have hB_sq_le : B ^ 2 ≤ fidelityGen ρ.toJointDensity τ.toJointDensity ^ 2 :=
      (sq_le_sq₀ hB_nn hfg_nn).mpr hfg_lb
    calc purifiedDistance ρ.toJointDensity τ.toJointDensity ^ 2
        = 1 - fidelityGen ρ.toJointDensity τ.toJointDensity ^ 2 :=
            purifiedDistance_sq ρ.toJointDensity τ.toJointDensity
      _ ≤ 1 - B ^ 2 := by linarith
      _ ≤ w := hscalar
  have hP_nn : 0 ≤ CQState.purifiedDistance ρ τ := by
    unfold CQState.purifiedDistance
    exact purifiedDistance_nonneg ρ.toJointDensity τ.toJointDensity
  have hsqrt_nn : 0 ≤ Real.sqrt w := Real.sqrt_nonneg _
  have hsq_le : CQState.purifiedDistance ρ τ ^ 2 ≤ (Real.sqrt w) ^ 2 := by
    rwa [Real.sq_sqrt hw_nn]
  have hP_le : CQState.purifiedDistance ρ τ ≤ Real.sqrt w :=
    (sq_le_sq₀ hP_nn hsqrt_nn).mp hsq_le
  simpa [τ, w] using hP_le

/-- Feasibility scales linearly in the CQ-state scalar: if `t` is feasible for
`ρ` against `σ`, then `c · t` is feasible for `c • ρ` against `σ`. -/
private lemma isFeasible_smulCQ_of_isFeasible {X : Type*} [Fintype X] {n : ℕ}
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n)
    (σ : SubDensityOp n) {t : ℝ} (ht : isFeasible ρ σ t) :
    isFeasible (smulCQ c hc_nn hc_le ρ) σ (c * t) := by
  refine ⟨mul_nonneg hc_nn ht.1, fun x => ?_⟩
  have hx := ht.2 x
  -- hx : opLe (ρ.stateMap x).toOp ((t : ℂ) • σ.toOp)
  -- Goal: opLe ((c • ρ).stateMap x).toOp ((c * t : ℂ) • σ.toOp)
  rw [smulCQ_stateMap_toOp]
  have hscaled :
      opLe ((c : ℂ) • (ρ.stateMap x).toOp) ((c : ℂ) • (t : ℂ) • σ.toOp) :=
    opLe_smul_nonneg hc_nn hx
  have h_smul :
      ((c : ℂ) • (t : ℂ) • σ.toOp) = ((c * t : ℝ) : ℂ) • σ.toOp := by
    rw [smul_smul, ← Complex.ofReal_mul]
  rw [h_smul] at hscaled
  exact hscaled

/-- `minFeasibleLambda` scales linearly under blockwise CQ scaling. -/
private lemma minFeasibleLambda_smulCQ_le {X : Type*} [Fintype X] {n : ℕ}
    [NeZero n]
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) (ρ : CQState X n)
    (σ : SubDensityOp n) (hfeas : hasFeasibleLambda ρ σ) :
    minFeasibleLambda (smulCQ c hc_nn hc_le ρ) σ ≤
      c * minFeasibleLambda ρ σ := by
  have hscale : ∀ {t : ℝ},
      isFeasible ρ σ t → isFeasible (smulCQ c hc_nn hc_le ρ) σ (c * t) :=
    fun {t} ht => isFeasible_smulCQ_of_isFeasible c hc_nn hc_le ρ σ ht
  exact
    minFeasibleLambda_le_mul_of_isFeasible_scaling
      ρ σ (smulCQ c hc_nn hc_le ρ) σ hc_nn hfeas hscale

/-- Maximally mixed witness at a chosen outcome `x₀` for the boundary
`weight = 0` case.  The state has `(stateMap x₀)` equal to `c · maxMixed` (a
scalar fraction of the maximally mixed state) and zero in every other
outcome. -/
private noncomputable def maxMixedAt
    {X : Type*} [Fintype X] [DecidableEq X] (n : ℕ) [NeZero n]
    (x₀ : X) (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) : CQState X n where
  stateMap x :=
    if x = x₀ then
      SubDensityOp.smul (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) c hc_nn hc_le
    else 0
  weight_le_one := by
    classical
    have hzero_trace : SubDensityOp.trace (0 : SubDensityOp n) = 0 := by
      unfold SubDensityOp.trace
      change ((0 : Op n).trace).re = 0
      simp
    have hsum_eq : (∑ x : X,
        (if x = x₀ then
            SubDensityOp.smul (DensityOp.toSubDensityOp (DensityOp.maxMixed n))
              c hc_nn hc_le
          else (0 : SubDensityOp n)).trace) = c := by
      rw [Finset.sum_eq_single x₀]
      · simp only [if_true, SubDensityOp.smul_trace]
        rw [toSubDensityOp_trace]
        ring
      · intro b _ hbne
        simp only [if_neg hbne]
        exact hzero_trace
      · intro h
        exact (h (Finset.mem_univ x₀)).elim
    rw [hsum_eq]; exact hc_le

private lemma maxMixedAt_stateMap_at {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} [NeZero n] (x₀ : X) (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) :
    (maxMixedAt n x₀ c hc_nn hc_le).stateMap x₀ =
      SubDensityOp.smul (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) c hc_nn hc_le := by
  change (if x₀ = x₀ then
      SubDensityOp.smul (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) c hc_nn hc_le
    else (0 : SubDensityOp n)) = _
  rw [if_pos rfl]

private lemma maxMixedAt_stateMap_off {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} [NeZero n] (x₀ : X) (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1)
    {x : X} (hx : x ≠ x₀) :
    (maxMixedAt n x₀ c hc_nn hc_le).stateMap x = (0 : SubDensityOp n) := by
  change (if x = x₀ then
      SubDensityOp.smul (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) c hc_nn hc_le
    else (0 : SubDensityOp n)) = _
  rw [if_neg hx]

private lemma sum_maxMixedAt_stateMap_trace
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} [NeZero n]
    (x₀ : X) (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) :
    (∑ x : X, ((maxMixedAt n x₀ c hc_nn hc_le).stateMap x).trace) = c := by
  classical
  have hzero_trace : SubDensityOp.trace (0 : SubDensityOp n) = 0 := by
    unfold SubDensityOp.trace
    change ((0 : Op n).trace).re = 0
    simp
  rw [Finset.sum_eq_single x₀]
  · rw [maxMixedAt_stateMap_at]
    rw [SubDensityOp.smul_trace, toSubDensityOp_trace]
    ring
  · intro b _ hbne
    rw [maxMixedAt_stateMap_off x₀ c hc_nn hc_le hbne]
    exact hzero_trace
  · intro h
    exact (h (Finset.mem_univ x₀)).elim

/-- `0 ≤_PSD (c : ℂ) • A` when `c ≥ 0` and `A` is positive semidefinite. -/
private lemma opLe_zero_smul_of_psd {n : ℕ} {A : Op n} (hA : A.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    opLe (0 : Op n) ((c : ℂ) • A) := by
  apply opLe_of_posSemidef_sub
  rw [sub_zero]
  exact Quantum.Metrics.posSemidef_ofReal_smul _ hA c hc

/-- The maximally mixed witness is feasible against the maximally mixed
reference with feasible scalar `c`.  This is `(c • maxMixed) ≤_PSD c • maxMixed`
(trivial) at `x₀` and `0 ≤_PSD c • maxMixed` (vacuous) elsewhere. -/
private lemma isFeasible_maxMixedAt {X : Type*} [Fintype X] [DecidableEq X]
    {n : ℕ} [NeZero n] (x₀ : X) (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) :
    isFeasible (maxMixedAt n x₀ c hc_nn hc_le)
      (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) c := by
  classical
  refine ⟨hc_nn, fun x => ?_⟩
  by_cases hx : x = x₀
  · -- At outcome x₀: opLe ((c • maxMixed).toOp) ((c : ℂ) • maxMixed.toOp).
    have hat : (maxMixedAt n x₀ c hc_nn hc_le).stateMap x =
        SubDensityOp.smul
          (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) c hc_nn hc_le := by
      rw [hx]; exact maxMixedAt_stateMap_at x₀ c hc_nn hc_le
    have heq :
        ((maxMixedAt n x₀ c hc_nn hc_le).stateMap x).toOp =
          (c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed n)).toOp := by
      rw [hat]; rfl
    rw [heq]
    exact opLe_refl _
  · have hzero :
        ((maxMixedAt n x₀ c hc_nn hc_le).stateMap x).toOp = (0 : Op n) := by
      rw [maxMixedAt_stateMap_off x₀ c hc_nn hc_le hx]
      rfl
    rw [hzero]
    exact opLe_zero_smul_of_psd
      (posSemidefOp_implies_mathlib
        (DensityOp.toSubDensityOp (DensityOp.maxMixed n)).toPosSemidefOp) hc_nn

/-- Purified distance bound for the maxMixed witness against the zero CQ state
(the witness has trace exactly `c`, so the trace gap is `c`). -/
private lemma purifiedDistance_zero_maxMixedAt_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (x₀ : X) (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1)
    (ρ : CQState X n)
    (hρ_zero : ∀ x : X, (ρ.stateMap x).toOp = 0) :
    CQState.purifiedDistance ρ (maxMixedAt n x₀ c hc_nn hc_le) ≤
      Real.sqrt (2 * c) := by
  classical
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  -- Strategy: ρ has all blocks zero, so ρ ≤_PSD maxMixedAt blockwise.
  -- Apply the trace-gap purifiedDistance bound from (maxMixedAt, ρ) direction,
  -- then use symmetry.
  have hρ_le_ρ' : ∀ x : X,
      opLe (ρ.stateMap x).toOp ((maxMixedAt n x₀ c hc_nn hc_le).stateMap x).toOp := by
    intro x
    have h_ps : ((maxMixedAt n x₀ c hc_nn hc_le).stateMap x).toOp.PosSemidef :=
      posSemidefOp_implies_mathlib
        ((maxMixedAt n x₀ c hc_nn hc_le).stateMap x).toPosSemidefOp
    apply opLe_of_posSemidef_sub
    rw [hρ_zero x, sub_zero]
    exact h_ps
  have hsum_ρ_zero : (∑ x : X, (ρ.stateMap x).trace) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have : (ρ.stateMap x).toOp.trace.re = 0 := by
      rw [hρ_zero x, Matrix.trace_zero]; simp
    simpa [SubDensityOp.trace] using this
  have hweight_diff :
      (∑ x : X, ((maxMixedAt n x₀ c hc_nn hc_le).stateMap x).trace) -
          (∑ x : X, (ρ.stateMap x).trace) = c := by
    rw [sum_maxMixedAt_stateMap_trace, hsum_ρ_zero, sub_zero]
  -- Apply CQ trace-gap bound to (maxMixedAt, ρ), get P(maxMixedAt, ρ) ≤ √(2c).
  -- Then use symmetry to flip to P(ρ, maxMixedAt) ≤ √(2c).
  have hP : CQState.purifiedDistance (maxMixedAt n x₀ c hc_nn hc_le) ρ ≤
      Real.sqrt (2 * c) :=
    CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      (maxMixedAt n x₀ c hc_nn hc_le) ρ hc_nn hρ_le_ρ' (le_of_eq hweight_diff)
  rw [CQState.purifiedDistance_symm]
  exact hP

/-- At a positive radius whose ball reaches zero, signed conditional entropy against a
positive-definite reference has arbitrarily large values in the smoothing ball. -/
theorem exists_gt_smoothedSetReal_of_posDef_of_weight_le_eps_sq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : SubDensityOp n) (hσ_pd : σ.toOp.PosDef) (ε : ℝ)
    (hε_pos : 0 < ε)
    (hweight_le : (∑ x : X, (ρ.stateMap x).trace) ≤ ε ^ 2)
    (a : ℝ) :
    ∃ h ∈ setOf (isInSmoothedSetReal ε ρ σ), a < h := by
  classical
  set w : ℝ := ∑ x : X, (ρ.stateMap x).trace with hw_def
  have hw_nn : 0 ≤ w := Finset.sum_nonneg (fun x _ => (ρ.stateMap x).trace_nonneg)
  have hε_nn : 0 ≤ ε := le_of_lt hε_pos
  have hε_eq : Real.sqrt (ε ^ 2) = ε := by rw [sq, Real.sqrt_mul_self hε_nn]
  set targetLam : ℝ := Real.exp (-(a + 1) * Real.log 2) with htgt_def
  have htgt_pos : 0 < targetLam := Real.exp_pos _
  by_cases hw_pos : 0 < w
  · -- Scaling branch: witness `ρ' = c · ρ`.
    set lamρ : ℝ := minFeasibleLambda ρ σ with hlamρ_def
    have hlamρ_nn : 0 ≤ lamρ := minFeasibleLambda_nonneg ρ σ
    have hfeas_ρ : hasFeasibleLambda ρ σ := hasFeasibleLambda_of_posDef ρ σ hσ_pd
    have hlamρ_pos : 0 < lamρ :=
      minFeasibleLambda_pos_of_posDef_of_weight_pos ρ σ hσ_pd hw_pos
    set c : ℝ := min 1 (targetLam / lamρ) with hc_def
    have htgt_div_pos : 0 < targetLam / lamρ := div_pos htgt_pos hlamρ_pos
    have hc_pos : 0 < c := lt_min (by norm_num) htgt_div_pos
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have hc_le_one : c ≤ 1 := min_le_left _ _
    have hc_le_targetdiv : c ≤ targetLam / lamρ := min_le_right _ _
    set ρ' : CQState X n := smulCQ c hc_nn hc_le_one ρ with hρ'_def
    have hlamρ'_le : minFeasibleLambda ρ' σ ≤ c * lamρ := by
      simpa [ρ', hlamρ_def] using minFeasibleLambda_smulCQ_le c hc_nn hc_le_one ρ σ hfeas_ρ
    have hlamρ'_le_target : minFeasibleLambda ρ' σ ≤ targetLam := by
      calc minFeasibleLambda ρ' σ
          ≤ c * lamρ := hlamρ'_le
        _ ≤ (targetLam / lamρ) * lamρ :=
            mul_le_mul_of_nonneg_right hc_le_targetdiv hlamρ_nn
        _ = targetLam := by field_simp
    have hP_le : CQState.purifiedDistance ρ ρ' ≤ ε := by
      have h := purifiedDistance_smulCQ_le_sqrt_weight c hc_nn hc_le_one ρ
      have hw_le_eps_sq : w ≤ ε ^ 2 := by simpa [hw_def] using hweight_le
      calc CQState.purifiedDistance ρ ρ'
          ≤ Real.sqrt w := by simpa [ρ', hw_def] using h
        _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hw_le_eps_sq
        _ = ε := hε_eq
    have hweight_ρ'_pos : 0 < ∑ x : X, (ρ'.stateMap x).trace := by
      have : (∑ x : X, (ρ'.stateMap x).trace) = c * w := by
        simpa [ρ', hw_def] using sum_smulCQ_stateMap_trace c hc_nn hc_le_one ρ
      rw [this]; exact mul_pos hc_pos hw_pos
    have hlamρ'_pos : 0 < minFeasibleLambda ρ' σ :=
      minFeasibleLambda_pos_of_posDef_of_weight_pos ρ' σ hσ_pd hweight_ρ'_pos
    have hH_lb : a + 1 ≤ conditionalMinEntropyReal ρ' σ :=
      conditionalMinEntropyReal_ge_of_minFeasibleLambda_le_exp_neg_mul_log_two
        ρ' σ (a + 1) hlamρ'_pos hlamρ'_le_target
    exact ⟨conditionalMinEntropyReal ρ' σ, ⟨ρ', rfl, hP_le⟩, by linarith⟩
  · -- Zero-weight branch: ρ has all blocks zero; witness `maxMixedAt x₀ k`.
    push_neg at hw_pos
    have hw_zero : w = 0 := le_antisymm hw_pos hw_nn
    have hρ_blocks_zero : ∀ x : X, (ρ.stateMap x).toOp = 0 := by
      intro x
      apply cqState_stateMap_toOp_eq_zero_of_weight_nonpos
      intro hpos
      have : 0 < w := by simpa [hw_def] using hpos
      linarith
    obtain ⟨x₀⟩ := ‹Nonempty X›
    set m₀ : CQState X n := maxMixedAt n x₀ 1 zero_le_one le_rfl with hm₀_def
    have hfeas_m₀ : hasFeasibleLambda m₀ σ := hasFeasibleLambda_of_posDef m₀ σ hσ_pd
    set L₀ : ℝ := minFeasibleLambda m₀ σ with hL₀_def
    have hL₀_nn : 0 ≤ L₀ := minFeasibleLambda_nonneg m₀ σ
    have hL₀1_pos : 0 < L₀ + 1 := by linarith
    set k : ℝ := min 1 (min (ε ^ 2 / 2) (targetLam / (L₀ + 1))) with hk_def
    have hε_sq_half_pos : 0 < ε ^ 2 / 2 := by positivity
    have htgtdiv_pos : 0 < targetLam / (L₀ + 1) := div_pos htgt_pos hL₀1_pos
    have hk_pos : 0 < k := lt_min (by norm_num) (lt_min hε_sq_half_pos htgtdiv_pos)
    have hk_nn : 0 ≤ k := le_of_lt hk_pos
    have hk_le_one : k ≤ 1 := min_le_left _ _
    have hk_le_eps_sq_half : k ≤ ε ^ 2 / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hk_le_targetdiv : k ≤ targetLam / (L₀ + 1) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    set ρ' : CQState X n := maxMixedAt n x₀ k hk_nn hk_le_one with hρ'_def
    -- Blockwise scaling identity `ρ'.stateMap = k · m₀.stateMap`.
    have hblock : ∀ x : X, (ρ'.stateMap x).toOp = (k : ℂ) • (m₀.stateMap x).toOp := by
      intro x
      by_cases hx : x = x₀
      · subst hx
        rw [hρ'_def, maxMixedAt_stateMap_at, hm₀_def, maxMixedAt_stateMap_at]
        change (k : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed n)).toOp =
          (k : ℂ) • ((1 : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed n)).toOp)
        rw [one_smul]
      · rw [hρ'_def, maxMixedAt_stateMap_off x₀ k hk_nn hk_le_one hx,
          hm₀_def, maxMixedAt_stateMap_off x₀ 1 zero_le_one le_rfl hx]
        change (0 : Op n) = (k : ℂ) • (0 : Op n)
        rw [smul_zero]
    have hscale : ∀ {t : ℝ}, isFeasible m₀ σ t → isFeasible ρ' σ (k * t) := by
      intro t ht
      refine ⟨mul_nonneg hk_nn ht.1, fun x => ?_⟩
      rw [hblock x]
      have hscaled := opLe_smul_nonneg hk_nn (ht.2 x)
      have h_smul : ((k : ℂ) • (t : ℂ) • σ.toOp) = ((k * t : ℝ) : ℂ) • σ.toOp := by
        rw [smul_smul, ← Complex.ofReal_mul]
      rwa [h_smul] at hscaled
    have hlamρ'_le : minFeasibleLambda ρ' σ ≤ k * L₀ :=
      minFeasibleLambda_le_mul_of_isFeasible_scaling m₀ σ ρ' σ hk_nn hfeas_m₀ hscale
    have hlamρ'_le_target : minFeasibleLambda ρ' σ ≤ targetLam := by
      have hfrac : k * L₀ ≤ targetLam := by
        have h2 : (targetLam / (L₀ + 1)) * L₀ ≤ targetLam := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hL₀1_pos]
          nlinarith [htgt_pos.le, hL₀_nn]
        exact le_trans (mul_le_mul_of_nonneg_right hk_le_targetdiv hL₀_nn) h2
      exact le_trans hlamρ'_le hfrac
    have hP_le : CQState.purifiedDistance ρ ρ' ≤ ε := by
      have h := purifiedDistance_zero_maxMixedAt_le x₀ k hk_nn hk_le_one ρ hρ_blocks_zero
      have h2k_le : 2 * k ≤ ε ^ 2 := by linarith
      calc CQState.purifiedDistance ρ ρ'
          ≤ Real.sqrt (2 * k) := by simpa [ρ'] using h
        _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt h2k_le
        _ = ε := hε_eq
    have hweight_ρ'_pos : 0 < ∑ x : X, (ρ'.stateMap x).trace := by
      have hsum_ρ' : (∑ x : X, (ρ'.stateMap x).trace) = k := by
        simpa [ρ'] using sum_maxMixedAt_stateMap_trace (X := X) (n := n) x₀ k hk_nn hk_le_one
      rw [hsum_ρ']; exact hk_pos
    have hlamρ'_pos : 0 < minFeasibleLambda ρ' σ :=
      minFeasibleLambda_pos_of_posDef_of_weight_pos ρ' σ hσ_pd hweight_ρ'_pos
    have hH_lb : a + 1 ≤ conditionalMinEntropyReal ρ' σ :=
      conditionalMinEntropyReal_ge_of_minFeasibleLambda_le_exp_neg_mul_log_two
        ρ' σ (a + 1) hlamρ'_pos hlamρ'_le_target
    exact ⟨conditionalMinEntropyReal ρ' σ, ⟨ρ', rfl, hP_le⟩, by linarith⟩

/-- At positive radius, the signed real smoothing set against a positive-definite reference
is unbounded above whenever `weight(ρ) ≤ ε²`. -/
theorem smoothedSetReal_not_bddAbove_of_weight_le_eps_sq_of_posDef
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : SubDensityOp n) (hσ_pd : σ.toOp.PosDef) (ε : ℝ)
    (hε_pos : 0 < ε)
    (hweight_le : (∑ x : X, (ρ.stateMap x).trace) ≤ ε ^ 2) :
    ¬ BddAbove (setOf (isInSmoothedSetReal ε ρ σ)) := by
  rw [not_bddAbove_iff]
  intro a
  exact exists_gt_smoothedSetReal_of_posDef_of_weight_le_eps_sq ρ σ hσ_pd ε hε_pos hweight_le a
/-- Equal-weight centers have the same unboundedness behavior for signed smoothing at maximally
mixed references. -/
theorem smoothedSetReal_maxMixed_not_bddAbove_of_weight_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n m : ℕ} [NeZero n] [NeZero m]
    (ρn : CQState X n) (ρm : CQState X m) (ε : ℝ)
    (hε_nn : 0 ≤ ε)
    (hweight :
      (∑ x : X, (ρn.stateMap x).trace) =
        ∑ x : X, (ρm.stateMap x).trace)
    (hnot :
      ¬ BddAbove (setOf (isInSmoothedSetReal ε ρn
        (DensityOp.toSubDensityOp (DensityOp.maxMixed n))))) :
    ¬ BddAbove (setOf (isInSmoothedSetReal ε ρm
      (DensityOp.toSubDensityOp (DensityOp.maxMixed m)))) := by
  rcases lt_or_eq_of_le hε_nn with hε_pos | hε_eq
  · -- Strict `ε > 0` branch.
    have hweight_n_le_eps_sq :
        (∑ x : X, (ρn.stateMap x).trace) ≤ ε ^ 2 := by
      by_contra hlt
      push_neg at hlt
      exact hnot
        (smoothMinEntropyReal_bddAbove_of_eps_sq_lt_weight ε hε_pos.le ρn
          (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) hlt)
    have hweight_m_le_eps_sq :
        (∑ x : X, (ρm.stateMap x).trace) ≤ ε ^ 2 := by
      rw [← hweight]
      exact hweight_n_le_eps_sq
    exact
      smoothedSetReal_not_bddAbove_of_weight_le_eps_sq_of_posDef ρm
        (DensityOp.toSubDensityOp (DensityOp.maxMixed m))
        maxMixed_toSubDensityOp_posDef ε hε_pos hweight_m_le_eps_sq
  · -- ε = 0 branch: smoothed set is a singleton, contradicting `hnot`.
    exfalso
    apply hnot
    refine ⟨conditionalMinEntropyReal ρn
      (DensityOp.toSubDensityOp (DensityOp.maxMixed n)), ?_⟩
    intro h hh
    rcases hh with ⟨ρn', hh_eq, hd⟩
    haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card X) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
    have hP_nn : 0 ≤ CQState.purifiedDistance ρn ρn' := by
      unfold CQState.purifiedDistance
      exact purifiedDistance_nonneg ρn.toJointDensity ρn'.toJointDensity
    rw [← hε_eq] at hd
    have hd_eq : CQState.purifiedDistance ρn ρn' = 0 :=
      le_antisymm hd hP_nn
    have hJoint : ρn.toJointDensity = ρn'.toJointDensity :=
      (purifiedDistance_eq_zero_iff _ _).mp hd_eq
    have hH_eq :
        conditionalMinEntropyReal ρn
            (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) =
          conditionalMinEntropyReal ρn'
            (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) :=
      conditionalMinEntropyReal_congr_toJointDensity _ hJoint
    rw [hh_eq, ← hH_eq]

/-- If the marginal signed smoothing set at a maximally mixed reference is unbounded above, the
extension set is also unbounded above. -/
theorem smoothedSetReal_extension_maxMixed_not_bddAbove_of_marginal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (_hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (ε : ℝ)
    (hε_nn : 0 ≤ ε)
    (hnot :
      ¬ BddAbove (setOf (isInSmoothedSetReal ε ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))))) :
    ¬ BddAbove (setOf (isInSmoothedSetReal ε ρER
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))))) := by
  have hweight :
      (∑ x : X, (ρE.stateMap x).trace) =
        ∑ x : X, (ρER.stateMap x).trace := by
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [← _hblocks x, trace_partialTraceB]
  exact smoothedSetReal_maxMixed_not_bddAbove_of_weight_eq
    ρE ρER ε hε_nn hweight hnot


end InfoTheory.SmoothMinEntropy

end -- noncomputable section
