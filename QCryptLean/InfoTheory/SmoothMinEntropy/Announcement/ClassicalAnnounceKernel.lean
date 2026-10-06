import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty

/-!
# Classical announcement entropy charges

Classical announcement kernels preserve purified-distance bounds and transfer feasible
coefficients. Announcing a finite classical register costs at most its logarithmic cardinality,
expressed as an additive `ENNReal` penalty for smooth entropy.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **A.5a — the classical-announce constructor.**

Tensor every block of a CQ state on the right by an `x`-**dependent** sub-normalized block `K x`.
The classical register is unchanged and the quantum register grows from `dE` to `dE * dC`.

This is the `x`-dependent sibling of `CQState.tensorAncilla`: there the appended block is a single
fixed ancilla (decoupled from the secret, hence penalty-free); here it is the announcement itself,
a function of the classical value `x`. -/
def CQState.tensorRightKernel {X : Type*} [Fintype X] {dE dC : ℕ}
    (ρ : CQState X dE) (K : X → SubDensityOp dC) : CQState X (dE * dC) where
  stateMap x := (ρ.stateMap x).tensor (K x)
  weight_le_one := by
    refine le_trans (Finset.sum_le_sum (fun x _ => ?_)) ρ.weight_le_one
    rw [SubDensityOp.tensor_trace]
    exact mul_le_of_le_one_right (ρ.stateMap x).trace_nonneg (K x).trace_le_one

@[simp] lemma CQState.tensorRightKernel_stateMap {X : Type*} [Fintype X] {dE dC : ℕ}
    (ρ : CQState X dE) (K : X → SubDensityOp dC) (x : X) :
    (ρ.tensorRightKernel K).stateMap x = (ρ.stateMap x).tensor (K x) := rfl

/-- Normalised announce blocks preserve the total classical weight of a CQ state. -/
lemma CQState.tensorRightKernel_weight {X : Type*} [Fintype X] {dE dC : ℕ}
    (ρ : CQState X dE) (K : X → SubDensityOp dC) (hK : ∀ x, (K x).trace = 1) :
    ∑ x : X, ((ρ.tensorRightKernel K).stateMap x).trace = ∑ x : X, (ρ.stateMap x).trace := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [CQState.tensorRightKernel_stateMap, SubDensityOp.tensor_trace, hK x, mul_one]

/-- **The generic worst-case announce constant.**  Every sub-normalised block is dominated by
`dC` times the maximally mixed state, because a PSD operator of trace at most `1` has all
eigenvalues at most `1`, i.e. `K ≼ 1 = dC · (1/dC)`.  Announcing an arbitrary `dC`-dimensional
kernel therefore always costs at most `log₂ dC` bits — the classical bound.  A structured kernel
can do better: a factor that is already normalised on its own register (a uniformly averaged seed,
say) contributes `1`, not its dimension. -/
lemma opLe_toOp_dim_smul_maxMixed {dC : ℕ} [NeZero dC] (K : SubDensityOp dC) :
    opLe K.toOp ((dC : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp) := by
  have hone : ((dC : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp)
      = (1 : Op dC) := by
    rw [toSubDensityOp_maxMixed_toOp_eq, smul_smul]
    have hdC : (dC : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne dC)
    rw [mul_one_div, div_self hdC, one_smul]
  rw [hone]
  have hPSD : K.toOp.PosSemidef := posSemidefOp_implies_mathlib K.toPosSemidefOp
  have hblock : opLe K.toOp (Complex.ofReal K.toOp.trace.re • (1 : Op dC)) :=
    psd_opLe_trace_re_smul_one K.toOp hPSD
  refine opLe_trans hblock ?_
  intro v
  rw [quadraticForm_ofReal_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hmul := mul_le_mul_of_nonneg_right K.trace_le_one (quadraticForm_one_re_nonneg v)
  linarith [hmul]

/-- With no feasible scalar at all, the feasible optimum is the empty infimum `0`. -/
private lemma minFeasibleLambda_eq_zero_of_no_feasible {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (h : ¬ hasFeasibleLambda ρ σ) :
    minFeasibleLambda ρ σ = 0 := by
  have hempty : Set.ofPred (isFeasible ρ σ) = ∅ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun ht => h ⟨t, ht⟩
  rw [minFeasibleLambda, hempty, Real.sInf_empty]

/-- **A.5b — feasibility transfer, forwards.**

If `K x ≼ c · (1/dC)` for every `x`, then a scalar `t` feasible for `(ρ, σ)` scales to `c · t`
feasible for the announced pair `(ρ ⊗ K, σ ⊗ 1/dC)`: blockwise
`ρ_x ⊗ K x ≼ (t·σ) ⊗ (c/dC) = (c·t)·(σ ⊗ 1/dC)`. -/
lemma isFeasible_tensorRightKernel_of_isFeasible
    {X : Type*} [Fintype X] {dE dC : ℕ} [NeZero dC]
    (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x, opLe (K x).toOp
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp))
    {t : ℝ} (ht : isFeasible ρ σ t) :
    isFeasible (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) (c * t) := by
  refine ⟨mul_nonneg hc ht.1, fun x => ?_⟩
  have hmmPSD :
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp).PosSemidef :=
    (posSemidefOp_implies_mathlib
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toPosSemidefOp).smul
      (Complex.zero_le_real.mpr hc)
  have hbase :
      opLe ((ρ.stateMap x).toOp ⊗ (K x).toOp)
        (((Complex.ofReal t) • σ.toOp) ⊗
          ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp)) :=
    opLe_tensor_psd (ρ.stateMap x).isHermitian
      ((posSemidefOp_implies_mathlib σ.toPosSemidefOp).smul (Complex.zero_le_real.mpr ht.1))
      (posSemidefOp_implies_mathlib (K x).toPosSemidefOp) hmmPSD.isHermitian
      (ht.2 x) (hdom x)
  have hrw :
      (((Complex.ofReal t) • σ.toOp) ⊗
          ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp))
        = (Complex.ofReal (c * t)) • (σ.tensorMaxMixed dC).toOp := by
    change _ = (Complex.ofReal (c * t)) •
      (σ.toOp ⊗ (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp)
    rw [Quantum.TensorProducts.Op.tensor_smul_left,
      Quantum.TensorProducts.Op.tensor_smul_right, smul_smul, ← Complex.ofReal_mul]
    congr 2
    ring
  rw [CQState.tensorRightKernel_stateMap,
    show ((ρ.stateMap x).tensor (K x)).toOp = (ρ.stateMap x).toOp ⊗ (K x).toOp from rfl, ← hrw]
  exact hbase

/-- **A.5b′ — feasibility transfer, backwards, with no penalty.**

Because every announce block is normalised, the partial trace over the announcement register maps
`ρ_x ⊗ K x ↦ ρ_x` and `t·(σ ⊗ 1/dC) ↦ t·σ`, so a feasible scalar for the announced pair is
feasible for the base pair with the **same** `t`.  This is what lets the unsmoothed bound below
dispense with a feasibility hypothesis. -/
lemma isFeasible_of_isFeasible_tensorRightKernel
    {X : Type*} [Fintype X] {dE dC : ℕ} [NeZero dC]
    (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).trace = 1) {t : ℝ}
    (h : isFeasible (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) t) :
    isFeasible ρ σ t := by
  refine ⟨h.1, fun x => ?_⟩
  have hx := h.2 x
  rw [CQState.tensorRightKernel_stateMap,
    show ((ρ.stateMap x).tensor (K x)).toOp = (ρ.stateMap x).toOp ⊗ (K x).toOp from rfl,
    show (Complex.ofReal t) • (σ.tensorMaxMixed dC).toOp
        = ((Complex.ofReal t) • σ.toOp) ⊗
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp from
      (Quantum.TensorProducts.Op.tensor_smul_left _ _ _).symm] at hx
  have hpt := partialTraceB_opLe_of_opLe hx
  rw [partialTraceB_tensor_op, partialTraceB_tensor_op] at hpt
  have htrK : Matrix.trace (K x).toOp = 1 := by
    refine Complex.ext ?_ ?_
    · change (K x).trace = _
      rw [hK x]; rfl
    · rw [(K x).trace_im_eq_zero]; rfl
  have htrMM : Matrix.trace (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp = 1 :=
    (DensityOp.maxMixed dC).trace_one
  rwa [htrK, htrMM, one_smul, one_smul] at hpt

/-- **A.5c — the unsmoothed classical-announce bound.**

Announcing `K` into the conditioning register costs at most `log₂ c`, where `c` is the domination
constant of `hdom`.  No feasibility hypothesis is needed: both degenerate branches close, the
`λ = 0` one because `λ_announced ≤ c·λ_base`, the infeasible one because feasibility descends
(`isFeasible_of_isFeasible_tensorRightKernel`).  `1 ≤ c` rather than `0 < c` is the right
hypothesis for exactly the reason recorded on
`conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling_sameState`: at the sentinel the claim
reduces to `−log c / log 2 ≤ 0`. -/
theorem conditionalMinEntropyReal_tensorRightKernel_ge_sub_log
    {X : Type*} [Fintype X] [Nonempty X] {dE dC : ℕ} [NeZero dC]
    (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC) {c : ℝ} (hc : 1 ≤ c)
    (hK : ∀ x, (K x).trace = 1)
    (hdom : ∀ x, opLe (K x).toOp
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp)) :
    conditionalMinEntropyReal ρ σ - Real.log c / Real.log 2 ≤
      conditionalMinEntropyReal (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) := by
  have hc0 : (0 : ℝ) ≤ c := le_trans zero_le_one hc
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hpen : 0 ≤ Real.log c / Real.log 2 :=
    div_nonneg (Real.log_nonneg hc) hlog2.le
  by_cases hfeas : hasFeasibleLambda ρ σ
  · have hscale : ∀ {t : ℝ}, isFeasible ρ σ t →
        isFeasible (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) (c * t) :=
      fun {_} ht => isFeasible_tensorRightKernel_of_isFeasible ρ σ K hc0 hdom ht
    have hlamB_le : minFeasibleLambda (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) ≤
        c * minFeasibleLambda ρ σ :=
      minFeasibleLambda_le_mul_of_isFeasible_scaling ρ σ (ρ.tensorRightKernel K)
        (σ.tensorMaxMixed dC) hc0 hfeas hscale
    rcases eq_or_lt_of_le (minFeasibleLambda_nonneg ρ σ) with hlamA0 | hlamApos
    · -- Base optimum is the sentinel `0`; so is the announced one.
      have hlamB0 : minFeasibleLambda (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) = 0 := by
        refine le_antisymm ?_ (minFeasibleLambda_nonneg _ _)
        rw [← hlamA0, mul_zero] at hlamB_le; exact hlamB_le
      unfold conditionalMinEntropyReal
      rw [← hlamA0, hlamB0, Real.log_zero, neg_zero, zero_div]
      linarith
    · -- Nondegenerate branch: positive base weight lifts to a positive announced optimum.
      have hwρ : 0 < ∑ x : X, (ρ.stateMap x).trace := by
        by_contra hw
        have hzero := CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρ hw
        have hfeas0 : isFeasible ρ σ 0 :=
          ⟨le_refl 0, fun x => by
            rw [hzero x, Complex.ofReal_zero, zero_smul]; exact fun _ => le_refl _⟩
        have := minFeasibleLambda_le_of_isFeasible ρ σ hfeas0
        linarith
      have hwB : 0 < ∑ x : X, ((ρ.tensorRightKernel K).stateMap x).trace := by
        rw [CQState.tensorRightKernel_weight ρ K hK]; exact hwρ
      have hfeasB : hasFeasibleLambda (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) := by
        obtain ⟨t, ht⟩ := hfeas
        exact ⟨c * t, hscale ht⟩
      have hlamBpos : 0 < minFeasibleLambda (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) :=
        minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos _ _ hwB hfeasB
      exact conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling ρ σ
        (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) hcpos hfeas hlamApos hlamBpos hscale
  · -- No feasible scalar for the base pair; feasibility descends, so none for the announced pair.
    have hfeasB : ¬ hasFeasibleLambda (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) := by
      rintro ⟨t, ht⟩
      exact hfeas ⟨t, isFeasible_of_isFeasible_tensorRightKernel ρ σ K hK ht⟩
    unfold conditionalMinEntropyReal
    rw [minFeasibleLambda_eq_zero_of_no_feasible ρ σ hfeas,
      minFeasibleLambda_eq_zero_of_no_feasible _ _ hfeasB,
      Real.log_zero, neg_zero, zero_div]
    linarith

/-- **A.5d — the smoothing ball transports at the same radius.**

Because every announce block is normalised (`hK`), the per-block fidelities and the total traces
are preserved exactly, so the generalized fidelity is unchanged and the CQ purified distance does
not increase.  Contrast `CQState.purifiedDistance_tensorRightSub_le`, where the constant ancilla
may be sub-normalised and a Bhattacharyya step is needed. -/
lemma CQState.purifiedDistance_tensorRightKernel_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dC : ℕ} [NeZero dE] [NeZero dC] [NeZero (dE * dC)]
    (ρ σ : CQState X dE) (K : X → SubDensityOp dC) (hK : ∀ x, (K x).trace = 1) :
    CQState.purifiedDistance (ρ.tensorRightKernel K) (σ.tensorRightKernel K) ≤
      CQState.purifiedDistance ρ σ := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (dE * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne _)⟩
  have : NeZero ((dE * dC) * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (dE * dC)) (NeZero.ne _)⟩
  unfold CQState.purifiedDistance
  apply purifiedDistance_le_of_fidelityGen_ge
  have htr_ρ : (ρ.tensorRightKernel K).toJointDensity.trace = ρ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [CQState.tensorRightKernel_stateMap, SubDensityOp.tensor_trace, hK x, mul_one]
  have htr_σ : (σ.tensorRightKernel K).toJointDensity.trace = σ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [CQState.tensorRightKernel_stateMap, SubDensityOp.tensor_trace, hK x, mul_one]
  have hfid : Quantum.Metrics.fidelity (ρ.tensorRightKernel K).toJointDensity.toPosSemidefOp
        (σ.tensorRightKernel K).toJointDensity.toPosSemidefOp
      = Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
        σ.toJointDensity.toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity
        (ρ := ρ.tensorRightKernel K) (σ := σ.tensorRightKernel K),
      CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity (ρ := ρ) (σ := σ)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [CQState.tensorRightKernel_stateMap, CQState.tensorRightKernel_stateMap]
    have hbρ : ((ρ.stateMap x).tensor (K x)).toPosSemidefOp
        = (ρ.stateMap x).toPosSemidefOp.tensor (K x).toPosSemidefOp := by
      apply Quantum.Operators.PosSemidefOp.ext; rfl
    have hbσ : ((σ.stateMap x).tensor (K x)).toPosSemidefOp
        = (σ.stateMap x).toPosSemidefOp.tensor (K x).toPosSemidefOp := by
      apply Quantum.Operators.PosSemidefOp.ext; rfl
    rw [hbρ, hbσ, Quantum.Metrics.fidelity_tensor_mul, Quantum.Metrics.fidelity_self_posSemidefOp]
    change _ * (K x).trace = _
    rw [hK x, mul_one]
  unfold fidelityGen
  rw [htr_ρ, htr_σ, hfid]

/-! ## A.5′ — the announcement in the HIGH digit

`Op.tensor A B` puts `A` in the high digit of the product index, so `CQState.tensorRightKernel`
leaves the announcement in the LOW digits of the quantum register: `(E R) ⊗ C`.  A consumer whose
index arithmetic is fixed by a channel definition may need the opposite orientation, `C ⊗ (E R)`.
The whole seam mirrors, because every ingredient is orientation-symmetric:

* the forward feasibility transfer runs on `opLe_tensor_psd`, which is stated for a general
  `A ⊗ C ≼ B ⊗ D`;
* the backward transfer runs on the partial trace of the announcement register, which is
  `partialTraceA` instead of `partialTraceB` (`partialTraceA_opLe_of_opLe` below is the mirror of
  `Quantum.Operators.partialTraceB_opLe_of_opLe`);
* the smoothing-ball transport runs on `Quantum.Metrics.fidelity_tensor_mul`, which is symmetric
  in the two factors.

Nothing below is a new result; each declaration is the mirror image of its `…RightKernel…` twin
above, with the same statement content.
-/

/-- **Löwner-monotonicity of the partial trace over the first factor.**

If `A ≼ B` on `R ⊗ E`, then `Tr_R A ≼ Tr_R B` on `E`.  This is the mirror of
`Quantum.Operators.partialTraceB_opLe_of_opLe` (`Quantum/TensorProducts/PSDOrder.lean`), with
`leftBlockVector` / `quadraticForm_partialTraceA_re_eq_sum` in place of the right-block twins.
Its natural home is beside that lemma in `PSDOrder.lean`; it is declared here so that adding it
does not re-fire the whole library's rebuild cone. -/
theorem partialTraceA_opLe_of_opLe {dR dE : ℕ} {A B : Op (dR * dE)} (h : opLe A B) :
    opLe (Quantum.TensorProducts.partialTraceA A) (Quantum.TensorProducts.partialTraceA B) := by
  intro v
  rw [quadraticForm_partialTraceA_re_eq_sum, quadraticForm_partialTraceA_re_eq_sum]
  exact Finset.sum_le_sum (fun k _ => h (leftBlockVector k v))

/-- Tensor the normalized maximally mixed reference on a register of dimension `dR` onto the
**left** of a sub-normalized operator.  Mirror of `SubDensityOp.tensorMaxMixed`
(`ExtensionPenalty.lean`), whose natural home it shares. -/
def SubDensityOp.maxMixedTensor {dE : ℕ} (dR : ℕ) [NeZero dR]
    (ρ : SubDensityOp dE) : SubDensityOp (dR * dE) where
  toOp := (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toOp ⊗ ρ.toOp
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Quantum.TensorProducts.Op.tensor_conjTranspose,
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).isHermitian, ρ.isHermitian]
  pos_semidef :=
    Op.tensor_posSemidef (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toOp ρ.toOp
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).isHermitian ρ.isHermitian
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).pos_semidef ρ.pos_semidef
  trace_le_one := by
    rw [Op.trace_tensor,
      show (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toOp.trace = 1 from
        (DensityOp.maxMixed dR).trace_one, one_mul]
    exact ρ.trace_le_one

@[simp] lemma SubDensityOp.maxMixedTensor_toOp {dE dR : ℕ} [NeZero dR] (ρ : SubDensityOp dE) :
    (ρ.maxMixedTensor dR).toOp =
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toOp ⊗ ρ.toOp := rfl

/-- **A.5a′ — the classical-announce constructor, announcement in the high digit.**

Mirror of `CQState.tensorRightKernel`: the announced block is tensored on the **left**, so the
quantum register grows from `dE` to `dC * dE` with the announcement in the high digits. -/
def CQState.tensorLeftKernel {X : Type*} [Fintype X] {dE dC : ℕ}
    (ρ : CQState X dE) (K : X → SubDensityOp dC) : CQState X (dC * dE) where
  stateMap x := (K x).tensor (ρ.stateMap x)
  weight_le_one := by
    refine le_trans (Finset.sum_le_sum (fun x _ => ?_)) ρ.weight_le_one
    rw [SubDensityOp.tensor_trace]
    exact mul_le_of_le_one_left (ρ.stateMap x).trace_nonneg (K x).trace_le_one

@[simp] lemma CQState.tensorLeftKernel_stateMap {X : Type*} [Fintype X] {dE dC : ℕ}
    (ρ : CQState X dE) (K : X → SubDensityOp dC) (x : X) :
    (ρ.tensorLeftKernel K).stateMap x = (K x).tensor (ρ.stateMap x) := rfl

/-- Normalised announce blocks preserve the total classical weight. -/
lemma CQState.tensorLeftKernel_weight {X : Type*} [Fintype X] {dE dC : ℕ}
    (ρ : CQState X dE) (K : X → SubDensityOp dC) (hK : ∀ x, (K x).trace = 1) :
    ∑ x : X, ((ρ.tensorLeftKernel K).stateMap x).trace = ∑ x : X, (ρ.stateMap x).trace := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [CQState.tensorLeftKernel_stateMap, SubDensityOp.tensor_trace, hK x, one_mul]

/-- **A.5b′ — feasibility transfer, forwards.**  Mirror of
`isFeasible_tensorRightKernel_of_isFeasible`. -/
lemma isFeasible_tensorLeftKernel_of_isFeasible
    {X : Type*} [Fintype X] {dE dC : ℕ} [NeZero dC]
    (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x, opLe (K x).toOp
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp))
    {t : ℝ} (ht : isFeasible ρ σ t) :
    isFeasible (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) (c * t) := by
  refine ⟨mul_nonneg hc ht.1, fun x => ?_⟩
  have hmmPSD :
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp).PosSemidef :=
    (posSemidefOp_implies_mathlib
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toPosSemidefOp).smul
      (Complex.zero_le_real.mpr hc)
  have hbase :
      opLe ((K x).toOp ⊗ (ρ.stateMap x).toOp)
        (((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp) ⊗
          ((Complex.ofReal t) • σ.toOp)) :=
    opLe_tensor_psd (K x).isHermitian hmmPSD
      (posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)
      ((posSemidefOp_implies_mathlib σ.toPosSemidefOp).smul
        (Complex.zero_le_real.mpr ht.1)).isHermitian
      (hdom x) (ht.2 x)
  have hrw :
      (((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp) ⊗
          ((Complex.ofReal t) • σ.toOp))
        = (Complex.ofReal (c * t)) • (σ.maxMixedTensor dC).toOp := by
    change _ = (Complex.ofReal (c * t)) •
      ((DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp ⊗ σ.toOp)
    rw [Quantum.TensorProducts.Op.tensor_smul_left,
      Quantum.TensorProducts.Op.tensor_smul_right, smul_smul, ← Complex.ofReal_mul]
  rw [CQState.tensorLeftKernel_stateMap,
    show ((K x).tensor (ρ.stateMap x)).toOp = (K x).toOp ⊗ (ρ.stateMap x).toOp from rfl, ← hrw]
  exact hbase

/-- **A.5b″ — feasibility transfer, backwards, with no penalty.**  Mirror of
`isFeasible_of_isFeasible_tensorRightKernel`, tracing out the announcement register with
`partialTraceA`. -/
lemma isFeasible_of_isFeasible_tensorLeftKernel
    {X : Type*} [Fintype X] {dE dC : ℕ} [NeZero dC]
    (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).trace = 1) {t : ℝ}
    (h : isFeasible (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) t) :
    isFeasible ρ σ t := by
  refine ⟨h.1, fun x => ?_⟩
  have hx := h.2 x
  rw [CQState.tensorLeftKernel_stateMap,
    show ((K x).tensor (ρ.stateMap x)).toOp = (K x).toOp ⊗ (ρ.stateMap x).toOp from rfl,
    show (Complex.ofReal t) • (σ.maxMixedTensor dC).toOp
        = (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp ⊗
            ((Complex.ofReal t) • σ.toOp) from
      (Quantum.TensorProducts.Op.tensor_smul_right _ _ _).symm] at hx
  have hpt := partialTraceA_opLe_of_opLe hx
  rw [partialTraceA_tensor_op, partialTraceA_tensor_op] at hpt
  have htrK : Matrix.trace (K x).toOp = 1 := by
    refine Complex.ext ?_ ?_
    · change (K x).trace = _
      rw [hK x]; rfl
    · rw [(K x).trace_im_eq_zero]; rfl
  have htrMM : Matrix.trace (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp = 1 :=
    (DensityOp.maxMixed dC).trace_one
  rwa [htrK, htrMM, one_smul, one_smul] at hpt

/-- **A.5c′ — the unsmoothed classical-announce bound, announcement in the high digit.**
Mirror of `conditionalMinEntropyReal_tensorRightKernel_ge_sub_log`. -/
theorem conditionalMinEntropyReal_tensorLeftKernel_ge_sub_log
    {X : Type*} [Fintype X] [Nonempty X] {dE dC : ℕ} [NeZero dC]
    (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC) {c : ℝ} (hc : 1 ≤ c)
    (hK : ∀ x, (K x).trace = 1)
    (hdom : ∀ x, opLe (K x).toOp
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp)) :
    conditionalMinEntropyReal ρ σ - Real.log c / Real.log 2 ≤
      conditionalMinEntropyReal (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) := by
  have hc0 : (0 : ℝ) ≤ c := le_trans zero_le_one hc
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hpen : 0 ≤ Real.log c / Real.log 2 :=
    div_nonneg (Real.log_nonneg hc) hlog2.le
  by_cases hfeas : hasFeasibleLambda ρ σ
  · have hscale : ∀ {t : ℝ}, isFeasible ρ σ t →
        isFeasible (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) (c * t) :=
      fun {_} ht => isFeasible_tensorLeftKernel_of_isFeasible ρ σ K hc0 hdom ht
    have hlamB_le : minFeasibleLambda (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) ≤
        c * minFeasibleLambda ρ σ :=
      minFeasibleLambda_le_mul_of_isFeasible_scaling ρ σ (ρ.tensorLeftKernel K)
        (σ.maxMixedTensor dC) hc0 hfeas hscale
    rcases eq_or_lt_of_le (minFeasibleLambda_nonneg ρ σ) with hlamA0 | hlamApos
    · have hlamB0 : minFeasibleLambda (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) = 0 := by
        refine le_antisymm ?_ (minFeasibleLambda_nonneg _ _)
        rw [← hlamA0, mul_zero] at hlamB_le; exact hlamB_le
      unfold conditionalMinEntropyReal
      rw [← hlamA0, hlamB0, Real.log_zero, neg_zero, zero_div]
      linarith
    · have hwρ : 0 < ∑ x : X, (ρ.stateMap x).trace := by
        by_contra hw
        have hzero := CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρ hw
        have hfeas0 : isFeasible ρ σ 0 :=
          ⟨le_refl 0, fun x => by
            rw [hzero x, Complex.ofReal_zero, zero_smul]; exact fun _ => le_refl _⟩
        have := minFeasibleLambda_le_of_isFeasible ρ σ hfeas0
        linarith
      have hwB : 0 < ∑ x : X, ((ρ.tensorLeftKernel K).stateMap x).trace := by
        rw [CQState.tensorLeftKernel_weight ρ K hK]; exact hwρ
      have hfeasB : hasFeasibleLambda (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) := by
        obtain ⟨t, ht⟩ := hfeas
        exact ⟨c * t, hscale ht⟩
      have hlamBpos : 0 < minFeasibleLambda (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) :=
        minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos _ _ hwB hfeasB
      exact conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling ρ σ
        (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) hcpos hfeas hlamApos hlamBpos hscale
  · have hfeasB : ¬ hasFeasibleLambda (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) := by
      rintro ⟨t, ht⟩
      exact hfeas ⟨t, isFeasible_of_isFeasible_tensorLeftKernel ρ σ K hK ht⟩
    unfold conditionalMinEntropyReal
    rw [minFeasibleLambda_eq_zero_of_no_feasible ρ σ hfeas,
      minFeasibleLambda_eq_zero_of_no_feasible _ _ hfeasB,
      Real.log_zero, neg_zero, zero_div]
    linarith

/-- **A.5d′ — the smoothing ball transports at the same radius.**  Mirror of
`CQState.purifiedDistance_tensorRightKernel_le`. -/
lemma CQState.purifiedDistance_tensorLeftKernel_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dC : ℕ} [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    (ρ σ : CQState X dE) (K : X → SubDensityOp dC) (hK : ∀ x, (K x).trace = 1) :
    CQState.purifiedDistance (ρ.tensorLeftKernel K) (σ.tensorLeftKernel K) ≤
      CQState.purifiedDistance ρ σ := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (dE * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne _)⟩
  have : NeZero ((dC * dE) * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (dC * dE)) (NeZero.ne _)⟩
  unfold CQState.purifiedDistance
  apply purifiedDistance_le_of_fidelityGen_ge
  have htr_ρ : (ρ.tensorLeftKernel K).toJointDensity.trace = ρ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [CQState.tensorLeftKernel_stateMap, SubDensityOp.tensor_trace, hK x, one_mul]
  have htr_σ : (σ.tensorLeftKernel K).toJointDensity.trace = σ.toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [CQState.tensorLeftKernel_stateMap, SubDensityOp.tensor_trace, hK x, one_mul]
  have hfid : Quantum.Metrics.fidelity (ρ.tensorLeftKernel K).toJointDensity.toPosSemidefOp
        (σ.tensorLeftKernel K).toJointDensity.toPosSemidefOp
      = Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
        σ.toJointDensity.toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity
        (ρ := ρ.tensorLeftKernel K) (σ := σ.tensorLeftKernel K),
      CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity (ρ := ρ) (σ := σ)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [CQState.tensorLeftKernel_stateMap, CQState.tensorLeftKernel_stateMap]
    have hbρ : ((K x).tensor (ρ.stateMap x)).toPosSemidefOp
        = (K x).toPosSemidefOp.tensor (ρ.stateMap x).toPosSemidefOp := by
      apply Quantum.Operators.PosSemidefOp.ext; rfl
    have hbσ : ((K x).tensor (σ.stateMap x)).toPosSemidefOp
        = (K x).toPosSemidefOp.tensor (σ.stateMap x).toPosSemidefOp := by
      apply Quantum.Operators.PosSemidefOp.ext; rfl
    rw [hbρ, hbσ, Quantum.Metrics.fidelity_tensor_mul, Quantum.Metrics.fidelity_self_posSemidefOp]
    change (K x).trace * _ = _
    rw [hK x, one_mul]
  unfold fidelityGen
  rw [htr_ρ, htr_σ, hfid]

/-- A normalized announcement kernel costs at most the positive part of `log₂ c` in
extended smooth entropy. -/
theorem smoothMinEntropy_tensorRightKernel_ge_sub_log
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dC : ℕ} [NeZero dE] [NeZero dC] [NeZero (dE * dC)]
    (ε : ℝ) (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC)
    {c : ℝ} (hc : 1 ≤ c) (hK : ∀ x, (K x).trace = 1)
    (hdom : ∀ x, opLe (K x).toOp
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp)) :
    smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) +
        ENNReal.ofReal (Real.log c / Real.log 2) := by
  apply smoothMinEntropy_le_add_of_transport
  intro τ hd
  refine ⟨τ.tensorRightKernel K,
    (CQState.purifiedDistance_tensorRightKernel_le ρ τ K hK).trans hd, ?_⟩
  intro k hk
  rw [two_rpow_neg_sub_log k (lt_of_lt_of_le zero_lt_one hc)]
  exact isFeasible_tensorRightKernel_of_isFeasible τ σ K (zero_le_one.trans hc) hdom hk

/-- A normalized announcement kernel costs at most the positive part of `log₂ c` in
extended smooth entropy. -/
theorem smoothMinEntropy_tensorLeftKernel_ge_sub_log
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dC : ℕ} [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    (ε : ℝ) (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC)
    {c : ℝ} (hc : 1 ≤ c) (hK : ∀ x, (K x).trace = 1)
    (hdom : ∀ x, opLe (K x).toOp
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp)) :
    smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) +
        ENNReal.ofReal (Real.log c / Real.log 2) := by
  apply smoothMinEntropy_le_add_of_transport
  intro τ hd
  refine ⟨τ.tensorLeftKernel K,
    (CQState.purifiedDistance_tensorLeftKernel_le ρ τ K hK).trans hd, ?_⟩
  intro k hk
  rw [two_rpow_neg_sub_log k (lt_of_lt_of_le zero_lt_one hc)]
  exact isFeasible_tensorLeftKernel_of_isFeasible τ σ K (zero_le_one.trans hc) hdom hk


/-- Appending a normalized right kernel dominated by `c` times the maximally mixed state costs
at most `log c / log 2` in signed smooth min-entropy. -/
theorem smoothMinEntropyReal_tensorRightKernel_ge_sub_log
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dC : ℕ} [NeZero dE] [NeZero dC] [NeZero (dE * dC)]
    (ε : ℝ) (hε : 0 ≤ ε) (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC)
    {c : ℝ} (hc : 1 ≤ c) (hK : ∀ x, (K x).trace = 1)
    (hdom : ∀ x, opLe (K x).toOp
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp))
    (hbdd : BddAbove
      (Set.ofPred (isInSmoothedSetReal ε (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC)))) :
    smoothMinEntropyReal ε ρ σ - Real.log c / Real.log 2 ≤
      smoothMinEntropyReal ε (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC) := by
  have key : ∀ a ∈ Set.ofPred (isInSmoothedSetReal ε ρ σ),
      ∃ b ∈ Set.ofPred (isInSmoothedSetReal ε (ρ.tensorRightKernel K) (σ.tensorMaxMixed dC)),
        a - Real.log c / Real.log 2 ≤ b := by
    intro a ha
    obtain ⟨blockbar, rfl, hd⟩ := ha
    refine ⟨conditionalMinEntropyReal (blockbar.tensorRightKernel K) (σ.tensorMaxMixed dC),
      ⟨blockbar.tensorRightKernel K, rfl, ?_⟩, ?_⟩
    · exact le_trans (CQState.purifiedDistance_tensorRightKernel_le ρ blockbar K hK) hd
    · exact conditionalMinEntropyReal_tensorRightKernel_ge_sub_log blockbar σ K hc hK hdom
  exact csSup_sub_le_csSup_of_forall_exists_sub_le _ _ (Real.log c / Real.log 2)
    (smoothedSetReal_nonempty hε ρ σ) hbdd key

/-- Appending a normalized left kernel dominated by `c` times the maximally mixed state costs at
most `log c / log 2` in signed smooth min-entropy. -/
theorem smoothMinEntropyReal_tensorLeftKernel_ge_sub_log
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dC : ℕ} [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    (ε : ℝ) (hε : 0 ≤ ε) (ρ : CQState X dE) (σ : SubDensityOp dE) (K : X → SubDensityOp dC)
    {c : ℝ} (hc : 1 ≤ c) (hK : ∀ x, (K x).trace = 1)
    (hdom : ∀ x, opLe (K x).toOp
      ((c : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed dC)).toOp))
    (hbdd : BddAbove
      (Set.ofPred (isInSmoothedSetReal ε (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC)))) :
    smoothMinEntropyReal ε ρ σ - Real.log c / Real.log 2 ≤
      smoothMinEntropyReal ε (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC) := by
  have key : ∀ a ∈ Set.ofPred (isInSmoothedSetReal ε ρ σ),
      ∃ b ∈ Set.ofPred (isInSmoothedSetReal ε (ρ.tensorLeftKernel K) (σ.maxMixedTensor dC)),
        a - Real.log c / Real.log 2 ≤ b := by
    intro a ha
    obtain ⟨blockbar, rfl, hd⟩ := ha
    refine ⟨conditionalMinEntropyReal (blockbar.tensorLeftKernel K) (σ.maxMixedTensor dC),
      ⟨blockbar.tensorLeftKernel K, rfl, ?_⟩, ?_⟩
    · exact le_trans (CQState.purifiedDistance_tensorLeftKernel_le ρ blockbar K hK) hd
    · exact conditionalMinEntropyReal_tensorLeftKernel_ge_sub_log blockbar σ K hc hK hdom
  exact csSup_sub_le_csSup_of_forall_exists_sub_le _ _ (Real.log c / Real.log 2)
    (smoothedSetReal_nonempty hε ρ σ) hbdd key

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
