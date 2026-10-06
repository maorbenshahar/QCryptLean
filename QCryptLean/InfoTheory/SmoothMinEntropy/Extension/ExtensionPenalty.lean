import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.DimensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.SmoothPartialTrace
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.TensorMaxMixedDistance
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.CQExtensionFiber
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.Quantum.Metrics.FidelityOrder

/-!
# Register-extension entropy bounds

Feasible-coefficient transport compares a CQ extension with its marginal at the same smoothing
radius. Maximally mixed and free-reference constructions produce finite logarithmic dimension
penalties, written additively for extended smooth entropy. Signed conditional entropy identities
support the coefficient calculations.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder Pointwise

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The `(toSubDensityOp (maxMixed d)).toOp` operator is `(1 / d) • 1`. -/
lemma toSubDensityOp_maxMixed_toOp_eq (d : ℕ) [NeZero d] :
    (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp =
      ((1 / d : ℂ) • (1 : Op d)) := by
  rfl

private lemma ofReal_nat_sq_mul_inv_natCast (d : ℕ) [NeZero d] :
    Complex.ofReal ((d : ℝ) ^ 2) * (1 / (d : ℂ)) =
      Complex.ofReal (d : ℝ) := by
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne d)]

/-- Scaling the `E` maximally mixed reference tensored with `1_R` gives the
maximally mixed reference on `E ⊗ R` with the `(dim R)^2` factor. -/
lemma right_dim_smul_maxMixed_tensor_one_eq_sq_smul_maxMixed
    {dE dR : ℕ} [NeZero dE] [NeZero dR] (t : ℝ) :
    (Complex.ofReal (dR : ℝ)) •
        (((Complex.ofReal t) •
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp) ⊗
          (1 : Op dR)) =
      (Complex.ofReal ((dR : ℝ) ^ 2 * t)) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))).toOp := by
  calc
    (Complex.ofReal (dR : ℝ)) •
        (((Complex.ofReal t) •
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp) ⊗
          (1 : Op dR))
        = (Complex.ofReal (dR : ℝ)) •
            (((Complex.ofReal t) • ((1 / dE : ℂ) • (1 : Op dE))) ⊗
              (1 : Op dR)) := by
            rw [toSubDensityOp_maxMixed_toOp_eq]
    _ = (Complex.ofReal (dR : ℝ)) •
            (((Complex.ofReal t * (1 / dE : ℂ)) • (1 : Op dE)) ⊗
              (1 : Op dR)) := by
            rw [smul_smul]
    _ = (Complex.ofReal (dR : ℝ)) •
            ((Complex.ofReal t * (1 / dE : ℂ)) •
              ((1 : Op dE) ⊗ (1 : Op dR))) := by
            rw [Quantum.TensorProducts.Op.tensor_smul_left]
    _ = (Complex.ofReal (dR : ℝ)) •
            ((Complex.ofReal t * (1 / dE : ℂ)) • (1 : Op (dE * dR))) := by
            rw [Op.tensor_one]
    _ = (Complex.ofReal (dR : ℝ) *
            (Complex.ofReal t * (1 / dE : ℂ))) • (1 : Op (dE * dR)) := by
            rw [smul_smul]
    _ = (Complex.ofReal ((dR : ℝ) ^ 2 * t) *
            (1 / ((dE * dR : ℕ) : ℂ))) • (1 : Op (dE * dR)) := by
            congr 1
            push_cast
            field_simp [Nat.cast_ne_zero.mpr (NeZero.ne dE),
              Nat.cast_ne_zero.mpr (NeZero.ne dR)]
    _ = (Complex.ofReal ((dR : ℝ) ^ 2 * t)) •
            ((1 / ((dE * dR : ℕ) : ℂ)) • (1 : Op (dE * dR))) := by
            rw [smul_smul]
    _ = (Complex.ofReal ((dR : ℝ) ^ 2 * t)) •
            (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))).toOp := by
            rw [toSubDensityOp_maxMixed_toOp_eq]

/-- Feasibility lifts from the `E` marginal to an `E ⊗ R` extension with the
standard `(dim R)^2` cost for normalized maximally mixed references. -/
lemma isFeasible_extension_maxMixed_of_isFeasible
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    {t : ℝ}
    (ht :
      isFeasible ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t) :
    isFeasible ρER
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR)))
      ((dR : ℝ) ^ 2 * t) := by
  rcases ht with ⟨ht_nonneg, ht_dom⟩
  refine ⟨mul_nonneg (sq_nonneg _) ht_nonneg, fun x => ?_⟩
  -- `ρ_ER(x) ≤ d_R (ρ_E(x) ⊗ 1)`: the partial-trace bound, with `Tr_R ρ_ER(x) = ρ_E(x)`
  have hdom_ext := Quantum.Operators.opLe_le_card_smul_partialTraceB_tensor_one
    (posSemidefOp_implies_mathlib (ρER.stateMap x).toPosSemidefOp)
  rw [hblocks x] at hdom_ext
  -- `ρ_E(x) ⊗ 1 ≤ (t σ_E) ⊗ 1`, from the feasibility of `t`
  have htσE_psd : ((Complex.ofReal t) •
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp).PosSemidef :=
    (posSemidefOp_implies_mathlib
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toPosSemidefOp).smul
      (RCLike.ofReal_nonneg.mpr ht_nonneg)
  have ht_tensor := opLe_tensor_psd (C := (1 : Op dR)) (D := 1)
    (ρE.stateMap x).toPosSemidefOp.toHermitianOp.isHermitian htσE_psd Matrix.PosSemidef.one
    Matrix.isHermitian_one (ht_dom x) (fun _ => le_rfl)
  -- `d_R ((t σ_E) ⊗ 1) = (d_R² t) σ_ER`
  rw [← right_dim_smul_maxMixed_tensor_one_eq_sq_smul_maxMixed (dE := dE) (dR := dR) t]
  exact opLe_trans hdom_ext (opLe_smul_nonneg (Nat.cast_nonneg dR) ht_tensor)

/-- Feasible-lambda comparison for an extension whose per-outcome blocks have
the prescribed `E` marginal. With maximally mixed references, the normalized
reference on `E ⊗ R` costs a factor `(dim R)^2`. -/
theorem minFeasibleLambda_extension_maxMixed_le_dimR_sq
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (hfeasE :
      hasFeasibleLambda ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))) :
    minFeasibleLambda ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) ≤
      (dR : ℝ) ^ 2 *
        minFeasibleLambda ρE
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  let σER : SubDensityOp (dE * dR) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))
  let σE : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  let c : ℝ := (dR : ℝ) ^ 2
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact sq_nonneg _
  have hsub :
      c • setOf (isFeasible ρE σE) ⊆ setOf (isFeasible ρER σER) := by
    rintro u ⟨t, ht, rfl⟩
    have ht_lift :
        isFeasible ρER
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR)))
          ((dR : ℝ) ^ 2 * t) :=
      isFeasible_extension_maxMixed_of_isFeasible ρER ρE hblocks
        (by simpa [σE] using ht)
    simpa [σER, c, smul_eq_mul] using ht_lift
  have hscaled_nonempty : (c • setOf (isFeasible ρE σE) : Set ℝ).Nonempty := by
    obtain ⟨t, ht⟩ := hfeasE
    exact ⟨c • t, ⟨t, by simpa [σE] using ht, rfl⟩⟩
  have hle_scaled :
      sInf (setOf (isFeasible ρER σER)) ≤
        sInf (c • setOf (isFeasible ρE σE) : Set ℝ) :=
    csInf_le_csInf (minFeasibleLambda_bddBelow ρER σER) hscaled_nonempty hsub
  have hscaled_inf :
      sInf (c • setOf (isFeasible ρE σE) : Set ℝ) =
        c * sInf (setOf (isFeasible ρE σE)) := by
    simpa [smul_eq_mul] using
      Real.sInf_smul_of_nonneg hc_nonneg (setOf (isFeasible ρE σE))
  calc
    minFeasibleLambda ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR)))
        = sInf (setOf (isFeasible ρER σER)) := by
          simp [minFeasibleLambda, σER]
    _ ≤ sInf (c • setOf (isFeasible ρE σE) : Set ℝ) := hle_scaled
    _ = c * sInf (setOf (isFeasible ρE σE)) := hscaled_inf
    _ = (dR : ℝ) ^ 2 *
        minFeasibleLambda ρE
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
          simp [minFeasibleLambda, σE, c]

/-- Conditional min-entropy comparison for an extension controlled only through
its per-outcome partial trace.

The real-valued min-entropy API has explicit positivity side conditions because
`Real.log 0 = 0` is used as a boundary sentinel. -/
theorem conditionalMinEntropyReal_extension_maxMixed_ge_sub_twice_log_dim
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (hfeasE :
      hasFeasibleLambda ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)))
    (hposER :
      0 < minFeasibleLambda ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))))
    (hposE :
      0 < minFeasibleLambda ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))) :
    conditionalMinEntropyReal ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
        ((2 : ℝ) * Real.log (dR : ℝ)) / Real.log 2 ≤
      conditionalMinEntropyReal ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) := by
  let lamER :=
    minFeasibleLambda ρER
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR)))
  let lamE :=
    minFeasibleLambda ρE
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))
  have hlam : lamER ≤ (dR : ℝ) ^ 2 * lamE := by
    simpa [lamER, lamE] using
      minFeasibleLambda_extension_maxMixed_le_dimR_sq ρER ρE hblocks hfeasE
  have hposER' : 0 < lamER := by
    simpa [lamER] using hposER
  have hposE' : 0 < lamE := by
    simpa [lamE] using hposE
  have hdR_pos : 0 < (dR : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dR)
  have hdR_sq_pos : 0 < (dR : ℝ) ^ 2 :=
    sq_pos_of_pos hdR_pos
  have hdR_sq_ne : ((dR : ℝ) ^ 2) ≠ 0 :=
    ne_of_gt hdR_sq_pos
  have hlamE_ne : lamE ≠ 0 :=
    ne_of_gt hposE'
  have hlog_le : Real.log lamER ≤ Real.log (((dR : ℝ) ^ 2) * lamE) :=
    Real.log_le_log hposER' hlam
  have hlog_rhs :
      Real.log (((dR : ℝ) ^ 2) * lamE) =
        2 * Real.log (dR : ℝ) + Real.log lamE := by
    rw [Real.log_mul hdR_sq_ne hlamE_ne, Real.log_pow]
    norm_num
  have hlog_bound : Real.log lamER ≤ 2 * Real.log (dR : ℝ) + Real.log lamE := by
    simpa [hlog_rhs] using hlog_le
  have hlog2_pos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  unfold conditionalMinEntropyReal
  change
    -Real.log lamE / Real.log 2 -
        (2 * Real.log (dR : ℝ)) / Real.log 2 ≤
      -Real.log lamER / Real.log 2
  rw [← sub_div]
  have hnum : -Real.log lamE - 2 * Real.log (dR : ℝ) ≤ -Real.log lamER := by
    linarith
  exact div_le_div_of_nonneg_right hnum hlog2_pos.le

/-!
## Smoothed extension: radius cost for tensoring with maximally mixed register

The following results establish the smoothed counterpart of the unsmoothed
extension penalty. The key insight (Tomamichel 2016, Lemma 6.7): tensoring ρ with
the maximally mixed state on R lies within purified distance `extensionRadius dR`
of ρ itself (when ρ is viewed as a sub-normalized operator on E ⊗ R via the
trivial R-extension), so any ρ̃E in the ε-ball of ρE lifts to a state within
`ε + extensionRadius dR` of ρER. Moreover the lifted state has the same
conditional min-entropy against I/(dE·dR) as the original against I/dE — no
penalty — because the reference factorizes.
-/

/-- The extension radius for a reference register of dimension `dR`:
    `√(1 − 1/dR²)`. This is the purified distance from ρ to ρ ⊗ I/dR
    (Tomamichel 2016, §6.2.4). -/
noncomputable def extensionRadius (dR : ℕ) : ℝ :=
  Real.sqrt (1 - 1 / (dR : ℝ) ^ 2)

/-- The extension radius is nonneg. -/
lemma extensionRadius_nonneg (dR : ℕ) : 0 ≤ extensionRadius dR := Real.sqrt_nonneg _

/-- The extension radius for `dR = 1` is zero: `√(1 − 1/1²) = √0 = 0`. -/
@[simp]
lemma extensionRadius_one_eq_zero : extensionRadius 1 = 0 := by
  unfold extensionRadius
  norm_num

/-- The extension radius is monotone on positive arguments: if `1 ≤ dR ≤ dR'` then
    `extensionRadius dR ≤ extensionRadius dR'`, since `extensionRadius dR = √(1 − 1/dR²)`
    is increasing in `dR ≥ 1` because `1/dR²` is decreasing on positive integers.
    (Monotonicity can fail at `dR = 0` because division by zero is `0` in Lean.) -/
lemma extensionRadius_mono {dR dR' : ℕ} [NeZero dR] (h : dR ≤ dR') :
    extensionRadius dR ≤ extensionRadius dR' := by
  unfold extensionRadius
  apply Real.sqrt_le_sqrt
  have hdR_pos : (0 : ℝ) < dR := Nat.cast_pos.mpr (NeZero.pos dR)
  have hdR'_pos : (0 : ℝ) < dR' := by
    have : 0 < dR' := Nat.lt_of_lt_of_le (NeZero.pos dR) h
    exact Nat.cast_pos.mpr this
  have hcast : (dR : ℝ) ≤ dR' := Nat.cast_le.mpr h
  have hsq : (dR : ℝ) ^ 2 ≤ (dR' : ℝ) ^ 2 := by nlinarith
  have hdR_sq_pos : (0 : ℝ) < (dR : ℝ) ^ 2 := by positivity
  have hinv : 1 / (dR' : ℝ) ^ 2 ≤ 1 / (dR : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) hdR_sq_pos hsq
  linarith

/-- The extension radius is less than 1 when `dR ≥ 1`. -/
lemma extensionRadius_lt_one (dR : ℕ) [NeZero dR] : extensionRadius dR < 1 := by
  unfold extensionRadius
  have hdR_pos : 0 < (dR : ℝ) := Nat.cast_pos.mpr (NeZero.pos dR)
  have hdR_sq_pos : 0 < (dR : ℝ) ^ 2 := sq_pos_of_pos hdR_pos
  have harg_lt_one : 1 - 1 / (dR : ℝ) ^ 2 < 1 := by
    linarith [div_pos one_pos hdR_sq_pos]
  have harg_nonneg : 0 ≤ 1 - 1 / (dR : ℝ) ^ 2 := by
    have hdR_ge1 : (1 : ℝ) ≤ (dR : ℝ) := by
      exact_mod_cast NeZero.pos dR
    have hdR_sq_ge1 : (dR : ℝ) ^ 2 ≥ 1 := by nlinarith
    have : 1 / (dR : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one hdR_sq_pos]
      linarith
    linarith
  calc Real.sqrt (1 - 1 / (dR : ℝ) ^ 2)
      < Real.sqrt 1 := Real.sqrt_lt_sqrt harg_nonneg harg_lt_one
    _ = 1 := Real.sqrt_one

/-- Tensor a sub-normalized operator with the normalized maximally mixed
reference on a register of dimension `dR`. -/
def SubDensityOp.tensorMaxMixed {dE : ℕ} (dR : ℕ) [NeZero dR]
    (ρ : SubDensityOp dE) : SubDensityOp (dE * dR) where
  toOp := ρ.toOp ⊗ (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toOp
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Quantum.TensorProducts.Op.tensor_conjTranspose]
    rw [ρ.isHermitian,
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).isHermitian]
  pos_semidef := by
    exact Op.tensor_posSemidef ρ.toOp
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toOp
      ρ.isHermitian
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).isHermitian
      ρ.pos_semidef
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).pos_semidef
  trace_le_one := by
    rw [Op.trace_tensor]
    have hσ_trace :
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toOp.trace = 1 :=
      (DensityOp.maxMixed dR).trace_one
    rw [hσ_trace, mul_one]
    exact ρ.trace_le_one

@[simp]
lemma SubDensityOp.tensorMaxMixed_toOp {dE dR : ℕ} [NeZero dR]
    (ρ : SubDensityOp dE) :
    (ρ.tensorMaxMixed dR).toOp =
      ρ.toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)) := by
  simp [SubDensityOp.tensorMaxMixed, toSubDensityOp_maxMixed_toOp_eq]

@[simp]
lemma SubDensityOp.tensorMaxMixed_trace {dE dR : ℕ} [NeZero dR]
    (ρ : SubDensityOp dE) :
    (ρ.tensorMaxMixed dR).trace = ρ.trace := by
  unfold SubDensityOp.trace SubDensityOp.tensorMaxMixed
  rw [Op.trace_tensor]
  have hσ_trace :
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toOp.trace = 1 :=
    (DensityOp.maxMixed dR).trace_one
  rw [hσ_trace, mul_one]

/-- Partial trace over the maximally mixed tensor factor returns the left
operator. -/
lemma partialTraceB_tensor_maxMixed_toOp {dE dR : ℕ} [NeZero dR]
    (A : Op dE) :
    partialTraceB (A ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))) = A := by
  ext i j
  unfold partialTraceB Op.tensor
  simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]
  rw [← Finset.mul_sum]
  have h_trace :
      (∑ k : Fin dR, (((1 / (dR : ℂ)) • (1 : Op dR)) k k)) = 1 := by
    simp
  rw [h_trace, mul_one]

/-- Partial trace preserves Mathlib PSD for the second tensor factor. -/
lemma partialTraceB_posSemidef_mathlib_of_posSemidef {dE dR : ℕ}
    {A : Op (dE * dR)} (hA : A.PosSemidef) :
    (partialTraceB A).PosSemidef := by
  let Apsd : PosSemidefOp (dE * dR) :=
    { toOp := A
      isHermitian := hA.isHermitian
      pos_semidef := by
        intro v
        have hv := hA.dotProduct_mulVec_nonneg v
        rw [Complex.nonneg_iff] at hv
        exact hv.1 }
  exact posSemidef_of_isHermitian_of_quadraticForm_re_nonneg
    (partialTraceB_hermitian A hA.isHermitian)
    (by simpa [Apsd] using partialTraceB_posSemidef Apsd)

/-- The normalized maximally mixed reference on `E ⊗ R` factorizes. -/
lemma maxMixed_mul_toSubDensityOp_toOp_eq {dE dR : ℕ} [NeZero dE] [NeZero dR] :
    (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))).toOp =
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp ⊗
        ((1 / (dR : ℂ)) • (1 : Op dR)) := by
  rw [toSubDensityOp_maxMixed_toOp_eq, toSubDensityOp_maxMixed_toOp_eq]
  rw [Quantum.TensorProducts.Op.smul_tensor_smul, Op.tensor_one]
  congr 1
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne dE),
    Nat.cast_ne_zero.mpr (NeZero.ne dR)]

/-- The `E`-partial trace of the product maximally mixed reference is the
maximally mixed reference on `E`. -/
lemma partialTraceB_maxMixed_mul_toSubDensityOp_toOp_eq
    {dE dR : ℕ} [NeZero dE] [NeZero dR] :
    partialTraceB
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))).toOp =
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp := by
  rw [maxMixed_mul_toSubDensityOp_toOp_eq]
  exact partialTraceB_tensor_maxMixed_toOp
    (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp

/-- **Floor push-through to the `E`-marginal.**

A scalar maximally-mixed floor on the joint `E ⊗ R` reference descends through the
`R`-partial trace to the same scalar floor on the `E`-marginal reference: if
`c · maxMixed_{dE·dR} ⪯ σER`, then `c · maxMixed_dE ⪯ partialTraceB σER`.

This is the load-bearing regularization step of the Nahar et al. B17 register-restoration:
the joint floor `(1/polyDim)·maxMixed_{dE·dR} ⪯ σER` (the `h_floor` hypothesis)
yields `(1/polyDim)·maxMixed_dE ⪯ σE := partialTraceB σER`, i.e.
`λ_min(σE) ≥ 1/(polyDim·dE)`, making `σE` full-rank.

Proof: `partialTraceB_opLe_of_opLe` (Löwner-monotonicity of the partial trace)
applied to the floor, then `partialTraceB (c • maxMixed_{dE·dR}) = c • maxMixed_dE`
via `partialTraceB_smul` and `partialTraceB_maxMixed_mul_toSubDensityOp_toOp_eq`. -/
lemma partialTraceB_maxMixed_floor_pushThrough
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (c : ℂ) (σER : Op (dE * dR))
    (h_floor : opLe (c • (DensityOp.maxMixed (dE * dR)).toOp) σER) :
    opLe (c • (DensityOp.maxMixed dE).toOp)
      (Quantum.TensorProducts.partialTraceB σER) := by
  have hmono := partialTraceB_opLe_of_opLe h_floor
  have hmm : Quantum.TensorProducts.partialTraceB
        (c • (DensityOp.maxMixed (dE * dR)).toOp)
      = c • (DensityOp.maxMixed dE).toOp := by
    rw [partialTraceB_smul]
    congr 1
    exact partialTraceB_maxMixed_mul_toSubDensityOp_toOp_eq
  rwa [hmm] at hmono

/-- Feasibility descends from an `E ⊗ R` extension to its `E` marginal when both
references are maximally mixed. -/
lemma isFeasible_marginal_maxMixed_of_isFeasible_extension
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    {t : ℝ}
    (ht :
      isFeasible ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) t) :
    isFeasible ρE
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t := by
  rcases ht with ⟨ht_nonneg, ht_dom⟩
  refine ⟨ht_nonneg, fun x => ?_⟩
  let σER : SubDensityOp (dE * dR) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))
  have hσER_psd : σER.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib σER.toPosSemidefOp
  have htσER_psd : ((Complex.ofReal t) • σER.toOp).PosSemidef :=
    Matrix.PosSemidef.smul hσER_psd (RCLike.ofReal_nonneg.mpr ht_nonneg)
  have hdiff_psd :
      (((Complex.ofReal t) • σER.toOp) - (ρER.stateMap x).toOp).PosSemidef :=
    opLe.posSemidef_sub
      (ρER.stateMap x).toPosSemidefOp.toHermitianOp.isHermitian
      htσER_psd.isHermitian
      (by simpa [σER] using ht_dom x)
  have hpartial_psd :
      (partialTraceB
        (((Complex.ofReal t) • σER.toOp) - (ρER.stateMap x).toOp)).PosSemidef :=
    partialTraceB_posSemidef_mathlib_of_posSemidef hdiff_psd
  have hpartial_eq :
      partialTraceB
          (((Complex.ofReal t) • σER.toOp) - (ρER.stateMap x).toOp) =
        ((Complex.ofReal t) •
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp) -
          (ρE.stateMap x).toOp := by
    rw [partialTraceB_sub, partialTraceB_smul]
    rw [partialTraceB_maxMixed_mul_toSubDensityOp_toOp_eq]
    rw [hblocks x]
  apply opLe_of_posSemidef_sub
  rw [hpartial_eq] at hpartial_psd
  exact hpartial_psd

/-- Feasible-lambda comparison for an extension and its per-block
`partialTraceB` marginal, with maximally mixed references. -/
lemma minFeasibleLambda_marginal_maxMixed_le_extension
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (hfeasER :
      hasFeasibleLambda ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR)))) :
    minFeasibleLambda ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) ≤
      minFeasibleLambda ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) := by
  let σER : SubDensityOp (dE * dR) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))
  let σE : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  unfold minFeasibleLambda
  have hsub : setOf (isFeasible ρER σER) ⊆ setOf (isFeasible ρE σE) := by
    intro t ht
    exact isFeasible_marginal_maxMixed_of_isFeasible_extension ρER ρE hblocks
      (by simpa [σER] using ht)
  obtain ⟨t, ht⟩ := hfeasER
  have hne : (setOf (isFeasible ρER σER)).Nonempty :=
    ⟨t, by simpa [σER] using ht⟩
  exact csInf_le_csInf (minFeasibleLambda_bddBelow ρE σE) hne hsub

/-- Unsmoothed real min-entropy data processing for discarding the explicit
`R` register, away from the `Real.log 0` sentinel boundary. -/
lemma conditionalMinEntropyReal_marginal_maxMixed_ge_extension_of_pos
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (hfeasER :
      hasFeasibleLambda ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))))
    (hposE :
      0 < minFeasibleLambda ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))) :
    conditionalMinEntropyReal ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) ≤
      conditionalMinEntropyReal ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  let lamER :=
    minFeasibleLambda ρER
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR)))
  let lamE :=
    minFeasibleLambda ρE
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))
  have hle : lamE ≤ lamER := by
    simpa [lamER, lamE] using
      minFeasibleLambda_marginal_maxMixed_le_extension ρER ρE hblocks hfeasER
  have hposE' : 0 < lamE := by
    simpa [lamE] using hposE
  have hposER : 0 < lamER := lt_of_lt_of_le hposE' hle
  have hlog_le : Real.log lamE ≤ Real.log lamER :=
    Real.log_le_log hposE' hle
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold conditionalMinEntropyReal
  change -Real.log lamER / Real.log 2 ≤ -Real.log lamE / Real.log 2
  exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2_pos.le

/-- The maximally mixed reference admits a feasible domination scalar for every
finite CQ state. -/
lemma hasFeasibleLambda_maxMixed
    {X : Type*} [Fintype X] {d : ℕ} [NeZero d]
    (ρ : CQState X d) :
    hasFeasibleLambda ρ
      (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) := by
  refine ⟨(d : ℝ), ?_⟩
  refine ⟨by exact_mod_cast Nat.zero_le d, fun x => ?_⟩
  exact (ρ.stateMap x).opLe_dim_smul_maxMixed

/-- A sub-normalized operator with zero trace is the zero operator, since it is
positive semidefinite. -/
lemma SubDensityOp.toOp_eq_zero_of_trace_eq_zero
    {d : ℕ} (ρ : SubDensityOp d) (htrace : ρ.trace = 0) :
    ρ.toOp = 0 := by
  have hpsd : Matrix.PosSemidef ρ.toOp :=
    posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have htrace_complex : ρ.toOp.trace = 0 := by
    rw [SubDensityOp.trace_complex_eq, htrace]
    norm_num
  exact hpsd.trace_eq_zero_iff.mp htrace_complex

/-- If the total weight of a CQ state is nonpositive, then every per-outcome
block operator is zero. -/
lemma CQState.stateMap_toOp_eq_zero_of_weight_nonpos
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
  exact SubDensityOp.toOp_eq_zero_of_trace_eq_zero (ρ.stateMap x) hx_trace_zero

/-- Unsmoothed real min-entropy data processing for discarding the explicit
`R` register, including the zero-weight sentinel boundary for the real-valued
variant. -/
lemma conditionalMinEntropyReal_marginal_maxMixed_ge_extension
    {X : Type*} [Fintype X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp) :
    conditionalMinEntropyReal ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) ≤
      conditionalMinEntropyReal ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  let σER : SubDensityOp (dE * dR) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))
  let σE : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  have hfeasER : hasFeasibleLambda ρER σER := by
    simpa [σER] using hasFeasibleLambda_maxMixed ρER
  by_cases hposE : 0 < minFeasibleLambda ρE σE
  · exact conditionalMinEntropyReal_marginal_maxMixed_ge_extension_of_pos
      ρER ρE hblocks (by simpa [σER] using hfeasER) (by simpa [σE] using hposE)
  · have hfeasE : hasFeasibleLambda ρE σE := by
      simpa [σE] using hasFeasibleLambda_maxMixed ρE
    have hweightE_not_pos : ¬ 0 < ∑ x : X, (ρE.stateMap x).trace := by
      intro hweight
      have hposE' : 0 < minFeasibleLambda ρE σE :=
        minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρE σE hweight hfeasE
      exact hposE hposE'
    have hE_zero : ∀ x : X, (ρE.stateMap x).toOp = 0 :=
      CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρE hweightE_not_pos
    have hweight_eq :
        (∑ x : X, (ρER.stateMap x).trace) =
          ∑ x : X, (ρE.stateMap x).trace := by
      apply Finset.sum_congr rfl
      intro x _
      unfold SubDensityOp.trace
      rw [← hblocks x, trace_partialTraceB]
    have hweightER_not_pos : ¬ 0 < ∑ x : X, (ρER.stateMap x).trace := by
      intro hweight
      exact hweightE_not_pos (by rwa [← hweight_eq])
    have hER_zero : ∀ x : X, (ρER.stateMap x).toOp = 0 :=
      CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρER hweightER_not_pos
    have hlamE : minFeasibleLambda ρE σE = 0 :=
      minFeasibleLambda_eq_zero_of_stateMap_zero ρE hE_zero σE
    have hlamER : minFeasibleLambda ρER σER = 0 :=
      minFeasibleLambda_eq_zero_of_stateMap_zero ρER hER_zero σER
    unfold conditionalMinEntropyReal
    rw [hlamER, hlamE, Real.log_zero, neg_zero, zero_div]

/-- Feasibility lifts exactly through tensoring every block and reference with
the normalized maximally mixed register. -/
lemma isFeasible_tensorMaxMixed_of_isFeasible
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρEtensor : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))
    {t : ℝ}
    (ht :
      isFeasible ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t) :
    isFeasible ρEtensor
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) t := by
  rcases ht with ⟨ht_nonneg, ht_dom⟩
  refine ⟨ht_nonneg, fun x => ?_⟩
  let σE : SubDensityOp dE := DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  let mR : Op dR := (1 / (dR : ℂ)) • (1 : Op dR)
  have hσE_psd : σE.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib σE.toPosSemidefOp
  have htσE_psd : ((Complex.ofReal t) • σE.toOp).PosSemidef :=
    Matrix.PosSemidef.smul hσE_psd (RCLike.ofReal_nonneg.mpr ht_nonneg)
  have hmR_psd : mR.PosSemidef := by
    have h :
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toOp.PosSemidef :=
      posSemidefOp_implies_mathlib
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dR)).toPosSemidefOp
    simpa [mR, toSubDensityOp_maxMixed_toOp_eq] using h
  have hmR_herm : mR.IsHermitian := by
    simp [mR]
  have ht_tensor :
      opLe ((ρE.stateMap x).toOp ⊗ mR)
        (((Complex.ofReal t) • σE.toOp) ⊗ mR) := by
    exact opLe_tensor_psd
      (ρE.stateMap x).toPosSemidefOp.toHermitianOp.isHermitian
      htσE_psd hmR_psd hmR_herm
      (by simpa [σE] using ht_dom x) (fun _ => le_rfl)
  have hrhs :
      (((Complex.ofReal t) • σE.toOp) ⊗ mR) =
        (Complex.ofReal t) •
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))).toOp := by
    calc
      (((Complex.ofReal t) • σE.toOp) ⊗ mR)
          = (Complex.ofReal t) • (σE.toOp ⊗ mR) := by
              rw [Quantum.TensorProducts.Op.tensor_smul_left]
      _ = (Complex.ofReal t) •
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))).toOp := by
              rw [maxMixed_mul_toSubDensityOp_toOp_eq]
  rw [hblocks x]
  rw [hrhs] at ht_tensor
  exact ht_tensor

/-- Feasibility reflects back from the product lift by partial tracing over the
maximally mixed register. -/
lemma isFeasible_of_isFeasible_tensorMaxMixed
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρEtensor : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))
    {t : ℝ}
    (ht :
      isFeasible ρEtensor
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) t) :
    isFeasible ρE
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t := by
  rcases ht with ⟨ht_nonneg, ht_dom⟩
  refine ⟨ht_nonneg, fun x => ?_⟩
  let σER : SubDensityOp (dE * dR) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))
  have hσER_psd : σER.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib σER.toPosSemidefOp
  have htσER_psd : ((Complex.ofReal t) • σER.toOp).PosSemidef :=
    Matrix.PosSemidef.smul hσER_psd (RCLike.ofReal_nonneg.mpr ht_nonneg)
  have hdiff_psd :
      (((Complex.ofReal t) • σER.toOp) - (ρEtensor.stateMap x).toOp).PosSemidef :=
    opLe.posSemidef_sub
      (ρEtensor.stateMap x).toPosSemidefOp.toHermitianOp.isHermitian
      htσER_psd.isHermitian
      (by simpa [σER] using ht_dom x)
  have hpartial_psd :
      (partialTraceB
        (((Complex.ofReal t) • σER.toOp) - (ρEtensor.stateMap x).toOp)).PosSemidef :=
    partialTraceB_posSemidef_mathlib_of_posSemidef hdiff_psd
  have hpartial_eq :
      partialTraceB
          (((Complex.ofReal t) • σER.toOp) - (ρEtensor.stateMap x).toOp) =
        ((Complex.ofReal t) •
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)).toOp) -
          (ρE.stateMap x).toOp := by
    rw [partialTraceB_sub, partialTraceB_smul]
    rw [partialTraceB_maxMixed_mul_toSubDensityOp_toOp_eq]
    rw [hblocks x, partialTraceB_tensor_maxMixed_toOp]
  apply opLe_of_posSemidef_sub
  rw [hpartial_eq] at hpartial_psd
  exact hpartial_psd

/-- The feasible scalar set is unchanged by tensoring all blocks and the
reference with the normalized maximally mixed register. -/
lemma isFeasible_tensorMaxMixed_iff
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρEtensor : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))
    {t : ℝ} :
    isFeasible ρEtensor
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) t ↔
      isFeasible ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t := by
  exact ⟨
    isFeasible_of_isFeasible_tensorMaxMixed ρEtensor ρE hblocks,
    isFeasible_tensorMaxMixed_of_isFeasible ρEtensor ρE hblocks⟩

/-- Tensoring all blocks and the reference with a normalized maximally mixed
register leaves the feasible infimum unchanged. -/
lemma minFeasibleLambda_tensorMaxMixed_eq
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρEtensor : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))) :
    minFeasibleLambda ρEtensor
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) =
      minFeasibleLambda ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  unfold minFeasibleLambda
  congr 1
  ext t
  exact isFeasible_tensorMaxMixed_iff ρEtensor ρE hblocks

/-- The CQState obtained by tensoring each outcome block with I/dR is again a CQState.
Each block is `ρE(x) ⊗ I/dR`, and the total weight is unchanged. -/
theorem CQState.tensorMaxMixed_exists {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE : ℕ} [NeZero dE] (dR : ℕ) [NeZero dR]
    (ρE : CQState X dE) :
    ∃ ρER : CQState X (dE * dR),
      (∀ x : X, (ρER.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))) := by
  refine ⟨
    { stateMap := fun x => (ρE.stateMap x).tensorMaxMixed dR
      weight_le_one := by
        simpa using ρE.weight_le_one },
    ?_⟩
  intro x
  simp

private lemma purifiedDistance_le_extensionRadius_of_inv_dim_le_fidelityGen
    {n dR : ℕ} [NeZero n] [NeZero dR] {ρ σ : SubDensityOp n}
    (hfg : 1 / (dR : ℝ) ≤ fidelityGen ρ σ) :
    purifiedDistance ρ σ ≤ extensionRadius dR := by
  unfold purifiedDistance extensionRadius
  apply Real.sqrt_le_sqrt
  have hfg_nonneg : 0 ≤ fidelityGen ρ σ := fidelityGen_nonneg ρ σ
  have hinv_nonneg : 0 ≤ 1 / (dR : ℝ) := by positivity
  have hsq : (1 / (dR : ℝ)) ^ 2 ≤ fidelityGen ρ σ ^ 2 := by
    have hprod :
        0 ≤ (fidelityGen ρ σ - 1 / (dR : ℝ)) *
          (fidelityGen ρ σ + 1 / (dR : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hfg) (add_nonneg hfg_nonneg hinv_nonneg)
    nlinarith
  have hinv_sq : (1 / (dR : ℝ)) ^ 2 = 1 / (dR : ℝ) ^ 2 := by
    ring
  nlinarith

private lemma inv_dim_le_fidelityGen_of_trace_div_dim_le_fidelity
    {n dR : ℕ} [NeZero n] [NeZero dR] (ρ σ : SubDensityOp n)
    (htrace : σ.trace = ρ.trace)
    (hF :
      ρ.trace / (dR : ℝ) ≤
        Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp) :
    1 / (dR : ℝ) ≤ fidelityGen ρ σ := by
  unfold fidelityGen
  rw [htrace]
  have hcorr :
      Real.sqrt ((1 - ρ.trace) * (1 - ρ.trace)) = 1 - ρ.trace := by
    rw [Real.sqrt_mul_self ρ.one_sub_trace_nonneg]
  rw [hcorr]
  have ht0 : 0 ≤ ρ.trace := ρ.trace_nonneg
  have ht1 : ρ.trace ≤ 1 := ρ.trace_le_one
  have hdR_pos : 0 < (dR : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dR)
  have hinv_le_one : 1 / (dR : ℝ) ≤ 1 := by
    rw [div_le_one hdR_pos]
    exact_mod_cast NeZero.pos dR
  have harith : 1 / (dR : ℝ) ≤ ρ.trace / (dR : ℝ) + (1 - ρ.trace) := by
    have hprod : 0 ≤ (1 - ρ.trace) * (1 - 1 / (dR : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hinv_le_one)
    have hident :
        ρ.trace / (dR : ℝ) + (1 - ρ.trace) - 1 / (dR : ℝ) =
          (1 - ρ.trace) * (1 - 1 / (dR : ℝ)) := by
      ring
    nlinarith
  linarith

/-- A positive operator is dominated by `(dim R)^2` times its partial trace
tensored with the normalized maximally mixed operator on `R`. -/
lemma opLe_le_dimR_sq_smul_partialTraceB_tensor_maxMixed
    {dE dR : ℕ} [NeZero dE] [NeZero dR] {A : Op (dE * dR)}
    (hA : A.PosSemidef) :
    opLe A
      ((Complex.ofReal ((dR : ℝ) ^ 2)) •
        (partialTraceB A ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))) := by
  have hdom :
      opLe A
        ((Complex.ofReal (dR : ℝ)) •
          (partialTraceB A ⊗ (1 : Op dR))) :=
    Quantum.Operators.opLe_le_card_smul_partialTraceB_tensor_one (A := A) hA
  have hscaled :
      (Complex.ofReal ((dR : ℝ) ^ 2) •
          (partialTraceB A ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))) =
        (Complex.ofReal (dR : ℝ)) •
          (partialTraceB A ⊗ (1 : Op dR)) := by
    rw [Quantum.TensorProducts.Op.tensor_smul_right, smul_smul,
      ofReal_nat_sq_mul_inv_natCast]
  rw [hscaled]
  exact hdom

/-- Replacing each CQ block by its partial trace tensored with `I/dR` preserves
the trace of the CQ joint density. -/
lemma CQState.toJointDensity_trace_eq_of_stateMap_eq_partialTraceB_tensor_maxMixed
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρEtensor : CQState X (dE * dR))
    (hblocks : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        Quantum.TensorProducts.partialTraceB (ρER.stateMap x).toOp ⊗
          ((1 / (dR : ℂ)) • (1 : Op dR))) :
    ρEtensor.toJointDensity.trace = ρER.toJointDensity.trace := by
  rw [CQState.toJointDensity_trace_eq_sum,
    CQState.toJointDensity_trace_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  unfold SubDensityOp.trace
  rw [hblocks x, Op.trace_tensor]
  have hmR_trace :
      (((1 / (dR : ℂ)) • (1 : Op dR)).trace) = 1 := by
    simp
  rw [hmR_trace, mul_one, trace_partialTraceB]

/-- The CQ joint density is dominated by `(dim R)^2` times the joint density
whose blocks are the partial traces tensored with `I/dR`. -/
lemma CQState.toJointDensity_opLe_dimR_sq_smul_of_stateMap_eq_partialTraceB_tensor_maxMixed
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρEtensor : CQState X (dE * dR))
    (hblocks : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        Quantum.TensorProducts.partialTraceB (ρER.stateMap x).toOp ⊗
          ((1 / (dR : ℂ)) • (1 : Op dR))) :
    opLe ρER.toJointDensity.toOp
      ((Complex.ofReal ((dR : ℝ) ^ 2)) • ρEtensor.toJointDensity.toOp) := by
  apply CQState.toJointDensity_opLe_of_forall
  · exact sq_nonneg (dR : ℝ)
  · intro x
    have hA_psd : (ρER.stateMap x).toOp.PosSemidef :=
      posSemidefOp_implies_mathlib (ρER.stateMap x).toPosSemidefOp
    simpa [hblocks x] using
      opLe_le_dimR_sq_smul_partialTraceB_tensor_maxMixed
        (A := (ρER.stateMap x).toOp) hA_psd

/-- The purified distance from `ρER` to its `E`-marginal tensored with `I/dR`
is bounded by `extensionRadius dR`. -/
theorem CQState.purifiedDistance_tensorMaxMixed_le_extensionRadius
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρEtensor : CQState X (dE * dR))
    (hblocks : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        Quantum.TensorProducts.partialTraceB (ρER.stateMap x).toOp ⊗
          ((1 / (dR : ℂ)) • (1 : Op dR))) :
    CQState.purifiedDistance ρER ρEtensor ≤
      extensionRadius dR := by
  unfold CQState.purifiedDistance
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero ((dE * dR) * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  apply purifiedDistance_le_extensionRadius_of_inv_dim_le_fidelityGen
  apply inv_dim_le_fidelityGen_of_trace_div_dim_le_fidelity
  · exact CQState.toJointDensity_trace_eq_of_stateMap_eq_partialTraceB_tensor_maxMixed
      ρER ρEtensor hblocks
  · have hdom_joint :=
      CQState.toJointDensity_opLe_dimR_sq_smul_of_stateMap_eq_partialTraceB_tensor_maxMixed
        ρER ρEtensor hblocks
    have hfid :
        ρER.toJointDensity.trace / Real.sqrt ((dR : ℝ) ^ 2) ≤
          Quantum.Metrics.fidelity
            ρER.toJointDensity.toPosSemidefOp
            ρEtensor.toJointDensity.toPosSemidefOp :=
      Quantum.Metrics.trace_div_sqrt_le_fidelity_of_opLe
        ρER.toJointDensity.toPosSemidefOp
        ρEtensor.toJointDensity.toPosSemidefOp
        (by exact sq_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos dR)))
        hdom_joint
    have hsqrt_dim : Real.sqrt ((dR : ℝ) ^ 2) = (dR : ℝ) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      exact_mod_cast Nat.zero_le dR
    simpa [SubDensityOp.trace, hsqrt_dim] using hfid

/-- Conditional min-entropy is unchanged when all blocks and the maximally mixed
reference are tensored with the normalized maximally mixed register. -/
theorem conditionalMinEntropyReal_tensorMaxMixed_maxMixed_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρEtensor : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))) :
    conditionalMinEntropyReal ρEtensor
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) =
      conditionalMinEntropyReal ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  unfold conditionalMinEntropyReal
  rw [minFeasibleLambda_tensorMaxMixed_eq ρEtensor ρE hblocks]

/-- The extension radius is at most `1 - 1 / (2 * dR^2)` for nonzero reference
dimension `dR`. -/
theorem extensionRadius_le_one_sub_inv_two_dimR (dR : ℕ) [NeZero dR] :
    extensionRadius dR ≤ 1 - 1 / (2 * (dR : ℝ) ^ 2) := by
  unfold extensionRadius
  have hdR_pos : (0 : ℝ) < dR := Nat.cast_pos.mpr (NeZero.pos dR)
  have hdR_sq_pos : (0 : ℝ) < (dR : ℝ) ^ 2 := sq_pos_of_pos hdR_pos
  have harg_nonneg : 0 ≤ 1 - 1 / (dR : ℝ) ^ 2 := by
    have : 1 / (dR : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one hdR_sq_pos]
      have : (1 : ℝ) ≤ dR := by exact_mod_cast NeZero.pos dR
      nlinarith
    linarith
  have hle1 : 1 / (dR : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one hdR_sq_pos]
    have : (1 : ℝ) ≤ dR := by exact_mod_cast NeZero.pos dR
    nlinarith
  -- sqrt(1-x) ≤ 1 - x/2 when 0 ≤ x ≤ 1: equivalent to (1-x/2)² ≥ 1-x, i.e. x²/4 ≥ 0.
  set x := 1 / (dR : ℝ) ^ 2 with hx_def
  have hx_nn : 0 ≤ x := div_nonneg one_pos.le hdR_sq_pos.le
  have hsq_bound : Real.sqrt (1 - x) ≤ 1 - x / 2 := by
    have hrhs_nn : 0 ≤ 1 - x / 2 := by linarith
    rw [← Real.sqrt_sq hrhs_nn]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (x / 2)]
  have hconv : 1 - x / 2 = 1 - 1 / (2 * (dR : ℝ) ^ 2) := by
    rw [hx_def]; ring
  linarith [hsq_bound.trans_eq hconv]

/-!
## Free-reference (optimal-reference) register extension — Nahar et al. B17 / [47, Eq. (8)]

The maximally-mixed twin above floors against `maxMixed_{E⊗R}` and forces the lift
`ρE(x) ⊗ I/dR` (a product extension). Nahar et al. B17 = Winkler–Tomamichel–Hengl–Renner
[47, Eq. (8)] (Tomamichel 2016, §6 dimension lemma) is the **free-reference**
statement: adjoining a `dV`-dimensional register `V` to an arbitrary, possibly
**correlated** CQ state `ρEV` costs at most `2·log₂ dV` on the smooth min-entropy,
at the **same** smoothing radius, with the reference chosen freely as
`σE ⊗ I_V/dV = σE.tensorMaxMixed dV`. It is **transport-free**: the keystone is the
reduction operator inequality `B ≼ dV·(partialTraceB B ⊗ I_V)`
(`Quantum.Operators.opLe_le_card_smul_partialTraceB_tensor_one`), the lift is the same-radius CQ
Uhlmann/fiber extension (`CQState.exists_extension_of_partialTraceB_purifiedDistance`),
and the penalty `2·log₂ dV` comes from the dimension of the reference factor `I_V/dV`,
not from transporting the state.

Source: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B, Eq. (B17); [47] =
Winkler–Tomamichel–
Hengl–Renner, PRL 107, 090502 (2011); Tomamichel 2016 (arXiv:1504.00233) §6.
-/

/-- Scaling the free reference `(t • σE) ⊗ I_V` by `dV` gives the `σE`-tensor-maximally-mixed
reference on `E ⊗ V` with the `dV^2` factor. -/
lemma right_dim_smul_freeRef_tensor_one_eq_sq_smul_tensorMaxMixed
    {dE dV : ℕ} [NeZero dV] (σE : SubDensityOp dE) (t : ℝ) :
    (Complex.ofReal (dV : ℝ)) •
        (((Complex.ofReal t) • σE.toOp) ⊗ (1 : Op dV)) =
      (Complex.ofReal ((dV : ℝ) ^ 2 * t)) • (σE.tensorMaxMixed dV).toOp := by
  rw [SubDensityOp.tensorMaxMixed_toOp]
  calc
    (Complex.ofReal (dV : ℝ)) •
        (((Complex.ofReal t) • σE.toOp) ⊗ (1 : Op dV))
        = (Complex.ofReal (dV : ℝ)) •
            ((Complex.ofReal t) • (σE.toOp ⊗ (1 : Op dV))) := by
          rw [Quantum.TensorProducts.Op.tensor_smul_left]
    _ = ((Complex.ofReal (dV : ℝ)) * (Complex.ofReal t)) •
            (σE.toOp ⊗ (1 : Op dV)) := by
          rw [smul_smul]
    _ = (Complex.ofReal ((dV : ℝ) ^ 2 * t)) •
            (σE.toOp ⊗ ((1 / (dV : ℂ)) • (1 : Op dV))) := by
          rw [Quantum.TensorProducts.Op.tensor_smul_right, smul_smul]
          congr 1
          push_cast
          field_simp [Nat.cast_ne_zero.mpr (NeZero.ne dV)]

/-- Feasibility lifts from the `E` marginal to an arbitrary (correlated) `E ⊗ V`
extension with the standard `dV^2` cost, using the free reference `σE.tensorMaxMixed dV`
and the reduction inequality `B ≼ dV·(partialTraceB B ⊗ I_V)`. -/
lemma isFeasible_extension_freeRef_of_isFeasible
    {X : Type*} [Fintype X]
    {dE dV : ℕ} [NeZero dE] [NeZero dV]
    (ρEV : CQState X (dE * dV)) (ρE : CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp)
    {t : ℝ}
    (ht : isFeasible ρE σE t) :
    isFeasible ρEV (σE.tensorMaxMixed dV) ((dV : ℝ) ^ 2 * t) := by
  rcases ht with ⟨ht_nonneg, ht_dom⟩
  refine ⟨mul_nonneg (sq_nonneg _) ht_nonneg, fun x => ?_⟩
  -- `ρ_EV(x) ≤ d_V (ρ_E(x) ⊗ 1)`: the partial-trace bound, with `Tr_V ρ_EV(x) = ρ_E(x)`
  have hdom_ext := Quantum.Operators.opLe_le_card_smul_partialTraceB_tensor_one
    (posSemidefOp_implies_mathlib (ρEV.stateMap x).toPosSemidefOp)
  rw [hblocks x] at hdom_ext
  -- `ρ_E(x) ⊗ 1 ≤ (t σ_E) ⊗ 1`, from the feasibility of `t`
  have htσE_psd : ((Complex.ofReal t) • σE.toOp).PosSemidef :=
    (posSemidefOp_implies_mathlib σE.toPosSemidefOp).smul (RCLike.ofReal_nonneg.mpr ht_nonneg)
  have ht_tensor := opLe_tensor_psd (C := (1 : Op dV)) (D := 1)
    (ρE.stateMap x).toPosSemidefOp.toHermitianOp.isHermitian htσE_psd Matrix.PosSemidef.one
    Matrix.isHermitian_one (ht_dom x) (fun _ => le_rfl)
  -- `d_V ((t σ_E) ⊗ 1) = (d_V² t) (σ_E ⊗ I_V/d_V)`
  rw [← right_dim_smul_freeRef_tensor_one_eq_sq_smul_tensorMaxMixed σE t]
  exact opLe_trans hdom_ext (opLe_smul_nonneg (Nat.cast_nonneg dV) ht_tensor)

/-- Feasibility descends from a correlated `E ⊗ V` extension to its `E` marginal:
if `t·(σE ⊗ I_V/dV)` dominates every block of `ρEV`, then `t·σE` dominates every
block of the `E`-marginal `ρE` (partial-trace of the domination, using
`partialTraceB (σE ⊗ I_V/dV) = σE`). No dimension penalty in this direction. -/
lemma isFeasible_marginal_freeRef_of_isFeasible_extension
    {X : Type*} [Fintype X]
    {dE dV : ℕ} [NeZero dE] [NeZero dV]
    (ρEV : CQState X (dE * dV)) (ρE : CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp)
    {t : ℝ}
    (ht : isFeasible ρEV (σE.tensorMaxMixed dV) t) :
    isFeasible ρE σE t := by
  rcases ht with ⟨ht_nonneg, ht_dom⟩
  refine ⟨ht_nonneg, fun x => ?_⟩
  have hσEV_psd : (σE.tensorMaxMixed dV).toOp.PosSemidef :=
    posSemidefOp_implies_mathlib (σE.tensorMaxMixed dV).toPosSemidefOp
  have htσEV_psd :
      ((Complex.ofReal t) • (σE.tensorMaxMixed dV).toOp).PosSemidef :=
    Matrix.PosSemidef.smul hσEV_psd (RCLike.ofReal_nonneg.mpr ht_nonneg)
  have hdiff_psd :
      (((Complex.ofReal t) • (σE.tensorMaxMixed dV).toOp) -
        (ρEV.stateMap x).toOp).PosSemidef :=
    opLe.posSemidef_sub
      (ρEV.stateMap x).toPosSemidefOp.toHermitianOp.isHermitian
      htσEV_psd.isHermitian
      (ht_dom x)
  have hpartial_psd :
      (partialTraceB
        (((Complex.ofReal t) • (σE.tensorMaxMixed dV).toOp) -
          (ρEV.stateMap x).toOp)).PosSemidef :=
    partialTraceB_posSemidef_mathlib_of_posSemidef hdiff_psd
  have hpartial_eq :
      partialTraceB
          (((Complex.ofReal t) • (σE.tensorMaxMixed dV).toOp) -
            (ρEV.stateMap x).toOp) =
        ((Complex.ofReal t) • σE.toOp) - (ρE.stateMap x).toOp := by
    rw [partialTraceB_sub, partialTraceB_smul, SubDensityOp.tensorMaxMixed_toOp,
      partialTraceB_tensor_maxMixed_toOp, hblocks x]
  apply opLe_of_posSemidef_sub
  rw [hpartial_eq] at hpartial_psd
  exact hpartial_psd

/-- Feasible-lambda comparison for a correlated extension whose per-outcome blocks
have the prescribed `E` marginal. With the free reference `σE.tensorMaxMixed dV`,
the optimal feasible scalar costs a factor `dV^2` (Nahar et al. B17).

No feasibility hypothesis is needed: when the `E` feasible set is empty both sides
collapse to the `sInf ∅ = 0` sentinel (the `E ⊗ V` feasible set is then also empty,
by the marginal-direction feasibility lemma). -/
theorem minFeasibleLambda_extension_freeRef_le
    {X : Type*} [Fintype X]
    {dE dV : ℕ} [NeZero dE] [NeZero dV]
    (ρEV : CQState X (dE * dV)) (ρE : CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp) :
    minFeasibleLambda ρEV (σE.tensorMaxMixed dV) ≤
      (dV : ℝ) ^ 2 * minFeasibleLambda ρE σE := by
  by_cases hfeasE : (setOf (isFeasible ρE σE)).Nonempty
  · let c : ℝ := (dV : ℝ) ^ 2
    have hc_nonneg : 0 ≤ c := sq_nonneg _
    have hsub :
        c • setOf (isFeasible ρE σE) ⊆ setOf (isFeasible ρEV (σE.tensorMaxMixed dV)) := by
      rintro u ⟨s, hs, rfl⟩
      have ht_lift :
          isFeasible ρEV (σE.tensorMaxMixed dV) ((dV : ℝ) ^ 2 * s) :=
        isFeasible_extension_freeRef_of_isFeasible ρEV ρE σE hblocks hs
      simpa [c, smul_eq_mul] using ht_lift
    have hscaled_nonempty :
        (c • setOf (isFeasible ρE σE) : Set ℝ).Nonempty := by
      obtain ⟨s, hs⟩ := hfeasE
      exact ⟨c • s, ⟨s, hs, rfl⟩⟩
    have hle_scaled :
        sInf (setOf (isFeasible ρEV (σE.tensorMaxMixed dV))) ≤
          sInf (c • setOf (isFeasible ρE σE) : Set ℝ) :=
      csInf_le_csInf (minFeasibleLambda_bddBelow ρEV (σE.tensorMaxMixed dV))
        hscaled_nonempty hsub
    have hscaled_inf :
        sInf (c • setOf (isFeasible ρE σE) : Set ℝ) =
          c * sInf (setOf (isFeasible ρE σE)) := by
      simpa [smul_eq_mul] using
        Real.sInf_smul_of_nonneg hc_nonneg (setOf (isFeasible ρE σE))
    calc
      minFeasibleLambda ρEV (σE.tensorMaxMixed dV)
          = sInf (setOf (isFeasible ρEV (σE.tensorMaxMixed dV))) := rfl
      _ ≤ sInf (c • setOf (isFeasible ρE σE) : Set ℝ) := hle_scaled
      _ = c * sInf (setOf (isFeasible ρE σE)) := hscaled_inf
      _ = (dV : ℝ) ^ 2 * minFeasibleLambda ρE σE := rfl
  · -- `E` feasible set empty: both `minFeasibleLambda`s are the `sInf ∅ = 0` sentinel.
    have hE_empty : setOf (isFeasible ρE σE) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hfeasE
    have hEV_empty : setOf (isFeasible ρEV (σE.tensorMaxMixed dV)) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨t, ht⟩
      have hfeasEt : isFeasible ρE σE t :=
        isFeasible_marginal_freeRef_of_isFeasible_extension ρEV ρE σE hblocks ht
      exact hfeasE ⟨t, hfeasEt⟩
    have hlamEV : minFeasibleLambda ρEV (σE.tensorMaxMixed dV) = 0 := by
      unfold minFeasibleLambda; rw [hEV_empty, Real.sInf_empty]
    have hlamE : minFeasibleLambda ρE σE = 0 := by
      unfold minFeasibleLambda; rw [hE_empty, Real.sInf_empty]
    rw [hlamEV, hlamE, mul_zero]

/-- Feasible-lambda comparison in the marginal direction: discarding `V` cannot
increase the optimal feasible scalar (no dimension penalty). -/
theorem minFeasibleLambda_marginal_freeRef_le_extension
    {X : Type*} [Fintype X]
    {dE dV : ℕ} [NeZero dE] [NeZero dV]
    (ρEV : CQState X (dE * dV)) (ρE : CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp)
    (hfeasEV : hasFeasibleLambda ρEV (σE.tensorMaxMixed dV)) :
    minFeasibleLambda ρE σE ≤
      minFeasibleLambda ρEV (σE.tensorMaxMixed dV) := by
  unfold minFeasibleLambda
  have hsub :
      setOf (isFeasible ρEV (σE.tensorMaxMixed dV)) ⊆ setOf (isFeasible ρE σE) := by
    intro t ht
    exact isFeasible_marginal_freeRef_of_isFeasible_extension ρEV ρE σE hblocks ht
  obtain ⟨t, ht⟩ := hfeasEV
  have hne : (setOf (isFeasible ρEV (σE.tensorMaxMixed dV))).Nonempty := ⟨t, ht⟩
  exact csInf_le_csInf (minFeasibleLambda_bddBelow ρE σE) hne hsub

/-- Unsmoothed free-reference register-extension penalty (Nahar et al. B17), away from the
`Real.log 0` boundary: adjoining a `dV`-register costs at most `2·log₂ dV`. -/
theorem conditionalMinEntropyReal_extension_freeRef_ge_sub_twice_log_dim
    {X : Type*} [Fintype X]
    {dE dV : ℕ} [NeZero dE] [NeZero dV]
    (ρEV : CQState X (dE * dV)) (ρE : CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp)
    (hposEV : 0 < minFeasibleLambda ρEV (σE.tensorMaxMixed dV))
    (hposE : 0 < minFeasibleLambda ρE σE) :
    conditionalMinEntropyReal ρE σE -
        ((2 : ℝ) * Real.log (dV : ℝ)) / Real.log 2 ≤
      conditionalMinEntropyReal ρEV (σE.tensorMaxMixed dV) := by
  set lamEV := minFeasibleLambda ρEV (σE.tensorMaxMixed dV) with hlamEV
  set lamE := minFeasibleLambda ρE σE with hlamE
  have hlam : lamEV ≤ (dV : ℝ) ^ 2 * lamE :=
    minFeasibleLambda_extension_freeRef_le ρEV ρE σE hblocks
  have hdV_pos : 0 < (dV : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dV)
  have hdV_sq_pos : 0 < (dV : ℝ) ^ 2 := sq_pos_of_pos hdV_pos
  have hdV_sq_ne : ((dV : ℝ) ^ 2) ≠ 0 := ne_of_gt hdV_sq_pos
  have hlamE_ne : lamE ≠ 0 := ne_of_gt hposE
  have hlog_le : Real.log lamEV ≤ Real.log (((dV : ℝ) ^ 2) * lamE) :=
    Real.log_le_log hposEV hlam
  have hlog_rhs :
      Real.log (((dV : ℝ) ^ 2) * lamE) =
        2 * Real.log (dV : ℝ) + Real.log lamE := by
    rw [Real.log_mul hdV_sq_ne hlamE_ne, Real.log_pow]
    norm_num
  have hlog_bound :
      Real.log lamEV ≤ 2 * Real.log (dV : ℝ) + Real.log lamE := by
    simpa [hlog_rhs] using hlog_le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold conditionalMinEntropyReal
  change
    -Real.log lamE / Real.log 2 -
        (2 * Real.log (dV : ℝ)) / Real.log 2 ≤
      -Real.log lamEV / Real.log 2
  rw [← sub_div]
  have hnum : -Real.log lamE - 2 * Real.log (dV : ℝ) ≤ -Real.log lamEV := by
    linarith
  exact div_le_div_of_nonneg_right hnum hlog2_pos.le

/-- Marginal-direction conditional-min-entropy bound: discarding `V` cannot
decrease the conditional min-entropy, away from the `Real.log 0` boundary. -/
theorem conditionalMinEntropyReal_marginal_freeRef_ge_extension_of_pos
    {X : Type*} [Fintype X]
    {dE dV : ℕ} [NeZero dE] [NeZero dV]
    (ρEV : CQState X (dE * dV)) (ρE : CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp)
    (hfeasEV : hasFeasibleLambda ρEV (σE.tensorMaxMixed dV))
    (hposE : 0 < minFeasibleLambda ρE σE) :
    conditionalMinEntropyReal ρEV (σE.tensorMaxMixed dV) ≤
      conditionalMinEntropyReal ρE σE := by
  set lamEV := minFeasibleLambda ρEV (σE.tensorMaxMixed dV) with hlamEV
  set lamE := minFeasibleLambda ρE σE with hlamE
  have hle : lamE ≤ lamEV :=
    minFeasibleLambda_marginal_freeRef_le_extension ρEV ρE σE hblocks hfeasEV
  have hposEV : 0 < lamEV := lt_of_lt_of_le hposE hle
  have hlog_le : Real.log lamE ≤ Real.log lamEV := Real.log_le_log hposE hle
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold conditionalMinEntropyReal
  change -Real.log lamEV / Real.log 2 ≤ -Real.log lamE / Real.log 2
  exact div_le_div_of_nonneg_right (neg_le_neg hlog_le) hlog2_pos.le

/-! ## Decoupled-ancilla announce seam

The penalty-free register-move lemma family for announcing an `x`-independent quantum
ancilla block `τ` into the conditioning register.  Unlike the maximally-mixed reference
extension above, `τ` is referenced to **itself** (feasible-scalar transfer `t ↦ t`,
`polyDim = 1`), so **no** `log g` penalty is charged and the smoothing radius `ε` is
preserved.  This is the seam consumed at the per-Carathéodory-point BB84 floor, where the
PE-round product block is `x`-independent (before the mixture over the de Finetti measure,
where it becomes `σ`-correlated and the penalty-free `≤` is false).

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B Eqs.
(B16)–(B19); Renner 2005 (arXiv:quant-ph/0512258v2) §6.5; Tomamichel 2016 §6.1–6.2. -/

/-- Tensor every block of a CQ state on the right by a fixed sub-normalized ancilla `τ`.

The classical register is unchanged — the announced ancilla carries no classical outcome —
while the quantum register grows from `dE` to `dE * dτ`.  This is the conditioning-side
announce constructor: the announced block `τ` is `x`-independent, so it is decoupled from the
classical (secret) register. -/
noncomputable def CQState.tensorAncilla {X : Type*} [Fintype X] {dE dτ : ℕ}
    (ρ : CQState X dE) (τ : SubDensityOp dτ) : CQState X (dE * dτ) where
  stateMap x := (ρ.stateMap x).tensor τ
  weight_le_one := by
    calc ∑ x : X, ((ρ.stateMap x).tensor τ).trace
        = (∑ x : X, (ρ.stateMap x).trace) * τ.trace := by
          simp_rw [SubDensityOp.tensor_trace]; rw [← Finset.sum_mul]
      _ ≤ 1 * 1 :=
          mul_le_mul ρ.weight_le_one τ.trace_le_one τ.trace_nonneg zero_le_one
      _ = 1 := one_mul 1

/-- Each block of `CQState.tensorAncilla ρ τ` is the tensor of the corresponding block of `ρ`
with the fixed ancilla `τ`. -/
@[simp] lemma CQState.tensorAncilla_stateMap {X : Type*} [Fintype X] {dE dτ : ℕ}
    (ρ : CQState X dE) (τ : SubDensityOp dτ) (x : X) :
    (ρ.tensorAncilla τ).stateMap x = (ρ.stateMap x).tensor τ := rfl

/-- The trace of a CQ state's quantum marginal equals its total classical weight. -/
lemma CQState.quantumMarginal_trace {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) :
    ρ.quantumMarginal.trace = ∑ x : X, (ρ.stateMap x).trace := by
  change (ρ.quantumMarginalOp).trace.re = _
  rw [CQState.quantumMarginalOp, Matrix.trace_sum, Complex.re_sum]
  rfl

/-- **The unsmoothed decoupled-ancilla announce bound.**

Announcing an `x`-independent quantum ancilla `τ` into the conditioning register — moving from
`ρE` referenced to `σE` to `ρEV` (per-block product `ρE.block ⊗ τ`) referenced to `σE ⊗ τ` —
cannot decrease the conditional min-entropy.  The reference `τ` is referenced to itself, so the
feasible-scalar transfer is `t ↦ t` (`polyDim = 1`) and no dimension penalty is charged.

`hτ_weight` (the ancilla carries positive weight) makes the inequality nondegenerate: it forces
the tensor optimum strictly positive whenever the base optimum is, so `Real.log` monotonicity
applies on the nondegenerate branch.  This is the general-`σE`, `polyDim = 1` sibling of the
paired-CKR product-reference control lemma; the smoothing wrapper
`smoothMinEntropy_le_condTensor_decoupled_ancilla` mirrors the witness transport of
`smoothMinEntropy_le_tensor_own_marginal`, with this lemma discharging the per-witness step. -/
theorem conditionalMinEntropyReal_le_condTensor_decoupled_ancilla
    {X : Type*} [Fintype X] [Nonempty X] {dE dτ : ℕ}
    (ρE : CQState X dE) (ρEV : CQState X (dE * dτ))
    (σE : SubDensityOp dE) (τ : SubDensityOp dτ)
    (hproduct : ∀ x : X, (ρEV.stateMap x).toOp = ((ρE.stateMap x).tensor τ).toOp)
    (hτ_weight : 0 < τ.trace)
    (hfeas : hasFeasibleLambda ρE σE) :
    conditionalMinEntropyReal ρE σE ≤
      conditionalMinEntropyReal ρEV (SubDensityOp.tensor σE τ) := by
  -- Feasible-scalar transfer `t ↦ 1 · t` from `(ρE, σE)` to `(ρEV, σE ⊗ τ)`.
  have htransfer : ∀ {t : ℝ}, isFeasible ρE σE t →
      isFeasible ρEV (SubDensityOp.tensor σE τ) (1 * t) := by
    intro t ht
    rw [one_mul]
    refine ⟨ht.1, fun x => ?_⟩
    have hbase :
        opLe ((ρE.stateMap x).toOp ⊗ τ.toOp)
          (((Complex.ofReal t) • σE.toOp) ⊗ τ.toOp) :=
      opLe_tensor_psd (ρE.stateMap x).isHermitian
        ((posSemidefOp_implies_mathlib σE.toPosSemidefOp).smul (Complex.zero_le_real.mpr ht.1))
        (posSemidefOp_implies_mathlib τ.toPosSemidefOp) τ.isHermitian
        (ht.2 x) (fun _ => le_refl _)
    have hEV : (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp ⊗ τ.toOp := by
      rw [hproduct x]; rfl
    rw [hEV,
      show (Complex.ofReal t) • (SubDensityOp.tensor σE τ).toOp
          = ((Complex.ofReal t) • σE.toOp) ⊗ τ.toOp from
        (Op.tensor_smul_left (Complex.ofReal t) σE.toOp τ.toOp).symm]
    exact hbase
  -- Per-block trace factorizes: `weight ρEV = weight ρE · τ.trace`.
  have htr : ∀ x : X, (ρEV.stateMap x).trace = (ρE.stateMap x).trace * τ.trace := by
    intro x
    have h1 : (ρEV.stateMap x).trace = ((ρE.stateMap x).tensor τ).trace := by
      unfold SubDensityOp.trace; rw [hproduct x]
    rw [h1, SubDensityOp.tensor_trace]
  unfold conditionalMinEntropyReal
  set lamE := minFeasibleLambda ρE σE with hlamE
  set lamEV := minFeasibleLambda ρEV (SubDensityOp.tensor σE τ) with hlamEV
  have hlamEV_le : lamEV ≤ lamE := by
    have h := minFeasibleLambda_le_mul_of_isFeasible_scaling ρE σE ρEV
      (SubDensityOp.tensor σE τ) (c := 1) zero_le_one hfeas (fun {t} ht => htransfer ht)
    rwa [one_mul, ← hlamE, ← hlamEV] at h
  have hlamE_nn : 0 ≤ lamE := minFeasibleLambda_nonneg _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases eq_or_lt_of_le hlamE_nn with hlamE0 | hlamEpos
  · -- `lamE = 0` ⟹ `lamEV = 0`; both sides are the sentinel `0`.
    have hlamEV0 : lamEV = 0 :=
      le_antisymm (hlamE0 ▸ hlamEV_le) (minFeasibleLambda_nonneg _ _)
    rw [← hlamE0, hlamEV0, Real.log_zero, neg_zero, zero_div]
  · -- `lamE > 0` ⟹ `lamEV > 0`: positive base weight lifts to positive tensor weight.
    have hwE : 0 < ∑ x : X, (ρE.stateMap x).trace := by
      by_contra hw
      have hzero := CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρE hw
      have hfeas0 : isFeasible ρE σE 0 :=
        ⟨le_refl 0, fun x => by
          rw [hzero x, Complex.ofReal_zero, zero_smul]; exact fun _ => le_refl _⟩
      have hle0 := minFeasibleLambda_le_of_isFeasible ρE σE hfeas0
      rw [← hlamE] at hle0; linarith
    have hwEV : 0 < ∑ x : X, (ρEV.stateMap x).trace := by
      simp_rw [htr]; rw [← Finset.sum_mul]; exact mul_pos hwE hτ_weight
    have hfeasEV : hasFeasibleLambda ρEV (SubDensityOp.tensor σE τ) := by
      obtain ⟨t, ht⟩ := hfeas
      exact ⟨1 * t, htransfer ht⟩
    have hlamEVpos : 0 < lamEV := by
      rw [hlamEV]
      exact minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρEV
        (SubDensityOp.tensor σE τ) hwEV hfeasEV
    exact div_le_div_of_nonneg_right
      (neg_le_neg (Real.log_le_log hlamEVpos hlamEV_le)) hlog2.le

/-- The right-tensor extension of a CQ state by a fixed `SubDensityOp` block `τ`: the
`x`-independent ancilla `τ` is appended to the quantum register of every classical block,
raising the quantum dimension from `dE` to `dE * dτ`.  This is the explicit witness-transport
map underlying `smoothMinEntropy_le_condTensor_decoupled_ancilla`. -/
private noncomputable def CQState.tensorRightSub {X : Type*} [Fintype X] {dE dτ : ℕ}
    (ρ : CQState X dE) (τ : SubDensityOp dτ) : CQState X (dE * dτ) where
  stateMap x := (ρ.stateMap x).tensor τ
  weight_le_one := by
    have hsum : ∑ x : X, ((ρ.stateMap x).tensor τ).trace
        = (∑ x : X, (ρ.stateMap x).trace) * τ.trace := by
      simp_rw [SubDensityOp.tensor_trace]; rw [← Finset.sum_mul]
    rw [hsum]
    exact mul_le_one₀ ρ.weight_le_one τ.trace_nonneg τ.trace_le_one

@[simp] private lemma CQState.tensorRightSub_stateMap {X : Type*} [Fintype X] {dE dτ : ℕ}
    (ρ : CQState X dE) (τ : SubDensityOp dτ) (x : X) :
    (ρ.tensorRightSub τ).stateMap x = (ρ.stateMap x).tensor τ := rfl

/-- Cancelling a common positive real scalar from both sides of the operator order. -/
private lemma opLe_of_smul_ofReal_pos {n : ℕ} {A B : Op n} {c : ℝ} (hc : 0 < c)
    (h : opLe (Complex.ofReal c • A) (Complex.ofReal c • B)) : opLe A B := by
  intro v
  have hv := h v
  rw [quadraticForm_smul, quadraticForm_smul] at hv
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hv
  exact le_of_mul_le_mul_left hv hc

/-- Feasibility descends through the right-tensor extension: if `t` is feasible for the
`τ`-extended state against `σ ⊗ τ`, it is feasible for the base state against `σ`.  The
`τ` factor is cancelled by the (opLe-monotone) partial trace, using its positive weight. -/
private lemma isFeasible_of_isFeasible_tensorRightSub {X : Type*} [Fintype X] {dE dτ : ℕ}
    (ρ : CQState X dE) (σ : SubDensityOp dE) (τ : SubDensityOp dτ)
    (hτ : 0 < τ.trace) {t : ℝ}
    (h : isFeasible (ρ.tensorRightSub τ) (SubDensityOp.tensor σ τ) t) :
    isFeasible ρ σ t := by
  refine ⟨h.1, fun x => ?_⟩
  have hx := h.2 x
  rw [CQState.tensorRightSub_stateMap,
    show ((ρ.stateMap x).tensor τ).toOp = (ρ.stateMap x).toOp ⊗ τ.toOp from rfl,
    show (SubDensityOp.tensor σ τ).toOp = σ.toOp ⊗ τ.toOp from rfl,
    ← Op.tensor_smul_left] at hx
  have hpt := partialTraceB_opLe_of_opLe hx
  rw [partialTraceB_tensor_op, partialTraceB_tensor_op] at hpt
  have htr : Matrix.trace τ.toOp = Complex.ofReal τ.trace := by
    apply Complex.ext
    · rfl
    · rw [Complex.ofReal_im]; exact τ.trace_im_eq_zero
  rw [htr] at hpt
  exact opLe_of_smul_ofReal_pos hτ hpt

/-- With no feasible scalar, the minimal feasible `λ` is the empty infimum `0`. -/
private lemma minFeasibleLambda_eq_zero_of_not_feasible {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : SubDensityOp n) (h : ¬ hasFeasibleLambda ρ σ) :
    minFeasibleLambda ρ σ = 0 := by
  have hempty : setOf (isFeasible ρ σ) = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun ht => h ⟨t, ht⟩
  rw [minFeasibleLambda, hempty, Real.sInf_empty]

/-- The unsmoothed decoupled-ancilla bound, valid on both feasibility branches: the
right-tensor extension never decreases the conditional min-entropy, with no feasibility
hypothesis on the base pair.  On the feasible branch this is
`conditionalMinEntropyReal_le_condTensor_decoupled_ancilla`; on the infeasible branch both
sides collapse to the sentinel `0` (feasibility descends by
`isFeasible_of_isFeasible_tensorRightSub`). -/
private lemma conditionalMinEntropyReal_le_tensorRightSub {X : Type*} [Fintype X] [Nonempty X]
    {dE dτ : ℕ} (ρ : CQState X dE) (σ : SubDensityOp dE) (τ : SubDensityOp dτ)
    (hτ : 0 < τ.trace) :
    conditionalMinEntropyReal ρ σ ≤
      conditionalMinEntropyReal (ρ.tensorRightSub τ) (SubDensityOp.tensor σ τ) := by
  by_cases hfeas : hasFeasibleLambda ρ σ
  · exact conditionalMinEntropyReal_le_condTensor_decoupled_ancilla ρ (ρ.tensorRightSub τ)
      σ τ (fun x => rfl) hτ hfeas
  · have hnf : ¬ hasFeasibleLambda (ρ.tensorRightSub τ) (SubDensityOp.tensor σ τ) := by
      rintro ⟨t, ht⟩
      exact hfeas ⟨t, isFeasible_of_isFeasible_tensorRightSub ρ σ τ hτ ht⟩
    have h1 : conditionalMinEntropyReal ρ σ = 0 := by
      unfold conditionalMinEntropyReal
      rw [minFeasibleLambda_eq_zero_of_not_feasible ρ σ hfeas,
        Real.log_zero, neg_zero, zero_div]
    have h2 : conditionalMinEntropyReal (ρ.tensorRightSub τ) (SubDensityOp.tensor σ τ) = 0 := by
      unfold conditionalMinEntropyReal
      rw [minFeasibleLambda_eq_zero_of_not_feasible _ _ hnf,
        Real.log_zero, neg_zero, zero_div]
    exact le_of_eq (h1.trans h2.symm)

/-- The Bhattacharyya scalar bound behind the purified-distance contraction: for base
overlap `F` bounded by the geometric mean of the block weights `a, b`, and ancilla weight
`t`, the generalized fidelity does not decrease when both weights are scaled by `t` and the
overlap by `t`.  Reduces to `Real.sqrt_mul_add_sqrt_one_sub_mul_one_sub_le_one`. -/
private lemma fidelityGen_tensorRightSub_scalar
    {a b t F : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hF_nn : 0 ≤ F) (hF_le : F ≤ Real.sqrt (a * b)) :
    F + Real.sqrt ((1 - a) * (1 - b)) ≤
      t * F + Real.sqrt ((1 - a * t) * (1 - b * t)) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨ht0, ht1⟩ := ht
  have hbha : Real.sqrt (a * b) + Real.sqrt ((1 - a) * (1 - b)) ≤ 1 :=
    Real.sqrt_mul_add_sqrt_one_sub_mul_one_sub_le_one ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
  set u := Real.sqrt ((1 - a) * (1 - b)) with hu_def
  set w := Real.sqrt (a * b) with hw_def
  have hu_nn : 0 ≤ u := Real.sqrt_nonneg _
  have hw_nn : 0 ≤ w := hF_nn.trans hF_le
  have hu2 : u ^ 2 = (1 - a) * (1 - b) := by
    rw [hu_def, sq]; exact Real.mul_self_sqrt (mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1))
  have hw2 : w ^ 2 = a * b := by
    rw [hw_def, sq]; exact Real.mul_self_sqrt (mul_nonneg ha0 hb0)
  have huw1 : u + w ≤ 1 := by linarith only [hbha]
  have hstar : u + (1 - t) * w ≤ Real.sqrt ((1 - a * t) * (1 - b * t)) := by
    have hlhs_nn : 0 ≤ u + (1 - t) * w := add_nonneg hu_nn (mul_nonneg (sub_nonneg.mpr ht1) hw_nn)
    -- `1 - t ≥ 0`, and `(u + w)² ≤ 1` since `0 ≤ u + w ≤ 1`
    have hprod : 0 ≤ (1 - t) * (1 - (u + w) ^ 2) :=
      mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (pow_le_one₀ (add_nonneg hu_nn hw_nn) huw1))
    have hident : (1 - a * t) * (1 - b * t) - (u + (1 - t) * w) ^ 2
        = (1 - t) * (1 - (u + w) ^ 2) := by
      linear_combination (-t) * hu2 + (t * (1 - t)) * hw2
    have hsq_le : (u + (1 - t) * w) ^ 2 ≤ (1 - a * t) * (1 - b * t) := by
      linarith only [hident, hprod]
    calc u + (1 - t) * w
        = Real.sqrt ((u + (1 - t) * w) ^ 2) := (Real.sqrt_sq hlhs_nn).symm
      _ ≤ Real.sqrt ((1 - a * t) * (1 - b * t)) := Real.sqrt_le_sqrt hsq_le
  have hwF : (1 - t) * F ≤ (1 - t) * w := mul_le_mul_of_nonneg_left hF_le (sub_nonneg.mpr ht1)
  linarith only [hstar, hwF]

/-- Tensoring both CQ states blockwise with the same fixed ancilla `τ` on the right does not
increase CQ purified distance.  The per-block fidelity factorizes (`fidelity_tensor_mul` +
`fidelity_self_posSemidefOp`) as `τ.trace ·` the base fidelity, the traces scale by `τ.trace`,
and the generalized-fidelity comparison is the Bhattacharyya bound
`fidelityGen_tensorRightSub_scalar`. -/
private lemma CQState.purifiedDistance_tensorRightSub_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dτ : ℕ} [NeZero dE] [NeZero dτ] [NeZero (dE * dτ)]
    (ρ σ : CQState X dE) (τ : SubDensityOp dτ) :
    CQState.purifiedDistance (ρ.tensorRightSub τ) (σ.tensorRightSub τ) ≤
      CQState.purifiedDistance ρ σ := by
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (dE * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne _)⟩
  haveI : NeZero ((dE * dτ) * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (dE * dτ)) (NeZero.ne _)⟩
  unfold CQState.purifiedDistance
  apply purifiedDistance_le_of_fidelityGen_ge
  have ha : ρ.toJointDensity.trace ∈ Set.Icc (0:ℝ) 1 := ρ.toJointDensity.trace_mem_unit_interval
  have hb : σ.toJointDensity.trace ∈ Set.Icc (0:ℝ) 1 := σ.toJointDensity.trace_mem_unit_interval
  have ht : τ.trace ∈ Set.Icc (0:ℝ) 1 := τ.trace_mem_unit_interval
  have hF_nn : 0 ≤ Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
      σ.toJointDensity.toPosSemidefOp :=
    Quantum.Metrics.fidelity_nonneg_posSemidefOp _ _
  have hF_le : Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
        σ.toJointDensity.toPosSemidefOp
      ≤ Real.sqrt (ρ.toJointDensity.trace * σ.toJointDensity.trace) :=
    Quantum.Metrics.fidelity_le_sqrt_trace_mul_trace ρ.toJointDensity.toPosSemidefOp
      σ.toJointDensity.toPosSemidefOp
  have htr_ρ : (ρ.tensorRightSub τ).toJointDensity.trace
      = ρ.toJointDensity.trace * τ.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by
      rw [CQState.tensorRightSub_stateMap, SubDensityOp.tensor_trace]
  have htr_σ : (σ.tensorRightSub τ).toJointDensity.trace
      = σ.toJointDensity.trace * τ.trace := by
    rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by
      rw [CQState.tensorRightSub_stateMap, SubDensityOp.tensor_trace]
  have hfid : Quantum.Metrics.fidelity (ρ.tensorRightSub τ).toJointDensity.toPosSemidefOp
        (σ.tensorRightSub τ).toJointDensity.toPosSemidefOp
      = τ.trace * Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
        σ.toJointDensity.toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity (ρ := ρ.tensorRightSub τ)
        (σ := σ.tensorRightSub τ),
      CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity (ρ := ρ) (σ := σ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [CQState.tensorRightSub_stateMap, CQState.tensorRightSub_stateMap]
    have hbρ : ((ρ.stateMap x).tensor τ).toPosSemidefOp
        = (ρ.stateMap x).toPosSemidefOp.tensor τ.toPosSemidefOp := by
      apply Quantum.Operators.PosSemidefOp.ext; rfl
    have hbσ : ((σ.stateMap x).tensor τ).toPosSemidefOp
        = (σ.stateMap x).toPosSemidefOp.tensor τ.toPosSemidefOp := by
      apply Quantum.Operators.PosSemidefOp.ext; rfl
    rw [hbρ, hbσ, Quantum.Metrics.fidelity_tensor_mul, Quantum.Metrics.fidelity_self_posSemidefOp]
    rw [mul_comm]
    rfl
  unfold fidelityGen
  rw [htr_ρ, htr_σ, hfid]
  exact fidelityGen_tensorRightSub_scalar ha hb ht hF_nn hF_le

/-- A maximally mixed extension preserves the marginal's extended smooth entropy after
increasing the radius by `extensionRadius dR`. -/
theorem smoothMinEntropy_extension_maxMixed_ge_marginal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X, partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (ε : ℝ) :
    smoothMinEntropy ε ρE (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) ≤
      smoothMinEntropy (ε + extensionRadius dR) ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) := by
  haveI : NeZero (dE * dR) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR)⟩
  apply smoothMinEntropy_le_of_transport
  intro τ hd
  obtain ⟨ρtensor, hρtensor⟩ := CQState.tensorMaxMixed_exists (X := X) (dE := dE) dR ρE
  obtain ⟨τtensor, hτtensor⟩ := CQState.tensorMaxMixed_exists (X := X) (dE := dE) dR τ
  refine ⟨τtensor, ?_, fun _ ht => isFeasible_tensorMaxMixed_of_isFeasible _ _ hτtensor ht⟩
  have hradius : CQState.purifiedDistance ρER ρtensor ≤ extensionRadius dR := by
    apply CQState.purifiedDistance_tensorMaxMixed_le_extensionRadius
    intro x
    rw [hρtensor x, hblocks x]
  have hcontract := CQState.purifiedDistance_tensorMaxMixed_contract
    ρtensor τtensor ρE τ hρtensor hτtensor
  exact (CQState.purifiedDistance_triangle ρER ρtensor τtensor).trans
    (by simpa only [add_comm] using add_le_add hradius (hcontract.trans hd))

/-- Discarding a register increases extended smooth entropy against maximally mixed
references at the same radius. -/
theorem smoothMinEntropy_marginal_maxMixed_ge_extension
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X, partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (ε : ℝ) :
    smoothMinEntropy ε ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) ≤
      smoothMinEntropy ε ρE (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  haveI : NeZero (dE * dR) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR)⟩
  apply smoothMinEntropy_le_of_transport
  intro τ hd
  refine ⟨τ.partialTraceB, ?_, fun _ ht =>
    isFeasible_marginal_maxMixed_of_isFeasible_extension τ τ.partialTraceB (fun _ => rfl) ht⟩
  rw [← CQState.partialTraceB_eq_of_stateMap_toOp ρER ρE hblocks]
  exact (CQState.purifiedDistance_partialTraceB_contract ρER τ).trans hd

/-- Tensoring a maximally mixed register onto the state and the maximally mixed reference
preserves extended smooth min-entropy exactly, at the same radius. -/
theorem smoothMinEntropy_tensorMaxMixed_maxMixed_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρEtensor : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X, (ρEtensor.stateMap x).toOp =
      (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR))) (ε : ℝ) :
    smoothMinEntropy ε ρEtensor
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) =
      smoothMinEntropy ε ρE (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  haveI : NeZero (dE * dR) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR)⟩
  apply le_antisymm
  · apply smoothMinEntropy_marginal_maxMixed_ge_extension ρEtensor ρE _ ε
    intro x
    rw [hblocks x]
    exact partialTraceB_tensor_maxMixed_toOp _
  · apply smoothMinEntropy_le_of_transport
    intro τ hd
    obtain ⟨τtensor, hτtensor⟩ := CQState.tensorMaxMixed_exists (X := X) (dE := dE) dR τ
    refine ⟨τtensor, ?_, fun _ ht => isFeasible_tensorMaxMixed_of_isFeasible _ _ hτtensor ht⟩
    exact (CQState.purifiedDistance_tensorMaxMixed_contract
      ρEtensor τtensor ρE τ hblocks hτtensor).trans hd

/-- A correlated extension costs at most twice the logarithm of the added dimension in
extended smooth entropy, with the marginal reference tensored by the maximally mixed state. -/
theorem smoothMinEntropy_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dV : ℕ} [NeZero dE] [NeZero dV]
    (ρEV : CQState X (dE * dV)) (ρE : CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X, partialTraceB (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp)
    (ε : ℝ) :
    smoothMinEntropy ε ρE σE ≤
      smoothMinEntropy ε ρEV (σE.tensorMaxMixed dV) +
        ENNReal.ofReal ((2 : ℝ) * Real.log (dV : ℝ) / Real.log 2) := by
  haveI : NeZero (dE * dV) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dV)⟩
  apply smoothMinEntropy_le_add_of_transport
  intro τ hd
  have hmarg := CQState.partialTraceB_eq_of_stateMap_toOp ρEV ρE hblocks
  obtain ⟨τEV, hdEV, hpartial⟩ :=
    CQState.exists_extension_of_partialTraceB_purifiedDistance_stateMap_toOp_eq
      (α := X) (dR := dV) ρEV τ ε (by rw [hmarg]; exact hd)
  refine ⟨τEV, hdEV, fun k hk => ?_⟩
  have hdim : (0 : ℝ) < dV := Nat.cast_pos.mpr (NeZero.pos dV)
  have hpow := two_rpow_neg_sub_log k (sq_pos_of_pos hdim)
  rw [Real.log_pow, Nat.cast_ofNat] at hpow
  rw [hpow]
  exact isFeasible_extension_freeRef_of_isFeasible τEV τ σE hpartial hk

/-- Appending a decoupled ancilla referenced to itself increases extended smooth entropy,
including a zero ancilla. -/
theorem smoothMinEntropy_le_condTensor_decoupled_ancilla
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dτ : ℕ} [NeZero dE] [NeZero dτ] [NeZero (dE * dτ)]
    (ε : ℝ) (ρE : CQState X dE) (ρEV : CQState X (dE * dτ))
    (σE : SubDensityOp dE) (τ : SubDensityOp dτ)
    (hproduct : ∀ x : X, (ρEV.stateMap x).toOp = ((ρE.stateMap x).tensor τ).toOp) :
    smoothMinEntropy ε ρE σE ≤ smoothMinEntropy ε ρEV (SubDensityOp.tensor σE τ) := by
  have heq : ρEV = ρE.tensorRightSub τ := by
    obtain ⟨m, w⟩ := ρEV
    congr 1
    funext x
    exact SubDensityOp.ext (hproduct x)
  rw [heq]
  apply smoothMinEntropy_le_of_transport
  intro ρbar hd
  refine ⟨ρbar.tensorRightSub τ,
    (CQState.purifiedDistance_tensorRightSub_le ρE ρbar τ).trans hd, ?_⟩
  intro t ht
  refine ⟨ht.1, fun x => ?_⟩
  have hbase := opLe_tensor_psd (ρbar.stateMap x).isHermitian
    ((posSemidefOp_implies_mathlib σE.toPosSemidefOp).smul (Complex.zero_le_real.mpr ht.1))
    (posSemidefOp_implies_mathlib τ.toPosSemidefOp) τ.isHermitian (ht.2 x) (fun _ => le_rfl)
  simp only [Op.tensor_smul_left] at hbase
  exact hbase

/-- An extension inherits the marginal signed smooth entropy against maximally mixed references
when the enlarged target ball is bounded above. -/
theorem smoothMinEntropyReal_extension_maxMixed_ge_marginal_of_bddAbove
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (hbdd : BddAbove (setOf (isInSmoothedSetReal (ε + extensionRadius dR) ρER
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR)))))) :
    smoothMinEntropyReal ε ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) ≤
      smoothMinEntropyReal (ε + extensionRadius dR) ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) := by
  unfold smoothMinEntropyReal
  apply csSup_le_csSup hbdd
  · exact ⟨conditionalMinEntropyReal ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)), ρE, rfl, by
        rw [CQState.purifiedDistance_self_zero]
        exact hε_nn⟩
  · intro v hv
    rcases hv with ⟨ρEtilde, rfl, hdE⟩
    obtain ⟨ρEtensor, hρEtensor⟩ :=
      CQState.tensorMaxMixed_exists (X := X) (dE := dE) dR ρE
    obtain ⟨ρTtensor, hρTtensor⟩ :=
      CQState.tensorMaxMixed_exists (X := X) (dE := dE) dR ρEtilde
    refine ⟨ρTtensor, ?_, ?_⟩
    · exact (conditionalMinEntropyReal_tensorMaxMixed_maxMixed_eq
        ρTtensor ρEtilde hρTtensor).symm
    · have hradius :
          CQState.purifiedDistance ρER ρEtensor ≤ extensionRadius dR := by
        apply CQState.purifiedDistance_tensorMaxMixed_le_extensionRadius
        intro x
        rw [hρEtensor x, hblocks x]
      have hcontract :
          CQState.purifiedDistance ρEtensor ρTtensor ≤
            CQState.purifiedDistance ρE ρEtilde :=
        CQState.purifiedDistance_tensorMaxMixed_contract
          ρEtensor ρTtensor ρE ρEtilde hρEtensor hρTtensor
      have hsecond :
          CQState.purifiedDistance ρEtensor ρTtensor ≤ ε :=
        le_trans hcontract hdE
      have htri :=
        CQState.purifiedDistance_triangle ρER ρEtensor ρTtensor
      calc
        CQState.purifiedDistance ρER ρTtensor
            ≤ CQState.purifiedDistance ρER ρEtensor +
                CQState.purifiedDistance ρEtensor ρTtensor := htri
        _ ≤ extensionRadius dR + ε := add_le_add hradius hsecond
        _ = ε + extensionRadius dR := by ring

/-- A normalized extension inherits the marginal signed smooth entropy against maximally mixed
references after enlarging the radius by `extensionRadius dR`. -/
theorem smoothMinEntropyReal_extension_maxMixed_ge_marginal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (hε_lt : ε + extensionRadius dR < 1)
    (hρERnorm : ∑ x : X, (ρER.stateMap x).trace = 1)
    (_hfeasE :
      hasFeasibleLambda ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))) :
    smoothMinEntropyReal ε ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) ≤
      smoothMinEntropyReal (ε + extensionRadius dR) ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) := by
  exact
    smoothMinEntropyReal_extension_maxMixed_ge_marginal_of_bddAbove
      ρER ρE hblocks ε hε_nn
    (smoothMinEntropyReal_bddAbove (ε + extensionRadius dR) hε_lt ρER hρERnorm
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))))

/-- Taking the marginal does not decrease signed smooth min-entropy against the corresponding
maximally mixed references. -/
theorem smoothMinEntropyReal_marginal_maxMixed_ge_extension
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρER : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp)
    (ε : ℝ) :
    smoothMinEntropyReal ε ρER
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) ≤
      smoothMinEntropyReal ε ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  classical
  let σER : SubDensityOp (dE * dR) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))
  let σE : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  by_cases hε_nn : 0 ≤ ε
  · unfold smoothMinEntropyReal
    by_cases hbddE : BddAbove (setOf (isInSmoothedSetReal ε ρE σE))
    · apply csSup_le
      · exact ⟨conditionalMinEntropyReal ρER σER, ρER, rfl, by
          rw [CQState.purifiedDistance_self_zero]
          exact hε_nn⟩
      · intro v hv
        rcases hv with ⟨ρERtilde, rfl, hdER⟩
        let ρEtilde : CQState X dE := ρERtilde.partialTraceB
        have hρE_eq : ρER.partialTraceB = ρE :=
          CQState.partialTraceB_eq_of_stateMap_toOp ρER ρE hblocks
        have hdist : CQState.purifiedDistance ρE ρEtilde ≤ ε := by
          rw [← hρE_eq]
          exact le_trans
            (by
              simpa [ρEtilde] using
                CQState.purifiedDistance_partialTraceB_contract ρER ρERtilde)
            hdER
        have hmem :
            conditionalMinEntropyReal ρEtilde σE ∈
              setOf (isInSmoothedSetReal ε ρE σE) :=
          ⟨ρEtilde, rfl, hdist⟩
        have hblocks_tilde : ∀ x : X,
            partialTraceB (ρERtilde.stateMap x).toOp =
              (ρEtilde.stateMap x).toOp := by
          intro x
          rfl
        have hH :
            conditionalMinEntropyReal ρERtilde σER ≤
              conditionalMinEntropyReal ρEtilde σE := by
          simpa [σER, σE] using
            conditionalMinEntropyReal_marginal_maxMixed_ge_extension
              ρERtilde ρEtilde hblocks_tilde
        exact le_trans hH (le_csSup hbddE hmem)
    · have hnotER :
          ¬ BddAbove (setOf (isInSmoothedSetReal ε ρER σER)) := by
        simpa [σER, σE] using
          smoothedSetReal_extension_maxMixed_not_bddAbove_of_marginal
            ρER ρE hblocks ε hε_nn (by simpa [σE] using hbddE)
      rw [show sSup (setOf (isInSmoothedSetReal ε ρER σER)) =
          sSup (∅ : Set ℝ) from csSup_of_not_bddAbove hnotER,
        show sSup (setOf (isInSmoothedSetReal ε ρE σE)) =
          sSup (∅ : Set ℝ) from csSup_of_not_bddAbove hbddE]
  · have hε_lt : ε < 0 := lt_of_not_ge hε_nn
    unfold smoothMinEntropyReal
    have hleft_empty : setOf (isInSmoothedSetReal ε ρER σER) = ∅ := by
      ext v
      constructor
      · intro hv
        rcases hv with ⟨ρERtilde, _, hd⟩
        have hnn : 0 ≤ CQState.purifiedDistance ρER ρERtilde := by
          unfold CQState.purifiedDistance
          exact purifiedDistance_nonneg ρER.toJointDensity ρERtilde.toJointDensity
        linarith
      · intro hv
        cases hv
    have hright_empty : setOf (isInSmoothedSetReal ε ρE σE) = ∅ := by
      ext v
      constructor
      · intro hv
        rcases hv with ⟨ρEtilde, _, hd⟩
        have hnn : 0 ≤ CQState.purifiedDistance ρE ρEtilde := by
          unfold CQState.purifiedDistance
          exact purifiedDistance_nonneg ρE.toJointDensity ρEtilde.toJointDensity
        linarith
      · intro hv
        cases hv
    rw [hleft_empty, hright_empty, Real.sSup_empty]

/-- Tensoring with a maximally mixed register preserves the signed smooth floor after
subtracting `2 * log dR / log 2` at the same radius. -/
theorem smoothMinEntropyReal_extension_maxMixed_ge_marginal_sub_twice_log_dim_sameRadius
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρEtensor : CQState X (dE * dR)) (ρE : CQState X dE)
    (hblocks : ∀ x : X,
      (ρEtensor.stateMap x).toOp =
        (ρE.stateMap x).toOp ⊗ ((1 / (dR : ℂ)) • (1 : Op dR)))
    (ε : ℝ) (hε_nn : 0 ≤ ε) :
    smoothMinEntropyReal ε ρE
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
        (2 : ℝ) * Real.log (dR : ℝ) / Real.log 2 ≤
      smoothMinEntropyReal ε ρEtensor
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR))) := by
  classical
  set σE : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE) with hσE
  set σER : SubDensityOp (dE * dR) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR)) with hσER
  set penalty : ℝ := (2 : ℝ) * Real.log (dR : ℝ) / Real.log 2 with hpenalty
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogdR_nn : 0 ≤ Real.log (dR : ℝ) :=
    Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hpenalty_nn : 0 ≤ penalty := by
    rw [hpenalty]; positivity
  set A := setOf (isInSmoothedSetReal ε ρE σE) with hA
  set B := setOf (isInSmoothedSetReal ε ρEtensor σER) with hB
  have hA_ne : A.Nonempty := ⟨conditionalMinEntropyReal ρE σE, ρE, rfl, by
    rw [CQState.purifiedDistance_self_zero]; exact hε_nn⟩
  have h_AB : ∀ a ∈ A, ∃ b ∈ B, a - penalty ≤ b := by
    rintro a ⟨ρ', rfl, hd⟩
    obtain ⟨ρ'tensor, hρ'tensor⟩ :=
      CQState.tensorMaxMixed_exists (X := X) (dE := dE) dR ρ'
    refine ⟨conditionalMinEntropyReal ρ'tensor σER, ⟨ρ'tensor, rfl, ?_⟩, ?_⟩
    · -- SAME radius: tensoring a fixed register contracts the distance.
      have hcontract :
          CQState.purifiedDistance ρEtensor ρ'tensor ≤
            CQState.purifiedDistance ρE ρ' :=
        CQState.purifiedDistance_tensorMaxMixed_contract
          ρEtensor ρ'tensor ρE ρ' hblocks hρ'tensor
      exact le_trans hcontract hd
    · -- The conditional min-entropy is EXACTLY equal, so `a - penalty ≤ a = b`.
      have heq :
          conditionalMinEntropyReal ρ'tensor σER =
            conditionalMinEntropyReal ρ' σE := by
        simpa [hσER, hσE] using
          conditionalMinEntropyReal_tensorMaxMixed_maxMixed_eq
            ρ'tensor ρ' hρ'tensor
      rw [heq]; linarith [hpenalty_nn]
  have h_BA : ∀ b ∈ B, ∃ a ∈ A, b ≤ a := by
    rintro b ⟨ρtilde, rfl, hd⟩
    set ρtildeE : CQState X dE := ρtilde.partialTraceB with hρtildeE
    refine ⟨conditionalMinEntropyReal ρtildeE σE, ⟨ρtildeE, rfl, ?_⟩, ?_⟩
    · -- The `E`-marginal of `ρEtensor` is `ρE`, so partialTraceB contracts to `≤ ε`.
      have hmarg : ρEtensor.partialTraceB = ρE :=
        CQState.partialTraceB_eq_of_stateMap_toOp ρEtensor ρE (fun x => by
          rw [hblocks x]; exact partialTraceB_tensor_maxMixed_toOp _)
      have hcontract :
          CQState.purifiedDistance ρEtensor.partialTraceB ρtilde.partialTraceB ≤
            CQState.purifiedDistance ρEtensor ρtilde :=
        CQState.purifiedDistance_partialTraceB_contract ρEtensor ρtilde
      rw [hmarg] at hcontract
      exact le_trans hcontract hd
    · -- Discarding `R` cannot decrease the conditional min-entropy.
      have hblocks_tilde : ∀ x : X,
          partialTraceB (ρtilde.stateMap x).toOp = (ρtildeE.stateMap x).toOp :=
        fun x => rfl
      simpa [hσER, hσE] using
        conditionalMinEntropyReal_marginal_maxMixed_ge_extension
          ρtilde ρtildeE hblocks_tilde
  change sSup A - penalty ≤ sSup B
  by_cases hBddB : BddAbove B
  · -- B bounded above: use the csSup transfer helper directly.
    exact csSup_sub_le_csSup_of_forall_exists_sub_le A B penalty hA_ne hBddB h_AB
  · -- B not bounded above: `sSup B = 0`. Show `sSup A - penalty ≤ 0`.
    rw [Real.sSup_of_not_bddAbove hBddB]
    by_cases hBddA : BddAbove A
    · -- A bounded above: the reverse map bounds B by `sSup A`, contradiction.
      exfalso
      apply hBddB
      refine ⟨sSup A, ?_⟩
      intro b hb
      obtain ⟨a, ha_mem, hba⟩ := h_BA b hb
      exact le_trans hba (le_csSup hBddA ha_mem)
    · -- A not bounded above: `sSup A = 0`. Need `0 - penalty ≤ 0`.
      rw [Real.sSup_of_not_bddAbove hBddA]
      linarith [hpenalty_nn]

/-- Extending the marginal by a register of dimension `dV` costs at most `2 * log dV / log 2` in
signed smooth min-entropy at the same radius. -/
theorem smoothMinEntropyReal_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dV : ℕ} [NeZero dE] [NeZero dV]
    (ρEV : CQState X (dE * dV)) (ρE : CQState X dE) (σE : SubDensityOp dE)
    (hblocks : ∀ x : X,
      partialTraceB (ρEV.stateMap x).toOp = (ρE.stateMap x).toOp)
    (ε : ℝ) (hε_nn : 0 ≤ ε) :
    smoothMinEntropyReal ε ρE σE -
        (2 : ℝ) * Real.log (dV : ℝ) / Real.log 2 ≤
      smoothMinEntropyReal ε ρEV (σE.tensorMaxMixed dV) := by
  classical
  haveI : NeZero (dE * dV) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dV)⟩
  set penalty : ℝ := (2 : ℝ) * Real.log (dV : ℝ) / Real.log 2 with hpenalty
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogdV_nn : 0 ≤ Real.log (dV : ℝ) :=
    Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hpenalty_nn : 0 ≤ penalty := by rw [hpenalty]; positivity
  set A := setOf (isInSmoothedSetReal ε ρE σE) with hA
  set B := setOf (isInSmoothedSetReal ε ρEV (σE.tensorMaxMixed dV)) with hB
  have hA_ne : A.Nonempty := ⟨conditionalMinEntropyReal ρE σE, ρE, rfl, by
    rw [CQState.purifiedDistance_self_zero]; exact hε_nn⟩
  have hmarg : ρEV.partialTraceB = ρE :=
    CQState.partialTraceB_eq_of_stateMap_toOp ρEV ρE hblocks
  have h_AB : ∀ a ∈ A, ∃ b ∈ B, a - penalty ≤ b := by
    rintro a ⟨ρ', rfl, hd⟩
    obtain ⟨ρ'EV, hdEV, hpartial'⟩ :=
      CQState.exists_extension_of_partialTraceB_purifiedDistance_stateMap_toOp_eq
        (α := X) (dR := dV) ρEV ρ' ε (by rw [hmarg]; exact hd)
    refine ⟨conditionalMinEntropyReal ρ'EV (σE.tensorMaxMixed dV),
      ⟨ρ'EV, rfl, hdEV⟩, ?_⟩
    by_cases hposE : 0 < minFeasibleLambda ρ' σE
    · -- `λ_E > 0` forces `λ_EV > 0`: apply the unsmoothed free-reference penalty.
      have hsetE_ne : (setOf (isFeasible ρ' σE)).Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        have : minFeasibleLambda ρ' σE = 0 := by
          unfold minFeasibleLambda; rw [hempty, Real.sInf_empty]
        exact (ne_of_gt hposE) this
      obtain ⟨s, hs⟩ := hsetE_ne
      have hfeasEV : hasFeasibleLambda ρ'EV (σE.tensorMaxMixed dV) :=
        ⟨(dV : ℝ) ^ 2 * s,
          isFeasible_extension_freeRef_of_isFeasible ρ'EV ρ' σE hpartial' hs⟩
      have hposEV : 0 < minFeasibleLambda ρ'EV (σE.tensorMaxMixed dV) :=
        lt_of_lt_of_le hposE
          (minFeasibleLambda_marginal_freeRef_le_extension
            ρ'EV ρ' σE hpartial' hfeasEV)
      have hbound :=
        conditionalMinEntropyReal_extension_freeRef_ge_sub_twice_log_dim
          ρ'EV ρ' σE hpartial' hposEV hposE
      simpa [hpenalty] using hbound
    · -- `λ_E = 0`: then `a = 0`, `λ_EV ≤ dV²·0 = 0` so `b = 0`, hence `a - penalty ≤ 0 = b`.
      have hlamE0 : minFeasibleLambda ρ' σE = 0 :=
        le_antisymm (not_lt.mp hposE) (minFeasibleLambda_nonneg ρ' σE)
      have ha0 : conditionalMinEntropyReal ρ' σE = 0 := by
        unfold conditionalMinEntropyReal
        rw [hlamE0, Real.log_zero, neg_zero, zero_div]
      have hlamEV_le : minFeasibleLambda ρ'EV (σE.tensorMaxMixed dV) ≤ 0 := by
        have := minFeasibleLambda_extension_freeRef_le ρ'EV ρ' σE hpartial'
        rwa [hlamE0, mul_zero] at this
      have hlamEV0 : minFeasibleLambda ρ'EV (σE.tensorMaxMixed dV) = 0 :=
        le_antisymm hlamEV_le
          (minFeasibleLambda_nonneg ρ'EV (σE.tensorMaxMixed dV))
      have hb0 : conditionalMinEntropyReal ρ'EV (σE.tensorMaxMixed dV) = 0 := by
        unfold conditionalMinEntropyReal
        rw [hlamEV0, Real.log_zero, neg_zero, zero_div]
      rw [ha0, hb0]; linarith [hpenalty_nn]
  have h_BA : ∀ b ∈ B, ∃ a ∈ A, b ≤ a := by
    rintro b ⟨ρtilde, rfl, hd⟩
    set ρtildeE : CQState X dE := ρtilde.partialTraceB with hρtildeE
    refine ⟨conditionalMinEntropyReal ρtildeE σE, ⟨ρtildeE, rfl, ?_⟩, ?_⟩
    · -- `partialTraceB` contracts the distance; the center marginal is `ρE`.
      have hcontract :
          CQState.purifiedDistance ρEV.partialTraceB ρtilde.partialTraceB ≤
            CQState.purifiedDistance ρEV ρtilde :=
        CQState.purifiedDistance_partialTraceB_contract ρEV ρtilde
      rw [hmarg] at hcontract
      exact le_trans hcontract hd
    · -- Discarding `V` cannot decrease the conditional min-entropy.
      have hblocks_tilde : ∀ x : X,
          partialTraceB (ρtilde.stateMap x).toOp = (ρtildeE.stateMap x).toOp :=
        fun x => rfl
      by_cases hposE : 0 < minFeasibleLambda ρtildeE σE
      · by_cases hfeasEV :
            hasFeasibleLambda ρtilde (σE.tensorMaxMixed dV)
        · exact conditionalMinEntropyReal_marginal_freeRef_ge_extension_of_pos
            ρtilde ρtildeE σE hblocks_tilde hfeasEV hposE
        · -- EV feasible set empty: `b = conditionalMinEntropyReal ρtilde (...) = 0 ≤ a`.
          have hEV_empty : setOf (isFeasible ρtilde (σE.tensorMaxMixed dV)) = ∅ := by
            apply Set.not_nonempty_iff_eq_empty.mp
            rintro ⟨t, ht⟩; exact hfeasEV ⟨t, ht⟩
          have hb0 : conditionalMinEntropyReal ρtilde (σE.tensorMaxMixed dV) = 0 := by
            unfold conditionalMinEntropyReal minFeasibleLambda
            rw [hEV_empty, Real.sInf_empty, Real.log_zero, neg_zero, zero_div]
          rw [hb0]
          exfalso
          have hE_empty : setOf (isFeasible ρtildeE σE) = ∅ := by
            apply Set.not_nonempty_iff_eq_empty.mp
            rintro ⟨t, ht⟩
            exact hfeasEV ⟨(dV : ℝ) ^ 2 * t,
              isFeasible_extension_freeRef_of_isFeasible ρtilde ρtildeE σE
                hblocks_tilde ht⟩
          have hlamE0 : minFeasibleLambda ρtildeE σE = 0 := by
            unfold minFeasibleLambda; rw [hE_empty, Real.sInf_empty]
          exact (ne_of_gt hposE) hlamE0
      · -- `λ_E = 0`: `a = 0`. Then `λ_EV ≤ dV²·0 = 0`, so `b = 0 ≤ 0 = a`.
        have hlamE0 : minFeasibleLambda ρtildeE σE = 0 :=
          le_antisymm (not_lt.mp hposE) (minFeasibleLambda_nonneg ρtildeE σE)
        have ha0 : conditionalMinEntropyReal ρtildeE σE = 0 := by
          unfold conditionalMinEntropyReal
          rw [hlamE0, Real.log_zero, neg_zero, zero_div]
        have hlamEV_le :
            minFeasibleLambda ρtilde (σE.tensorMaxMixed dV) ≤ 0 := by
          have := minFeasibleLambda_extension_freeRef_le
            ρtilde ρtildeE σE hblocks_tilde
          rwa [hlamE0, mul_zero] at this
        have hlamEV0 : minFeasibleLambda ρtilde (σE.tensorMaxMixed dV) = 0 :=
          le_antisymm hlamEV_le
            (minFeasibleLambda_nonneg ρtilde (σE.tensorMaxMixed dV))
        have hb0 : conditionalMinEntropyReal ρtilde (σE.tensorMaxMixed dV) = 0 := by
          unfold conditionalMinEntropyReal
          rw [hlamEV0, Real.log_zero, neg_zero, zero_div]
        rw [ha0, hb0]
  change sSup A - penalty ≤ sSup B
  by_cases hBddB : BddAbove B
  · exact csSup_sub_le_csSup_of_forall_exists_sub_le A B penalty hA_ne hBddB h_AB
  · rw [Real.sSup_of_not_bddAbove hBddB]
    by_cases hBddA : BddAbove A
    · exfalso
      apply hBddB
      refine ⟨sSup A, ?_⟩
      intro b hb
      obtain ⟨a, ha_mem, hba⟩ := h_BA b hb
      exact le_trans hba (le_csSup hBddA ha_mem)
    · rw [Real.sSup_of_not_bddAbove hBddA]
      linarith [hpenalty_nn]

/-- Tensoring both state and reference with a positive-weight independent ancilla does not
decrease signed smooth min-entropy when the target ball is bounded above. -/
theorem smoothMinEntropyReal_le_condTensor_decoupled_ancilla
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dτ : ℕ} [NeZero dE] [NeZero dτ] [NeZero (dE * dτ)]
    (ε : ℝ) (hε : 0 ≤ ε)
    (ρE : CQState X dE) (ρEV : CQState X (dE * dτ))
    (σE : SubDensityOp dE) (τ : SubDensityOp dτ)
    (hproduct : ∀ x : X, (ρEV.stateMap x).toOp = ((ρE.stateMap x).tensor τ).toOp)
    (hτ_weight : 0 < τ.trace)
    (hbdd : BddAbove (setOf (isInSmoothedSetReal ε ρEV (SubDensityOp.tensor σE τ)))) :
    smoothMinEntropyReal ε ρE σE ≤ smoothMinEntropyReal ε ρEV (SubDensityOp.tensor σE τ) := by
  have hρEV_eq : ρEV = ρE.tensorRightSub τ := by
    obtain ⟨m, w⟩ := ρEV
    congr 1
    funext x
    exact SubDensityOp.ext (hproduct x)
  subst hρEV_eq
  have key : ∀ a ∈ setOf (isInSmoothedSetReal ε ρE σE),
      ∃ b ∈ setOf (isInSmoothedSetReal ε (ρE.tensorRightSub τ) (SubDensityOp.tensor σE τ)),
        a - 0 ≤ b := by
    intro a ha
    obtain ⟨blockbar, rfl, hd⟩ := ha
    refine ⟨conditionalMinEntropyReal (blockbar.tensorRightSub τ) (SubDensityOp.tensor σE τ),
      ⟨blockbar.tensorRightSub τ, rfl, ?_⟩, ?_⟩
    · exact le_trans (CQState.purifiedDistance_tensorRightSub_le ρE blockbar τ) hd
    · rw [sub_zero]
      exact conditionalMinEntropyReal_le_tensorRightSub blockbar σE τ hτ_weight
  have hmain := csSup_sub_le_csSup_of_forall_exists_sub_le _ _ 0
    (smoothedSetReal_nonempty hε ρE σE) hbdd key
  simpa only [smoothMinEntropyReal, sub_zero] using hmain

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
