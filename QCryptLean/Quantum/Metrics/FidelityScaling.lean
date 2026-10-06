import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.Quantum.Metrics.TraceNorm.FidelitySymm
import QCryptLean.Quantum.Operators.MatrixSqrt

/-!
# Fidelity Scaling — CFC-square-root scaling, Uhlmann fidelity under smul, trace-product bound

This module collects ingredients for fidelity estimates between
sub-normalized PSD operators: the homogeneity of `CFC.sqrt` under real
scaling, the resulting scaling identity for Uhlmann fidelity, and a
trace-product upper bound reduced to the normalized case.

## Main statements
- `Quantum.Metrics.fidelity_smul_smul`:
  `F(α • A, β • B) = √(α β) · F(A, B)` for `α β ≥ 0` and PSD `A, B`.
- `Quantum.Metrics.fidelity_le_sqrt_trace_mul_trace`:
  For PSD operators `A B`, `F(A, B) ≤ √((tr A).re · (tr B).re)`.
  The generic case is reduced to the normalized case via the scaling
  identity `fidelity_smul_smul` (together with `fidelity_le_one`), and the
  `tr A = 0` boundary is handled via `Matrix.PosSemidef.trace_eq_zero_iff`.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-! ## The scaling identity

For nonneg scalars `α β` and PSD operators `A B`,
`F(α • A, β • B) = √(α β) · F(A, B)`.

The identity at the level of `CFC.sqrt` is: for `0 ≤ r` and `0 ≤ A`,
`CFC.sqrt (r • A) = Real.sqrt r • CFC.sqrt A`.  That is
`Quantum.Operators.sqrt_ofReal_smul` in
`QCryptLean.Quantum.Operators.MatrixSqrt`; this file only uses it.
-/

/-- Scaling identity for the Uhlmann fidelity:
    `F(α • A, β • B) = √(α β) · F(A, B)` for `α β ≥ 0` and PSD `A B`.

    Phrased at the underlying matrix level so it does not depend on a
    `SMul ℝ (PosSemidefOp n)` instance. -/
lemma fidelity_smul_smul {n : ℕ} [NeZero n]
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (A B : PosSemidefOp n) :
    letI : PartialOrder (Op n) := Matrix.instPartialOrder
    letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
    letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
    (Matrix.trace
      (CFC.sqrt
        (CFC.sqrt (((α : ℂ) • A.toOp))
          * (((β : ℂ) • B.toOp))
          * CFC.sqrt (((α : ℂ) • A.toOp))))).re
        = Real.sqrt (α * β) * fidelity A B := by
  let : PartialOrder (Op n) := Matrix.instPartialOrder
  let : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  -- Abbreviations
  set sqrtA : Op n := CFC.sqrt A.toOp
  set sandwich : Op n := sqrtA * B.toOp * sqrtA
  have hA_ps : A.toOp.PosSemidef := posSemidefOp_implies_mathlib A
  have hB_ps : B.toOp.PosSemidef := posSemidefOp_implies_mathlib B
  have hαβ_nn : 0 ≤ α * β := mul_nonneg hα hβ
  -- sqrtA is Hermitian (needed for PSD of sandwich)
  have hsqrtA_herm : sqrtA.IsHermitian :=
    ((CFC.sqrt_nonneg (a := A.toOp)).posSemidef).isHermitian
  have hsandwich_ps : sandwich.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hB_ps sqrtA
    rwa [hsqrtA_herm.eq] at h
  -- Step 1: pull out √α from CFC.sqrt (α • A.toOp)
  have hsq_α : CFC.sqrt ((α : ℂ) • A.toOp) = (Real.sqrt α : ℂ) • sqrtA :=
    sqrt_ofReal_smul hα hA_ps
  -- Step 2: compute the scalar √α * β * √α = α * β (lifted to ℂ)
  have hscalar :
      (Real.sqrt α : ℂ) * (β : ℂ) * (Real.sqrt α : ℂ) = ((α * β : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc Real.sqrt α * β * Real.sqrt α
        = Real.sqrt α * Real.sqrt α * β := by ring
      _ = α * β := by rw [Real.mul_self_sqrt hα]
  -- Step 3: reduce the full sandwich
  have hbig :
      CFC.sqrt ((α : ℂ) • A.toOp) * ((β : ℂ) • B.toOp)
          * CFC.sqrt ((α : ℂ) • A.toOp)
        = ((α * β : ℝ) : ℂ) • sandwich := by
    rw [hsq_α, smul_mul_smul_comm, smul_mul_smul_comm, hscalar]
  -- Step 4: pull out √(α β) from CFC.sqrt of the scaled sandwich
  have hsq_sw :
      CFC.sqrt (((α * β : ℝ) : ℂ) • sandwich)
        = (Real.sqrt (α * β) : ℂ) • CFC.sqrt sandwich :=
    sqrt_ofReal_smul hαβ_nn hsandwich_ps
  -- Step 5: take trace and real part
  rw [hbig, hsq_sw, Matrix.trace_smul, smul_eq_mul]
  change (((Real.sqrt (α * β) : ℝ) : ℂ) * Matrix.trace (CFC.sqrt sandwich)).re
      = Real.sqrt (α * β) * fidelity A B
  rw [Complex.re_ofReal_mul]
  rfl

/-! ## Trace-product fidelity bound

For PSD operators `A, B` with `tr A ≤ 1` and `tr B ≤ 1`, we have
`F(A, B) ≤ √(tr A · tr B)`.

Strategy:
* If `tr A = 0` then `A = 0` by `Matrix.PosSemidef.trace_eq_zero_iff`, hence
  `√A = 0`, the sandwich `√A · B · √A = 0`, and fidelity is `0`.
* If `tr A > 0` and `tr B > 0`, normalize `A / tr A` and `B / tr B` to get
  `DensityOp`s, apply `fidelity_le_one`, and rescale by `fidelity_smul_smul`.
-/

/-- Normalize a PSD operator with strictly positive trace to a density operator.
    The underlying matrix is `((tr A).re)⁻¹ • A.toOp`, which is PSD and has
    trace `1`. -/
noncomputable def normalizePosSemidefOp {n : ℕ}
    (A : PosSemidefOp n) (ha : 0 < (Matrix.trace A.toOp).re) : DensityOp n :=
  let a : ℝ := (Matrix.trace A.toOp).re
  have hA_ps : A.toOp.PosSemidef := posSemidefOp_implies_mathlib A
  have ha_nn : (0 : ℝ) ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hP_ps : (((a⁻¹ : ℝ) : ℂ) • A.toOp).PosSemidef :=
    posSemidef_ofReal_smul A.toOp hA_ps a⁻¹ ha_nn
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hIm_zero : (Matrix.trace A.toOp).im = 0 := by
    have h := hA_ps.trace_nonneg
    rw [Complex.le_def] at h
    exact h.2.symm
  have hcoerce : Matrix.trace A.toOp = (a : ℂ) := by
    apply Complex.ext
    · show (Matrix.trace A.toOp).re = ((a : ℂ)).re
      rw [Complex.ofReal_re]
    · show (Matrix.trace A.toOp).im = ((a : ℂ)).im
      rw [Complex.ofReal_im, hIm_zero]
  { toOp := ((a⁻¹ : ℝ) : ℂ) • A.toOp
    isHermitian := hP_ps.1
    pos_semidef := fun x => by
      have h := hP_ps.dotProduct_mulVec_nonneg x
      rw [Complex.nonneg_iff] at h
      exact h.1
    trace_one := by
      rw [Matrix.trace_smul, smul_eq_mul, hcoerce,
          ← Complex.ofReal_mul, inv_mul_cancel₀ ha_ne,
          Complex.ofReal_one] }

/-- The underlying `Op` of `normalizePosSemidefOp A ha` is `(tr A).re⁻¹ • A.toOp`. -/
lemma normalizePosSemidefOp_toOp {n : ℕ}
    (A : PosSemidefOp n) (ha : 0 < (Matrix.trace A.toOp).re) :
    (normalizePosSemidefOp A ha).toOp =
      ((((Matrix.trace A.toOp).re)⁻¹ : ℝ) : ℂ) • A.toOp := rfl

/-- For PSD operators `A B`, the fidelity is bounded by
    the geometric mean of the traces: `F(A, B) ≤ √(tr A · tr B)`.

    Strategy: if either trace is zero, `PosSemidef.trace_eq_zero_iff` makes the
    corresponding operator zero and both sides collapse. Otherwise normalize to
    density operators, apply `fidelity_le_one`, and rescale via
    `fidelity_smul_smul`. -/
lemma fidelity_le_sqrt_trace_mul_trace {n : ℕ} [NeZero n]
    (A B : PosSemidefOp n) :
    fidelity A B ≤ Real.sqrt ((Matrix.trace A.toOp).re * (Matrix.trace B.toOp).re) := by
  let : PartialOrder (Op n) := Matrix.instPartialOrder
  let : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  set a : ℝ := (Matrix.trace A.toOp).re with ha_def
  set b : ℝ := (Matrix.trace B.toOp).re with hb_def
  have hA_ps : A.toOp.PosSemidef := posSemidefOp_implies_mathlib A
  have hB_ps : B.toOp.PosSemidef := posSemidefOp_implies_mathlib B
  have ha_nn : 0 ≤ a := (Complex.nonneg_iff.mp hA_ps.trace_nonneg).1
  have hb_nn : 0 ≤ b := (Complex.nonneg_iff.mp hB_ps.trace_nonneg).1
  have hA_im : (Matrix.trace A.toOp).im = 0 :=
    ((Complex.nonneg_iff.mp hA_ps.trace_nonneg).2).symm
  have hB_im : (Matrix.trace B.toOp).im = 0 :=
    ((Complex.nonneg_iff.mp hB_ps.trace_nonneg).2).symm
  have hF_nn : 0 ≤ fidelity A B := fidelity_nonneg_posSemidefOp A B
  -- Boundary case: `a = 0`. Then `A.toOp = 0`, fidelity is 0, and RHS is 0.
  by_cases ha_zero : a = 0
  · have hA_trace_zero : Matrix.trace A.toOp = 0 := by
      apply Complex.ext
      · simp only [Complex.zero_re]; exact ha_zero
      · rw [Complex.zero_im]; exact hA_im
    have hA_zero : A.toOp = 0 := hA_ps.trace_eq_zero_iff.mp hA_trace_zero
    have hFid_zero : fidelity A B = 0 := by
      unfold fidelity sqrtPosSemidefOp
      simp [hA_zero]
    rw [hFid_zero, ha_zero, zero_mul, Real.sqrt_zero]
  -- Boundary case: `b = 0`. Then `B.toOp = 0`, fidelity is 0, and RHS is 0.
  by_cases hb_zero : b = 0
  · have hB_trace_zero : Matrix.trace B.toOp = 0 := by
      apply Complex.ext
      · simp only [Complex.zero_re]; exact hb_zero
      · rw [Complex.zero_im]; exact hB_im
    have hB_zero : B.toOp = 0 := hB_ps.trace_eq_zero_iff.mp hB_trace_zero
    have hFid_zero : fidelity A B = 0 := by
      unfold fidelity sqrtPosSemidefOp
      simp [hB_zero]
    rw [hFid_zero, hb_zero, mul_zero, Real.sqrt_zero]
  -- Generic case: both traces strictly positive.
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nn (Ne.symm ha_zero)
  have hb_pos : 0 < b := lt_of_le_of_ne hb_nn (Ne.symm hb_zero)
  have ha_ne : a ≠ 0 := ha_zero
  have hb_ne : b ≠ 0 := hb_zero
  -- Normalize: A = a • A', B = b • B' with A', B' density operators.
  set A' : DensityOp n := normalizePosSemidefOp A ha_pos with hA'_def
  set B' : DensityOp n := normalizePosSemidefOp B hb_pos with hB'_def
  have hA'_toOp : A'.toOp = ((a : ℂ))⁻¹ • A.toOp := by
    change (normalizePosSemidefOp A ha_pos).toOp = ((a : ℂ))⁻¹ • A.toOp
    rw [normalizePosSemidefOp_toOp, Complex.ofReal_inv]
  have hB'_toOp : B'.toOp = ((b : ℂ))⁻¹ • B.toOp := by
    change (normalizePosSemidefOp B hb_pos).toOp = ((b : ℂ))⁻¹ • B.toOp
    rw [normalizePosSemidefOp_toOp, Complex.ofReal_inv]
  have ha_cne : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha_ne
  have hb_cne : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb_ne
  have hA_scale : ((a : ℂ) • A'.toOp) = A.toOp := by
    rw [hA'_toOp, smul_smul, mul_inv_cancel₀ ha_cne, one_smul]
  have hB_scale : ((b : ℂ) • B'.toOp) = B.toOp := by
    rw [hB'_toOp, smul_smul, mul_inv_cancel₀ hb_cne, one_smul]
  -- fidelity_smul_smul: the scaled trace expression equals √(ab)·F(A', B').
  have h_scaling :=
    fidelity_smul_smul (α := a) (β := b) ha_nn hb_nn
      A'.toPosSemidefOp B'.toPosSemidefOp
  -- Rewrite the scaled expression back into fidelity A B via hA_scale/hB_scale.
  have h_expand : fidelity A B =
      Real.sqrt (a * b) * fidelity A'.toPosSemidefOp B'.toPosSemidefOp := by
    rw [← h_scaling, hA_scale, hB_scale]
    rfl
  -- fidelity_le_one on the normalized pair.
  have h_fid_le_one :
      Quantum.Metrics.fidelity A'.toPosSemidefOp B'.toPosSemidefOp ≤ 1 :=
    fidelity_le_one A' B'
  have h_fid_nn :
      0 ≤ Quantum.Metrics.fidelity A'.toPosSemidefOp B'.toPosSemidefOp :=
    fidelity_nonneg_posSemidefOp A'.toPosSemidefOp B'.toPosSemidefOp
  have h_sqrt_nn : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  calc fidelity A B
      = Real.sqrt (a * b) * fidelity A'.toPosSemidefOp B'.toPosSemidefOp := h_expand
    _ ≤ Real.sqrt (a * b) * 1 :=
          mul_le_mul_of_nonneg_left h_fid_le_one h_sqrt_nn
    _ = Real.sqrt (a * b) := mul_one _

end Quantum.Metrics

end
