import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.Quantum.Operators.InverseSqrt

/-!
# Quantum LHL Algebra — trace expansions and uniform-output quadratic cancellation

Matrix trace identities used in the quantum leftover hash lemma. The file
first proves pure complex matrix identities for shifted squares, finite sums,
and fixed outer sandwiches, then instantiates the real-part identity for
`extractorWeightedOp` and `CQState.quantumMarginalOp`.

## Main definitions

This file defines no new structures.

## Main statements

- `sandwich_sq_expand`: pointwise expansion of `(A - c • B)^2`.
- `sum_trace_outer_sandwich_sq_expand_re`: real-part finite-sum trace expansion
  under a fixed outer sandwich.
- `uniform_card_quadratic_coeff`: scalar cancellation for the uniform output block.
- `sum_tr_SDsqS_eq_sum_tr_SMzsqS_sub_loss`: LHL-centered block-square expansion.
-/

open Matrix Quantum.Operators
open InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

/-!
## Pure algebra layer
-/

/-- Pointwise expansion of a shifted square in matrix algebra:
    `(A - c • B)(A - c • B) = A*A - c•(A*B) - c•(B*A) + c²•(B*B)`.

    Works for any two square matrices `A B : Matrix ι ι ℂ` and any scalar `c : ℂ`. -/
lemma sandwich_sq_expand {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (c : ℂ) :
    (A - c • B) * (A - c • B) =
      A * A - c • (A * B) - c • (B * A) + (c * c) • (B * B) := by
  calc (A - c • B) * (A - c • B)
      = A * A - A * (c • B) - ((c • B) * A - (c • B) * (c • B)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    _ = A * A - c • (A * B) - (c • (B * A) - (c * c) • (B * B)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = A * A - c • (A * B) - c • (B * A) + (c * c) • (B * B) := by
        abel

/-- Trace of the pointwise square expansion. -/
lemma trace_sandwich_sq_expand {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (c : ℂ) :
    ((A - c • B) * (A - c • B)).trace =
      (A * A).trace - c * (A * B).trace - c * (B * A).trace +
        (c * c) * (B * B).trace := by
  rw [sandwich_sq_expand]
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
  rw [Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]

/-- If a finite sum of matrices is `B`, tracing after fixed left and right
multiplication commutes with the sum. -/
lemma sum_trace_mul_left_right_of_sum {ι Z : Type*} [Fintype ι] [Fintype Z]
    (A : Z → Matrix ι ι ℂ) (B L R : Matrix ι ι ℂ)
    (hSum : ∑ z : Z, A z = B) :
    ∑ z : Z, (L * A z * R).trace = (L * B * R).trace := by
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, hSum]

/-- If a finite sum of matrices is `B`, tracing after fixed right
multiplication commutes with the sum. -/
lemma sum_trace_mul_right_of_sum {ι Z : Type*} [Fintype ι] [Fintype Z]
    (A : Z → Matrix ι ι ℂ) (B R : Matrix ι ι ℂ)
    (hSum : ∑ z : Z, A z = B) :
    ∑ z : Z, (A z * R).trace = (B * R).trace := by
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hSum]

/-- If a finite sum of matrices is `B`, tracing after fixed left
multiplication commutes with the sum. -/
lemma sum_trace_mul_left_of_sum {ι Z : Type*} [Fintype ι] [Fintype Z]
    (A : Z → Matrix ι ι ℂ) (B L : Matrix ι ι ℂ)
    (hSum : ∑ z : Z, A z = B) :
    ∑ z : Z, (L * A z).trace = (L * B).trace := by
  rw [← Matrix.trace_sum, ← Finset.mul_sum, hSum]

/-- Summed trace identity for centered squares when `∑ z, A z = B`. -/
lemma sum_trace_sandwich_sq_expand {ι Z : Type*} [Fintype ι] [Fintype Z]
    (A : Z → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (c : ℂ)
    (hSum : ∑ z : Z, A z = B) :
    ∑ z : Z, ((A z - c • B) * (A z - c • B)).trace =
      (∑ z : Z, (A z * A z).trace) +
        (-2 * c + (Fintype.card Z : ℂ) * (c * c)) * (B * B).trace := by
  simp_rw [trace_sandwich_sq_expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hSumAB : ∑ z : Z, (A z * B).trace = (B * B).trace := by
    exact sum_trace_mul_right_of_sum (A := A) (B := B) (R := B) hSum
  have hSumBA : ∑ z : Z, (B * A z).trace = (B * B).trace := by
    exact sum_trace_mul_left_of_sum (A := A) (B := B) (L := B) hSum
  rw [hSumAB, hSumBA]
  ring

/-- Trace expansion of a shifted square with a fixed outer sandwich matrix. -/
lemma trace_outer_sandwich_sq_expand {ι : Type*} [Fintype ι]
    (S A B : Matrix ι ι ℂ) (c : ℂ) :
    (S * (A - c • B) * (A - c • B) * S).trace =
      (S * A * A * S).trace - c * (S * A * B * S).trace -
        c * (S * B * A * S).trace +
        (c * c) * (S * B * B * S).trace := by
  have h := congrArg (fun M : Matrix ι ι ℂ => (S * M * S).trace)
    (sandwich_sq_expand A B c)
  simpa only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] using h

/-- Summed outer-sandwich trace identity.  If `∑ z, A z = B`, the cross terms
collapse to the fixed `B` square. -/
lemma sum_trace_outer_sandwich_sq_expand {ι Z : Type*} [Fintype ι] [Fintype Z]
    (S : Matrix ι ι ℂ) (A : Z → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (c : ℂ)
    (hSum : ∑ z : Z, A z = B) :
    ∑ z : Z, (S * (A z - c • B) * (A z - c • B) * S).trace =
      (∑ z : Z, (S * A z * A z * S).trace) +
        (-2 * c + (Fintype.card Z : ℂ) * (c * c)) *
          (S * B * B * S).trace := by
  simp_rw [trace_outer_sandwich_sq_expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hSumSAB : ∑ z : Z, (S * A z * B * S).trace =
      (S * B * B * S).trace := by
    simpa only [Matrix.mul_assoc] using
      (sum_trace_mul_left_right_of_sum (A := A) (B := B)
        (L := S) (R := B * S) hSum)
  have hSumSBA : ∑ z : Z, (S * B * A z * S).trace =
      (S * B * B * S).trace := by
    simpa only [Matrix.mul_assoc] using
      (sum_trace_mul_left_right_of_sum (A := A) (B := B)
        (L := S * B) (R := S) hSum)
  rw [hSumSAB, hSumSBA]
  ring

/-- Real-part form of `sum_trace_outer_sandwich_sq_expand` for real scalars
coerced to complex matrix scalars. -/
lemma sum_trace_outer_sandwich_sq_expand_re {ι Z : Type*} [Fintype ι] [Fintype Z]
    (S : Matrix ι ι ℂ) (A : Z → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (c : ℝ)
    (hSum : ∑ z : Z, A z = B) :
    ∑ z : Z, (S * (A z - (c : ℂ) • B) * (A z - (c : ℂ) • B) * S).trace.re =
      (∑ z : Z, (S * A z * A z * S).trace.re) +
        (-2 * c + (Fintype.card Z : ℝ) * (c * c)) *
          (S * B * B * S).trace.re := by
  have h := congrArg Complex.re
    (sum_trace_outer_sandwich_sq_expand S A B (c : ℂ) hSum)
  simpa only [Complex.re_sum, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.neg_re, Complex.add_im, Complex.neg_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.natCast_re, Complex.natCast_im, zero_mul, mul_zero, sub_zero,
    add_zero, zero_add, neg_zero] using h

/-- The scalar coefficient left by the uniform-output quadratic expansion. -/
lemma uniform_card_quadratic_coeff {Z : Type*} [Fintype Z] [Nonempty Z] :
    -2 * (1 / (Fintype.card Z : ℝ)) +
        (Fintype.card Z : ℝ) *
          ((1 / (Fintype.card Z : ℝ)) * (1 / (Fintype.card Z : ℝ))) =
      -(1 / (Fintype.card Z : ℝ)) := by
  let q : ℝ := Fintype.card Z
  have hq : q ≠ 0 := by
    have hq_pos : (0 : ℝ) < (Fintype.card Z : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
    exact ne_of_gt (by simpa only [q] using hq_pos)
  change -2 * (1 / q) + q * ((1 / q) * (1 / q)) = -(1 / q)
  calc
    -2 * (1 / q) + q * ((1 / q) * (1 / q))
        = -2 * (1 / q) + (q * (1 / q)) * (1 / q) := by ring
    _ = -2 * (1 / q) + 1 * (1 / q) := by rw [one_div, mul_inv_cancel₀ hq]
    _ = -(1 / q) := by ring

/-!
## Quantum assembly layer
-/

/-- Expanding the uniform-output centered extractor square under the
inverse-square-root sandwich gives the marginal loss term. -/
lemma sum_tr_SDsqS_eq_sum_tr_SMzsqS_sub_loss
    {S X Z : Type*} [Fintype S] [Fintype X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ}
    (H : QuantumHashFamily S X Z)
    (ρ : CQState X n)
    {σ : Op n} (hσ : σ.PosDef) :
    ∑ z : Z,
        (hσ.inverseSqrt *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            hσ.inverseSqrt).trace.re =
      ∑ z : Z, (hσ.inverseSqrt * extractorWeightedOp H ρ z *
          extractorWeightedOp H ρ z * hσ.inverseSqrt).trace.re -
      (1 / (Fintype.card Z : ℝ)) *
        (hσ.inverseSqrt * ρ.quantumMarginalOp * ρ.quantumMarginalOp *
            hσ.inverseSqrt).trace.re := by
  have hExpand := sum_trace_outer_sandwich_sq_expand_re hσ.inverseSqrt
    (fun z : Z => extractorWeightedOp H ρ z) ρ.quantumMarginalOp
    ((1 : ℝ) / (Fintype.card Z : ℝ))
    (sum_extractorWeightedOp_eq_quantumMarginalOp H ρ)
  calc
    ∑ z : Z,
        (hσ.inverseSqrt *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            (extractorWeightedOp H ρ z -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            hσ.inverseSqrt).trace.re
        = (∑ z : Z, (hσ.inverseSqrt * extractorWeightedOp H ρ z *
              extractorWeightedOp H ρ z * hσ.inverseSqrt).trace.re) +
            (-2 * ((1 : ℝ) / (Fintype.card Z : ℝ)) +
                (Fintype.card Z : ℝ) *
                  (((1 : ℝ) / (Fintype.card Z : ℝ)) *
                    ((1 : ℝ) / (Fintype.card Z : ℝ)))) *
              (hσ.inverseSqrt * ρ.quantumMarginalOp * ρ.quantumMarginalOp *
                hσ.inverseSqrt).trace.re := by
          simpa using hExpand
    _ = (∑ z : Z, (hσ.inverseSqrt * extractorWeightedOp H ρ z *
              extractorWeightedOp H ρ z * hσ.inverseSqrt).trace.re) -
          (1 / (Fintype.card Z : ℝ)) *
            (hσ.inverseSqrt * ρ.quantumMarginalOp * ρ.quantumMarginalOp *
              hσ.inverseSqrt).trace.re := by
        rw [uniform_card_quadratic_coeff (Z := Z)]
        ring

end InfoTheory.QuantumLHL

end -- noncomputable section
