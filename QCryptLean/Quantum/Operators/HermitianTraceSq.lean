import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.Operators.InverseSqrt

/-!
# Hermitian Trace-Square Inequalities — Hilbert-Schmidt convexity and sandwich positivity

Small self-contained algebraic helpers used by the 2-universal LHL collision
bound and the λ*-bound assembly.

Given Hermitian operators, the map `A ↦ Tr(A²).re` is the squared
Hilbert–Schmidt norm; the lemmas below are the usual Cauchy–Schwarz-style
bounds on this functional.

## Main definitions

This file defines no new structures.

## Main statements

- `tr_sq_re_nonneg_of_isHermitian`: for Hermitian `A`, `0 ≤ (A*A).trace.re`.
- `trace_sandwich_sq_nonneg`: for positive-definite `σ` and Hermitian `A`,
  `0 ≤ Tr(σ⁻¹/² A A σ⁻¹/²).re`.
- `two_tr_mul_re_le_tr_sq_re_add_tr_sq_re`: for Hermitian `A`, `B`,
  `2 * (A*B).trace.re ≤ (A*A).trace.re + (B*B).trace.re`.
- `tr_sum_sq_re_le_card_mul_sum_tr_sq_re`: for Hermitian-valued `A : S → Op n`
  and finite `S`,
  `((∑ s, A s)*(∑ s, A s)).trace.re ≤ |S| * ∑ s, (A s * A s).trace.re`.
- `tr_smul_avg_sq_re_le_avg_tr_sq_re`: the normalized version, for `|S| ≥ 1`.
- `tr_smul_avg_right_mul_conjTranspose_mul_self_re_le_avg`: the corresponding
  Hilbert-Schmidt square Jensen inequality after right multiplication by a
  fixed operator; this version does not require Hermiticity.
- `tr_smul_avg_right_mul_sq_re_le_avg_tr_right_mul_sq_re`: the Hermitian
  cyclic form used by the quantum LHL sandwich bound.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace Quantum.Operators

/-- For Hermitian `A`, the real part of `Tr(A*A)` is nonnegative (it is the
squared Hilbert–Schmidt norm of `A`). -/
lemma tr_sq_re_nonneg_of_isHermitian {n : ℕ} {A : Op n} (hA : A.IsHermitian) :
    0 ≤ (A * A).trace.re := by
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rw [hA.eq] at h
  exact h.trace_re_nonneg

/-- **Hermitian sandwich-square trace positivity.**

For Hermitian `S` and Hermitian `A`, the real part of `Tr(S · A · A · S)` is
non-negative. Proof: `S · A · A · S = (S · A) · (S · A)†` (using `S† = S` and
`A† = A`), which is positive semidefinite, hence its trace is real and
non-negative. -/
lemma tr_S_ASqS_re_nonneg {n : ℕ}
    {S A : Op n} (hS : S.IsHermitian) (hA : A.IsHermitian) :
    0 ≤ (S * A * A * S).trace.re := by
  -- Set X := S * A. Then X * X† = S * A * (S * A)† = S * A * (A * S) = S * A * A * S.
  set X : Op n := S * A with hX_def
  have hXdag : X.conjTranspose = A * S := by
    rw [hX_def, Matrix.conjTranspose_mul, hA.eq, hS.eq]
  have hXXdag : X * X.conjTranspose = S * A * A * S := by
    rw [hXdag, hX_def]
    -- (S*A) * (A*S) = S*A*A*S by associativity
    simp [Matrix.mul_assoc]
  have hPSD : (X * X.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose X
  have hPSD' : (S * A * A * S).PosSemidef := by rw [← hXXdag]; exact hPSD
  exact hPSD'.trace_re_nonneg

/-- For any positive-definite `σ : Op n` and Hermitian `A : Op n`,
`(σ⁻¹/² · A · A · σ⁻¹/²).trace.re ≥ 0`. Holds because the sandwich form equals
`‖σ⁻¹/² · A‖²_HS` (a squared Hilbert-Schmidt norm). -/
lemma trace_sandwich_sq_nonneg
    {n : ℕ} [NeZero n]
    {σ : Op n} (hσ : σ.PosDef) (A : Op n) (hA : A.IsHermitian) :
    0 ≤ (hσ.inverseSqrt * A * A * hσ.inverseSqrt).trace.re := by
  have hS : hσ.inverseSqrt.IsHermitian := hσ.inverseSqrt_isHermitian
  have hEq :
      hσ.inverseSqrt * A * A * hσ.inverseSqrt =
        (hσ.inverseSqrt * A) * (hσ.inverseSqrt * A)ᴴ := by
    rw [Matrix.conjTranspose_mul, hA.eq, hS.eq]
    simp only [Matrix.mul_assoc]
  rw [hEq]
  exact (Matrix.posSemidef_self_mul_conjTranspose
    (hσ.inverseSqrt * A)).trace_re_nonneg

/-- Pair bound (squared Hilbert–Schmidt Cauchy–Schwarz in the real-part form):
for Hermitian `A`, `B`, `2 Re Tr(AB) ≤ Re Tr(A²) + Re Tr(B²)`. Obtained from
`0 ≤ Re Tr((A-B)²)`. -/
lemma two_tr_mul_re_le_tr_sq_re_add_tr_sq_re {n : ℕ}
    {A B : Op n} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    2 * (A * B).trace.re ≤ (A * A).trace.re + (B * B).trace.re := by
  have hAB : (A - B).IsHermitian := hA.sub hB
  have hNonneg : 0 ≤ ((A - B) * (A - B)).trace.re :=
    tr_sq_re_nonneg_of_isHermitian hAB
  -- Expand (A - B)(A - B) = A*A - A*B - B*A + B*B
  have hExpand : (A - B) * (A - B) = A * A - A * B - B * A + B * B := by
    noncomm_ring
  rw [hExpand] at hNonneg
  -- Compute real part of the expansion
  have hcomm : (B * A).trace = (A * B).trace := Matrix.trace_mul_comm B A
  have hTr :
      (A * A - A * B - B * A + B * B).trace =
        (A * A).trace - (A * B).trace - (B * A).trace + (B * B).trace := by
    simp [Matrix.trace_add, sub_eq_add_neg, Matrix.trace_neg]
  rw [hTr, hcomm] at hNonneg
  -- Now the real part splits
  have hRe :
      ((A * A).trace - (A * B).trace - (A * B).trace + (B * B).trace).re =
        (A * A).trace.re - (A * B).trace.re - (A * B).trace.re +
          (B * B).trace.re := by
    simp [Complex.sub_re, Complex.add_re]
  rw [hRe] at hNonneg
  linarith

/-- If a real kernel is pairwise bounded by diagonal weights, then its double
sum is bounded by cardinality times the sum of those weights. -/
lemma sum_sum_le_card_mul_sum_of_two_mul_le_add {S : Type*} [Fintype S]
    (b : S → S → ℝ) (d : S → ℝ)
    (h : ∀ s t, 2 * b s t ≤ d s + d t) :
    (∑ s : S, ∑ t : S, b s t) ≤
      (Fintype.card S : ℝ) * ∑ s, d s := by
  have hSumPair :
      2 * ∑ s : S, ∑ t : S, b s t ≤
        ∑ s : S, ∑ t : S, (d s + d t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t _ => h s t
  have hRHS :
      ∑ s : S, ∑ t : S, (d s + d t) =
        2 * (Fintype.card S : ℝ) * ∑ s, d s := by
    have hSplit :
        ∑ s : S, ∑ t : S, (d s + d t) =
          (∑ s : S, ∑ _ : S, d s) + (∑ _ : S, ∑ t : S, d t) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [← Finset.sum_add_distrib]
    rw [hSplit]
    have h1 : (∑ s : S, ∑ _ : S, d s) =
        (Fintype.card S : ℝ) * ∑ s, d s := by
      simp [Finset.sum_const, Finset.card_univ, Finset.sum_mul, mul_comm]
    have h2 : (∑ _ : S, ∑ t : S, d t) =
        (Fintype.card S : ℝ) * ∑ s, d s := by
      simp [Finset.sum_const, Finset.card_univ, Finset.sum_mul, mul_comm]
    rw [h1, h2]
    ring
  rw [hRHS] at hSumPair
  linarith

/-- Divide a `x ≤ |S| * y` bound by `|S|²`, for nonempty finite `S`. -/
lemma inv_card_sq_mul_le_inv_card_mul_of_le_card_mul {S : Type*} [Fintype S]
    [Nonempty S] {x y : ℝ} (h : x ≤ (Fintype.card S : ℝ) * y) :
    (1 / (Fintype.card S : ℝ)) * (1 / (Fintype.card S : ℝ)) * x ≤
      (1 / (Fintype.card S : ℝ)) * y := by
  set N : ℝ := (Fintype.card S : ℝ)
  change x ≤ N * y at h
  have hNpos : 0 < N :=
    (Nat.cast_pos (α := ℝ)).mpr Fintype.card_pos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hcoef_nn : 0 ≤ (1 / N) * (1 / N) := by
    have h1 : 0 ≤ 1 / N := by positivity
    exact mul_nonneg h1 h1
  have hmul := mul_le_mul_of_nonneg_left h hcoef_nn
  have hsimp : (1 / N) * (1 / N) * (N * y) = (1 / N) * y := by
    field_simp
  change (1 / N) * (1 / N) * x ≤ (1 / N) * y
  exact hmul.trans_eq hsimp

/-- For Hermitian-valued `A : S → Op n` over a finite type,
`((∑ s, A s) * (∑ s, A s)).trace.re ≤ |S| * ∑ s, (A s * A s).trace.re`. -/
lemma tr_sum_sq_re_le_card_mul_sum_tr_sq_re {S : Type*} [Fintype S] {n : ℕ}
    (A : S → Op n) (hA : ∀ s, (A s).IsHermitian) :
    ((∑ s, A s) * (∑ s, A s)).trace.re ≤
      (Fintype.card S : ℝ) * ∑ s, (A s * A s).trace.re := by
  have hExpand :
      ((∑ s, A s) * (∑ s, A s)).trace.re =
        ∑ s : S, ∑ s' : S, (A s * A s').trace.re := by
    rw [Finset.sum_mul_sum]
    simp only [Matrix.trace_sum, Complex.re_sum]
  rw [hExpand]
  exact sum_sum_le_card_mul_sum_of_two_mul_le_add
    (fun s s' => (A s * A s').trace.re)
    (fun s => (A s * A s).trace.re)
    (fun s s' => two_tr_mul_re_le_tr_sq_re_add_tr_sq_re (hA s) (hA s'))

/-- Normalized (averaged) form of `tr_sum_sq_re_le_card_mul_sum_tr_sq_re`
using ℝ-smul (matching the `extractorWeightedOp` convention):
`Re Tr(((1/|S|) • ∑ s, A s)²) ≤ (1/|S|) * ∑ s, Re Tr((A s)²)`. -/
lemma tr_smul_avg_sq_re_le_avg_tr_sq_re {S : Type*} [Fintype S] [Nonempty S]
    {n : ℕ} (A : S → Op n) (hA : ∀ s, (A s).IsHermitian) :
    (((1 / (Fintype.card S : ℝ)) • ∑ s, A s) *
        ((1 / (Fintype.card S : ℝ)) • ∑ s, A s)).trace.re ≤
      (1 / (Fintype.card S : ℝ)) * ∑ s, (A s * A s).trace.re := by
  set N : ℝ := (Fintype.card S : ℝ)
  have hsmul :
      ((1 / N : ℝ) • ∑ s, A s) * ((1 / N : ℝ) • ∑ s, A s) =
        ((1 / N : ℝ) * (1 / N : ℝ)) • ((∑ s, A s) * (∑ s, A s)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hsmul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change (1 / (Fintype.card S : ℝ)) * (1 / (Fintype.card S : ℝ)) *
      ((∑ s, A s) * (∑ s, A s)).trace.re ≤
    (1 / (Fintype.card S : ℝ)) * ∑ s, (A s * A s).trace.re
  exact inv_card_sq_mul_le_inv_card_mul_of_le_card_mul
    (S := S) (tr_sum_sq_re_le_card_mul_sum_tr_sq_re A hA)

/-!
## Hilbert-Schmidt square after right multiplication
-/

/-- For arbitrary `A`, the real part of `Tr(A†A)` is nonnegative. -/
lemma tr_conjTranspose_mul_self_re_nonneg {n : ℕ} (A : Op n) :
    0 ≤ (A.conjTranspose * A).trace.re :=
  (Matrix.posSemidef_conjTranspose_mul_self A).trace_re_nonneg

/-- Pair bound for the Hilbert-Schmidt trace pairing:
`2 Re Tr(A†B) ≤ Re Tr(A†A) + Re Tr(B†B)`. -/
lemma two_tr_conjTranspose_mul_re_le_tr_conjTranspose_mul_self_re_add
    {n : ℕ} (A B : Op n) :
    2 * (A.conjTranspose * B).trace.re ≤
      (A.conjTranspose * A).trace.re + (B.conjTranspose * B).trace.re := by
  have hNonneg : 0 ≤ ((A - B).conjTranspose * (A - B)).trace.re :=
    tr_conjTranspose_mul_self_re_nonneg (A - B)
  have hExpand :
      (A - B).conjTranspose * (A - B) =
        A.conjTranspose * A - A.conjTranspose * B -
          B.conjTranspose * A + B.conjTranspose * B := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  rw [hExpand] at hNonneg
  have hConjTrace :
      (B.conjTranspose * A).trace = star ((A.conjTranspose * B).trace) := by
    have h1 : ((A.conjTranspose * B).conjTranspose).trace =
        star ((A.conjTranspose * B).trace) :=
      Matrix.trace_conjTranspose _
    have h2 : (A.conjTranspose * B).conjTranspose = B.conjTranspose * A := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [← h1, h2]
  have hTr :
      (A.conjTranspose * A - A.conjTranspose * B -
            B.conjTranspose * A + B.conjTranspose * B).trace =
        (A.conjTranspose * A).trace - (A.conjTranspose * B).trace -
          (B.conjTranspose * A).trace + (B.conjTranspose * B).trace := by
    simp [Matrix.trace_add, sub_eq_add_neg, Matrix.trace_neg]
  rw [hTr, hConjTrace] at hNonneg
  have hRe :
      ((A.conjTranspose * A).trace - (A.conjTranspose * B).trace -
          star ((A.conjTranspose * B).trace) +
          (B.conjTranspose * B).trace).re =
        (A.conjTranspose * A).trace.re - (A.conjTranspose * B).trace.re -
          (A.conjTranspose * B).trace.re + (B.conjTranspose * B).trace.re := by
    simp [Complex.sub_re, Complex.add_re, Complex.conj_re]
  rw [hRe] at hNonneg
  linarith

/-- For arbitrary matrix-valued `A`, the Hilbert-Schmidt square of a finite sum
is bounded by cardinality times the sum of Hilbert-Schmidt squares. -/
lemma tr_conjTranspose_sum_mul_sum_re_le_card_mul_sum
    {S : Type*} [Fintype S] {n : ℕ} (A : S → Op n) :
    (((∑ s, A s).conjTranspose) * (∑ s, A s)).trace.re ≤
      (Fintype.card S : ℝ) *
        ∑ s, ((A s).conjTranspose * A s).trace.re := by
  have hExpand :
      (((∑ s, A s).conjTranspose) * (∑ s, A s)).trace.re =
        ∑ s : S, ∑ s' : S, ((A s).conjTranspose * A s').trace.re := by
    rw [Matrix.conjTranspose_sum, Finset.sum_mul_sum]
    simp only [Matrix.trace_sum, Complex.re_sum]
  rw [hExpand]
  exact sum_sum_le_card_mul_sum_of_two_mul_le_add
    (fun s s' => ((A s).conjTranspose * A s').trace.re)
    (fun s => ((A s).conjTranspose * A s).trace.re)
    (fun s s' => two_tr_conjTranspose_mul_re_le_tr_conjTranspose_mul_self_re_add (A s) (A s'))

/-- Normalized Hilbert-Schmidt Jensen inequality for arbitrary operators. -/
lemma tr_smul_avg_conjTranspose_mul_self_re_le_avg
    {S : Type*} [Fintype S] [Nonempty S] {n : ℕ} (A : S → Op n) :
    ((((1 / (Fintype.card S : ℝ)) • ∑ s, A s).conjTranspose) *
        ((1 / (Fintype.card S : ℝ)) • ∑ s, A s)).trace.re ≤
      (1 / (Fintype.card S : ℝ)) *
        ∑ s, ((A s).conjTranspose * A s).trace.re := by
  set N : ℝ := (Fintype.card S : ℝ)
  have hsmul :
      ((((1 / N : ℝ) • ∑ s, A s).conjTranspose) *
          ((1 / N : ℝ) • ∑ s, A s)) =
        ((1 / N : ℝ) * (1 / N : ℝ)) •
          (((∑ s, A s).conjTranspose) * (∑ s, A s)) := by
    simp [Matrix.conjTranspose_smul, smul_smul]
  rw [hsmul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change (1 / (Fintype.card S : ℝ)) * (1 / (Fintype.card S : ℝ)) *
      (((∑ s, A s).conjTranspose) * (∑ s, A s)).trace.re ≤
    (1 / (Fintype.card S : ℝ)) *
      ∑ s, ((A s).conjTranspose * A s).trace.re
  exact inv_card_sq_mul_le_inv_card_mul_of_le_card_mul
    (S := S) (tr_conjTranspose_sum_mul_sum_re_le_card_mul_sum A)

/-- Hilbert-Schmidt Jensen after right multiplication by a fixed operator. -/
lemma tr_smul_avg_right_mul_conjTranspose_mul_self_re_le_avg
    {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
    (A : S → Op n) (T : Op n) :
    ((((1 / (Fintype.card S : ℝ)) • ∑ s, A s) * T).conjTranspose *
        (((1 / (Fintype.card S : ℝ)) • ∑ s, A s) * T)).trace.re ≤
      (1 / (Fintype.card S : ℝ)) *
        ∑ s, (((A s * T).conjTranspose) * (A s * T)).trace.re := by
  have h := tr_smul_avg_conjTranspose_mul_self_re_le_avg (fun s => A s * T)
  have hsum : (∑ s, A s * T) = (∑ s, A s) * T := by
    rw [Finset.sum_mul]
  simpa [hsum, Matrix.smul_mul] using h

/-- A real average of Hermitian operators is Hermitian. -/
lemma isHermitian_smul_sum_of_isHermitian
    {S : Type*} [Fintype S] {n : ℕ} (A : S → Op n)
    (c : ℝ) (hA : ∀ s, (A s).IsHermitian) :
    (c • ∑ s, A s).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [RCLike.star_def]
  congr 1
  exact Finset.sum_congr rfl fun s _ => (hA s).eq

/-- Hermitian cyclic form of the right-multiplied Hilbert-Schmidt Jensen
inequality. If `T` and all `A s` are Hermitian, then
`Re Tr(T * avg(A) * avg(A) * T)` is bounded by the average of
`Re Tr(T * A_s * A_s * T)`. -/
lemma tr_smul_avg_right_mul_sq_re_le_avg_tr_right_mul_sq_re
    {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
    (A : S → Op n) (T : Op n)
    (hA : ∀ s, (A s).IsHermitian) (hT : T.IsHermitian) :
    (T * ((1 / (Fintype.card S : ℝ)) • ∑ s, A s) *
        ((1 / (Fintype.card S : ℝ)) • ∑ s, A s) * T).trace.re ≤
      (1 / (Fintype.card S : ℝ)) *
        ∑ s, (T * A s * A s * T).trace.re := by
  set avg : Op n := (1 / (Fintype.card S : ℝ)) • ∑ s, A s with havg_def
  have hAvg : avg.IsHermitian := by
    rw [havg_def]
    exact isHermitian_smul_sum_of_isHermitian A _ hA
  have h :=
    tr_smul_avg_right_mul_conjTranspose_mul_self_re_le_avg A T
  have hLeft :
      ((((1 / (Fintype.card S : ℝ)) • ∑ s, A s) * T).conjTranspose *
          (((1 / (Fintype.card S : ℝ)) • ∑ s, A s) * T)).trace.re =
        (T * ((1 / (Fintype.card S : ℝ)) • ∑ s, A s) *
          ((1 / (Fintype.card S : ℝ)) • ∑ s, A s) * T).trace.re := by
    rw [← havg_def]
    simp [Matrix.conjTranspose_mul, hT.eq, hAvg.eq, Matrix.mul_assoc]
  have hRight :
      (∑ s, (((A s * T).conjTranspose) * (A s * T)).trace.re) =
        ∑ s, (T * A s * A s * T).trace.re := by
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [Matrix.conjTranspose_mul, hT.eq, (hA s).eq, Matrix.mul_assoc]
  rw [hLeft, hRight] at h
  exact h

end Quantum.Operators

end -- noncomputable section
