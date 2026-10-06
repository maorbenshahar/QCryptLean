import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.Metrics.TraceNormDilation
import QCryptLean.Quantum.Channels.CPTP.DiamondNorm

/-!
# Generalized Trace Distance for Sub-Normalized Operators

Trace distance extended to sub-normalized (positive semidefinite, trace ≤ 1)
operators, following Tomamichel 2016.

## Main definitions
- `traceDistanceGen`: generalized trace distance for PSD operators (eq. 3.23)

## Main statements
- `traceDistanceGen_nonneg`: nonnegativity
- `traceDistanceGen_symm`: symmetry
- `traceDistanceGen_eq_traceDistance`: agrees with `traceDistance` when both operators
  have equal traces (in particular for normalized density operators)
- `traceDistanceGen_le_of_traceNorm_sub_le_of_trace_re_sub_eq`: monotonicity from
  trace-norm contraction and trace-gap preservation
- `traceDistanceGen_triangle`: triangle inequality
- `traceDistanceGen_le_of_posSemidef_of_trace_eq`: two PSD operators of equal weight are
  at generalized trace distance at most that weight
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-!
## Generalized Trace Distance

For sub-normalized PSD operators, the standard `½‖ρ-σ‖₁` does not capture
the "gap" when traces differ. The generalized distance (Tomamichel §3.2, eq. 3.23)
corrects for this by adding half the absolute difference of traces.
-/

/-- Generalized trace distance for positive semidefinite operators.

    Tomamichel 2016, eq. 3.23:
      D(ρ, σ) := ½‖ρ - σ‖₁ + ½|tr ρ - tr σ|

    For normalized density operators this reduces to the standard trace distance
    `½‖ρ - σ‖₁` since `tr ρ = tr σ = 1`. -/
noncomputable def traceDistanceGen {n : ℕ} [NeZero n]
    (ρ σ : Op n) : ℝ :=
  (1 / 2) * traceNorm (ρ - σ) + (1 / 2) * |((ρ.trace - σ.trace).re)|

/-- Generalized trace distance is nonneg. -/
theorem traceDistanceGen_nonneg {n : ℕ} [NeZero n]
    (ρ σ : Op n) : 0 ≤ traceDistanceGen ρ σ := by
  unfold traceDistanceGen
  apply add_nonneg
  · apply mul_nonneg
    · norm_num
    · unfold traceNorm
      apply Finset.sum_nonneg
      intro i _; exact Real.sqrt_nonneg _
  · apply mul_nonneg
    · norm_num
    · exact abs_nonneg _

/-- Generalized trace distance is symmetric. -/
theorem traceDistanceGen_symm {n : ℕ} [NeZero n]
    (ρ σ : Op n) :
    traceDistanceGen ρ σ = traceDistanceGen σ ρ := by
  unfold traceDistanceGen
  have h1 : traceNorm (ρ - σ) = traceNorm (σ - ρ) := by
    unfold traceNorm
    have heq : (ρ - σ)† * (ρ - σ) = (σ - ρ)† * (σ - ρ) := by
      rw [← neg_sub ρ σ, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    simp_rw [heq]
  have h2 : |(ρ.trace - σ.trace).re| = |(σ.trace - ρ.trace).re| := by
    rw [← neg_sub, Complex.neg_re, abs_neg]
  simp only [h1, h2]

/-- Generalized trace distance vanishes on the diagonal. -/
theorem traceDistanceGen_self_zero {n : ℕ} [NeZero n]
    (ρ : Op n) : traceDistanceGen ρ ρ = 0 := by
  unfold traceDistanceGen
  simp only [sub_self, Complex.zero_re, abs_zero, mul_zero, add_zero]
  have : traceNorm (0 : Op n) = 0 := by
    rw [traceNorm_hermitian_eq 0 (by simp [Matrix.IsHermitian]),
        (traceNormHermitian_eq_zero_iff 0 (by simp [Matrix.IsHermitian])).mpr rfl]
  simpa

/-- The trace-norm part of the generalized trace distance is bounded by twice
    the generalized trace distance. -/
theorem traceNorm_sub_le_two_traceDistanceGen {n : ℕ} [NeZero n]
    (ρ σ : Op n) :
    traceNorm (ρ - σ) ≤ 2 * traceDistanceGen ρ σ := by
  unfold traceDistanceGen
  have hnorm : 0 ≤ traceNorm (ρ - σ) := by
    unfold traceNorm
    positivity
  have htrace : 0 ≤ |((ρ.trace - σ.trace).re)| := abs_nonneg _
  nlinarith

/-- CPTP postprocessing of an operator difference is bounded by twice the
generalized trace distance of the inputs. -/
theorem traceNorm_cptp_sub_le_two_traceDistanceGen {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : Quantum.Channels.IsCPTP Φ) (ρ σ : Op n) :
    traceNorm (Φ (ρ - σ)) ≤ 2 * traceDistanceGen ρ σ :=
  (traceNorm_cptp_contractive_general Φ hΦ (ρ - σ)).trans
    (traceNorm_sub_le_two_traceDistanceGen ρ σ)

/-- If an operator is a CPTP postprocessing of a difference, its trace norm is
bounded by twice the generalized trace distance of the two inputs. -/
theorem traceNorm_le_two_traceDistanceGen_of_cptp_postprocess_eq
    {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : Quantum.Channels.IsCPTP Φ)
    (ρ σ : Op n) (out : Op m) (hout : out = Φ (ρ - σ)) :
    traceNorm out ≤ 2 * traceDistanceGen ρ σ := by
  rw [hout]
  exact traceNorm_cptp_sub_le_two_traceDistanceGen Φ hΦ ρ σ

/-- When both operators have the same real-valued trace, the generalized trace
    distance reduces to the standard trace distance. -/
theorem traceDistanceGen_eq_traceDistance {n : ℕ} [NeZero n]
    (ρ σ : Op n)
    (h : ρ.trace.re = σ.trace.re) :
    traceDistanceGen ρ σ = traceDistance ρ σ := by
  unfold traceDistanceGen traceDistance
  have : (ρ.trace - σ.trace).re = 0 := by simp [Complex.sub_re, h, sub_self]
  simp [this]

/-- Generalized trace distance is monotone under trace-norm contraction when
the real trace gap is preserved. -/
lemma traceDistanceGen_le_of_traceNorm_sub_le_of_trace_re_sub_eq
    {m n : ℕ} [NeZero m] [NeZero n]
    {ρ σ : Op m} {ρ' σ' : Op n}
    (hnorm : traceNorm (ρ - σ) ≤ traceNorm (ρ' - σ'))
    (htrace : (ρ.trace - σ.trace).re = (ρ'.trace - σ'.trace).re) :
    traceDistanceGen ρ σ ≤ traceDistanceGen ρ' σ' := by
  unfold traceDistanceGen
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hnorm_half : (1 / 2) * traceNorm (ρ - σ) ≤
      (1 / 2) * traceNorm (ρ' - σ') :=
    mul_le_mul_of_nonneg_left hnorm hhalf
  have htrace_half : (1 / 2) * |(ρ.trace - σ.trace).re| =
      (1 / 2) * |(ρ'.trace - σ'.trace).re| := by
    rw [htrace]
  linarith

/-- **Triangle inequality for the generalized trace distance.**

The generalized trace distance is `(1/2)·‖ρ−σ‖₁ + (1/2)·|(tr ρ − tr σ).re|`;
both summands satisfy a triangle inequality (the first via `traceNorm_sub_le`,
the second via `abs_add` on ℝ), and the bound assembles. -/
theorem traceDistanceGen_triangle {n : ℕ} [NeZero n]
    (ρ σ τ : Op n) :
    traceDistanceGen ρ τ ≤ traceDistanceGen ρ σ + traceDistanceGen σ τ := by
  unfold traceDistanceGen
  have h1 : Quantum.Metrics.traceNorm (ρ - τ) ≤
      Quantum.Metrics.traceNorm (ρ - σ) + Quantum.Metrics.traceNorm (σ - τ) := by
    rw [show ρ - τ = (ρ - σ) + (σ - τ) from by abel]
    exact Quantum.Metrics.traceNorm_add_le (ρ - σ) (σ - τ)
  have h2 : |((ρ.trace - τ.trace).re)| ≤
      |((ρ.trace - σ.trace).re)| + |((σ.trace - τ.trace).re)| := by
    rw [show ρ.trace - τ.trace = (ρ.trace - σ.trace) + (σ.trace - τ.trace) from by ring,
      Complex.add_re]
    exact abs_add_le _ _
  linarith

/-- Trace-norm triangle for a difference of positive semidefinite operators:
    `‖U − V‖₁ ≤ Tr U + Tr V`. -/
lemma traceNorm_sub_le_of_posSemidef {d : ℕ} [NeZero d] {U V : Op d}
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    traceNorm (U - V) ≤ (Matrix.trace U).re + (Matrix.trace V).re := by
  have h := traceNorm_sub_le U V
  rw [Quantum.Channels.traceNorm_posSemidef_eq_trace U hU,
    Quantum.Channels.traceNorm_posSemidef_eq_trace V hV] at h
  exact h

/-- **Two positive-semidefinite operators of the same weight are at generalized trace distance at
most that weight.**

For PSD `a`, `traceNorm a = (trace a).re` (`Quantum.Channels.traceNorm_posSemidef_eq_trace`), so if
`a` and `b` are both PSD with `(trace a).re = (trace b).re = w` then the trace-norm half of
`traceDistanceGen` is `½‖a − b‖₁ ≤ ½(‖a‖₁ + ‖b‖₁) = w` by `traceNorm_sub_le`, and the trace-gap half
vanishes.

This is the generic form of the "small-weight blocks are automatically close" step: no structural
relation between `a` and `b` is used, only that they carry the same total weight. -/
theorem traceDistanceGen_le_of_posSemidef_of_trace_eq {d : ℕ} [NeZero d]
    (a b : Op d) (w : ℝ) (ha : a.PosSemidef) (hb : b.PosSemidef)
    (hatr : a.trace.re = w) (hbtr : b.trace.re = w) :
    Quantum.Metrics.traceDistanceGen a b ≤ w := by
  have hsub := traceNorm_sub_le_of_posSemidef ha hb
  rw [hatr, hbtr] at hsub
  have habs : |(a.trace - b.trace).re| = 0 := by
    rw [Complex.sub_re, hatr, hbtr, sub_self, abs_zero]
  unfold Quantum.Metrics.traceDistanceGen
  rw [habs]
  linarith

end Quantum.Metrics

end -- noncomputable section
