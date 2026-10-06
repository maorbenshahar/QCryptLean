import QCryptLean.Quantum.Metrics.TraceNorm.Basic

/-!
# Trace norm versus Frobenius norm

On a `d`-dimensional space the trace norm is at most `√d` times the Frobenius
(Hilbert–Schmidt) norm `√(Tr A†A)`:

`‖A‖₁ ≤ √d · √(Tr A†A) = √(d · Tr A†A)`.

The singular values `σᵢ = √λᵢ(A†A)` satisfy `‖A‖₁ = ∑ᵢ σᵢ` and `Tr A†A = ∑ᵢ σᵢ²`, so the bound
is the Cauchy–Schwarz inequality for the `d`-term sum `∑ᵢ σᵢ · 1`. Equality holds at `A = 1`,
where both sides equal `d`, so the constant `√d` cannot be lowered.

## Main statements
- `traceNorm_le_sqrt_dim_mul_sqrt_frobenius`: `‖A‖₁ ≤ √d · √(Tr A†A)`.
- `traceNorm_le_sqrt_dim_mul_frobenius`: the same bound in the single-root form `√(d · Tr A†A)`.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder

noncomputable section

namespace Quantum.Metrics

/-- **Trace norm versus Frobenius norm.** On a `d`-dimensional space,
`‖A‖₁ ≤ √d · √(Tr A†A)`. -/
theorem traceNorm_le_sqrt_dim_mul_sqrt_frobenius {d : ℕ} [NeZero d] (A : Op d) :
    traceNorm A ≤ √(d : ℝ) * √((A† * A).trace.re) := by
  unfold traceNorm
  have hAA : (A† * A).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hAA_psd : (A† * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have h_sum : ∑ i, hAA.eigenvalues i = (A† * A).trace.re := by
    rw [hAA.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  -- Cauchy–Schwarz against the constant function `1` on `Fin d`.
  have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin d))
    (f := hAA.eigenvalues) (g := fun _ => (1 : ℝ)) hAA_psd.eigenvalues_nonneg
    (fun _ => zero_le_one)
  simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hcs
  rw [h_sum] at hcs
  calc ∑ i, √(hAA.eigenvalues i) ≤ √((A† * A).trace.re) * √(d : ℝ) := hcs
    _ = √(d : ℝ) * √((A† * A).trace.re) := mul_comm _ _

/-- `traceNorm_le_sqrt_dim_mul_sqrt_frobenius` in the single-root form
`‖A‖₁ ≤ √(d · Tr A†A)`; the two right-hand sides are equal by `Real.sqrt_mul`. -/
theorem traceNorm_le_sqrt_dim_mul_frobenius {d : ℕ} [NeZero d] (A : Op d) :
    traceNorm A ≤ √((d : ℝ) * (A† * A).trace.re) := by
  rw [Real.sqrt_mul (Nat.cast_nonneg d)]
  exact traceNorm_le_sqrt_dim_mul_sqrt_frobenius A

end Quantum.Metrics
