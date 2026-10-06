import QCryptLean.Quantum.Metrics.TraceNormHoelder

/-!
# Trace norm of the Cartesian parts

Every operator decomposes as `M = Re M + i · Im M` with Hermitian parts
`Re M = (M + M†) / 2` and `Im M = (M − M†) / (2i)` (Mathlib's `realPart` and `imaginaryPart`,
recombined by `realPart_add_I_smul_imaginaryPart`). By the triangle inequality and
`‖M†‖₁ = ‖M‖₁`, neither part has larger trace norm than `M`. This is the step that extends a
trace-norm bound for Hermitian inputs to all inputs at the cost of a factor `2`.

## Main statements
- `traceNorm_realPart_le`: `‖Re M‖₁ ≤ ‖M‖₁`.
- `traceNorm_imaginaryPart_le`: `‖Im M‖₁ ≤ ‖M‖₁`.
-/

open Quantum.Operators Matrix

noncomputable section

namespace Quantum.Metrics

/-- The trace norm of the Hermitian real part is at most the trace norm. -/
theorem traceNorm_realPart_le {k : ℕ} [NeZero k] (M : Op k) :
    traceNorm (↑(realPart M) : Op k) ≤ traceNorm M := by
  rw [realPart_apply_coe, ← Complex.coe_smul, TraceNormHoelder.traceNorm_smul_eq,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := traceNorm_add_le M (star M)
  rw [traceNorm_star] at h
  linarith

/-- The trace norm of the Hermitian imaginary part is at most the trace norm. -/
theorem traceNorm_imaginaryPart_le {k : ℕ} [NeZero k] (M : Op k) :
    traceNorm (↑(imaginaryPart M) : Op k) ≤ traceNorm M := by
  rw [imaginaryPart_apply_coe, ← Complex.coe_smul, smul_smul,
    TraceNormHoelder.traceNorm_smul_eq, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := traceNorm_sub_le M (star M)
  rw [traceNorm_star] at h
  linarith

end Quantum.Metrics
