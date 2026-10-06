import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized

/-!
# Trace of the zero sub-density operator

The (real) trace of the zero `SubDensityOp` is `0`. Salvaged verbatim from the
retired BB84 good-σ trace-gap route; the statement mentions no protocol objects.
-/

open Matrix

noncomputable section

namespace InfoTheory.SmoothMinEntropy

lemma subDensityOp_trace_zero (d : ℕ) :
    SubDensityOp.trace (0 : SubDensityOp d) = 0 := by
  unfold SubDensityOp.trace
  simp only [show (0 : SubDensityOp d).toOp = 0 from rfl,
    Matrix.trace_zero, Complex.zero_re]

end InfoTheory.SmoothMinEntropy
