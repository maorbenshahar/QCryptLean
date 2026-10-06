import QCryptLean.Quantum.Metrics.TraceNormHoelder

/-!
# Trace norm of a scalar multiple of an isometric conjugation

## Main statements
- `traceNorm_smul_isometry_conjTranspose`: trace norm of a scalar multiple of an isometric
conjugation.
-/

open Quantum.Operators Matrix
open scoped Matrix ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-- Trace norm of a scalar multiple of an isometric conjugation. -/
lemma traceNorm_smul_isometry_conjTranspose
    {m k : ℕ} [NeZero m] [NeZero k]
    (c : ℂ) (W : Matrix (Fin m) (Fin k) ℂ) (A : Op k)
    (hW : Wᴴ * W = (1 : Op k)) :
    Quantum.Metrics.traceNorm (c • (W * A * Wᴴ)) =
      ‖c‖ * Quantum.Metrics.traceNorm A := by
  rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
  rw [Quantum.Metrics.TraceNormHoelder.traceNorm_isometry_mul_left W A hW]

end QKD.BB84.Engine
