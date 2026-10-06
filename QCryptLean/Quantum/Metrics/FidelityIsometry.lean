import QCryptLean.Quantum.Metrics.TraceNorm.FidelitySymm
import QCryptLean.Quantum.Metrics.TraceNormHoelder

/-!
# Fidelity under rectangular isometries

This module packages the trace-norm/CFC facts from `TraceNormHoelder.lean` into a
standard Uhlmann-fidelity invariance statement for simultaneous conjugation by
a rectangular isometry.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-- Uhlmann fidelity is invariant when both PSD operands are conjugated by the
same rectangular isometry. The target PSD operands are passed explicitly so
callers can use their existing bundled positivity proofs. -/
lemma fidelity_isometry_conj_of_toOp_eq {m n : ℕ} [NeZero m] [NeZero n]
    (V : Matrix (Fin m) (Fin n) ℂ)
    (A B : PosSemidefOp n) (A' B' : PosSemidefOp m)
    (hV : V.conjTranspose * V = 1)
    (hA' : A'.toOp = V * A.toOp * V.conjTranspose)
    (hB' : B'.toOp = V * B.toOp * V.conjTranspose) :
    fidelity A' B' = fidelity A B := by
  rw [fidelity_eq_traceNorm_sqrtProduct,
    fidelity_eq_traceNorm_sqrtProduct]
  have hsqrtA :
      sqrtPosSemidefOp A' =
        V * sqrtPosSemidefOp A * V.conjTranspose := by
    rw [show sqrtPosSemidefOp A' = CFC.sqrt A'.toOp from rfl, hA']
    simpa [sqrtPosSemidefOp] using
      TraceNormHoelder.cfc_sqrt_isometry_conj V A.toOp hV
        (posSemidefOp_implies_mathlib A)
  have hsqrtB :
      sqrtPosSemidefOp B' =
        V * sqrtPosSemidefOp B * V.conjTranspose := by
    rw [show sqrtPosSemidefOp B' = CFC.sqrt B'.toOp from rfl, hB']
    simpa [sqrtPosSemidefOp] using
      TraceNormHoelder.cfc_sqrt_isometry_conj V B.toOp hV
        (posSemidefOp_implies_mathlib B)
  rw [hsqrtA, hsqrtB]
  have hmul :
      (V * sqrtPosSemidefOp A * V.conjTranspose) *
          (V * sqrtPosSemidefOp B * V.conjTranspose) =
        V * (sqrtPosSemidefOp A * sqrtPosSemidefOp B) *
          V.conjTranspose := by
    calc
      (V * sqrtPosSemidefOp A * V.conjTranspose) *
          (V * sqrtPosSemidefOp B * V.conjTranspose)
          = V * sqrtPosSemidefOp A * (V.conjTranspose * V) *
              sqrtPosSemidefOp B * V.conjTranspose := by
              simp only [Matrix.mul_assoc]
      _ = V * sqrtPosSemidefOp A *
              (1 : Op n) *
              sqrtPosSemidefOp B * V.conjTranspose := by rw [hV]
      _ = V * (sqrtPosSemidefOp A * sqrtPosSemidefOp B) *
              V.conjTranspose := by
              simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [hmul]
  exact TraceNormHoelder.traceNorm_isometry_mul_left V
    (sqrtPosSemidefOp A * sqrtPosSemidefOp B) hV

end Quantum.Metrics

end
