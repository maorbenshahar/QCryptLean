import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.Metrics.FidelityIsometry
import QCryptLean.Quantum.Metrics.FidelityPartialTraceMonotone

/-!
# Fidelity Monotonicity under CPTP Maps — Stinespring dilation and partial trace

This module packages the standard Uhlmann-fidelity data-processing inequality
for finite-dimensional CPTP maps.  The proof factors a CPTP map through its
Stinespring isometry, uses fidelity invariance under the isometry, and then
uses monotonicity under the partial trace.

## Main definitions
- `posSemidefOp_conj`: bundled PSD operator obtained by rectangular conjugation

## Main statements
- `fidelity_le_fidelity_cptp_of_toOp_eq`: Uhlmann fidelity is monotone under a
  CPTP postprocessing map
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-- Conjugating a positive semidefinite operator by a rectangular matrix preserves
positive semidefiniteness. -/
def posSemidefOp_conj {n m : ℕ}
    (V : Matrix (Fin m) (Fin n) ℂ) (A : PosSemidefOp n) :
    PosSemidefOp m := {
  toOp := V * A.toOp * V.conjTranspose
  isHermitian :=
    ((Quantum.Operators.posSemidefOp_implies_mathlib A).mul_mul_conjTranspose_same
      V).isHermitian
  pos_semidef :=
    Quantum.Operators.posSemidef_re_quadraticForm_nonneg
      ((Quantum.Operators.posSemidefOp_implies_mathlib A).mul_mul_conjTranspose_same V)
}

/-- A Stinespring recovery identifies the partial trace of the dilated PSD
operator with the stated CPTP image. -/
lemma posSemidefOp_conj_partialTraceB_eq_of_dilation_recovers
    {n m envDim : ℕ} [NeZero n] [NeZero m] [NeZero envDim] [NeZero (m * envDim)]
    (Φ : Op n → Op m)
    (V : Matrix (Fin (m * envDim)) (Fin n) ℂ)
    (hrec : Quantum.Channels.DilationRecovers Φ V)
    (A : PosSemidefOp n) (A' : PosSemidefOp m)
    (hA' : A'.toOp = Φ A.toOp) :
    (posSemidefOp_conj V A).partialTraceB = A' := by
  apply PosSemidefOp.ext
  change partialTraceB (V * A.toOp * V.conjTranspose) = A'.toOp
  rw [← hrec A.toOp]
  exact hA'.symm

/-- Uhlmann fidelity is monotone under a CPTP postprocessing map.

The output PSD operands are passed explicitly so callers can reuse their
existing bundled positivity proofs. -/
theorem fidelity_le_fidelity_cptp_of_toOp_eq
    {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : Quantum.Channels.IsCPTP Φ)
    (A B : PosSemidefOp n) (A' B' : PosSemidefOp m)
    (hA' : A'.toOp = Φ A.toOp)
    (hB' : B'.toOp = Φ B.toOp) :
    fidelity A B ≤ fidelity A' B' := by
  obtain ⟨envDim, henv, hme, V, hV, hrec⟩ :=
    Quantum.Channels.stinespring_dilation Φ hΦ
  letI : NeZero envDim := henv
  letI : NeZero (m * envDim) := hme
  let Aiso : PosSemidefOp (m * envDim) := posSemidefOp_conj V A
  let Biso : PosSemidefOp (m * envDim) := posSemidefOp_conj V B
  have hAptr : Aiso.partialTraceB = A' :=
    posSemidefOp_conj_partialTraceB_eq_of_dilation_recovers Φ V hrec A A' hA'
  have hBptr : Biso.partialTraceB = B' :=
    posSemidefOp_conj_partialTraceB_eq_of_dilation_recovers Φ V hrec B B' hB'
  calc
    fidelity A B = fidelity Aiso Biso := by
      exact (fidelity_isometry_conj_of_toOp_eq V A B Aiso Biso hV rfl rfl).symm
    _ ≤ fidelity Aiso.partialTraceB Biso.partialTraceB :=
      fidelity_le_fidelity_partialTraceB Aiso Biso
    _ = fidelity A' B' := by
      rw [hAptr, hBptr]

end Quantum.Metrics

end
