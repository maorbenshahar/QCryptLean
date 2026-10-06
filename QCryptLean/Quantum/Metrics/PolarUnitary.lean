import QCryptLean.Math.LinearAlgebra.UnitaryExtension
import QCryptLean.Quantum.Operators.Types
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Polar-Unitary Trace Witnesses — square-root Gram identities and trace maximizers

This file isolates the finite-dimensional polar-decomposition witness needed by
the same-ancilla purification proof: a unitary factor whose trace pairing with a
matrix realizes the trace of the square root of `X * X†`. It also records the
small Gram-matrix and trace-cyclicity facts used to package that witness.

## Main statements
- `cfcSqrt_mul_conjTranspose_gram_eq`: `√(X X†)` and `X†` have the same column
  Gram matrix
- `trace_mul_eq_trace_of_unitary_mul_eq_conjTranspose`: a unitary polar factor
  realizes the trace of its Hermitian factor
- `exists_unitary_trace_mul_eq_trace_cfcSqrt_mul_conjTranspose`: a unitary trace
  witness for `Tr √(X X†)`
- `Op.exists_unitary_polar_left`: every `M : Op d` factors as
  `M = √(M M†) · W` for some unitary `W : UnitaryOp d`
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics.PolarUnitary

/-- The square root of `X * X†` has the same column Gram matrix as `X†`. -/
lemma cfcSqrt_mul_conjTranspose_gram_eq
    {d : ℕ} (X : Op d) :
    (CFC.sqrt (X * X.conjTranspose)).conjTranspose *
        CFC.sqrt (X * X.conjTranspose) =
      X.conjTranspose.conjTranspose * X.conjTranspose := by
  let P : Op d := CFC.sqrt (X * X.conjTranspose)
  have hP_herm : P.conjTranspose = P :=
    ((CFC.sqrt_nonneg (X * X.conjTranspose)).posSemidef).isHermitian.eq
  have hXX_nonneg : (0 : Op d) ≤ X * X.conjTranspose :=
    (Matrix.posSemidef_self_mul_conjTranspose X).nonneg
  have hP_sq : P * P = X * X.conjTranspose := by
    simpa [P] using
      CFC.sqrt_mul_sqrt_self (X * X.conjTranspose) (ha := hXX_nonneg)
  change P.conjTranspose * P =
    X.conjTranspose.conjTranspose * X.conjTranspose
  rw [hP_herm, hP_sq, Matrix.conjTranspose_conjTranspose]

/-- A unitary left polar factor realizes the trace of its Hermitian factor. -/
lemma trace_mul_eq_trace_of_unitary_mul_eq_conjTranspose
    {d : ℕ} (X P : Op d) (U : UnitaryOp d)
    (hP_herm : P.conjTranspose = P)
    (hUP : U.toOp * P = X.conjTranspose) :
    (U.toOp * X).trace = P.trace := by
  have hX : X = P * U.toOp.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hUP
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP_herm] at h
    exact h.symm
  calc
    (U.toOp * X).trace
        = (U.toOp * (P * U.toOp.conjTranspose)).trace := by rw [hX]
    _ = (U.toOp * P * U.toOp.conjTranspose).trace := by rw [Matrix.mul_assoc]
    _ = (U.toOp.conjTranspose * (U.toOp * P)).trace := by
          rw [Matrix.trace_mul_comm]
    _ = ((U.toOp.conjTranspose * U.toOp) * P).trace := by
          rw [← Matrix.mul_assoc]
    _ = P.trace := by rw [U.unitary_left, Matrix.one_mul]

/-- Polar-unitary trace maximizer.

For every finite complex matrix `X`, there is a unitary `U` whose trace pairing
with `X` is exactly `Tr √(X X†)`. This is the finite-dimensional polar
decomposition input needed for the Uhlmann witness in the same-ancilla
purification file.

The only nontrivial structural input is
`Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq`:
apply it to `A = √(X X†)` and `B = X†`, whose column Gram matrices are both
`X X†`. -/
theorem exists_unitary_trace_mul_eq_trace_cfcSqrt_mul_conjTranspose
    {d : ℕ} (X : Op d) :
    ∃ U : UnitaryOp d,
      (U.toOp * X).trace = (CFC.sqrt (X * X.conjTranspose)).trace := by
  let P : Op d := CFC.sqrt (X * X.conjTranspose)
  have hP_herm : P.conjTranspose = P :=
    ((CFC.sqrt_nonneg (X * X.conjTranspose)).posSemidef).isHermitian.eq
  have hgram : P.conjTranspose * P =
      X.conjTranspose.conjTranspose * X.conjTranspose := by
    simpa [P] using cfcSqrt_mul_conjTranspose_gram_eq X
  obtain ⟨Umat, hU_left, hU_right, hUPmat⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq
      P X.conjTranspose hgram
  let U : UnitaryOp d := ⟨Umat, hU_left, hU_right⟩
  refine ⟨U, ?_⟩
  have hUP : U.toOp * P = X.conjTranspose := by
    simpa [U] using hUPmat
  exact trace_mul_eq_trace_of_unitary_mul_eq_conjTranspose X P U hP_herm hUP

/-- **Abstract polar decomposition (left form).**

Every `M : Op d` factors as `M = √(M M†) · W` for some unitary `W : UnitaryOp d`.
The proof applies the unitary extension of
`Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq`
to `A := √(M M†)` and `B := M.conjTranspose`, whose column Grams agree by
`cfcSqrt_mul_conjTranspose_gram_eq`, obtains a unitary `U` with
`U · √(M M†) = M†`, and takes conjugate transposes to set `W := U†`. -/
lemma Op.exists_unitary_polar_left
    {d : ℕ} (M : Op d) :
    ∃ W : UnitaryOp d,
      M = CFC.sqrt (M * M.conjTranspose) * W.toOp := by
  have hgram :
      (CFC.sqrt (M * M.conjTranspose)).conjTranspose *
          CFC.sqrt (M * M.conjTranspose) =
        M.conjTranspose.conjTranspose * M.conjTranspose :=
    cfcSqrt_mul_conjTranspose_gram_eq M
  obtain ⟨Umat, hU_left, hU_right, hUP⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq
      (CFC.sqrt (M * M.conjTranspose)) M.conjTranspose hgram
  -- `U` has `U * √(M M†) = M†`. Set `W := U†`.
  have hsqrt_herm :
      (CFC.sqrt (M * M.conjTranspose)).conjTranspose =
        CFC.sqrt (M * M.conjTranspose) :=
    ((CFC.sqrt_nonneg (M * M.conjTranspose)).posSemidef).isHermitian.eq
  -- Build the unitary `W := U†` directly.
  let W : UnitaryOp d :=
    ⟨Umat.conjTranspose,
      by rw [conjTranspose_conjTranspose]; exact hU_right,
      by rw [conjTranspose_conjTranspose]; exact hU_left⟩
  refine ⟨W, ?_⟩
  -- Take conjugate transposes of `U * √(M M†) = M†` to get `√(M M†) * U† = M`.
  have h := congrArg Matrix.conjTranspose hUP
  rw [conjTranspose_mul, conjTranspose_conjTranspose, hsqrt_herm] at h
  -- `h : (√(M M†)) * Umat.conjTranspose = M`
  exact h.symm

end Quantum.Metrics.PolarUnitary
