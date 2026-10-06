import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Basic
import QCryptLean.Math.LinearAlgebra.UnitaryExtension

/-!
# Isometric extension of a partial isometry — matrix version (finite-dim ℂ)

This file provides a matrix-level packaging of the classical Gram-Schmidt
orthonormal-extension argument.  The main result is
`Matrix.exists_isometric_extension_of_partialIsometry`.

## Mathematical content

A partial isometry `V : Matrix (Fin n) (Fin m) ℂ` satisfying `V * Vᴴ * V = V`
has initial support `Vᴴ * V`, a projection on `ℂ^m`.  Restricted to the initial
support, V acts as an isometry into `ℂ^n`.  Because `m ≤ n`, there is enough room
to extend the column vectors of V (after Gram-Schmidt normalisation on the column
space) to a full orthonormal m-tuple in `ℂ^n`.  The resulting matrix W satisfies:

  1. `Wᴴ * W = 1`  (W has orthonormal columns — it is a left-isometry), and
  2. `W * (Vᴴ * V) = V`  (W agrees with V on the initial support of V).

## Strategy

The proof bypasses an explicit Gram-Schmidt construction by reducing to the
project's
`Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq`:
embed `V` into `n × n` square matrices via the rectangular inclusion
`J : Fin m → Fin n` (so `Jᴴ * J = 1`), define `A := J · (Vᴴ · V) · Jᴴ`
and `B := V · Jᴴ`, verify `Aᴴ · A = Bᴴ · B` (both equal `J · (Vᴴ · V) · Jᴴ`
using `V · Vᴴ · V = V`), invoke unitary extension to obtain `U` with
`U · A = B`, and take `W := U · J`.

## Reference

Standard Gram-Schmidt argument; see also Paulsen (2002), Theorem 4.4.
-/

open Matrix
open scoped Matrix ComplexConjugate

noncomputable section

namespace Matrix

/-- **Isometric extension of a partial isometry** (matrix version, finite-dim ℂ).

Any partial isometry `V : Matrix (Fin n) (Fin m) ℂ` (satisfying `V * Vᴴ * V = V`)
with `m ≤ n` extends to a left-isometry `W : Matrix (Fin n) (Fin m) ℂ`
(satisfying `Wᴴ * W = 1`) that agrees with V on the initial support of V:

    W * (Vᴴ * V) = V.

Concretely, `Wᴴ * W = 1` means W has m pairwise-orthonormal columns in `ℂ^n`, and
`W * (Vᴴ * V) = V` means that for every vector x in the initial space of V,
`W x = V x`.

The dimension bound `m ≤ n` is necessary: `Wᴴ * W = 1` forces `rank W = m`, which
requires the ambient dimension `n ≥ m`. -/
theorem exists_isometric_extension_of_partialIsometry
    {n m : ℕ} [NeZero n] [NeZero m]
    (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : V * Vᴴ * V = V)
    (hdim : m ≤ n) :
    ∃ W : Matrix (Fin n) (Fin m) ℂ,
      Wᴴ * W = (1 : Matrix (Fin m) (Fin m) ℂ) ∧
      W * (Vᴴ * V) = V := by
  let P : Matrix (Fin m) (Fin m) ℂ := Vᴴ * V
  let e : Fin m → Fin n := fun j => ⟨j.1, Nat.lt_of_lt_of_le j.2 hdim⟩
  let J : Matrix (Fin n) (Fin m) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e
  have hP_selfAdj : Pᴴ = P := by
    simp [P, Matrix.conjTranspose_mul]
  have hVh : Vᴴ * V * Vᴴ = Vᴴ := by
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
      congrArg Matrix.conjTranspose hV
  have hP_idem : P * P = P := by
    calc
      P * P = (Vᴴ * V * Vᴴ) * V := by
        simp [P, Matrix.mul_assoc]
      _ = Vᴴ * V := by rw [hVh]
      _ = P := rfl
  have hJ : Jᴴ * J = (1 : Matrix (Fin m) (Fin m) ℂ) := by
    have hJt : Jᴴ = (1 : Matrix (Fin n) (Fin n) ℂ).submatrix e id := by
      ext i j
      by_cases hij : e i = j
      · subst j
        have hleft : (1 : Matrix (Fin n) (Fin n) ℂ) (id (e i)) (e i) = 1 := by
          rw [Matrix.one_apply]
          simp
        have hright : (1 : Matrix (Fin n) (Fin n) ℂ) (e i) (id (e i)) = 1 := by
          rw [Matrix.one_apply]
          simp
        rw [show Jᴴ i (e i) = star ((1 : Matrix (Fin n) (Fin n) ℂ) (id (e i)) (e i)) by
              simp [J, Matrix.conjTranspose, Matrix.submatrix]]
        rw [show ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix e id) i (e i) =
              (1 : Matrix (Fin n) (Fin n) ℂ) (e i) (id (e i)) by
              simp [Matrix.submatrix]]
        rw [hleft, hright]
        simp
      · have hne : j ≠ e i := by
          simpa [eq_comm] using hij
        rw [show Jᴴ i j = star ((1 : Matrix (Fin n) (Fin n) ℂ) (id j) (e i)) by
              simp [J, Matrix.conjTranspose, Matrix.submatrix]]
        rw [show ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix e id) i j =
              (1 : Matrix (Fin n) (Fin n) ℂ) (e i) (id j) by
              simp [Matrix.submatrix]]
        rw [Matrix.one_apply, Matrix.one_apply]
        simp [hij, hne]
    rw [hJt]
    change ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix e id) *
        ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e) = 1
    have hsub :
        ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix e id) *
            ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e) =
          ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e).submatrix e id := by
      simpa using
        (Matrix.one_submatrix_mul e (Equiv.refl (Fin n))
          ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e))
    rw [hsub]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hdiag : (1 : Matrix (Fin n) (Fin n) ℂ) (id (e i)) (e i) = 1 := by
        rw [Matrix.one_apply]
        simp
      simpa [Matrix.submatrix] using hdiag
    · have hne : e i ≠ e j := by
        intro hij'
        apply hij
        exact Fin.ext (by simpa [e] using congrArg Fin.val hij')
      simp [e, hij, hne]
  let A : Matrix (Fin n) (Fin n) ℂ := J * P * Jᴴ
  let B : Matrix (Fin n) (Fin n) ℂ := V * Jᴴ
  have hAgram : Aᴴ * A = J * P * Jᴴ := by
    calc
      Aᴴ * A = J * P * Jᴴ * (J * P * Jᴴ) := by
        simp [A, Matrix.conjTranspose_mul, Matrix.mul_assoc, hP_selfAdj]
      _ = J * P * (Jᴴ * J) * P * Jᴴ := by
        simp [Matrix.mul_assoc]
      _ = J * P * P * Jᴴ := by
        rw [hJ]
        simp [Matrix.mul_assoc]
      _ = J * (P * P) * Jᴴ := by
        simp [Matrix.mul_assoc]
      _ = J * P * Jᴴ := by
        simpa [Matrix.mul_assoc] using congrArg (fun X => J * X * Jᴴ) hP_idem
  have hBgram : Bᴴ * B = J * P * Jᴴ := by
    calc
      Bᴴ * B = J * Vᴴ * V * Jᴴ := by
        simp [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = J * P * Jᴴ := by
        simp [P, Matrix.mul_assoc]
  have hgram : Aᴴ * A = Bᴴ * B := by
    rw [hAgram, hBgram]
  obtain ⟨U, hU_left, hU_right, hUAB⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq
      A B hgram
  refine ⟨U * J, ?_, ?_⟩
  · calc
      (U * J)ᴴ * (U * J) = Jᴴ * (Uᴴ * U) * J := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jᴴ * J := by
        rw [hU_left]
        simp
      _ = 1 := hJ
  · have h := congrArg (fun M => M * J) hUAB
    simpa [A, B, P, Matrix.mul_assoc, hJ] using h

end Matrix

end
