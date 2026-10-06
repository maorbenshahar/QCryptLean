import QCryptLean.Quantum.Matrix.PartialIsometryExtension
import QCryptLean.Quantum.Operators.Types

/-!
# Rectangular Gram Isometry Factorization — coisometries and row-Gram transport

This file isolates the finite-dimensional rectangular linear algebra used by
purification uniqueness and live-purification transport with unequal reference
dimensions.

## Main definitions
This file introduces no new definitions.

## Main statements
- `Matrix.finCastLE_inclusion_conjTranspose_mul_self`: the coordinate inclusion
  into a larger `Fin` type is an isometry.
- `Matrix.mul_coisometry_mul_conjTranspose`: right multiplication by a
  coisometry preserves row Gram matrices.
- `Matrix.trace_conjTranspose_mul_right_coisometry`: right multiplication by a
  coisometry preserves rectangular trace overlaps.
- `Matrix.exists_coisometry_right_factor_of_mul_conjTranspose_eq`: equal row
  Grams imply a right-coisometry factorization when dimensions allow it.
- `Matrix.exists_unitary_right_mul_of_mul_conjTranspose_eq`: square equal row
  Grams imply a right-unitary factorization.
-/

open Matrix
open Quantum.Operators
open scoped Matrix ComplexConjugate

noncomputable section

namespace Matrix

/-- Square matrices with equal row Gram matrices differ by right multiplication
by a unitary. -/
lemma exists_unitary_right_mul_of_mul_conjTranspose_eq {d : ℕ}
    (A B : Op d) (hgram : A * A† = B * B†) :
    ∃ W : UnitaryOp d, B = A * W.toOp := by
  have hcol : A.conjTranspose.conjTranspose * A.conjTranspose =
      B.conjTranspose.conjTranspose * B.conjTranspose := by
    simpa [Matrix.conjTranspose_conjTranspose] using hgram
  obtain ⟨Wmat, hW_left, hW_right, hW_mul⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq
      A.conjTranspose B.conjTranspose hcol
  let W : UnitaryOp d :=
    ⟨Wmat.conjTranspose,
      by rw [Matrix.conjTranspose_conjTranspose]; exact hW_right,
      by rw [Matrix.conjTranspose_conjTranspose]; exact hW_left⟩
  refine ⟨W, ?_⟩
  have h := congrArg Matrix.conjTranspose hW_mul
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at h
  exact h.symm

/-- The standard coordinate inclusion `Fin m ↪ Fin n` is an isometry at matrix level. -/
lemma finCastLE_inclusion_conjTranspose_mul_self
    {m n : ℕ} (hdim : m ≤ n) :
    let e : Fin m → Fin n := fun j => ⟨j.1, Nat.lt_of_lt_of_le j.2 hdim⟩
    let J : Matrix (Fin n) (Fin m) ℂ := (1 : Op n).submatrix id e
    Jᴴ * J = (1 : Op m) := by
  intro e J
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (by simpa [e] using congrArg Fin.val hij)
  have hJt : Jᴴ = (1 : Op n).submatrix e id := by
    ext i j
    by_cases hij : e i = j
    · subst j
      rw [show Jᴴ i (e i) =
          star ((1 : Op n) (id (e i)) (e i)) by
            simp [J, Matrix.conjTranspose, Matrix.submatrix]]
      rw [show ((1 : Op n).submatrix e id) i (e i) =
          (1 : Op n) (e i) (id (e i)) by
            simp [Matrix.submatrix]]
      rw [Matrix.one_apply, Matrix.one_apply]
      simp
    · have hne : j ≠ e i := by
        simpa [eq_comm] using hij
      simp [J, Matrix.conjTranspose, Matrix.submatrix, Matrix.one_apply, hij, hne]
  rw [hJt]
  change ((1 : Op n).submatrix e id) *
      ((1 : Op n).submatrix id e) = 1
  have hsub :
      ((1 : Op n).submatrix e id) *
          ((1 : Op n).submatrix id e) =
        ((1 : Op n).submatrix id e).submatrix e id := by
    simpa using
      (Matrix.one_submatrix_mul e (Equiv.refl (Fin n))
        ((1 : Op n).submatrix id e))
  rw [hsub]
  simpa [Matrix.submatrix_submatrix, Function.comp_def] using
    (Matrix.submatrix_one (α := ℂ) e he)

/-- Right multiplication by a coisometry preserves the row Gram matrix. -/
lemma mul_coisometry_mul_conjTranspose
    {d r anc : ℕ}
    (M : Matrix (Fin d) (Fin r) ℂ)
    (W : Matrix (Fin r) (Fin anc) ℂ)
    (hW : W * W.conjTranspose = (1 : Op r)) :
    (M * W) * (M * W).conjTranspose = M * M.conjTranspose := by
  calc
    (M * W) * (M * W).conjTranspose
        = M * (W * W.conjTranspose) * M.conjTranspose := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = M * M.conjTranspose := by
            rw [hW]
            simp

/-- Right multiplication by a coisometry preserves the rectangular trace overlap. -/
lemma trace_conjTranspose_mul_right_coisometry
    {d r anc : ℕ}
    (M N : Matrix (Fin d) (Fin r) ℂ)
    (W : Matrix (Fin r) (Fin anc) ℂ)
    (hW : W * W.conjTranspose = (1 : Op r)) :
    ((M * W).conjTranspose * (N * W)).trace =
      (M.conjTranspose * N).trace := by
  calc
    ((M * W).conjTranspose * (N * W)).trace
        = (W.conjTranspose * ((M.conjTranspose * N) * W)).trace := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (W * (W.conjTranspose * (M.conjTranspose * N))).trace := by
            rw [Matrix.trace_mul_cycle']
    _ = ((W * W.conjTranspose) * (M.conjTranspose * N)).trace := by
            rw [Matrix.mul_assoc]
    _ = (M.conjTranspose * N).trace := by
            rw [hW]
            simp

/-- **Rectangular Douglas/unitary-extension step.**

If two rectangular matrices have the same row Gram matrix and the first reference
dimension is no larger than the second, then the second matrix is obtained from the
first by right multiplication with a coisometry.

The intended proof combines the square Gram-matrix unitary extension
`Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_conjTranspose_mul_self_eq`
with `Matrix.exists_isometric_extension_of_partialIsometry`. -/
theorem exists_coisometry_right_factor_of_mul_conjTranspose_eq
    {d r₁ r₂ : ℕ} [NeZero d] [NeZero r₁] [NeZero r₂]
    (M₁ : Matrix (Fin d) (Fin r₁) ℂ)
    (M₂ : Matrix (Fin d) (Fin r₂) ℂ)
    (hgram : M₁ * M₁ᴴ = M₂ * M₂ᴴ)
    (hdim : r₁ ≤ r₂) :
    ∃ W : Matrix (Fin r₁) (Fin r₂) ℂ,
      W * Wᴴ = (1 : Op r₁) ∧
      M₂ = M₁ * W := by
  let e : Fin r₁ → Fin r₂ := fun j => ⟨j.1, Nat.lt_of_lt_of_le j.2 hdim⟩
  let J : Matrix (Fin r₂) (Fin r₁) ℂ := (1 : Op r₂).submatrix id e
  have hJ : Jᴴ * J = (1 : Op r₁) := by
    simpa [e, J] using finCastLE_inclusion_conjTranspose_mul_self (m := r₁) (n := r₂) hdim
  let A : Matrix (Fin r₂) (Fin d) ℂ := J * M₁ᴴ
  let B : Matrix (Fin r₂) (Fin d) ℂ := M₂ᴴ
  have hcolGram : Aᴴ * A = Bᴴ * B := by
    calc
      Aᴴ * A = M₁ * (Jᴴ * J) * M₁ᴴ := by
        simp [A, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = M₁ * M₁ᴴ := by
        rw [hJ]
        simp
      _ = M₂ * M₂ᴴ := hgram
      _ = Bᴴ * B := by
        simp [B, Matrix.conjTranspose_conjTranspose]
  obtain ⟨U, hU_left, _hU_right, hUA⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_unitary_left_mul_of_rect_conjTranspose_mul_self_eq
      A B hcolGram
  refine ⟨(U * J)ᴴ, ?_, ?_⟩
  · calc
      (U * J)ᴴ * ((U * J)ᴴ)ᴴ = Jᴴ * (Uᴴ * U) * J := by
        simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Jᴴ * J := by
        rw [hU_left]
        simp
      _ = 1 := hJ
  · have h := congrArg Matrix.conjTranspose hUA
    simpa [A, B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using h.symm

/-- Conjugation by a rectangular isometry preserves the trace. -/
theorem trace_isometry_conj {m k : ℕ} (V : Matrix (Fin m) (Fin k) ℂ) (A : Op k)
    (hV : Vᴴ * V = 1) : (V * A * Vᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_comm (V * A) Vᴴ, ← Matrix.mul_assoc, hV, Matrix.one_mul]

end Matrix

end
