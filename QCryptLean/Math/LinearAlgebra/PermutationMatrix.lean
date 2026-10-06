import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Permutation Matrices — coordinate-projector conjugation and unitarity

This file provides small reusable facts about Mathlib permutation matrices used
by BB84 transcript and public-announcement registers.

## Main statements
- `Equiv.Perm.permMatrix_conj_single`: conjugation relabels a coordinate projector.
- `Equiv.Perm.permMatrix_conjTranspose_mul_self`: permutation matrices are unitary.
-/

open Matrix
open scoped ComplexConjugate

namespace Equiv.Perm

/-- Conjugating a coordinate projector by a permutation matrix relabels its coordinate. -/
lemma permMatrix_conj_single {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (i : α) :
    Equiv.Perm.permMatrix ℂ σ.symm * Matrix.single i i (1 : ℂ) *
        (Equiv.Perm.permMatrix ℂ σ.symm)ᴴ =
      Matrix.single (σ i) (σ i) (1 : ℂ) := by
  rw [Matrix.conjTranspose_permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rw [PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.single_apply, Equiv.Perm.inv_def,
    Equiv.eq_symm_apply, Equiv.symm_symm, id_eq]

/-- Permutation matrices are unitary: their conjugate transpose is a left inverse. -/
lemma permMatrix_conjTranspose_mul_self {α : Type*} [DecidableEq α]
    [Fintype α] (σ : Equiv.Perm α) :
    (Equiv.Perm.permMatrix ℂ σ)ᴴ * Equiv.Perm.permMatrix ℂ σ = 1 := by
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

end Equiv.Perm
