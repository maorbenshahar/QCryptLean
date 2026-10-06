import QCryptLean.Quantum.TensorProducts.Rectangular

/-!
# Gram matrices of rectangular tensor products

Multiplying a local factor conjugates the joint Gram matrix by that factor tensored with identity.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-- Composing an Alice-side operator `K` into a rectangular product conjugates its Gram
operator by `K ⊗ 1`. -/
theorem tensorRect_mul_left_gram {a b c d e : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
    (B : Matrix (Fin c) (Fin d) ℂ) (K : Matrix (Fin b) (Fin e) ℂ) :
    (tensorRect (A * K) B)ᴴ * tensorRect (A * K) B =
      (tensorRect K (1 : Op d))ᴴ * ((tensorRect A B)ᴴ * tensorRect A B) * tensorRect K 1 := by
  rw [show tensorRect (A * K) B = tensorRect A B * tensorRect K (1 : Op d) by
    rw [tensorRect_mul, Matrix.mul_one]]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Composing a Bob-side operator `K` into a rectangular product conjugates its Gram operator
by `1 ⊗ K`. -/
theorem tensorRect_mul_right_gram {a b c d e : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
    (B : Matrix (Fin c) (Fin d) ℂ) (K : Matrix (Fin d) (Fin e) ℂ) :
    (tensorRect A (B * K))ᴴ * tensorRect A (B * K) =
      (tensorRect (1 : Op b) K)ᴴ * ((tensorRect A B)ᴴ * tensorRect A B) * tensorRect 1 K := by
  rw [show tensorRect A (B * K) = tensorRect A B * tensorRect (1 : Op b) K by
    rw [tensorRect_mul, Matrix.mul_one]]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Conjugation by a value-preserving dimension cast is injective. -/
theorem eq_of_castRect_conj_eq {n m : ℕ} (h : n = m) (M N : Op n)
    (hMN : castRect n m * M * (castRect n m)ᴴ = castRect n m * N * (castRect n m)ᴴ) : M = N := by
  have hiso : (castRect n m)ᴴ * castRect n m = 1 := castRect_isometry h
  have hcancel : ∀ P : Op n,
      (castRect n m)ᴴ * (castRect n m * P * (castRect n m)ᴴ) * castRect n m = P := by
    intro P
    simp only [Matrix.mul_assoc]
    rw [hiso, Matrix.mul_one, ← Matrix.mul_assoc, hiso, Matrix.one_mul]
  calc M = (castRect n m)ᴴ * (castRect n m * M * (castRect n m)ᴴ) * castRect n m :=
        (hcancel M).symm
    _ = (castRect n m)ᴴ * (castRect n m * N * (castRect n m)ᴴ) * castRect n m := by rw [hMN]
    _ = N := hcancel N

end Quantum.TensorProducts
