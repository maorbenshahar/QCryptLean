import QCryptLean.Quantum.Operators.BraKet.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Rectangular ketbra conjugation

Rank-one outer products under rectangular (dimension-changing) matrix conjugation:
sandwiching a rank-one operator `x (star y)` by rectangular matrices on each side
is the outer product of the transformed vectors, and the ketbra of a ket obtained as
the rectangular image of another ket is the corresponding conjugation of the source
ketbra.

The second half reads the same sandwich on the **computational basis**. Conjugation
`ρ ↦ K ρ Kᴴ` is linear, so it is determined by its values on the matrix units; on the rank-one
projector `|d⟩⟨d|` only the `d`-th column of `K` contributes, and the value is the outer product
of that column with itself (`Quantum.Operators.krausConj_single_entry`). When that column is a
multiple of a basis vector — which is the shape of every branch of a classical readout, of a
dimension-changing hash step and of their two-party lifts — the value is a multiple of a basis
projector (`Quantum.Operators.krausConj_single_of_col`), and when the column vanishes the whole
branch does. Composition and scaling of conjugations close the small calculus.
-/

open Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Matrix

/-- Rectangular rank-one sandwich identity.

Left- and right-multiplication of `vecMulVec x (star y)` by rectangular matrices
is the outer product of the corresponding image vectors. -/
theorem mul_vecMulVec_star_mul_rect
    {l m n p : Type*} [Fintype m] [Fintype n]
    (M : Matrix l m ℂ) (N : Matrix n p ℂ) (x : m → ℂ) (y : n → ℂ) :
    M * vecMulVec x (star y) * N =
      vecMulVec (M.mulVec x) (star (Nᴴ.mulVec y)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  have h := Matrix.star_mulVec Nᴴ y
  rw [Matrix.conjTranspose_conjTranspose] at h
  exact h.symm

end Matrix

namespace Quantum.Operators

/-- If a ket vector is the rectangular image of another ket vector, then its
ket-bra is the corresponding rectangular conjugation of the source ket-bra. -/
theorem ketbra_eq_rect_conj_of_vec_eq_mulVec
    {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (ψ : Ket dSrc) (φ : Ket dTgt)
    (hφ : φ.vec = K.mulVec ψ.vec) :
    φ * φ.dag = K * (ψ * ψ.dag) * Kᴴ := by
  rw [show φ * φ.dag = Matrix.vecMulVec φ.vec (star φ.vec) by
    ext i j
    simp [Matrix.vecMulVec]]
  rw [hφ]
  rw [show ψ * ψ.dag = Matrix.vecMulVec ψ.vec (star ψ.vec) by
    ext i j
    simp [Matrix.vecMulVec]]
  simpa [Matrix.conjTranspose_conjTranspose] using
    (Matrix.mul_vecMulVec_star_mul_rect K Kᴴ ψ.vec ψ.vec).symm

/-! ## Conjugation on the computational basis -/

/-- **Conjugating a basis projector reads exactly one column of the operator.** The entries of
`K |d⟩⟨d| Kᴴ` are the outer product of the `d`-th column of `K` with itself. -/
theorem krausConj_single_entry {p q : ℕ} (K : Matrix (Fin q) (Fin p) ℂ) (d : Fin p) (i j : Fin q) :
    (K * Matrix.single d d (1 : ℂ) * Kᴴ) i j = K i d * star (K j d) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hrow : ∀ a : Fin p, (Matrix.single d d (1 : ℂ) * Kᴴ) a j =
      if a = d then star (K j d) else 0 := by
    intro a
    rw [Matrix.mul_apply]
    by_cases ha : a = d
    · subst ha
      simp [Matrix.single_apply, Matrix.conjTranspose_apply]
    · simp [ha, Ne.symm ha]
  simp_rw [hrow]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ d fun a => K i a * star (K j d)]
  simp

/-- **A column that is a multiple of a basis vector.** If the `d`-th column of `K` is `c` times
the basis vector at `u`, then `K |d⟩⟨d| Kᴴ` is `|c|²` times the basis projector at `u`. Both the
register-preserving readouts and the dimension-changing hash steps have columns of this shape,
which is why one lemma covers every branch. -/
theorem krausConj_single_of_col {p q : ℕ} (K : Matrix (Fin q) (Fin p) ℂ) (d : Fin p) (u : Fin q)
    (c : ℂ) (h : ∀ i, K i d = if i = u then c else 0) :
    K * Matrix.single d d (1 : ℂ) * Kᴴ = (c * star c) • Matrix.single u u (1 : ℂ) := by
  ext i j
  rw [krausConj_single_entry K d i j, h i, h j]
  by_cases hi : i = u <;> by_cases hj : j = u
  · simp [hi, hj]
  · simp [hi, hj, Ne.symm hj]
  · simp [hi, Ne.symm hi]
  · simp [hi, Ne.symm hi]

/-- The zero-column case: a branch whose column at `d` vanishes contributes nothing. -/
theorem krausConj_single_of_col_zero {p q : ℕ} (K : Matrix (Fin q) (Fin p) ℂ) (d : Fin p)
    (h : ∀ i, K i d = 0) : K * Matrix.single d d (1 : ℂ) * Kᴴ = 0 := by
  ext i j
  rw [krausConj_single_entry K d i j, h i, h j]
  simp

/-! ## Composition and scaling -/

/-- Conjugating twice is conjugating by the product. -/
theorem conj_conj_eq_conj_mul {a b c : ℕ} (A : Matrix (Fin c) (Fin b) ℂ)
    (B : Matrix (Fin b) (Fin a) ℂ) (M : Op a) :
    A * (B * M * Bᴴ) * Aᴴ = A * B * M * (A * B)ᴴ := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Conjugating by a scaled operator scales by the squared modulus. -/
theorem conj_smul {p q : ℕ} (z : ℂ) (T : Matrix (Fin q) (Fin p) ℂ) (M : Op p) :
    (z • T) * M * (z • T)ᴴ = (z * star z) • (T * M * Tᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

end Quantum.Operators

end
