import QCryptLean.Quantum.TensorProducts.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Matrix units and block-diagonal families in the numeral tensor product

`Quantum.Operators.Op.tensor` is the Kronecker product read through the numeral identification
`finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)`, in which the first factor is the high digit.
This module records how that product meets the matrix-unit basis of its second — *label* —
factor: a matrix unit tensored with a matrix unit is again a matrix unit, and a family of
operators summed against the diagonal matrix units of the label register is block diagonal.

These are the two facts a classical label register needs: writing one label places an operator
in one block (`Quantum.TensorProducts.appendIndexKraus_conj`), and summing over the labels
assembles the blocks (`Quantum.TensorProducts.sum_appendIndexKraus_conj_eq_reindex_blockDiagonal`).

## Main statements

* `Quantum.TensorProducts.reindex_single`: a matrix unit stays a matrix unit under an index
  relabelling, at the relabelled indices.
* `Quantum.TensorProducts.Op.single_tensor_single`: the tensor of two matrix units is the matrix
  unit at the paired index, carrying the product of the two scalars.
  `Quantum.TensorProducts.Op.single_tensor_single_diag` is the diagonal case, in which both
  factors are multiples of rank-one projectors.
* `Quantum.TensorProducts.sum_kronecker_single_eq_blockDiagonal`: `∑ i, A i ⊗ₖ |i⟩⟨i|` is
  `Matrix.blockDiagonal A`, at the pair index.
* `Quantum.TensorProducts.sum_tensor_single_eq_reindex_blockDiagonal`: the same sum for
  `Op.tensor`, which is `Matrix.blockDiagonal A` reindexed by `finProdFinEquiv`.
* `Quantum.TensorProducts.sum_single_kronecker_eq_reindex_blockDiagonal` and
  `Quantum.TensorProducts.sum_single_tensor_eq_reindex_blockDiagonal`: the same two statements
  with the label register as the **first** factor. `Matrix.blockDiagonal` always indexes the
  label second, so the mirrors carry an explicit `Equiv.prodComm`.

## Relation to Mathlib

`Matrix.single_kronecker_single` and `Matrix.kronecker_diagonal` are Mathlib's pair-indexed
statements, and the first of them is what proves the law below. What is added here is the
numeral `Fin (n * m)` reading that this library uses everywhere; Mathlib fixes no such
identification.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators Kronecker

noncomputable section

namespace Quantum.TensorProducts

/-! ## 1. Matrix units -/

/-- **A relabelling carries a matrix unit to the matrix unit at the relabelled indices.** The
row and column relabellings are independent, so this covers a rectangular matrix and the
diagonal projectors alike. It is Mathlib's `Matrix.submatrix_single_equiv` in the
`Matrix.reindex` direction, which is the direction a register relabelling is written in. -/
theorem reindex_single {l m n o α : Type*} [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [DecidableEq o] [Zero α] (e : l ≃ n) (f : m ≃ o) (i : l) (j : m) (v : α) :
    Matrix.reindex e f (Matrix.single i j v) = Matrix.single (e i) (f j) v := by
  rw [Matrix.reindex_apply, Matrix.submatrix_single_equiv]
  simp only [Equiv.symm_symm]

/-- **The tensor of two matrix units is a matrix unit.** Its row and column indices are the
numerals of the two index pairs and its entry is the product of the two entries. This is
Mathlib's `Matrix.single_kronecker_single` read through `finProdFinEquiv`. -/
theorem Op.single_tensor_single {n m : ℕ} (a b : Fin n) (p q : Fin m) (x y : ℂ) :
    Op.tensor (Matrix.single a b x) (Matrix.single p q y) =
      Matrix.single (finProdFinEquiv (a, p)) (finProdFinEquiv (b, q)) (x * y) := by
  simp only [Op.tensor, Matrix.single_kronecker_single, Matrix.reindex_apply,
    Matrix.submatrix_single_equiv, Equiv.symm_symm]

/-- The diagonal case of `Quantum.TensorProducts.Op.single_tensor_single`: a multiple of the
rank-one projector `|a⟩⟨a|` tensored with the projector `|p⟩⟨p|` is the same multiple of the
projector at the paired index. This is the form in which a label register carrying one classical
value meets an interior operator. -/
theorem Op.single_tensor_single_diag {n m : ℕ} (a : Fin n) (p : Fin m) (x : ℂ) :
    Op.tensor (Matrix.single a a x) (Matrix.single p p (1 : ℂ)) =
      Matrix.single (finProdFinEquiv (a, p)) (finProdFinEquiv (a, p)) x := by
  rw [Op.single_tensor_single, mul_one]

/-! ## 2. Label families and block-diagonal form -/

/-- The Kronecker sum `∑ i, B i ⊗ₖ |i⟩⟨i|` equals `Matrix.blockDiagonal B`. -/
theorem sum_kronecker_single_eq_blockDiagonal {d k : ℕ} (B : Fin k → Op d) :
    ∑ i, B i ⊗ₖ (Matrix.single i i (1 : ℂ)) = Matrix.blockDiagonal B := by
  ext ⟨a, p⟩ ⟨b, q⟩
  simp only [Matrix.blockDiagonal_apply]
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [kroneckerMap_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · subst h; simp only [and_self, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · apply Finset.sum_eq_zero; intros x _
    simp only [ite_eq_right_iff]
    intro ⟨h1, h2⟩; exact absurd (h1 ▸ h2 ▸ rfl) h

/-- The numeral sum `∑ i, A i ⊗ |i⟩⟨i|` is `Matrix.blockDiagonal A` reindexed by
`finProdFinEquiv`. The reindex is not removable: `Matrix.blockDiagonal` is indexed by the pair,
`Op.tensor` by its numeral. -/
theorem sum_tensor_single_eq_reindex_blockDiagonal {d k : ℕ} (A : Fin k → Op d) :
    ∑ i, A i ⊗ (Matrix.single i i (1 : ℂ) : Op k) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.blockDiagonal A) := by
  simp only [Op.tensor]
  simp_rw [← Matrix.reindexLinearEquiv_apply ℂ ℂ]
  rw [← map_sum]
  congr 1
  exact sum_kronecker_single_eq_blockDiagonal A

/-- The mirror of `Quantum.TensorProducts.sum_kronecker_single_eq_blockDiagonal`, with the label
register as the **first** factor: `∑ i, |i⟩⟨i| ⊗ₖ B i` is `Matrix.blockDiagonal B` with its two
index factors exchanged. `Matrix.blockDiagonal` puts the label second, so the swap is forced. -/
theorem sum_single_kronecker_eq_reindex_blockDiagonal {d k : ℕ} (B : Fin k → Op d) :
    ∑ i, (Matrix.single i i (1 : ℂ) : Op k) ⊗ₖ B i =
      Matrix.reindex (Equiv.prodComm (Fin d) (Fin k)) (Equiv.prodComm (Fin d) (Fin k))
        (Matrix.blockDiagonal B) := by
  ext ⟨p, a⟩ ⟨q, b⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.blockDiagonal_apply]
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [kroneckerMap_apply, Matrix.single_apply, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · subst h; simp only [and_self, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · apply Finset.sum_eq_zero; intros x _
    simp only [ite_eq_right_iff]
    intro ⟨h1, h2⟩; exact absurd (h1 ▸ h2 ▸ rfl) h

/-- The mirror of `Quantum.TensorProducts.sum_tensor_single_eq_reindex_blockDiagonal`, with the
label register as the high digit. -/
theorem sum_single_tensor_eq_reindex_blockDiagonal {d k : ℕ} (B : Fin k → Op d) :
    ∑ i, (Matrix.single i i (1 : ℂ) : Op k) ⊗ B i =
      Matrix.reindex ((Equiv.prodComm (Fin d) (Fin k)).trans finProdFinEquiv)
        ((Equiv.prodComm (Fin d) (Fin k)).trans finProdFinEquiv) (Matrix.blockDiagonal B) := by
  simp only [Op.tensor]
  simp_rw [← Matrix.reindexLinearEquiv_apply ℂ ℂ]
  rw [← map_sum, sum_single_kronecker_eq_reindex_blockDiagonal]
  ext i j
  simp only [Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_trans_apply]

end Quantum.TensorProducts

end
