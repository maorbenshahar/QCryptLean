import QCryptLean.Quantum.TensorProducts.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Right-identity tensor shuffle lemmas, and the one-dimensional right factor

Generic Kronecker/tensor identities moving a matrix product through the
`(· ⊗ 1)` right-identity embedding: multiplying a reindexed `K ⊗ 1` by `P ⊗ 1`
(on either side, in reindexed or submatrix form) collapses to `(K * P) ⊗ 1`.
The statements mention no protocol objects.

The second half is the degenerate case `e = 1`, where the right factor carries no information
and the embedding is a pure dimension cast:
`op_castDim_mul_one_eq_tensor_one` for the identity `1₁`, and `op_tensor_single_card_one` for a
diagonal matrix unit on any one-element index type.  Both are used wherever a register is padded
by a trivial slot — the `eveDim = 1` attack-free channels, and the `Xo = Unit` announcement of a
LOCC program, which writes nothing.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

lemma tensorRightId_mul_tensorRightId
    {a b e : ℕ} [NeZero a] [NeZero b] [NeZero e]
    (K : Matrix (Fin b) (Fin a) ℂ)
    (P : Op a) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) K (1 : Op e))) *
      Op.tensor P (1 : Op e) =
    Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (K * P) (1 : Op e)) := by
  dsimp [Op.tensor]
  rw [Matrix.submatrix_mul_equiv]
  rw [← Matrix.mul_kronecker_mul]
  simp

lemma tensorRightId_mul_tensorRightId_left
    {a b e : ℕ} [NeZero a] [NeZero b] [NeZero e]
    (P : Op b)
    (K : Matrix (Fin b) (Fin a) ℂ) :
    Op.tensor P (1 : Op e) *
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) K (1 : Op e))) =
    Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (P * K) (1 : Op e)) := by
  dsimp [Op.tensor]
  rw [Matrix.submatrix_mul_equiv]
  rw [← Matrix.mul_kronecker_mul]
  simp

lemma tensorRightId_submatrix_mul_tensorRightId
    {a b e : ℕ} [NeZero a] [NeZero b] [NeZero e]
    (K : Matrix (Fin b) (Fin a) ℂ)
    (P : Op a) :
    (Matrix.kroneckerMap (· * ·) K (1 : Op e)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm *
      Op.tensor P (1 : Op e) =
    (Matrix.kroneckerMap (· * ·) (K * P) (1 : Op e)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  simpa [Matrix.reindex] using tensorRightId_mul_tensorRightId (e := e) K P

lemma tensorRightId_mul_tensorRightId_submatrix_left
    {a b e : ℕ} [NeZero a] [NeZero b] [NeZero e]
    (P : Op b)
    (K : Matrix (Fin b) (Fin a) ℂ) :
    Op.tensor P (1 : Op e) *
      (Matrix.kroneckerMap (· * ·) K (1 : Op e)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm =
    (Matrix.kroneckerMap (· * ·) (P * K) (1 : Op e)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  simpa [Matrix.reindex] using tensorRightId_mul_tensorRightId_left (e := e) P K

/-! ## A one-dimensional right factor is a dimension cast -/

/-- **Casting `M : Op m` along `m = m · 1` is tensoring with the one-dimensional identity.**

The one-dimensional register carries no information, so padding by it only relabels indices.
Every `eveDim = 1` slot spends this: it is what turns the `Nat.mul_one` transport into the
tensor form `A ⊗ 1₁` that permutation covariance and the partial trace over the side register
are stated against. -/
lemma op_castDim_mul_one_eq_tensor_one {m : ℕ} (M : Op m) :
    Op.castDim (Nat.mul_one m).symm M = Op.tensor M (1 : Op 1) := by
  ext i j
  rw [Op.castDim_apply]
  simp only [Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  have e1 : (finProdFinEquiv.symm i).1 = Fin.cast (Nat.mul_one m) i := by
    apply Fin.ext; simp [finProdFinEquiv, Nat.div_one]
  have e2 : (finProdFinEquiv.symm j).1 = Fin.cast (Nat.mul_one m) j := by
    apply Fin.ext; simp [finProdFinEquiv, Nat.div_one]
  have e3 : (1 : Op 1) (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 = 1 := by
    rw [Subsingleton.elim (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2,
      Matrix.one_apply_eq]
  rw [e3]
  simp only [mul_one]
  congr 1
  · exact e1.symm
  · exact e2.symm

/-- **A diagonal matrix unit on a one-element index type is a dimension cast.**

The same degeneracy as `op_castDim_mul_one_eq_tensor_one`, with the right factor presented as the
unique basis projector of a `c`-element type with `c = 1`.  Appending a one-outcome announcement
register to a LOCC transcript writes nothing, which is what makes an `Xo = Unit` step
transcript-free. -/
theorem op_tensor_single_card_one {N c : ℕ} (hc : c = 1) (a : Fin c) (h' : N = N * c)
    (M : Op N) : Op.tensor M (Matrix.single a a (1 : ℂ)) = Op.castDim h' M := by
  subst hc
  have ha : Matrix.single a a (1 : ℂ) = (1 : Op 1) := by
    ext p q
    rw [Subsingleton.elim p a, Subsingleton.elim q a]
    simp
  rw [ha, ← op_castDim_mul_one_eq_tensor_one]

end Quantum.TensorProducts
