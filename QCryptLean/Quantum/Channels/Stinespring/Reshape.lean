import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Stinespring reshape bijection

A pure-indexing module containing the column/row reshape between
`Matrix (Fin (m * r)) (Fin n) ℂ` and `Matrix (Fin (m * n)) (Fin r) ℂ`, along
with the algebraic identity that converts left multiplication by the Kronecker
block `I_m ⊗ W` into right multiplication by `Wᵀ` after the reshape.

These declarations are factored out of `Stinespring/Minimal.lean` so that the
lightweight matrix-indexing computations elaborate quickly and remain
interactively inspectable.
-/

open Matrix
open scoped Matrix BigOperators

noncomputable section

namespace Quantum.Channels

/-! ## Stinespring reshape bijection -/

/-- Column-to-row reshape exchanging the environment index with the input index. -/
def stinespringReshape {n m r : ℕ} [NeZero n] [NeZero m] [NeZero r]
    (U : Matrix (Fin (m * r)) (Fin n) ℂ) :
    Matrix (Fin (m * n)) (Fin r) ℂ :=
  Matrix.of fun p e =>
    let ai := finProdFinEquiv.symm p
    U (finProdFinEquiv (ai.1, e)) ai.2

/-- Row-to-column reshape, inverse of `stinespringReshape`. -/
def stinespringUnreshape {n m r : ℕ} [NeZero n] [NeZero m] [NeZero r]
    (A : Matrix (Fin (m * n)) (Fin r) ℂ) :
    Matrix (Fin (m * r)) (Fin n) ℂ :=
  Matrix.of fun p i =>
    let ae := finProdFinEquiv.symm p
    A (finProdFinEquiv (ae.1, i)) ae.2

lemma stinespringUnreshape_stinespringReshape {n m r : ℕ}
    [NeZero n] [NeZero m] [NeZero r]
    (U : Matrix (Fin (m * r)) (Fin n) ℂ) :
    stinespringUnreshape (stinespringReshape U) = U := by
  ext p i
  simp only [stinespringReshape, stinespringUnreshape, Matrix.of_apply,
    Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]

lemma stinespringReshape_stinespringUnreshape {n m r : ℕ}
    [NeZero n] [NeZero m] [NeZero r]
    (A : Matrix (Fin (m * n)) (Fin r) ℂ) :
    stinespringReshape (stinespringUnreshape A) = A := by
  ext p e
  simp only [stinespringReshape, stinespringUnreshape, Matrix.of_apply,
    Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The Stinespring reshape as an equivalence. -/
def stinespringReshapeEquiv (n m r : ℕ) [NeZero n] [NeZero m] [NeZero r] :
    Matrix (Fin (m * r)) (Fin n) ℂ ≃ Matrix (Fin (m * n)) (Fin r) ℂ where
  toFun := stinespringReshape
  invFun := stinespringUnreshape
  left_inv := stinespringUnreshape_stinespringReshape
  right_inv := stinespringReshape_stinespringUnreshape

/-!
### Algebraic identity for left multiplication by an env-block

The Kronecker block `I_m ⊗ W` acting on the (output, env) register of a Stinespring
isometry; under the reshape, this corresponds to right multiplication by `Wᵀ` on the
env-column register.  This identity, together with the reshape bijection, lets us convert
between the env-block intertwining form `U_B = (I_m ⊗ W) · U_A` and the reshape-equation
form `B̂ = Â · Wᵀ`.
-/

/-- The Kronecker block `I_m ⊗ W` acting on `Fin (m * r)`. -/
def idTensorBlock {m r : ℕ} [NeZero m] [NeZero r]
    (W : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin (m * r)) (Fin (m * r)) ℂ :=
  Matrix.of fun p q =>
    let ae := finProdFinEquiv.symm p
    let bf := finProdFinEquiv.symm q
    if ae.1 = bf.1 then W ae.2 bf.2 else 0

/-- Entry-wise formula for `idTensorBlock W * U`: the `(finProdFinEquiv (a, e), i)`
entry of `idTensorBlock W * U` equals `∑ f, W e f * U (finProdFinEquiv (a, f)) i`. -/
lemma idTensorBlock_mul_apply {n m r : ℕ}
    [NeZero n] [NeZero m] [NeZero r]
    (W : Matrix (Fin r) (Fin r) ℂ)
    (U : Matrix (Fin (m * r)) (Fin n) ℂ)
    (a : Fin m) (e : Fin r) (i : Fin n) :
    (idTensorBlock W * U : Matrix (Fin (m * r)) (Fin n) ℂ) (finProdFinEquiv (a, e)) i
      = ∑ f, W e f * U (finProdFinEquiv (a, f)) i := by
  rw [Matrix.mul_apply]
  -- Reindex the sum over `Fin (m * r)` via `finProdFinEquiv`.
  rw [← finProdFinEquiv.sum_comp
        (fun q : Fin (m * r) =>
          idTensorBlock W (finProdFinEquiv (a, e)) q * U q i)]
  rw [Fintype.sum_prod_type]
  -- Unfold `idTensorBlock` to a conditional indexed by the `Fin m` factor.
  have h : ∀ b : Fin m, ∀ f : Fin r,
      idTensorBlock W (finProdFinEquiv (a, e)) (finProdFinEquiv (b, f))
        * U (finProdFinEquiv (b, f)) i
      = (if a = b then W e f else 0) * U (finProdFinEquiv (b, f)) i := by
    intro b f
    congr 1
    simp only [idTensorBlock, Matrix.of_apply, Equiv.symm_apply_apply]
  simp_rw [h]
  -- Pull the `if` outside: when a ≠ b, the term is 0.
  have hb : ∀ b : Fin m,
      ∑ f, (if a = b then W e f else 0) * U (finProdFinEquiv (b, f)) i
        = if a = b then ∑ f, W e f * U (finProdFinEquiv (b, f)) i else 0 := by
    intro b
    by_cases hab : a = b <;> simp [hab]
  simp_rw [hb]
  rw [Finset.sum_ite_eq Finset.univ a
      (fun b => ∑ f, W e f * U (finProdFinEquiv (b, f)) i)]
  simp only [Finset.mem_univ, ite_true]

/-- Key algebraic identity: reshape of `(I_m ⊗ W) · U` equals `(reshape U) · Wᵀ`.

Left multiplication by a Kronecker env-block on the Stinespring side becomes right
multiplication by `Wᵀ` on the Kraus-packing side. -/
lemma stinespringReshape_idTensorBlock_mul {n m r : ℕ}
    [NeZero n] [NeZero m] [NeZero r]
    (W : Matrix (Fin r) (Fin r) ℂ)
    (U : Matrix (Fin (m * r)) (Fin n) ℂ) :
    stinespringReshape (idTensorBlock W * U) = stinespringReshape U * Wᵀ := by
  ext p e
  -- Decompose `p` via the bijection.
  set ai := finProdFinEquiv.symm p with hai
  -- LHS: unfold `stinespringReshape`, then use `idTensorBlock_mul_apply`.
  have hLHS :
      stinespringReshape (idTensorBlock W * U) p e
        = ∑ f, W e f * U (finProdFinEquiv (ai.1, f)) ai.2 := by
    simp only [stinespringReshape, Matrix.of_apply, ← hai]
    rw [idTensorBlock_mul_apply]
  -- RHS: unfold mul, transpose, reshape.
  have hRHS :
      (stinespringReshape U * Wᵀ) p e
        = ∑ f, U (finProdFinEquiv (ai.1, f)) ai.2 * W e f := by
    rw [Matrix.mul_apply]
    simp only [stinespringReshape, Matrix.of_apply, Matrix.transpose_apply, ← hai]
  rw [hLHS, hRHS]
  exact Finset.sum_congr rfl (fun f _ => mul_comm _ _)

/-- Entry of the row-Gram of the Stinespring reshape.

At the index pair `(finProdFinEquiv (a, i), finProdFinEquiv (b, j))`, the
`(a, i)`-th row of `stinespringReshape U` paired with the `(b, j)`-th row gives
the environment-index sum
`∑ e, U (finProdFinEquiv (a, e)) i * star (U (finProdFinEquiv (b, e)) j)`. -/
lemma stinespringReshape_mul_conjTranspose_apply {n m r : ℕ}
    [NeZero n] [NeZero m] [NeZero r]
    (U : Matrix (Fin (m * r)) (Fin n) ℂ)
    (a b : Fin m) (i j : Fin n) :
    (stinespringReshape U * (stinespringReshape U)ᴴ)
        (finProdFinEquiv (a, i)) (finProdFinEquiv (b, j))
      = ∑ e : Fin r,
          U (finProdFinEquiv (a, e)) i * star (U (finProdFinEquiv (b, e)) j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stinespringReshape,
    Matrix.of_apply, Equiv.symm_apply_apply]

end Quantum.Channels

end
