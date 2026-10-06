import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.TensorProducts.MatrixUnits
import QCryptLean.Math.Combinatorics.FinProductEquiv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Block-Diagonal Trace Norm Identity

For a family of matrices `A : Fin k → Op d` embedded as block-diagonal entries
via rank-1 projectors `|i⟩⟨i|`, the trace norm of the block-diagonal sum equals
the sum of trace norms:

  `‖∑ i, A i ⊗ |i⟩⟨i|‖₁ = ∑ i, ‖A i‖₁`

The key property is that the rank-1 projectors have mutually orthogonal supports,
so the singular values of the block-diagonal matrix are the union of the singular
values of each block.

## Main statements

- `Quantum.Metrics.traceNorm_blockDiagonal_sum`: the block-diagonal trace norm identity
- `Quantum.Metrics.adjoint_mul_sum_tensor_single`: orthogonal decomposition of `S†S`
- `Quantum.Metrics.charpoly_sum_tensor_single_eq_prod`: charpoly factorization
- `Quantum.Metrics.eigenvalue_multiset_sum_tensor_single`: eigenvalue multiset decomposition
- `Quantum.Metrics.sum_eigenvalues_block_decomp`: sums over eigenvalues decompose by block

The identification of `∑ i, A i ⊗ |i⟩⟨i|` with `Matrix.blockDiagonal A` is not a trace-norm
fact and lives in `MatrixUnits.lean`
(`Quantum.TensorProducts.sum_tensor_single_eq_reindex_blockDiagonal`); it is imported above.

## References

- CKR (2009) arXiv:0809.3019, proof of Theorem 1, block-diagonal step
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics
open scoped Matrix BigOperators Kronecker

noncomputable section

namespace Quantum.Metrics

section Orthogonality

/-- Orthogonality of rank-1 projectors in the tensor product:
    `(∑ i, A i ⊗ |i⟩⟨i|)† * (∑ i, A i ⊗ |i⟩⟨i|) = ∑ i, (A i† * A i) ⊗ |i⟩⟨i|`. -/
lemma adjoint_mul_sum_tensor_single {d k : ℕ} [NeZero d] [NeZero k] [NeZero (d * k)]
    (A : Fin k → Op d) :
    (∑ i, A i ⊗ (Matrix.single i i 1 : Op k))ᴴ *
    (∑ i, A i ⊗ (Matrix.single i i 1 : Op k)) =
    ∑ i, ((A i)ᴴ * A i) ⊗ (Matrix.single i i 1 : Op k) := by
  -- Bridge to blockDiagonal, factor via conjTranspose/mul, bridge back
  rw [sum_tensor_single_eq_reindex_blockDiagonal, conjTranspose_reindex]
  simp only [← Matrix.coe_reindexLinearEquiv ℂ ℂ]
  rw [Matrix.reindexLinearEquiv_mul]
  simp only [Matrix.coe_reindexLinearEquiv]
  rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  rw [← sum_tensor_single_eq_reindex_blockDiagonal]

end Orthogonality

section CharpolyFactorization

/-- Equivalence between `Fin d` and the fiber `{a : Fin d × Fin k // a.2 = j}`. -/
private def finFiberEquiv {d k : ℕ} (j : Fin k) :
    Fin d ≃ {a : Fin d × Fin k // a.2 = j} where
  toFun i := ⟨(i, j), rfl⟩
  invFun a := a.val.1
  left_inv _ := rfl
  right_inv a := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact a.prop.symm

/-- The `toSquareBlock` of `blockDiagonal B` at index `j` equals `reindex` of `B j`.
    This is the key identification for the charpoly factorization. -/
private lemma toSquareBlock_blockDiagonal_eq {d k : ℕ}
    (B : Fin k → Op d) (j : Fin k) :
    (Matrix.blockDiagonal B).toSquareBlock Prod.snd j =
    Matrix.reindex (finFiberEquiv j) (finFiberEquiv j) (B j) := by
  ext ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.reindex_apply,
             Matrix.submatrix_apply, finFiberEquiv]
  change j₁ = j at h₁; change j₂ = j at h₂
  subst h₁; subst h₂
  simp [Matrix.blockDiagonal_apply_eq]

/-- The characteristic polynomial of a block-diagonal sum factors as the product
    of the characteristic polynomials of the blocks. -/
lemma charpoly_sum_tensor_single_eq_prod {d k : ℕ} [NeZero d] [NeZero k] [NeZero (d * k)]
    (B : Fin k → Op d) :
    (∑ i, B i ⊗ (Matrix.single i i 1 : Op k)).charpoly = ∏ j, (B j).charpoly := by
  rw [sum_tensor_single_eq_reindex_blockDiagonal, Matrix.charpoly_reindex,
    (Matrix.blockTriangular_blockDiagonal B).charpoly]
  have hsurj : Function.Surjective (@Prod.snd (Fin d) (Fin k)) :=
    fun j => ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, j), rfl⟩
  rw [Finset.image_univ_of_surjective hsurj]
  congr 1; ext j
  rw [toSquareBlock_blockDiagonal_eq, Matrix.charpoly_reindex]

end CharpolyFactorization

section EigenvalueDecomposition

/-- The eigenvalue multiset of a block-diagonal Hermitian matrix is the union
    of eigenvalue multisets of the blocks. -/
lemma eigenvalue_multiset_sum_tensor_single
    {d k : ℕ} [NeZero d] [NeZero k] [NeZero (d * k)]
    (B : Fin k → Op d)
    (hB : ∀ j, (B j).IsHermitian)
    (hBig : (∑ i, B i ⊗ (Matrix.single i i 1 : Op k)).IsHermitian) :
    Multiset.map hBig.eigenvalues Finset.univ.val =
    Finset.univ.val.bind (fun j =>
      Multiset.map (hB j).eigenvalues Finset.univ.val) := by
  have hroots_big := hBig.roots_charpoly_eq_eigenvalues
  let ofR : ℝ → ℂ := @RCLike.ofReal ℂ _
  have hroots_j : ∀ j, (B j).charpoly.roots =
    Multiset.map (ofR ∘ (hB j).eigenvalues) Finset.univ.val :=
    fun j => (hB j).roots_charpoly_eq_eigenvalues
  have hcp := charpoly_sum_tensor_single_eq_prod B
  have hprod_ne : ∏ j ∈ Finset.univ, (B j).charpoly ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => (Matrix.charpoly_monic (B j)).ne_zero)
  have hroots_prod := Polynomial.roots_prod
    (fun j => (B j).charpoly) Finset.univ hprod_ne
  -- Chain charpoly roots over ℂ, then lift to ℝ via injectivity
  have heq_complex :
    Multiset.map (ofR ∘ hBig.eigenvalues) Finset.univ.val =
    Finset.univ.val.bind
      (fun j => Multiset.map (ofR ∘ (hB j).eigenvalues) Finset.univ.val) := by
    rw [← hroots_big, hcp, hroots_prod]
    congr 1; ext j; rw [hroots_j]
  apply Multiset.map_injective (RCLike.ofReal_injective (K := ℂ))
  rw [Multiset.map_map, Multiset.map_bind]
  simp_rw [Multiset.map_map]
  exact heq_complex

/-- Sum of a function over eigenvalues of a block-diagonal Hermitian matrix
    equals the sum over blocks. -/
lemma sum_eigenvalues_block_decomp
    {d k : ℕ} [NeZero d] [NeZero k] [NeZero (d * k)]
    (B : Fin k → Op d)
    (hB : ∀ j, (B j).IsHermitian)
    (hBig : (∑ i, B i ⊗ (Matrix.single i i 1 : Op k)).IsHermitian)
    (f : ℝ → ℝ) :
    ∑ p : Fin (d * k), f (hBig.eigenvalues p) =
    ∑ j : Fin k, ∑ i : Fin d, f ((hB j).eigenvalues i) := by
  have heig := eigenvalue_multiset_sum_tensor_single B hB hBig
  rw [show (∑ p : Fin (d * k), f (hBig.eigenvalues p)) =
    (Multiset.map f (Multiset.map hBig.eigenvalues Finset.univ.val)).sum from by
    rw [Multiset.map_map]; rfl]
  rw [heig, Multiset.map_bind, Multiset.sum_bind]
  simp_rw [Multiset.map_map]
  rfl

end EigenvalueDecomposition

/-- **Block-diagonal trace norm identity.**

For a family `A : Fin k → Op d`, the trace norm of the block-diagonal sum
`∑ i, A i ⊗ |i⟩⟨i|` equals the sum of individual trace norms `∑ i ‖A i‖₁`.

Reference: CKR (2009) arXiv:0809.3019, proof of Theorem 1, block-diagonal step. -/
lemma traceNorm_blockDiagonal_sum {d k : ℕ} [NeZero d] [NeZero k] [NeZero (d * k)]
    (A : Fin k → Op d) :
    traceNorm (∑ i, A i ⊗ (Matrix.single i i 1 : Op k)) = ∑ i, traceNorm (A i) := by
  set S := ∑ i, A i ⊗ (Matrix.single i i 1 : Op k)
  have hdecomp := adjoint_mul_sum_tensor_single A
  have hBj : ∀ j, ((A j)ᴴ * A j).IsHermitian := fun j =>
    Matrix.isHermitian_conjTranspose_mul_self (A j)
  have hSS : (Sᴴ * S).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self S
  have hBig : (∑ i, ((A i)ᴴ * A i) ⊗ (Matrix.single i i 1 : Op k)).IsHermitian :=
    hdecomp ▸ hSS
  have heig_eq : hSS.eigenvalues = hBig.eigenvalues :=
    (hSS.eigenvalues_eq_eigenvalues_iff hBig).mpr (congrArg Matrix.charpoly hdecomp)
  simp only [traceNorm]
  change ∑ i, √(hSS.eigenvalues i) = ∑ x, ∑ i, √((hBj x).eigenvalues i)
  simp_rw [heig_eq]
  exact sum_eigenvalues_block_decomp
    (fun j => (A j)ᴴ * A j) hBj hBig Real.sqrt

/-- The trace norm of a block diagonal matrix is the sum of block trace norms
after reassociating flattened product coordinates. -/
lemma traceNorm_blockDiagonal_submatrix_finProdAssoc {a b k : ℕ}
    [NeZero (a * b)] [NeZero k] [NeZero ((a * b) * k)] [NeZero (a * (b * k))]
    (M : Fin k → Op (a * b)) :
    traceNorm ((Matrix.blockDiagonal M).submatrix
      (finProdFinEquiv_assoc_right a b k) (finProdFinEquiv_assoc_right a b k)) =
    ∑ i, traceNorm (M i) := by
  set e := finProdFinEquiv_assoc_right a b k
  set φ : Fin (a * (b * k)) ≃ Fin ((a * b) * k) := e.trans finProdFinEquiv
  have h_eq : (Matrix.blockDiagonal M).submatrix (⇑e) (⇑e) =
      (∑ i, M i ⊗ (Matrix.single i i (1 : ℂ) : Op k)).submatrix φ φ := by
    rw [sum_tensor_single_eq_reindex_blockDiagonal, Matrix.reindex_apply,
      Matrix.submatrix_submatrix]
    congr 1 <;> funext x <;>
      simp [φ, e, finProdFinEquiv_assoc_right, Equiv.symm_apply_apply]
  rw [h_eq, traceNorm_submatrix_equiv _ φ]
  exact traceNorm_blockDiagonal_sum M

section ArbitraryIndex

/-- Reindexing a `Fin d × X`-indexed block diagonal along the product equivalence
    `(Equiv.refl _).prodCongr σ` produces the block diagonal of the relabeled family
    `f ∘ σ.symm`. This is a pure index-shuffle. -/
private lemma reindex_prodCongr_blockDiagonal
    {d k : ℕ} {X : Type*} [DecidableEq X]
    (σ : X ≃ Fin k) (f : X → Op d) :
    Matrix.reindex ((Equiv.refl (Fin d)).prodCongr σ)
        ((Equiv.refl (Fin d)).prodCongr σ) (Matrix.blockDiagonal f) =
      Matrix.blockDiagonal (f ∘ σ.symm) := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
             Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply,
             Equiv.coe_refl, Prod.map_apply, id_eq,
             Matrix.blockDiagonal_apply, Function.comp_apply]
  by_cases hjj : j = j'
  · subst hjj; simp
  · have hsig : σ.symm j ≠ σ.symm j' := fun h => hjj (σ.symm.injective h)
    rw [if_neg hjj, if_neg hsig]


/-!
## Block-diagonal trace norm for arbitrarily-indexed families

The `traceNorm_blockDiagonal_sum` above works on `Fin k`-indexed families with the
tensor-product embedding `A i ⊗ |i⟩⟨i|`. The following version states the same identity
for `Matrix.blockDiagonal` with an arbitrary finite index type `X` and `Fin`-indexed
matrices, as used by `CQState.toJointOp`.
-/

/-- **Block-diagonal trace norm identity — `Fin`-indexed blocks, arbitrary classical index.**

For a family `f : X → Op d` indexed by a finite type `X`,
the trace norm of the reindexed block-diagonal matrix on `Fin (d * Fintype.card X)`
equals the sum of individual trace norms:

  `‖reindex e e (blockDiagonal f)‖₁ = ∑ x, ‖f x‖₁`

where `e : Fin d × X ≃ Fin (d * Fintype.card X)` is the canonical reindexing
`(Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin X)).trans finProdFinEquiv`
(quantum index first, classical index second, matching `CQState.toJointDensity`'s layout).

This is the T1.4 block-diagonal identity of Tomamichel 2016 instantiated for
the CQ-state representation. It is used in the proof of Proposition 7.1 (eq. 7.35)
via `cqState_joint_traceNorm_eq_sum_blocks`.

Proof route: reindexing a matrix by a bijection is a unitary equivalence and preserves
the trace norm (since it preserves singular values). After reindexing, reduce to
`traceNorm_blockDiagonal_sum` applied with `(Fintype.equivFin X)` to relabel the
classical index from `X` to `Fin (Fintype.card X)`.

Note: `Matrix.trace_blockDiagonal` already exists in Mathlib (trace equals sum of
block traces). The trace-norm analogue requires a separate argument via singular values;
it does not follow from the trace identity alone. -/
lemma traceNorm_blockDiagonal {d : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    [NeZero d] [NeZero (Fintype.card X)] [NeZero (d * Fintype.card X)]
    (f : X → Op d) :
    let e : Fin d × X ≃ Fin (d * Fintype.card X) :=
      (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin X)).trans finProdFinEquiv
    Quantum.Metrics.traceNorm
        (Matrix.reindex e e (Matrix.blockDiagonal f)) =
      ∑ x : X, Quantum.Metrics.traceNorm (f x) := by
  intro e
  set σ : X ≃ Fin (Fintype.card X) := Fintype.equivFin X with hσ
  set g : Fin (Fintype.card X) → Op d := f ∘ σ.symm with hg
  -- Step 1: factor the composite reindex along `((refl).prodCongr σ).trans finProdFinEquiv`
  -- and collapse the inner reindex via `reindex_prodCongr_blockDiagonal`.
  have h1 : Matrix.reindex e e (Matrix.blockDiagonal f) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.blockDiagonal g) := by
    change (Matrix.blockDiagonal f).submatrix e.symm e.symm =
      (Matrix.blockDiagonal g).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
    have hcomp : e.symm = finProdFinEquiv.symm.trans
        ((Equiv.refl (Fin d)).prodCongr σ).symm := rfl
    rw [hcomp]
    rw [show (finProdFinEquiv.symm.trans ((Equiv.refl (Fin d)).prodCongr σ).symm :
              Fin (d * Fintype.card X) → Fin d × X) =
          (((Equiv.refl (Fin d)).prodCongr σ).symm : Fin d × Fin (Fintype.card X) → Fin d × X) ∘
          (finProdFinEquiv.symm : Fin (d * Fintype.card X) → Fin d × Fin (Fintype.card X)) from rfl]
    rw [← Matrix.submatrix_submatrix]
    congr 1
    have := reindex_prodCongr_blockDiagonal σ f
    simp only [Matrix.reindex_apply] at this
    exact this
  rw [h1, ← sum_tensor_single_eq_reindex_blockDiagonal g,
      traceNorm_blockDiagonal_sum g]
  -- Goal: ∑ i : Fin (card X), traceNorm (g i) = ∑ x : X, traceNorm (f x)
  exact Equiv.sum_comp σ.symm (fun x => Quantum.Metrics.traceNorm (f x))

end ArbitraryIndex

end Quantum.Metrics
