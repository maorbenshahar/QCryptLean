import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Scalar Block Trace Norm Identity

For a matrix `M : Op n` and a scalar `c ≥ 0`, the trace norm of the
`(n+1)×(n+1)` block-diagonal matrix
```
  ⎡ M  0 ⎤
  ⎣ 0  c ⎦
```
(with `M` in the top-left `n×n` block and the scalar `c` in the bottom-right
1×1 block, viewed via `Matrix.fromBlocks` and reindexed via `finSumFinEquiv`)
equals `traceNorm M + c`.

This is the 1-dimensional-block specialization of
`Quantum.Metrics.traceNorm_blockDiagonal_sum` from
`Quantum/Metrics/BlockDiagonalTraceNorm.lean`. It is the trace-norm half of
"Strategy A′" used in the proof of
`InfoTheory.SmoothMinEntropy.traceDistanceGen_le_purifiedDistance`
(Tomamichel 2016, Lemma 3.17 / eq. 3.29).

## Main statements
- `Quantum.Metrics.traceNorm_fromBlocks_scalar`: the scalar block trace-norm
  identity.

## References
- Tomamichel, M. *Quantum Information Processing with Finite Resources*.
  Springer, 2016. §3.4, Lemma 3.17.
-/

open Quantum.Operators Matrix

noncomputable section

namespace Quantum.Metrics

/-- The conjugate-transpose-times-self of a `fromBlocks M 0 0 (diagonal _)` block
matrix splits over the block structure, producing `Mᴴ * M` in the top-left block
and a `1×1` scalar `c* * c` in the bottom-right block. -/
private lemma fromBlocks_scalar_adjoint_mul {n : ℕ} (M : Op n) (c : ℂ) :
    (Matrix.fromBlocks M
        (0 : Matrix (Fin n) (Fin 1) ℂ)
        (0 : Matrix (Fin 1) (Fin n) ℂ)
        (Matrix.diagonal (fun _ : Fin 1 => c)))ᴴ *
      Matrix.fromBlocks M 0 0 (Matrix.diagonal (fun _ : Fin 1 => c)) =
    Matrix.fromBlocks (Mᴴ * M) 0 0
      (Matrix.diagonal (fun _ : Fin 1 => (starRingEnd ℂ) c * c)) := by
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  simp

/-- The characteristic polynomial of a `reindex`ed
`fromBlocks A 0 0 (diagonal [d])` factors as `A.charpoly * (X - C d)`. -/
private lemma charpoly_reindex_fromBlocks_scalar
    {n : ℕ} (A : Op n) (d : ℂ) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A
          (0 : Matrix (Fin n) (Fin 1) ℂ)
          (0 : Matrix (Fin 1) (Fin n) ℂ)
          (Matrix.diagonal (fun _ : Fin 1 => d)))).charpoly =
    A.charpoly * (Polynomial.X - Polynomial.C d) := by
  rw [Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂,
      Matrix.charpoly_diagonal]
  simp

/-- The eigenvalue multiset of a reindexed Hermitian scalar-block matrix is the
union of the eigenvalue multiset of the top-left block and the singleton `{d}`. -/
private lemma eigenvalues_multiset_reindex_fromBlocks_scalar
    {n : ℕ} (A : Op n) (hA : A.IsHermitian) (d : ℝ)
    (hB : (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks A
                (0 : Matrix (Fin n) (Fin 1) ℂ)
                (0 : Matrix (Fin 1) (Fin n) ℂ)
                (Matrix.diagonal (fun _ : Fin 1 => (d : ℂ))))).IsHermitian) :
    Multiset.map hB.eigenvalues Finset.univ.val =
    Multiset.map hA.eigenvalues Finset.univ.val + {d} := by
  let ofR : ℝ → ℂ := @RCLike.ofReal ℂ _
  have hB_roots := hB.roots_charpoly_eq_eigenvalues
  have hA_roots := hA.roots_charpoly_eq_eigenvalues
  have hB_cp := charpoly_reindex_fromBlocks_scalar A (d : ℂ)
  -- Compute roots over ℂ
  have hA_cp_ne : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hXsub_ne : (Polynomial.X - Polynomial.C (d : ℂ)) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have hroots_mul : (A.charpoly * (Polynomial.X - Polynomial.C (d : ℂ))).roots =
      A.charpoly.roots + (Polynomial.X - Polynomial.C (d : ℂ)).roots :=
    Polynomial.roots_mul (mul_ne_zero hA_cp_ne hXsub_ne)
  have hroots_X : (Polynomial.X - Polynomial.C (d : ℂ)).roots = {(d : ℂ)} :=
    Polynomial.roots_X_sub_C _
  have heq_complex :
      Multiset.map (ofR ∘ hB.eigenvalues) Finset.univ.val =
      Multiset.map (ofR ∘ hA.eigenvalues) Finset.univ.val + {(d : ℂ)} := by
    rw [← hB_roots, hB_cp, hroots_mul, hroots_X, hA_roots]
  apply Multiset.map_injective (RCLike.ofReal_injective (K := ℂ))
  simp only [Multiset.map_add, Multiset.map_map, Multiset.map_singleton]
  exact heq_complex

/-- **Scalar block trace-norm identity.**

For `M : Op n` and a scalar `c ≥ 0`, the trace norm of the block-diagonal
matrix obtained by placing `M` in the top-left `n×n` block and the scalar `c`
in the bottom-right `1×1` block (with zeros off-diagonal), viewed as a matrix
on `Fin (n+1)` via `finSumFinEquiv`, equals `traceNorm M + c`. -/
lemma traceNorm_fromBlocks_scalar {n : ℕ} [NeZero n] (M : Op n) (c : ℝ) (hc : 0 ≤ c) :
    traceNorm
      ((Matrix.fromBlocks M
          (0 : Matrix (Fin n) (Fin 1) ℂ)
          (0 : Matrix (Fin 1) (Fin n) ℂ)
          (Matrix.diagonal (fun _ : Fin 1 => (c : ℂ)))).reindex
        finSumFinEquiv finSumFinEquiv) =
      traceNorm M + c := by
  -- Set up the un-reindexed and reindexed block matrices.
  set X : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
    Matrix.fromBlocks M 0 0 (Matrix.diagonal (fun _ : Fin 1 => (c : ℂ))) with hXdef
  set Y : Op (n + 1) := Matrix.reindex finSumFinEquiv finSumFinEquiv X
  -- Step 1: Yᴴ * Y = reindex e e (Xᴴ * X)
  have hYadj_mul : Yᴴ * Y =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Xᴴ * X) := by
    simp only [Y, Matrix.conjTranspose_reindex]
    simp only [← Matrix.coe_reindexLinearEquiv (R := ℂ) (A := ℂ)]
    rw [Matrix.reindexLinearEquiv_mul]
  -- Step 2: Xᴴ * X splits into the scalar-block form, with c² (as a real) as
  -- the 1×1 block.
  have hXadj_mul : Xᴴ * X =
      Matrix.fromBlocks (Mᴴ * M) 0 0
        (Matrix.diagonal (fun _ : Fin 1 => (((c ^ 2 : ℝ) : ℂ)))) := by
    rw [hXdef, fromBlocks_scalar_adjoint_mul]
    congr 2
    funext _
    simp [Complex.conj_ofReal, sq]
  -- Combined: Yᴴ * Y matches the hypothesis of the eigenvalue helper.
  have hY_form : Yᴴ * Y =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (Mᴴ * M) 0 0
          (Matrix.diagonal (fun _ : Fin 1 => (((c ^ 2 : ℝ) : ℂ))))) := by
    rw [hYadj_mul, hXadj_mul]
  -- Hermitian witnesses.
  have hA : (Mᴴ * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hYY : (Yᴴ * Y).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self Y
  have hBform :
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (Mᴴ * M) 0 0
          (Matrix.diagonal (fun _ : Fin 1 => (((c ^ 2 : ℝ) : ℂ))))
        )).IsHermitian := hY_form ▸ hYY
  have heig_eq : hYY.eigenvalues = hBform.eigenvalues :=
    (hYY.eigenvalues_eq_eigenvalues_iff hBform).mpr (congrArg Matrix.charpoly hY_form)
  -- Multiset decomposition of the eigenvalues of the reindexed scalar-block.
  have heig_decomp :=
    eigenvalues_multiset_reindex_fromBlocks_scalar (Mᴴ * M) hA (c ^ 2) hBform
  -- Unfold `traceNorm` on both sides to an eigenvalue sum.
  unfold traceNorm
  change ∑ i, √(hYY.eigenvalues i) = (∑ i, √(hA.eigenvalues i)) + c
  -- Convert the left sum into `(Multiset.map (√ ∘ _) _).sum`.
  have hL :
      ∑ i, √(hYY.eigenvalues i) =
      (Multiset.map Real.sqrt
        (Multiset.map hYY.eigenvalues Finset.univ.val)).sum := by
    rw [Multiset.map_map]; rfl
  have hR :
      ∑ i, √(hA.eigenvalues i) =
      (Multiset.map Real.sqrt
        (Multiset.map hA.eigenvalues Finset.univ.val)).sum := by
    rw [Multiset.map_map]; rfl
  rw [hL, hR, heig_eq, heig_decomp, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton, Real.sqrt_sq hc]

end Quantum.Metrics

end -- noncomputable section
