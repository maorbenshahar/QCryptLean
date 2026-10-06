import QCryptLean.Quantum.TensorProducts.Basic
import Mathlib.Data.Matrix.Basis

/-!
# The tensor-lift commutant lemma for paired tensor-product registers

For a family `𝒮` of operators on the `R`-register `ℂ^{dR^n}`, the operators on the paired register
`ℂ^{dA^n} ⊗ ℂ^{dR^n}` that commute with every `1_{Aⁿ} ⊗ S` (`S ∈ 𝒮`) are exactly the
`ℂ`-linear span of the tensor products `X ⊗ M` with `X` free over all of `L(ℂ^{dA^n})` and `M` in
the `R`-side commutant of `𝒮`:

  `Com({1 ⊗ S}) = span_ℂ { X ⊗ M : X ∈ L(Aⁿ), M ∈ Com(𝒮) }`.

The crucial point is that the block operator `X` ranges over *all* of `L(Aⁿ)` —
the `1 ⊗ M`-only form is FALSE (dim 2 vs 32 at `(dA,dR,n)=(2,2,2)`). The proof expands
`T = ∑_{a,b} E_{ab} ⊗ T_{ab}` in `A`-side matrix units and shows each block `T_{ab}` lands in
`Com(𝒮)` by squeezing the commutation relation between `E_{0a} ⊗ 1` and `E_{b0} ⊗ 1`.

Notation: `Set.ofPred` (which delaborates to
`{T | …}`) is used instead of the `{T : … | …}` set-builder notation, since `open
Quantum.Operators` brings the Dirac ket `|i:n⟩` notation, whose `|` token (followed by a binder
`:`) makes the set-builder form unparseable here. The two forms produce identical `Set` terms.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped BigOperators

noncomputable section

namespace Quantum.TensorProducts

variable {dA dR n : ℕ} [NeZero dA] [NeZero dR] [NeZero n]

/-- Entry of a tensor product at a pair of blocked indices. -/
private lemma tensor_apply_pair {p q : ℕ} (A : Op p) (B : Op q)
    (a b : Fin p) (r r' : Fin q) :
    (Op.tensor A B) (finProdFinEquiv (a, r)) (finProdFinEquiv (b, r'))
      = A a b * B r r' := by
  unfold Op.tensor
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply]

/-- The `(a,b)`-block of `T` on the `R`-register. -/
private def blkOp (T : Op (dA ^ n * dR ^ n)) (a b : Fin (dA ^ n)) : Op (dR ^ n) :=
  Matrix.of fun r r' => T (finProdFinEquiv (a, r)) (finProdFinEquiv (b, r'))

omit [NeZero dA] [NeZero dR] [NeZero n] in
/-- The matrix-unit expansion `T = ∑_{a,b} E_{ab} ⊗ T_{ab}` on the `A`-register. -/
private lemma tensor_expansion (T : Op (dA ^ n * dR ^ n)) :
    T = ∑ a : Fin (dA ^ n), ∑ b : Fin (dA ^ n),
        Op.tensor (Matrix.single a b (1 : ℂ)) (blkOp T a b) := by
  ext k l
  rcases hk : finProdFinEquiv.symm k with ⟨a₀, r₀⟩
  rcases hl : finProdFinEquiv.symm l with ⟨b₀, r₀'⟩
  have hk' : k = finProdFinEquiv (a₀, r₀) := by rw [← hk, finProdFinEquiv.apply_symm_apply]
  have hl' : l = finProdFinEquiv (b₀, r₀') := by rw [← hl, finProdFinEquiv.apply_symm_apply]
  subst hk' hl'
  rw [Matrix.sum_apply]
  simp only [Matrix.sum_apply, tensor_apply_pair, blkOp, Matrix.of_apply, Matrix.single_apply]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [NeZero dA] [NeZero dR] [NeZero n] in
/-- A product of operators, evaluated at a pair of blocked indices, expands as a double sum over
    the intermediate blocked index. -/
private lemma mul_apply_pair (P Q : Op (dA ^ n * dR ^ n)) (a b : Fin (dA ^ n))
    (r r' : Fin (dR ^ n)) :
    (P * Q) (finProdFinEquiv (a, r)) (finProdFinEquiv (b, r'))
      = ∑ a' : Fin (dA ^ n), ∑ s : Fin (dR ^ n),
          P (finProdFinEquiv (a, r)) (finProdFinEquiv (a', s))
            * Q (finProdFinEquiv (a', s)) (finProdFinEquiv (b, r')) := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp finProdFinEquiv
    (fun m => P (finProdFinEquiv (a, r)) m * Q m (finProdFinEquiv (b, r'))), Fintype.sum_prod_type]

omit [NeZero dA] [NeZero dR] [NeZero n] in
/-- If `T` commutes with `1 ⊗ S`, then every `A`-block of `T` commutes with `S`. -/
private lemma blk_commute (T : Op (dA ^ n * dR ^ n)) (S : Op (dR ^ n))
    (hS : Op.tensor (1 : Op (dA ^ n)) S * T = T * Op.tensor (1 : Op (dA ^ n)) S)
    (a b : Fin (dA ^ n)) :
    S * blkOp T a b = blkOp T a b * S := by
  ext r r'
  have hEntry := congrFun (congrFun hS (finProdFinEquiv (a, r))) (finProdFinEquiv (b, r'))
  rw [mul_apply_pair, mul_apply_pair] at hEntry
  simp only [tensor_apply_pair, Matrix.one_apply, ite_mul, mul_ite, one_mul, zero_mul,
    mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at hEntry
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [blkOp, Matrix.of_apply]
  exact hEntry

omit [NeZero dA] [NeZero dR] [NeZero n] in
/-- **Paired tensor lift.** The paired-register commutant of `{1_{Aⁿ} ⊗ S : S ∈ 𝒮}` is the span of
`X ⊗ M` with `X` free over all of `L(Aⁿ)` and `M` ranging over the `R`-side commutant of `𝒮`. -/
theorem commutant_pairedTensorFamily_eq_tensorCommutantSpan
    (𝒮 : Set (Op (dR ^ n))) :
    {T | ∀ S ∈ 𝒮, Commute (Op.tensor (1 : Op (dA ^ n)) S) T}
      = (Submodule.span ℂ
          {T | ∃ (X : Op (dA ^ n)) (M : Op (dR ^ n)),
              (∀ S ∈ 𝒮, Commute S M) ∧ T = Op.tensor X M} :
        Set (Op (dA ^ n * dR ^ n))) := by
  -- Package the commutant `{T | ∀ S ∈ 𝒮, Commute (1 ⊗ S) T}` as a submodule `C`.
  set C : Submodule ℂ (Op (dA ^ n * dR ^ n)) :=
    { carrier := {T | ∀ S ∈ 𝒮, Commute (Op.tensor (1 : Op (dA ^ n)) S) T}
      zero_mem' := fun S _ => Commute.zero_right _
      add_mem' := fun ha hb S hS => (ha S hS).add_right (hb S hS)
      smul_mem' := fun c _ hx S hS => (hx S hS).smul_right c } with hC
  -- The theorem's LHS is exactly `↑C`, so it suffices to prove `C = span gen`.
  change (C : Set (Op (dA ^ n * dR ^ n))) = _
  rw [SetLike.coe_set_eq]
  apply le_antisymm
  · -- `C ≤ span gen`: expand `T = ∑ E_{ab} ⊗ T_{ab}`, each block commuting with `𝒮`.
    intro T hT
    rw [tensor_expansion T]
    refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ => ?_))
    exact Submodule.subset_span
      ⟨Matrix.single a b 1, blkOp T a b, fun S hS => blk_commute T S (hT S hS).eq a b, rfl⟩
  · -- `span gen ≤ C`: each generator `X ⊗ M` commutes with `1 ⊗ S`.
    rw [Submodule.span_le]
    rintro x ⟨X, M, hM, rfl⟩ S hS
    change Op.tensor (1 : Op (dA ^ n)) S * Op.tensor X M
      = Op.tensor X M * Op.tensor (1 : Op (dA ^ n)) S
    rw [Op.tensor_mul, Op.tensor_mul, one_mul, mul_one, (hM S hS).eq]

end Quantum.TensorProducts
