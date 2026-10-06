import QCryptLean.Math.Combinatorics.RoundRegrouping
import QCryptLean.Math.Combinatorics.PermutationAction
import QCryptLean.Quantum.TensorProducts.TensorFamily

/-!
# Operators under round regrouping

Regrouping paired rounds into one block per factor splits simultaneous round permutations and
products of per-round tensor factors. These are operator identities at arbitrary local dimensions.
-/

open Equiv

open Quantum.Operators Quantum.TensorProducts Matrix
open Math.RepresentationTheory
open scoped Matrix BigOperators Kronecker

noncomputable section

namespace Quantum.TensorProducts

/-- Regrouping paired rounds splits their permutation into one permutation of each block. -/
theorem reindex_roundGroupEquiv_permRep {dA dB n : ℕ} [NeZero dA] [NeZero dB]
    (π : Equiv.Perm (Fin n)) :
    Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        (permutationRepresentation (dA * dB) n π) =
      Op.tensor (permutationRepresentation dA n π) (permutationRepresentation dB n π) := by
  ext I J
  rw [Op_tensor_apply_finProd]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, permutationRepresentation,
    Matrix.of_apply]
  have key : ∀ (fA gA : Fin n → Fin dA) (fB gB : Fin n → Fin dB),
      ((fun k => finProdFinEquiv (fA k, fB k)) =
          (fun k => finProdFinEquiv (gA k, gB k)) ∘ ⇑π.symm ↔
        (fA = gA ∘ ⇑π.symm ∧ fB = gB ∘ ⇑π.symm)) := by
    intro fA gA fB gB
    constructor
    · intro h
      refine ⟨funext fun k => ?_, funext fun k => ?_⟩
      · have hk := congr_fun h k
        simp only [Function.comp_apply] at hk
        exact (Prod.mk.injEq _ _ _ _ ▸ finProdFinEquiv.injective hk).1
      · have hk := congr_fun h k
        simp only [Function.comp_apply] at hk
        exact (Prod.mk.injEq _ _ _ _ ▸ finProdFinEquiv.injective hk).2
    · rintro ⟨hA, hB⟩
      funext k
      simp only [Function.comp_apply]
      exact congrArg finProdFinEquiv (Prod.ext (congr_fun hA k) (congr_fun hB k))
  simp only [finFunctionFinEquiv_symm_roundGroupEquiv_symm, key]
  simp only [ite_and, ite_mul, one_mul, zero_mul]

/-- Regrouping a tensor family of pairs separates the two component tensor families. -/
theorem tensorFamily_pair_reindex_roundGroupEquiv {dA dB : ℕ} (n : ℕ)
    (A : Fin n → Op dA) (B : Fin n → Op dB) :
    Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        (tensorFamily fun a => Op.tensor (A a) (B a))
      = Op.tensor (tensorFamily A) (tensorFamily B) := by
  ext I J
  rw [Op_tensor_apply_finProd]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, tensorFamily_apply,
    finFunctionFinEquiv_symm_roundGroupEquiv_symm, Op_tensor_apply_finProd,
    Equiv.symm_apply_apply]
  rw [Finset.prod_mul_distrib]

/-- **Entry formula for the interleaved IID paired power.**  On the concatenated register
`Fin (d ^ n) × Fin (d ^ n)` (measured system first, purifier second — the orientation of
`Equiv.roundGroupEquiv`), the reindexed tensor power of a paired per-round state factorises
over rounds
into the single-round paired entries. -/
lemma interleaved_tensorPowGen_toOp_apply {d n : ℕ} [NeZero (d * d)]
    (ψ : DensityOp (d * d)) (u v u' v' : Fin n → Fin d) :
    (Matrix.reindex (Equiv.roundGroupEquiv d d n) (Equiv.roundGroupEquiv d d n)
      (ψ.tensorPowGen n).toOp)
        (finProdFinEquiv (finFunctionFinEquiv u, finFunctionFinEquiv v))
        (finProdFinEquiv (finFunctionFinEquiv u', finFunctionFinEquiv v')) =
      ∏ a : Fin n, ψ.toOp (finProdFinEquiv (u a, v a)) (finProdFinEquiv (u' a, v' a)) := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, DensityOp.tensorPowGen_toOp,
    Op.tensorPow_apply, finFunctionFinEquiv_symm_roundGroupEquiv_symm,
    Equiv.symm_apply_apply]

end Quantum.TensorProducts
