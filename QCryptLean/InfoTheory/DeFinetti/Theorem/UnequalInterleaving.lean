import QCryptLean.InfoTheory.DeFinetti.Measure

/-!
# Unequal-factor tensor-power interleaving

This file generalizes the tensor-power partial-trace bridge from equal factors
`d * d` to arbitrary bipartite dimensions `d * e`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Symmetry
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.DeFinetti

/-- Reassociate tensor-power product indices.

The equivalence maps grouped indices `(d^n) * (e^n)` to interleaved local indices
`(d * e)^n` by decoding both grouped tensor-power indices and pairing the
corresponding round indices. -/
noncomputable def tensorPowerProductEquiv (d e n : ℕ) :
    Fin (d ^ n * e ^ n) ≃ Fin ((d * e) ^ n) where
  toFun := fun i =>
    let ab := finProdFinEquiv.symm i
    let ta := finFunctionFinEquiv.symm ab.1
    let tb := finFunctionFinEquiv.symm ab.2
    finFunctionFinEquiv (fun j => finProdFinEquiv (ta j, tb j))
  invFun := fun i =>
    let t := finFunctionFinEquiv.symm i
    let pairs := fun j => finProdFinEquiv.symm (t j)
    finProdFinEquiv (finFunctionFinEquiv (fun j => (pairs j).1),
                     finFunctionFinEquiv (fun j => (pairs j).2))
  left_inv := fun i => by
    dsimp only
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.mk.eta]
  right_inv := fun i => by
    dsimp only
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.mk.eta]

/-- The unequal interleaving equivalence sends separately encoded tensor-power
indices to the tensor-power encoding of pointwise product indices. -/
lemma tensorPowerProductEquiv_fpfe_tie {d e n : ℕ}
    [NeZero d] [NeZero e]
    (α : Fin n → Fin d) (γ : Fin n → Fin e) :
    tensorPowerProductEquiv d e n
      (finProdFinEquiv
        (@finFunctionFinEquiv d n α, @finFunctionFinEquiv e n γ)) =
    @finFunctionFinEquiv (d * e) n
      (fun l => finProdFinEquiv (α l, γ l)) := by
  unfold tensorPowerProductEquiv
  dsimp only [Equiv.coe_fn_mk]
  congr 1
  funext l
  simp [Equiv.symm_apply_apply]

/-- Matrix entries of the tensor power of a partial trace, expanded as a sum
over environment digit functions. -/
lemma partialTraceB_tensorPowGen_toOp_eq_sum_prod {d e n : ℕ}
    [NeZero d] [NeZero e] (τ : DensityOp (d * e))
    (α β : Fin n → Fin d) :
    (τ.partialTraceB.tensorPowGen n).toOp
      (@finFunctionFinEquiv d n α) (@finFunctionFinEquiv d n β) =
      ∑ γ : Fin n → Fin e, ∏ l : Fin n,
        τ.toOp (finProdFinEquiv (α l, γ l))
          (finProdFinEquiv (β l, γ l)) := by
  rw [tensorPowGen_toOp_eq_prod]
  exact Fintype.prod_sum
    (fun l c => τ.toOp (finProdFinEquiv (α l, c))
      (finProdFinEquiv (β l, c)))

/-- Matrix entries of an unequal tensor power after deinterleaving, expanded as
a sum over environment digit functions. -/
lemma partialTraceB_reindexed_tensorPowGen_toOp_eq_sum_prod {d e n : ℕ}
    [NeZero d] [NeZero e] (τ : DensityOp (d * e))
    (α β : Fin n → Fin d) :
    (densityOp_reindex (tensorPowerProductEquiv d e n).symm
      (τ.tensorPowGen n)).partialTraceB.toOp
      (@finFunctionFinEquiv d n α) (@finFunctionFinEquiv d n β) =
      ∑ γ : Fin n → Fin e, ∏ l : Fin n,
        τ.toOp (finProdFinEquiv (α l, γ l))
          (finProdFinEquiv (β l, γ l)) := by
  simp only [DensityOp.partialTraceB, PosSemidefOp.partialTraceB,
      partialTraceB, Matrix.of, densityOp_reindex,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
  change ∑ c', (τ.tensorPowGen n).toOp
      ((tensorPowerProductEquiv d e n)
        (finProdFinEquiv (@finFunctionFinEquiv d n α, c')))
      ((tensorPowerProductEquiv d e n)
        (finProdFinEquiv (@finFunctionFinEquiv d n β, c')))
    = _
  let tie_e := @finFunctionFinEquiv e n
  exact Fintype.sum_equiv tie_e.symm _ _ (fun c' => by
    conv_lhs =>
      rw [show c' = tie_e (tie_e.symm c') from
          (tie_e.apply_symm_apply c').symm]
    rw [tensorPowerProductEquiv_fpfe_tie α (tie_e.symm c'),
        tensorPowerProductEquiv_fpfe_tie β (tie_e.symm c'),
        tensorPowGen_toOp_eq_prod])

/-- Partial trace distributes through tensor powers after deinterleaving unequal factors:
`Tr_{e^n}((τ^⊗n)_{(d*e)^n ≃ d^n*e^n}) = (Tr_e τ)^⊗n`. -/
theorem partialTraceB_tensorPow_reindex {d e n : ℕ}
    [NeZero d] [NeZero e] (τ : DensityOp (d * e)) :
    (densityOp_reindex (tensorPowerProductEquiv d e n).symm
      (τ.tensorPowGen n)).partialTraceB =
      τ.partialTraceB.tensorPowGen n := by
  apply DensityOp.ext
  ext i j
  rw [← (@finFunctionFinEquiv d n).apply_symm_apply i,
    ← (@finFunctionFinEquiv d n).apply_symm_apply j,
    partialTraceB_reindexed_tensorPowGen_toOp_eq_sum_prod,
    partialTraceB_tensorPowGen_toOp_eq_sum_prod]

end InfoTheory.DeFinetti

end
