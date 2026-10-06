import QCryptLean.InfoTheory.DeFinetti.Purification

/-!
# The vec-correspondence marginal of a maximally-entangled Kraus sandwich

One general identity, for an **arbitrary** (not necessarily Hermitian) operator `M`:

`Tr_A[(M ⊗ 𝟙)·Ω·(M ⊗ 𝟙)†] = (M† · M)ᵀ`,

where `Ω = maxEntangledOp N` is the (unnormalised) maximally entangled operator on the doubled
register.  This is the operator form of the *vec-correspondence* / *transpose trick*
(Watrous, *Theory of Quantum Information*, §2.2: `(A ⊗ 𝟙)|Ω⟩ = (𝟙 ⊗ Aᵀ)|Ω⟩`), and it is the reason
every announce-instrument image of a maximally-entangled-purified reference has a **closed
per-block form** rather than merely a block sum.

## Relation to `purificationOp_partialTraceA`

`InfoTheory.DeFinetti.purificationOp_partialTraceA` is the Hermitian special case `M = √ρ`
(`Tr_A[purificationOp ρ] = ρᵀ`): it runs exactly this argument, but folds in `(√ρ)† = √ρ` and
`√ρ·√ρ = ρ` at the end.  The general non-Hermitian statement below is what a **Kraus** sandwich
needs, because there the left factor `E·B_T` is a product of a projector and a Kraus operator and is
not Hermitian even when both factors are.

## Sources

* Watrous, *Theory of Quantum Information*, §2.2 (vec-correspondence).
* In-project: `maxEntangledOp_tensor_one_ricochet`, `maxEntangledOp_mul_tensor_one_ricochet`,
  `Quantum.TensorProducts.partialTraceA_one_tensor_sandwich`, `maxEntangledOp_partialTraceA`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators

noncomputable section

namespace InfoTheory.DeFinetti

/-- **The vec-correspondence marginal of a maximally-entangled Kraus sandwich.**

For any `M : Op N`,

`Tr_A[(M ⊗ 𝟙)·Ω·(M ⊗ 𝟙)†] = (M† · M)ᵀ`.

The untouched (`B`-side, here indexed by `partialTraceA`'s output) marginal of the vectorised
operator `(M ⊗ 𝟙)|Ω⟩` is the **transpose** of the Gram operator `M†M`.

Proof: ricochet both `M ⊗ 𝟙` factors onto the second tensor slot
(`maxEntangledOp_tensor_one_ricochet` on the left, `maxEntangledOp_mul_tensor_one_ricochet` on the
right), pull them out of the partial trace (`partialTraceA_one_tensor_sandwich`), and use
`Tr_A Ω = 𝟙` (`maxEntangledOp_partialTraceA`); the two transposes then recombine by
`Matrix.transpose_mul`.

This is `purificationOp_partialTraceA`'s argument with the Hermiticity of `√ρ` removed. -/
theorem partialTraceA_tensor_one_maxEntangled_sandwich {N : ℕ} (M : Op N) :
    partialTraceA (Op.tensor M (1 : Op N) * maxEntangledOp N * (Op.tensor M (1 : Op N))ᴴ)
      = (Mᴴ * M)ᵀ := by
  rw [Op.tensor_conjTranspose, conjTranspose_one]
  rw [mul_assoc, maxEntangledOp_mul_tensor_one_ricochet, ← mul_assoc,
    maxEntangledOp_tensor_one_ricochet,
    Quantum.TensorProducts.partialTraceA_one_tensor_sandwich,
    maxEntangledOp_partialTraceA, mul_one, ← Matrix.transpose_mul]

/-- The Kraus-sandwich marginal, with the two flanking operators given separately: this is the form
an announce instrument produces, where the left factor is `E · B` and the sandwich has already been
collapsed by Hermiticity of the announce projector.

`Tr_A[((A·B) ⊗ 𝟙)·Ω·((A·B) ⊗ 𝟙)†] = (B† · (A†·A) · B)ᵀ`. -/
theorem partialTraceA_tensor_one_maxEntangled_sandwich_mul {N : ℕ} (A B : Op N) :
    partialTraceA (Op.tensor (A * B) (1 : Op N) * maxEntangledOp N *
        (Op.tensor (A * B) (1 : Op N))ᴴ)
      = (Bᴴ * (Aᴴ * A) * B)ᵀ := by
  rw [partialTraceA_tensor_one_maxEntangled_sandwich (A * B), Matrix.conjTranspose_mul]
  congr 1
  noncomm_ring

end InfoTheory.DeFinetti

end -- noncomputable section
