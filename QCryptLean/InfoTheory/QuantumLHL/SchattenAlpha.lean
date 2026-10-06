import QCryptLean.InfoTheory.QuantumLHL.GeneralRefLHL

/-!
# Schatten-α power sums and the Rényi-α collision quantity

The `α`-indexed objects for the `α ∈ [1,2]`
generalisation of the σ-weighted collision quantity that drives the leftover-hash
chain. The eventual target of the module is the Rényi-α leftover-hash moment
inequality, whose assembled prefactor `2^{2/α - 1}` is the one restated as Dupuis'
Theorem 8 at arXiv:2311.01600, `adaptivepaper.tex:1086`
(`\label{lemma:LHLrenyi}`).

This file contains the two definitions and their `α = 2` anchors only. The anchors
are what tie the α-indexed objects to the shipped `α = 2` statements of
`GeneralRefLHL.lean`, so that specializing a later α-statement to `α = 2` recovers the
corresponding statement there.

## Main declarations
- `schattenPow` : `‖A‖_α^α = Tr[(Aᴴ A)^{α/2}]`, using `CFC.rpow` on the positive
  semidefinite matrix `Aᴴ A` (`Matrix.posSemidef_conjTranspose_mul_self`).
- `renyiCollisionQuantity` : `∑ x, ‖σ^{-γ} (V x) σ^{-γ}‖_α^α` with `γ = (α-1)/(2α)`.
- `schattenPow_two` : `schattenPow 2 A = (Aᴴ * A).trace.re`, the Hilbert–Schmidt square.
- `schattenPow_nonneg` : nonnegativity.
- `renyiCollisionQuantity_two` : `renyiCollisionQuantity 2 = collisionQuantity`
  (at `α = 2` the weight exponent `γ` is `1/4`, matching `weightedFrobeniusSq`).
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

/-!
## Definitions
-/

/-- **Schatten-α power sum.** `schattenPow α A = ‖A‖_α^α = Tr[(Aᴴ A)^{α/2}]`, the sum of
the `α`-th powers of the singular values of `A`. The power is `CFC.rpow` on the positive
semidefinite matrix `Aᴴ A` (`Matrix.posSemidef_conjTranspose_mul_self`), exactly as
`weightedFrobeniusSq` uses `σ ^ (-1/4 : ℝ)`. At `α = 2` it is the Hilbert–Schmidt square
`(Aᴴ * A).trace.re` (`schattenPow_two`). -/
noncomputable def schattenPow {n : ℕ} (α : ℝ) (A : Op n) : ℝ :=
  (((Aᴴ * A) ^ (α / 2 : ℝ)).trace).re

/-- **σ-weighted Rényi-α collision quantity.**
`renyiCollisionQuantity α σ V = ∑ x, ‖σ^{-γ} (V x) σ^{-γ}‖_α^α` with `γ = (α-1)/(2α)`.
At `α = 2` the exponent `γ` is `1/4` and this is `collisionQuantity`
(`renyiCollisionQuantity_two`). -/
noncomputable def renyiCollisionQuantity {X : Type*} [Fintype X] {n : ℕ}
    (α : ℝ) (σ : Op n) (V : X → Op n) : ℝ :=
  ∑ x : X, schattenPow α
    (σ ^ (-((α - 1) / (2 * α)) : ℝ) * V x * σ ^ (-((α - 1) / (2 * α)) : ℝ))

/-!
## The `α = 2` anchors
-/

/-- **`α = 2` anchor for `schattenPow`.** `schattenPow 2 A = (Aᴴ * A).trace.re`, the
Hilbert–Schmidt square: the exponent `α/2` is `1` and `CFC.rpow` at exponent `1` is the
identity on the positive semidefinite matrix `Aᴴ A`. -/
theorem schattenPow_two {n : ℕ} (A : Op n) : schattenPow 2 A = (Aᴴ * A).trace.re := by
  have h : ((2 : ℝ) / 2) = 1 := by norm_num
  rw [schattenPow, h, CFC.rpow_one _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg]

/-- **Nonnegativity of `schattenPow`.** `CFC.rpow` lands in the positive semidefinite cone,
and the real part of the trace of a positive semidefinite matrix is nonnegative.
The conclusion holds for every real `α`, since `CFC.rpow_nonneg` is unconditional in the
exponent. -/
theorem schattenPow_nonneg {n : ℕ} {α : ℝ} (A : Op n) :
    0 ≤ schattenPow α A := by
  rw [schattenPow]
  exact (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg).trace_re_nonneg

/-- **`α = 2` anchor for `renyiCollisionQuantity`.** At `α = 2` the weight exponent
`γ = (α-1)/(2α)` is `1/4`, so each summand is `weightedFrobeniusSq σ (V x)` and the sum is
`collisionQuantity σ V`. -/
theorem renyiCollisionQuantity_two {X : Type*} [Fintype X] {n : ℕ}
    (σ : Op n) (V : X → Op n) :
    renyiCollisionQuantity 2 σ V = collisionQuantity σ V := by
  have hγ : -(((2 : ℝ) - 1) / (2 * 2)) = (-1/4 : ℝ) := by norm_num
  simp only [renyiCollisionQuantity, collisionQuantity, hγ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [schattenPow_two, weightedFrobeniusSq]

end InfoTheory.QuantumLHL

end
