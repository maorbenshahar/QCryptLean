import QCryptLean.Quantum.TensorProducts.TensorFamily
import QCryptLean.Math.Combinatorics.FinPiFinEquiv

/-!
# Tensor products of finite families of matrices of varying shapes

For shapes `a b : Fin k → ℕ` and matrices `A j : Matrix (Fin (a j)) (Fin (b j)) ℂ`,
`Quantum.TensorProducts.tensorFamilyPi A` is the tensor (Kronecker) product of the `k` matrices, a
matrix indexed by `Fin (∏ j, a j)` and `Fin (∏ j, b j)`. It generalizes `tensorFamily`, whose
factors all have the same shape, and uses the same digit convention.

## Digit coordinates and factor order

Index `Fin (∏ j, a j)` by digit tuples through Mathlib's `finPiFinEquiv :
(∀ j, Fin (a j)) ≃ Fin (∏ j, a j)`, in which digit `j` has weight `∏ i < j, a i`. Factor `j` acts
on digit `j`:

  `tensorFamilyPi A (e f) (e g) = ∏ j, A j (f j) (g j)`   (`tensorFamilyPi_apply_finPiFinEquiv`),

and this entry formula is the definition. As for `tensorFamily`, factor `0` is the **low** digit:
in the Kronecker order of `tensorRect` the product is `A (k - 1) ⊗ ⋯ ⊗ A 0`
(`tensorFamilyPi_castSucc`, `tensorFamilyPi_succ`). With a common shape it is `tensorFamily` up to
the casts `∏ j, a = a ^ k` (`tensorFamilyPi_const`). The recursive product `Op.tensorProdFin`,
which puts factor `0` on the high digit, is the tensor product of the reversed family
(`Op.tensorProdFin_eq_tensorFamilyPi`, in `TensorProdFin.lean`).

No statement assumes nonzero dimensions.

## Main statements

* `tensorFamilyPi_mul`, `conjTranspose_tensorFamilyPi`, `transpose_tensorFamilyPi`,
  `tensorFamilyPi_one`: multiplicativity along composable families, adjoints, transposes and the
  unit; `tensorFamilyPiMonoidHom` bundles the square case.
* `conjTranspose_tensorFamilyPi_mul_self`, `tensorFamilyPi_mul_conjTranspose_self`,
  `isUnit_tensorFamilyPi`: isometries (rectangular ones included), co-isometries and invertible
  factors.
* `tensorFamilyPi_castRect`: a family of value-preserving casts is a value-preserving cast.
* `tensorFamilyPi_succ`, `tensorFamilyPi_castSucc`: the factor order.
* `Matrix.IsHermitian.tensorFamilyPi`, `Matrix.PosSemidef.tensorFamilyPi`,
  `Matrix.PosDef.tensorFamilyPi`, `trace_tensorFamilyPi`: positivity and traces.
* `tensorFamilyPi_const`: the common-shape case is `tensorFamily`.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

variable {k : ℕ}

variable {a b c : Fin k → ℕ}

/-! ## The definition and its entries -/

/-- The tensor product `A (k - 1) ⊗ ⋯ ⊗ A 0` of a family of matrices of shapes `a j × b j`, an
`(∏ j, a j) × (∏ j, b j)` matrix. In the digit coordinates of `finPiFinEquiv` its entries are the
products of the entries of the factors, factor `j` acting on digit `j`. -/
def tensorFamilyPi (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ) :
    Matrix (Fin (∏ j, a j)) (Fin (∏ j, b j)) ℂ :=
  Matrix.of fun I J => ∏ j, A j (finPiFinEquiv.symm I j) (finPiFinEquiv.symm J j)

/-- The entries of `tensorFamilyPi A` at arbitrary indices, read through the digits
`finPiFinEquiv.symm`. -/
theorem tensorFamilyPi_apply (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ) (I : Fin (∏ j, a j))
    (J : Fin (∏ j, b j)) :
    tensorFamilyPi A I J = ∏ j, A j (finPiFinEquiv.symm I j) (finPiFinEquiv.symm J j) :=
  rfl

/-- **Entry formula.** In digit coordinates the entries of `tensorFamilyPi A` are the products of
the entries of the factors. -/
@[simp] theorem tensorFamilyPi_apply_finPiFinEquiv (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ)
    (f : ∀ j, Fin (a j)) (g : ∀ j, Fin (b j)) :
    tensorFamilyPi A (finPiFinEquiv f) (finPiFinEquiv g) = ∏ j, A j (f j) (g j) := by
  simp only [tensorFamilyPi_apply, Equiv.symm_apply_apply]

/-- Two `(∏ j, a j) × (∏ j, b j)` matrices are equal once their entries agree in digit
coordinates. -/
theorem ext_finPiFinEquiv {M N : Matrix (Fin (∏ j, a j)) (Fin (∏ j, b j)) ℂ}
    (h : ∀ (f : ∀ j, Fin (a j)) (g : ∀ j, Fin (b j)),
      M (finPiFinEquiv f) (finPiFinEquiv g) = N (finPiFinEquiv f) (finPiFinEquiv g)) : M = N := by
  ext I J
  simpa using h (finPiFinEquiv.symm I) (finPiFinEquiv.symm J)

/-! ## Algebraic laws -/

/-- The tensor product of a family of identities is the identity. -/
@[simp] theorem tensorFamilyPi_one : tensorFamilyPi (fun j => (1 : Op (a j))) = 1 := by
  refine ext_finPiFinEquiv fun f g => ?_
  simp only [tensorFamilyPi_apply_finPiFinEquiv, one_apply, finPiFinEquiv.injective.eq_iff,
    Fintype.prod_boole, funext_iff]
  split_ifs <;> rfl

/-- The tensor product is multiplicative along composable families:
`(⊗ⱼ Aⱼ) (⊗ⱼ Bⱼ) = ⊗ⱼ (Aⱼ Bⱼ)`. -/
theorem tensorFamilyPi_mul (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ)
    (B : ∀ j, Matrix (Fin (b j)) (Fin (c j)) ℂ) :
    tensorFamilyPi A * tensorFamilyPi B = tensorFamilyPi fun j => A j * B j := by
  ext I J
  rw [mul_apply, ← (finPiFinEquiv (n := b)).sum_comp]
  simp only [tensorFamilyPi_apply, Equiv.symm_apply_apply, ← Finset.prod_mul_distrib, mul_apply]
  exact (Fintype.prod_sum fun j x =>
    A j (finPiFinEquiv.symm I j) x * B j x (finPiFinEquiv.symm J j)).symm

/-- The tensor product commutes with the adjoint: `(⊗ⱼ Aⱼ)ᴴ = ⊗ⱼ Aⱼᴴ`. -/
@[simp] theorem conjTranspose_tensorFamilyPi (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ) :
    (tensorFamilyPi A)ᴴ = tensorFamilyPi fun j => (A j)ᴴ := by
  ext I J
  simp [tensorFamilyPi_apply, conjTranspose_apply, star_prod]

/-- The tensor product commutes with the transpose: `(⊗ⱼ Aⱼ)ᵀ = ⊗ⱼ Aⱼᵀ`. -/
theorem transpose_tensorFamilyPi (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ) :
    (tensorFamilyPi A)ᵀ = tensorFamilyPi fun j => (A j)ᵀ := by
  ext I J
  simp [tensorFamilyPi_apply]

/-- The tensor product of square families as a monoid homomorphism
`(∀ j, Op (a j)) →* Op (∏ j, a j)`, for the pointwise monoid structure on families. -/
@[simps]
def tensorFamilyPiMonoidHom (a : Fin k → ℕ) : (∀ j, Op (a j)) →* Op (∏ j, a j) where
  toFun := tensorFamilyPi
  map_one' := tensorFamilyPi_one
  map_mul' A B := (tensorFamilyPi_mul A B).symm

/-- The tensor product of invertible factors is invertible. -/
theorem isUnit_tensorFamilyPi {A : ∀ j, Op (a j)} (hA : ∀ j, IsUnit (A j)) :
    IsUnit (tensorFamilyPi A) :=
  (Pi.isUnit_iff.mpr hA).map (tensorFamilyPiMonoidHom a)

/-- The tensor product of isometries `Aⱼᴴ Aⱼ = 1` is an isometry. The factors may be rectangular. -/
theorem conjTranspose_tensorFamilyPi_mul_self {A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ}
    (hA : ∀ j, (A j)ᴴ * A j = 1) : (tensorFamilyPi A)ᴴ * tensorFamilyPi A = 1 := by
  simp [tensorFamilyPi_mul, hA]

/-- The tensor product of co-isometries `Aⱼ Aⱼᴴ = 1` is a co-isometry. -/
theorem tensorFamilyPi_mul_conjTranspose_self {A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ}
    (hA : ∀ j, A j * (A j)ᴴ = 1) : tensorFamilyPi A * (tensorFamilyPi A)ᴴ = 1 := by
  simp [tensorFamilyPi_mul, hA]

/-- **A family of value-preserving casts is a value-preserving cast.** This lets a register
regrouping sit inside a tensor product; `castRect` takes no proof argument, so no transport
appears. -/
theorem tensorFamilyPi_castRect (a b : Fin k → ℕ) (h : ∀ j, a j = b j) :
    tensorFamilyPi (fun j => castRect (a j) (b j)) = castRect (∏ j, a j) (∏ j, b j) := by
  have hab : a = b := funext h
  subst hab
  simpa only [castRect_self] using tensorFamilyPi_one (a := a)

/-! ## The factor order -/

/-- Peeling factor `0`: it is the second (low-digit) tensor factor. -/
theorem tensorFamilyPi_succ {a b : Fin (k + 1) → ℕ} (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ) :
    tensorFamilyPi A =
      (tensorRect (tensorFamilyPi fun j => A j.succ) (A 0)).reindex
        (finCongr ((Fin.prod_univ_succ a).trans (Nat.mul_comm _ _)).symm)
        (finCongr ((Fin.prod_univ_succ b).trans (Nat.mul_comm _ _)).symm) := by
  refine ext_finPiFinEquiv fun f g => ?_
  rw [tensorFamilyPi_apply_finPiFinEquiv, reindex_apply, submatrix_apply, finCongr_symm,
    finCongr_symm, finCongr_apply, finCongr_apply, tensorRect_apply,
    finProdFinEquiv_symm_cast_finPiFinEquiv_succ f, finProdFinEquiv_symm_cast_finPiFinEquiv_succ g,
    tensorFamilyPi_apply_finPiFinEquiv, Fin.prod_univ_succ, mul_comm]

/-- Peeling the **last** factor: it is the first (high-digit) tensor factor. -/
theorem tensorFamilyPi_castSucc {a b : Fin (k + 1) → ℕ}
    (A : ∀ j, Matrix (Fin (a j)) (Fin (b j)) ℂ) :
    tensorFamilyPi A =
      (tensorRect (A (Fin.last k)) (tensorFamilyPi fun j => A j.castSucc)).reindex
        (finCongr ((Fin.prod_univ_castSucc a).trans (Nat.mul_comm _ _)).symm)
        (finCongr ((Fin.prod_univ_castSucc b).trans (Nat.mul_comm _ _)).symm) := by
  refine ext_finPiFinEquiv fun f g => ?_
  rw [tensorFamilyPi_apply_finPiFinEquiv, reindex_apply, submatrix_apply, finCongr_symm,
    finCongr_symm, finCongr_apply, finCongr_apply, tensorRect_apply,
    finProdFinEquiv_symm_cast_finPiFinEquiv_castSucc f,
    finProdFinEquiv_symm_cast_finPiFinEquiv_castSucc g, tensorFamilyPi_apply_finPiFinEquiv,
    Fin.prod_univ_castSucc, mul_comm]

/-! ## Positivity and traces -/

/-- The tensor product of Hermitian operators is Hermitian. -/
theorem _root_.Matrix.IsHermitian.tensorFamilyPi {A : ∀ j, Op (a j)}
    (hA : ∀ j, (A j).IsHermitian) : (tensorFamilyPi A).IsHermitian := by
  rw [IsHermitian, conjTranspose_tensorFamilyPi]
  exact congrArg _ (funext fun j => (hA j).eq)

/-- The tensor product of positive-semidefinite operators is positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.tensorFamilyPi {A : ∀ j, Op (a j)}
    (hA : ∀ j, (A j).PosSemidef) : (tensorFamilyPi A).PosSemidef := by
  induction k with
  | zero =>
    rw [Subsingleton.elim A fun _ => 1, tensorFamilyPi_one]
    exact PosSemidef.one
  | succ k ih =>
    rw [tensorFamilyPi_castSucc]
    exact (((hA _).kronecker (ih fun j => hA _)).submatrix finProdFinEquiv.symm).submatrix _

/-- The tensor product of positive-definite operators is positive definite. -/
theorem _root_.Matrix.PosDef.tensorFamilyPi {A : ∀ j, Op (a j)} (hA : ∀ j, (A j).PosDef) :
    (tensorFamilyPi A).PosDef :=
  (PosSemidef.tensorFamilyPi fun j => (hA j).posSemidef).posDef_iff_isUnit.mpr
    (isUnit_tensorFamilyPi fun j => (hA j).isUnit)

/-- The trace of a tensor product of operators is the product of the traces. -/
theorem trace_tensorFamilyPi (A : ∀ j, Op (a j)) :
    (tensorFamilyPi A).trace = ∏ j, (A j).trace := by
  simp only [trace, diag_apply]
  rw [← (finPiFinEquiv (n := a)).sum_comp]
  simp only [tensorFamilyPi_apply_finPiFinEquiv]
  exact (Fintype.prod_sum fun j x => A j x x).symm

/-! ## A common shape -/

/-- **The common-shape case is `tensorFamily`**, up to the casts `∏ j, a = a ^ k` and
`∏ j, b = b ^ k`. -/
theorem tensorFamilyPi_const {a b : ℕ} (A : Fin k → Matrix (Fin a) (Fin b) ℂ) :
    tensorFamilyPi (a := fun _ => a) (b := fun _ => b) A =
      (tensorFamily A).reindex (finCongr (Fin.prod_const k a).symm)
        (finCongr (Fin.prod_const k b).symm) := by
  refine ext_finPiFinEquiv fun f g => ?_
  rw [tensorFamilyPi_apply_finPiFinEquiv, reindex_apply, submatrix_apply, finCongr_symm,
    finCongr_symm, finCongr_apply, finCongr_apply, cast_finPiFinEquiv_const,
    cast_finPiFinEquiv_const, tensorFamily_apply_finFunctionFinEquiv]

end Quantum.TensorProducts

end
