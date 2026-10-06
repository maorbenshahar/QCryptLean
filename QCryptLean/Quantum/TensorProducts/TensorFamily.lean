import QCryptLean.Quantum.TensorProducts.TensorPow
import QCryptLean.Quantum.TensorProducts.Rectangular
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Tensor products of finite families of matrices

For a family `A : Fin n → Matrix (Fin a) (Fin b) ℂ`, `Quantum.TensorProducts.tensorFamily A` is the
tensor (Kronecker) product of the `n` matrices, a matrix indexed by `Fin (a ^ n)` and
`Fin (b ^ n)`. The factors may differ from site to site and may be rectangular, but all of them
have the same shape; `Op.tensorPow` is the case of a constant family, and factors of different
shapes are handled by `tensorFamilyPi` (`TensorFamilyPi.lean`). The companion
`tensorFamilyVec` is the tensor product of a family of vectors.

## Digit coordinates and factor order

Index `Fin (a ^ n)` by digit strings through Mathlib's `finFunctionFinEquiv :
(Fin n → Fin a) ≃ Fin (a ^ n)`, in which digit `k` has weight `a ^ k`. Site `k` of the family acts
on digit `k`:

  `tensorFamily A (e f) (e g) = ∏ k, A k (f k) (g k)`   (`tensorFamily_apply_finFunctionFinEquiv`),

and this entry formula is the definition. Site `0` is therefore the **low** digit. Since
`Op.tensor` and `tensorRect` put their first factor on the high digit, in that Kronecker order
`tensorFamily A` is `A (n - 1) ⊗ ⋯ ⊗ A 1 ⊗ A 0`: the last site is the first factor
(`tensorFamily_castSucc`), site `0` the second one (`tensorFamily_succ`), and a concatenated
family `Fin.append A B` is `tensorFamily B ⊗ tensorFamily A` (`tensorFamily_append`). Recursive
constructions that put the factor `f 0` first, such as `SubDensityOp.tensorFinProd` and
`Op.tensorProdFin`, are the tensor family of the reversed family `fun k => f (Fin.rev k)`
(`tensorFamily_comp_rev_castSucc`).

The matrix-family construction and its algebraic laws need no nonzero-dimension hypothesis: for
`a = 0` and `n > 0` there are no digit strings, and for `n = 0` the product is the identity of the
one-dimensional register.

## Main statements

* `tensorFamily_mul`, `conjTranspose_tensorFamily`, `transpose_tensorFamily`, `tensorFamily_one`,
  `tensorFamily_smul`, `tensorFamily_const_smul`, `tensorFamily_sum`, `tensorFamily_eq_zero`: the
  product is multiplicative along composable families, commutes with adjoints, is unital, and is
  multilinear in the factors. `tensorFamilyMonoidHom` bundles the square case.
* `conjTranspose_tensorFamily_mul_self`, `tensorFamily_mul_conjTranspose_self`,
  `tensorFamily_mem_unitaryGroup`, `isUnit_tensorFamily`: isometries (rectangular ones included),
  co-isometries, unitaries and invertible factors.
* `Matrix.IsHermitian.tensorFamily`, `Matrix.PosSemidef.tensorFamily`,
  `Matrix.PosDef.tensorFamily`, `Matrix.IsDiag.tensorFamily`: positivity and diagonality.
* `tensorFamily_diagonal`, `tensorFamily_single`, `tensorFamily_single_one`,
  `tensorFamily_vecMulVec`, `trace_tensorFamily`: diagonal matrices, matrix units, rank-one
  matrices and traces.
* `tensorFamily_zero`, `tensorFamily_fin_one`, `tensorFamily_castSucc`, `tensorFamily_succ`,
  `tensorFamily_append`, `tensorFamily_comp_rev_castSucc`: the factor order, through the
  rectangular tensor `tensorRect` and the value-preserving relabelling `finCongr`; the `_castDim`
  variants state it for square factors through `Op.tensor` and `Op.castDim`.
* `Op.tensorPow_eq_tensorFamily` and
  `Quantum.Operators.DensityOp.tensorPowGen_toOp_eq_tensorFamily`: the constant family.
* `tensorFamily_mulVec`, `dotProduct_tensorFamilyVec`, `star_tensorFamilyVec`,
  `tensorFamilyVec_smul`, `tensorFamilyVec_sum`: product vectors.
* `continuous_tensorFamily`, and `tensorFamily_castDim` for the single-site dimension.

The behaviour under permutations of the sites is in `SymmetricSubspace.lean`, next to
the permutation representation.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

variable {a b c d n : ℕ}

/-! ## The definitions and their entries -/

/-- The tensor product `A (n - 1) ⊗ ⋯ ⊗ A 0` of a family of `a × b` matrices, an
`a ^ n × b ^ n` matrix. In the digit coordinates of `finFunctionFinEquiv` its entries are the
products of the entries of the factors, site `k` acting on digit `k`. -/
def tensorFamily (A : Fin n → Matrix (Fin a) (Fin b) ℂ) : Matrix (Fin (a ^ n)) (Fin (b ^ n)) ℂ :=
  Matrix.of fun i j => ∏ k, A k (finFunctionFinEquiv.symm i k) (finFunctionFinEquiv.symm j k)

/-- The tensor product of a family of vectors of `ℂ ^ a`, a vector of `ℂ ^ (a ^ n)`, in the same
digit coordinates as `tensorFamily`. -/
def tensorFamilyVec (v : Fin n → Fin a → ℂ) : Fin (a ^ n) → ℂ :=
  fun i => ∏ k, v k (finFunctionFinEquiv.symm i k)

/-- The entries of a tensor family at arbitrary indices, read through the digits
`finFunctionFinEquiv.symm`. -/
theorem tensorFamily_apply (A : Fin n → Matrix (Fin a) (Fin b) ℂ) (i : Fin (a ^ n))
    (j : Fin (b ^ n)) :
    tensorFamily A i j =
      ∏ k, A k (finFunctionFinEquiv.symm i k) (finFunctionFinEquiv.symm j k) :=
  rfl

/-- **Entry formula.** In digit coordinates the entries of a tensor family are the products of the
entries of its factors. -/
@[simp] theorem tensorFamily_apply_finFunctionFinEquiv (A : Fin n → Matrix (Fin a) (Fin b) ℂ)
    (f : Fin n → Fin a) (g : Fin n → Fin b) :
    tensorFamily A (finFunctionFinEquiv f) (finFunctionFinEquiv g) = ∏ k, A k (f k) (g k) := by
  simp [tensorFamily_apply]

theorem tensorFamilyVec_apply (v : Fin n → Fin a → ℂ) (i : Fin (a ^ n)) :
    tensorFamilyVec v i = ∏ k, v k (finFunctionFinEquiv.symm i k) :=
  rfl

@[simp] theorem tensorFamilyVec_apply_finFunctionFinEquiv (v : Fin n → Fin a → ℂ)
    (f : Fin n → Fin a) : tensorFamilyVec v (finFunctionFinEquiv f) = ∏ k, v k (f k) := by
  simp [tensorFamilyVec_apply]

/-- Two `a ^ n × b ^ n` matrices are equal once their entries agree in digit coordinates. -/
theorem ext_finFunctionFinEquiv {M N : Matrix (Fin (a ^ n)) (Fin (b ^ n)) ℂ}
    (h : ∀ (f : Fin n → Fin a) (g : Fin n → Fin b),
      M (finFunctionFinEquiv f) (finFunctionFinEquiv g) =
        N (finFunctionFinEquiv f) (finFunctionFinEquiv g)) : M = N := by
  ext i j
  simpa using h (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j)

/-- The constant family is the tensor power. -/
theorem Op.tensorPow_eq_tensorFamily (M : Op d) (n : ℕ) :
    Op.tensorPow M n = tensorFamily fun _ : Fin n => M := by
  ext i j
  rw [Op.tensorPow_apply, tensorFamily_apply]

/-! ## Algebraic laws -/

/-- The tensor product of a family of identities is the identity. -/
@[simp] theorem tensorFamily_one : tensorFamily (fun _ : Fin n => (1 : Op d)) = 1 := by
  rw [← Op.tensorPow_eq_tensorFamily, Op.one_tensorPow]

/-- A tensor family over no sites is the identity of the one-dimensional register. -/
theorem tensorFamily_zero (A : Fin 0 → Op d) : tensorFamily A = 1 := by
  rw [Subsingleton.elim A fun _ => 1, tensorFamily_one]

/-- A tensor family over one site is its factor, up to the casts `a = a ^ 1` and `b = b ^ 1`. -/
theorem tensorFamily_fin_one (A : Fin 1 → Matrix (Fin a) (Fin b) ℂ) :
    tensorFamily A = (A 0).reindex (finCongr (pow_one a).symm) (finCongr (pow_one b).symm) := by
  refine ext_finFunctionFinEquiv fun f g => ?_
  rw [tensorFamily_apply_finFunctionFinEquiv, Fin.prod_univ_one, reindex_apply, submatrix_apply]
  congr 1 <;> exact Fin.ext (by simp)

/-- The tensor product is multiplicative along composable families:
`(⊗ₖ Aₖ) (⊗ₖ Bₖ) = ⊗ₖ (Aₖ Bₖ)`. -/
theorem tensorFamily_mul (A : Fin n → Matrix (Fin a) (Fin b) ℂ)
    (B : Fin n → Matrix (Fin b) (Fin c) ℂ) :
    tensorFamily A * tensorFamily B = tensorFamily fun k => A k * B k := by
  ext i j
  rw [mul_apply, ← finFunctionFinEquiv.sum_comp]
  simp only [tensorFamily_apply, Equiv.symm_apply_apply, ← Finset.prod_mul_distrib, mul_apply]
  exact (Fintype.prod_sum fun k x =>
    A k (finFunctionFinEquiv.symm i k) x * B k x (finFunctionFinEquiv.symm j k)).symm

/-- The tensor product commutes with the adjoint: `(⊗ₖ Aₖ)ᴴ = ⊗ₖ Aₖᴴ`. -/
@[simp] theorem conjTranspose_tensorFamily (A : Fin n → Matrix (Fin a) (Fin b) ℂ) :
    (tensorFamily A)ᴴ = tensorFamily fun k => (A k)ᴴ := by
  ext i j
  simp [tensorFamily_apply, conjTranspose_apply, star_prod]

/-- The tensor product commutes with the transpose: `(⊗ₖ Aₖ)ᵀ = ⊗ₖ Aₖᵀ`. -/
theorem transpose_tensorFamily (A : Fin n → Matrix (Fin a) (Fin b) ℂ) :
    (tensorFamily A)ᵀ = tensorFamily fun k => (A k)ᵀ := by
  ext i j
  simp [tensorFamily_apply]

/-- Scalars on the factors multiply: `⊗ₖ (sₖ Aₖ) = (∏ₖ sₖ) ⊗ₖ Aₖ`. -/
theorem tensorFamily_smul (s : Fin n → ℂ) (A : Fin n → Matrix (Fin a) (Fin b) ℂ) :
    tensorFamily (fun k => s k • A k) = (∏ k, s k) • tensorFamily A := by
  ext i j
  simp [tensorFamily_apply, Finset.prod_mul_distrib]

/-- A common scalar on every factor is raised to the number of sites. -/
theorem tensorFamily_const_smul (s : ℂ) (A : Fin n → Matrix (Fin a) (Fin b) ℂ) :
    tensorFamily (fun k => s • A k) = s ^ n • tensorFamily A := by
  rw [tensorFamily_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Multilinearity.** The tensor product of sums is the sum, over all choices of one summand per
site, of the tensor products: `⊗ₖ (∑ᵢ Fₖ i) = ∑_g ⊗ₖ Fₖ (g k)`. -/
theorem tensorFamily_sum {ι : Fin n → Type*} [∀ k, Fintype (ι k)]
    (F : ∀ k, ι k → Matrix (Fin a) (Fin b) ℂ) :
    tensorFamily (fun k => ∑ i, F k i) = ∑ g : ∀ k, ι k, tensorFamily fun k => F k (g k) := by
  ext x y
  simp only [tensorFamily_apply, sum_apply]
  exact Fintype.prod_sum fun k i =>
    F k i (finFunctionFinEquiv.symm x k) (finFunctionFinEquiv.symm y k)

/-- A vanishing factor kills the tensor product. -/
theorem tensorFamily_eq_zero {A : Fin n → Matrix (Fin a) (Fin b) ℂ} {k : Fin n} (hk : A k = 0) :
    tensorFamily A = 0 := by
  ext i j
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, zero_apply])

/-- The tensor product of square families as a monoid homomorphism `(Fin n → Op d) →* Op (d ^ n)`,
for the pointwise monoid structure on families. -/
@[simps]
def tensorFamilyMonoidHom (d n : ℕ) : (Fin n → Op d) →* Op (d ^ n) where
  toFun := tensorFamily
  map_one' := tensorFamily_one
  map_mul' A B := (tensorFamily_mul A B).symm

/-- The tensor product of invertible factors is invertible. -/
theorem isUnit_tensorFamily {A : Fin n → Op d} (hA : ∀ k, IsUnit (A k)) :
    IsUnit (tensorFamily A) :=
  (Pi.isUnit_iff.mpr hA).map (tensorFamilyMonoidHom d n)

/-! ## Isometries and unitaries -/

/-- The tensor product of isometries `Aₖᴴ Aₖ = 1` is an isometry. The factors may be rectangular. -/
theorem conjTranspose_tensorFamily_mul_self {A : Fin n → Matrix (Fin a) (Fin b) ℂ}
    (hA : ∀ k, (A k)ᴴ * A k = 1) : (tensorFamily A)ᴴ * tensorFamily A = 1 := by
  simp [tensorFamily_mul, hA]

/-- The tensor product of co-isometries `Aₖ Aₖᴴ = 1` is a co-isometry. -/
theorem tensorFamily_mul_conjTranspose_self {A : Fin n → Matrix (Fin a) (Fin b) ℂ}
    (hA : ∀ k, A k * (A k)ᴴ = 1) : tensorFamily A * (tensorFamily A)ᴴ = 1 := by
  simp [tensorFamily_mul, hA]

/-- The tensor product of unitaries is unitary. -/
theorem tensorFamily_mem_unitaryGroup {A : Fin n → Op d}
    (hA : ∀ k, A k ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    tensorFamily A ∈ Matrix.unitaryGroup (Fin (d ^ n)) ℂ := by
  simp only [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at hA ⊢
  exact tensorFamily_mul_conjTranspose_self hA

/-! ## The factor order -/

/-- Peeling the **last** site: it is the first (high-digit) tensor factor. -/
theorem tensorFamily_castSucc (A : Fin (n + 1) → Matrix (Fin a) (Fin b) ℂ) :
    tensorFamily A =
      (tensorRect (A (Fin.last n)) (tensorFamily fun k => A k.castSucc)).reindex
        (finCongr (pow_succ' a n).symm) (finCongr (pow_succ' b n).symm) := by
  refine ext_finFunctionFinEquiv fun f g => ?_
  rw [tensorFamily_apply_finFunctionFinEquiv, reindex_apply, submatrix_apply, finCongr_symm,
    finCongr_symm, finCongr_apply, finCongr_apply, tensorRect_apply,
    finProdFinEquiv_symm_cast_finFunctionFinEquiv f,
    finProdFinEquiv_symm_cast_finFunctionFinEquiv g, tensorFamily_apply_finFunctionFinEquiv,
    Fin.prod_univ_castSucc, mul_comm]
  rfl

/-- Peeling site `0`: it is the second (low-digit) tensor factor. -/
theorem tensorFamily_succ (A : Fin (n + 1) → Matrix (Fin a) (Fin b) ℂ) :
    tensorFamily A =
      (tensorRect (tensorFamily fun k => A k.succ) (A 0)).reindex
        (finCongr (pow_succ a n).symm) (finCongr (pow_succ b n).symm) := by
  refine ext_finFunctionFinEquiv fun f g => ?_
  rw [tensorFamily_apply_finFunctionFinEquiv, reindex_apply, submatrix_apply, finCongr_symm,
    finCongr_symm, finCongr_apply, finCongr_apply, tensorRect_apply,
    finProdFinEquiv_symm_cast_finFunctionFinEquiv' f,
    finProdFinEquiv_symm_cast_finFunctionFinEquiv' g, tensorFamily_apply_finFunctionFinEquiv,
    Fin.prod_univ_succ, mul_comm]
  rfl

/-- Splitting a digit string of length `m + p` into its `p` high digits and its `m` low digits: in
`Fin (a ^ p * a ^ m)` the index `finFunctionFinEquiv f` is the pair of the digit strings
`f ∘ Fin.natAdd m` (high) and `f ∘ Fin.castAdd p` (low). -/
theorem finProdFinEquiv_symm_cast_finFunctionFinEquiv_add {m p : ℕ} (f : Fin (m + p) → Fin a)
    (h : a ^ (m + p) = a ^ p * a ^ m) :
    finProdFinEquiv.symm (Fin.cast h (finFunctionFinEquiv f)) =
      (finFunctionFinEquiv (f ∘ Fin.natAdd m), finFunctionFinEquiv (f ∘ Fin.castAdd p)) := by
  rw [Equiv.symm_apply_eq, Fin.ext_iff, Fin.val_cast, finProdFinEquiv_apply_val,
    finFunctionFinEquiv_apply, finFunctionFinEquiv_apply, finFunctionFinEquiv_apply,
    Fin.sum_univ_add, Finset.mul_sum]
  simp only [Function.comp_apply, Fin.val_castAdd, Fin.val_natAdd, pow_add]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Concatenated families.** The tensor product of `Fin.append A B` is
`tensorFamily B ⊗ tensorFamily A`: the sites of `B`, placed after those of `A`, carry the high
digits. -/
theorem tensorFamily_append {m p : ℕ} (A : Fin m → Matrix (Fin a) (Fin b) ℂ)
    (B : Fin p → Matrix (Fin a) (Fin b) ℂ) :
    tensorFamily (Fin.append A B) =
      (tensorRect (tensorFamily B) (tensorFamily A)).reindex
        (finCongr ((pow_add a m p).trans (Nat.mul_comm _ _)).symm)
        (finCongr ((pow_add b m p).trans (Nat.mul_comm _ _)).symm) := by
  refine ext_finFunctionFinEquiv fun f g => ?_
  rw [tensorFamily_apply_finFunctionFinEquiv, reindex_apply, submatrix_apply, finCongr_symm,
    finCongr_symm, finCongr_apply, finCongr_apply, tensorRect_apply,
    finProdFinEquiv_symm_cast_finFunctionFinEquiv_add f,
    finProdFinEquiv_symm_cast_finFunctionFinEquiv_add g, tensorFamily_apply_finFunctionFinEquiv,
    tensorFamily_apply_finFunctionFinEquiv, Fin.prod_univ_add, mul_comm]
  simp only [Fin.append_left, Fin.append_right, Function.comp_apply]

/-- `tensorFamily_castSucc` for square factors, through `Op.tensor` and the dimension cast
`Op.castDim`. -/
theorem tensorFamily_castSucc_castDim (A : Fin (n + 1) → Op d) :
    tensorFamily A = Op.castDim (pow_succ' d n).symm
      (Op.tensor (A (Fin.last n)) (tensorFamily fun k => A k.castSucc)) := by
  rw [tensorFamily_castSucc, tensorRect_square, Op.castDim_eq_reindex_finCongr]

/-- `tensorFamily_succ` for square factors, through `Op.tensor` and the dimension cast
`Op.castDim`. -/
theorem tensorFamily_succ_castDim (A : Fin (n + 1) → Op d) :
    tensorFamily A = Op.castDim (pow_succ d n).symm
      (Op.tensor (tensorFamily fun k => A k.succ) (A 0)) := by
  rw [tensorFamily_succ, tensorRect_square, Op.castDim_eq_reindex_finCongr]

/-- `tensorFamily_append` for square factors, through `Op.tensor` and the dimension cast
`Op.castDim`. -/
theorem tensorFamily_append_castDim {m p : ℕ} (A : Fin m → Op d) (B : Fin p → Op d) :
    tensorFamily (Fin.append A B) = Op.castDim ((pow_add d m p).trans (Nat.mul_comm _ _)).symm
      (Op.tensor (tensorFamily B) (tensorFamily A)) := by
  rw [tensorFamily_append, tensorRect_square, Op.castDim_eq_reindex_finCongr]

/-- The recursion of a **reversed** family: `tensorFamily (fun k => A (Fin.rev k))` has `A 0` as
its first (high-digit) tensor factor. This is the factor order of recursive constructions that
put the factor of site `0` first. -/
theorem tensorFamily_comp_rev_castSucc (A : Fin (n + 1) → Matrix (Fin a) (Fin b) ℂ) :
    tensorFamily (fun k => A (Fin.rev k)) =
      (tensorRect (A 0) (tensorFamily fun k => A (Fin.rev k).succ)).reindex
        (finCongr (pow_succ' a n).symm) (finCongr (pow_succ' b n).symm) := by
  rw [tensorFamily_castSucc]
  simp only [Fin.rev_last, Fin.rev_castSucc]

/-! ## Positivity and diagonality -/

/-- The tensor product of Hermitian operators is Hermitian. -/
theorem _root_.Matrix.IsHermitian.tensorFamily {A : Fin n → Op d} (hA : ∀ k, (A k).IsHermitian) :
    (tensorFamily A).IsHermitian := by
  rw [IsHermitian, conjTranspose_tensorFamily]
  exact congrArg _ (funext fun k => (hA k).eq)

/-- The tensor product of positive-semidefinite operators is positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.tensorFamily {A : Fin n → Op d} (hA : ∀ k, (A k).PosSemidef) :
    (tensorFamily A).PosSemidef := by
  induction n with
  | zero => rw [tensorFamily_zero]; exact PosSemidef.one
  | succ n ih =>
    rw [tensorFamily_castSucc]
    exact (((hA _).kronecker (ih fun k => hA _)).submatrix finProdFinEquiv.symm).submatrix _

/-- The tensor product of positive-definite operators is positive definite. -/
theorem _root_.Matrix.PosDef.tensorFamily {A : Fin n → Op d} (hA : ∀ k, (A k).PosDef) :
    (tensorFamily A).PosDef :=
  (PosSemidef.tensorFamily fun k => (hA k).posSemidef).posDef_iff_isUnit.mpr
    (isUnit_tensorFamily fun k => (hA k).isUnit)

/-- The tensor product of diagonal operators is diagonal. -/
theorem _root_.Matrix.IsDiag.tensorFamily {A : Fin n → Op d} (hA : ∀ k, (A k).IsDiag) :
    (tensorFamily A).IsDiag := by
  intro i j hij
  obtain ⟨k, hk⟩ := Function.ne_iff.mp fun h => hij (finFunctionFinEquiv.symm.injective h)
  exact Finset.prod_eq_zero (Finset.mem_univ k) (hA k hk)

/-! ## Diagonal matrices, matrix units, rank-one matrices and traces -/

/-- The tensor product of diagonal matrices is the diagonal matrix of the products of the diagonal
entries along the digits. -/
theorem tensorFamily_diagonal (v : Fin n → Fin d → ℂ) :
    tensorFamily (fun k => diagonal (v k)) =
      diagonal fun J : Fin (d ^ n) => ∏ k, v k (finFunctionFinEquiv.symm J k) := by
  refine ext_finFunctionFinEquiv fun f g => ?_
  simp only [tensorFamily_apply_finFunctionFinEquiv, diagonal_apply, Equiv.symm_apply_apply,
    finFunctionFinEquiv.injective.eq_iff]
  by_cases hfg : f = g
  · subst hfg; simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp hfg
    rw [if_neg hfg]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- The tensor product of matrix units is the matrix unit at the digit strings of their positions,
with the product of their coefficients. -/
theorem tensorFamily_single (s : Fin n → Fin a) (t : Fin n → Fin b) (z : Fin n → ℂ) :
    tensorFamily (fun k => single (s k) (t k) (z k)) =
      single (finFunctionFinEquiv s) (finFunctionFinEquiv t) (∏ k, z k) := by
  refine ext_finFunctionFinEquiv fun f g => ?_
  simp only [tensorFamily_apply_finFunctionFinEquiv, single_apply,
    finFunctionFinEquiv.injective.eq_iff, Fintype.prod_ite_zero, funext_iff, forall_and]

/-- The tensor product of the matrix units `|sₖ⟩⟨tₖ|` is the matrix unit `|s⟩⟨t|` at the digit
strings. -/
theorem tensorFamily_single_one (s : Fin n → Fin a) (t : Fin n → Fin b) :
    tensorFamily (fun k => single (s k) (t k) (1 : ℂ)) =
      single (finFunctionFinEquiv s) (finFunctionFinEquiv t) 1 := by
  rw [tensorFamily_single s t fun _ => 1, Finset.prod_const_one]

/-- The tensor product of rank-one matrices `uₖ vₖᵀ` is the rank-one matrix of the tensor products
of the vectors. -/
theorem tensorFamily_vecMulVec (u : Fin n → Fin a → ℂ) (v : Fin n → Fin b → ℂ) :
    tensorFamily (fun k => vecMulVec (u k) (v k)) =
      vecMulVec (tensorFamilyVec u) (tensorFamilyVec v) := by
  refine ext_finFunctionFinEquiv fun f g => ?_
  simp [vecMulVec_apply, Finset.prod_mul_distrib]

/-- The trace of a tensor product of operators is the product of the traces. -/
theorem trace_tensorFamily (A : Fin n → Op d) : (tensorFamily A).trace = ∏ k, (A k).trace := by
  simp only [trace, diag_apply]
  rw [← finFunctionFinEquiv.sum_comp]
  simp only [tensorFamily_apply_finFunctionFinEquiv]
  exact (Fintype.prod_sum fun k x => A k x x).symm

/-! ## Product vectors -/

/-- A tensor family acts factorwise on product vectors: `(⊗ₖ Aₖ)(⊗ₖ vₖ) = ⊗ₖ (Aₖ vₖ)`. -/
theorem tensorFamily_mulVec (A : Fin n → Matrix (Fin a) (Fin b) ℂ) (v : Fin n → Fin b → ℂ) :
    tensorFamily A *ᵥ tensorFamilyVec v = tensorFamilyVec fun k => A k *ᵥ v k := by
  funext i
  simp only [mulVec, dotProduct, tensorFamilyVec_apply]
  rw [← finFunctionFinEquiv.sum_comp]
  simp only [tensorFamily_apply, Equiv.symm_apply_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun k x => A k (finFunctionFinEquiv.symm i k) x * v k x).symm

/-- The dot product of product vectors is the product of the dot products. -/
theorem dotProduct_tensorFamilyVec (u v : Fin n → Fin a → ℂ) :
    tensorFamilyVec u ⬝ᵥ tensorFamilyVec v = ∏ k, u k ⬝ᵥ v k := by
  simp only [dotProduct]
  rw [← finFunctionFinEquiv.sum_comp]
  simp only [tensorFamilyVec_apply_finFunctionFinEquiv, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun k x => u k x * v k x).symm

/-- Complex conjugation acts factorwise on product vectors. -/
theorem star_tensorFamilyVec (v : Fin n → Fin a → ℂ) :
    star (tensorFamilyVec v) = tensorFamilyVec fun k => star (v k) := by
  funext i
  simp [tensorFamilyVec_apply, star_prod]

/-- A vanishing factor kills a product vector. -/
theorem tensorFamilyVec_eq_zero {v : Fin n → Fin a → ℂ} {k : Fin n} (hk : v k = 0) :
    tensorFamilyVec v = 0 := by
  funext i
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, Pi.zero_apply])

/-- Scalars on the factors of a product vector multiply. -/
theorem tensorFamilyVec_smul (s : Fin n → ℂ) (v : Fin n → Fin a → ℂ) :
    tensorFamilyVec (fun k => s k • v k) = (∏ k, s k) • tensorFamilyVec v := by
  funext i
  simp [tensorFamilyVec_apply, Finset.prod_mul_distrib]

/-- **Multilinearity of product vectors.** The product vector of sums is the sum, over all choices
of one summand per site, of the product vectors. -/
theorem tensorFamilyVec_sum {ι : Fin n → Type*} [∀ k, Fintype (ι k)]
    (F : ∀ k, ι k → Fin a → ℂ) :
    tensorFamilyVec (fun k => ∑ i, F k i) = ∑ g : ∀ k, ι k, tensorFamilyVec fun k => F k (g k) := by
  funext x
  simp only [tensorFamilyVec_apply, Finset.sum_apply]
  exact Fintype.prod_sum fun k i => F k i (finFunctionFinEquiv.symm x k)

/-! ## Continuity and transport of the single-site dimension -/

/-- The tensor product is jointly continuous in the factors. -/
theorem continuous_tensorFamily :
    Continuous fun A : Fin n → Matrix (Fin a) (Fin b) ℂ => tensorFamily A :=
  continuous_matrix fun i j => by
    simp only [tensorFamily_apply]
    exact continuous_finsetProd _ fun k _ => (continuous_apply_apply _ _).comp (continuous_apply k)

/-- Casting every factor along `d = d'` casts the tensor product along `d ^ n = d' ^ n`. -/
theorem tensorFamily_castDim {d' : ℕ} (h : d = d') (A : Fin n → Op d) :
    tensorFamily (fun k => Op.castDim h (A k)) =
      Op.castDim (congrArg (· ^ n) h) (tensorFamily A) := by
  subst h; rfl

/-- **A round-major family that is the identity off a designated block of positions resolves the
identity when summed over that block's outcomes.**

If the positions `Fin n` are split by `e : Fin nK ⊕ Fin nP ≃ Fin n` and the family carries the
identity on the `inl` positions and a per-position POVM `G j` resolving the identity on the `inr`
positions with finite outcome types `ι j`, then summing the tensor product over all dependent
outcome strings `q : ∀ j, ι j` of the `inr` block gives `1`.
This is the resolution of the identity satisfied by an announced measurement that reads only the
`inr` positions. -/
theorem sum_tensorFamily_of_blockResolution {d nK nP n : ℕ}
    {ι : Fin nP → Type*} [∀ j, Fintype (ι j)]
    (e : Fin nK ⊕ Fin nP ≃ Fin n) (G : ∀ j, ι j → Op d)
    (hG : ∀ j, ∑ k : ι j, G j k = (1 : Op d)) :
    ∑ q : ∀ j, ι j,
        tensorFamily
          (fun a => Sum.elim (fun _ => (1 : Op d)) (fun j => G j (q j)) (e.symm a)) =
      (1 : Op (d ^ n)) := by
  rw [← tensorFamily_one (d := d) (n := n)]
  ext i j
  rw [Matrix.sum_apply]
  have key : ∀ q : ∀ j, ι j,
      tensorFamily
          (fun a => Sum.elim (fun _ => (1 : Op d)) (fun jj => G jj (q jj)) (e.symm a)) i j =
        (∏ u : Fin nK, (1 : Op d) ((@finFunctionFinEquiv d n).symm i (e (Sum.inl u)))
            ((@finFunctionFinEquiv d n).symm j (e (Sum.inl u)))) *
          ∏ v : Fin nP, (G v (q v)) ((@finFunctionFinEquiv d n).symm i (e (Sum.inr v)))
            ((@finFunctionFinEquiv d n).symm j (e (Sum.inr v))) := by
    intro q
    rw [tensorFamily_apply, ← Equiv.prod_comp e (fun a =>
      (Sum.elim (fun _ => (1 : Op d)) (fun jj => G jj (q jj)) (e.symm a))
        ((@finFunctionFinEquiv d n).symm i a) ((@finFunctionFinEquiv d n).symm j a)),
      Fintype.prod_sum_type]
    simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  have keyOne : tensorFamily (fun _ : Fin n => (1 : Op d)) i j =
      (∏ u : Fin nK, (1 : Op d) ((@finFunctionFinEquiv d n).symm i (e (Sum.inl u)))
          ((@finFunctionFinEquiv d n).symm j (e (Sum.inl u)))) *
        ∏ v : Fin nP, (1 : Op d) ((@finFunctionFinEquiv d n).symm i (e (Sum.inr v)))
          ((@finFunctionFinEquiv d n).symm j (e (Sum.inr v))) := by
    rw [tensorFamily_apply, ← Equiv.prod_comp e (fun a => (1 : Op d)
      ((@finFunctionFinEquiv d n).symm i a) ((@finFunctionFinEquiv d n).symm j a)),
      Fintype.prod_sum_type]
  simp_rw [key]
  rw [keyOne, ← Finset.mul_sum]
  congr 1
  have hone : ∀ v : Fin nP,
      (1 : Op d) ((@finFunctionFinEquiv d n).symm i (e (Sum.inr v)))
          ((@finFunctionFinEquiv d n).symm j (e (Sum.inr v))) =
        ∑ k : ι v, (G v k) ((@finFunctionFinEquiv d n).symm i (e (Sum.inr v)))
          ((@finFunctionFinEquiv d n).symm j (e (Sum.inr v))) := by
    intro v
    rw [← Matrix.sum_apply, hG v]
  simp_rw [hone]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end Quantum.TensorProducts

namespace Quantum.Operators

open Quantum.TensorProducts

/-- The underlying operator of the state tensor power `ρ.tensorPowGen n` is the tensor product of
the constant family `ρ`. -/
theorem DensityOp.tensorPowGen_toOp_eq_tensorFamily {d : ℕ} [NeZero d] (ρ : DensityOp d)
    (n : ℕ) : (ρ.tensorPowGen n).toOp = tensorFamily fun _ : Fin n => ρ.toOp := by
  rw [DensityOp.tensorPowGen_toOp, Op.tensorPow_eq_tensorFamily]

end Quantum.Operators

end
