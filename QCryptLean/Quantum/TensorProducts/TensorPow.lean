import QCryptLean.Quantum.TensorProducts.CastDim
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

/-!
# Tensor powers of an operator

`Quantum.TensorProducts.Op.tensorPow M n` is the `n`-fold tensor power
`M^{⊗n} = M ⊗ M ⊗ ⋯ ⊗ M` of an operator `M : Op d`, an operator on `d ^ n` dimensions. It is built
by the recursion `M^{⊗(n+1)} = M ⊗ M^{⊗n}` through `Op.tensor` and the dimension cast
`d * d ^ n = d ^ (n + 1)`, starting from the identity `M^{⊗0} = 1` on the one-dimensional register.
The new factor is the *first* tensor factor, so it sits on the high digit of the product index
(`finProdFinEquiv` puts the first factor on the high digit).

## Digit coordinates

Index `Fin (d ^ n)` by digit strings through Mathlib's `finFunctionFinEquiv :
(Fin n → Fin d) ≃ Fin (d ^ n)`, in which digit `k` has weight `d ^ k`. The entries of the power
factor over the digits, `M^{⊗n} (e f) (e g) = ∏ k, M (f k) (g k)`
(`Op.tensorPow_apply_finFunctionFinEquiv`). Because the factors are all equal, this product does
not depend on which digit carries which copy, which is why the power also satisfies the mirrored
recursion `M^{⊗(n+1)} = M^{⊗n} ⊗ M` (`Op.tensorPow_succ'`). Tensor products of *different* factors
do depend on the order. The digit-peeling index laws
`finProdFinEquiv_symm_cast_finFunctionFinEquiv` (high digit) and
`finProdFinEquiv_symm_cast_finFunctionFinEquiv'` (low digit) hold in every dimension, including
`d = 0`.

## Main statements

* `Op.tensorPow_zero`, `Op.tensorPow_succ`, `Op.tensorPow_succ'`, `Op.tensorPow_one`: the
  recursion in both orientations, and the first power.
* `Op.one_tensorPow`, `Op.mul_tensorPow`, `Op.smul_tensorPow`, `Op.conjTranspose_tensorPow`,
  `Op.transpose_tensorPow`: the power is multiplicative, unital, and commutes with adjoints;
  `Op.zero_tensorPow` for positive powers of `0`.
* `Op.tensorPowMonoidHom`: the power as a monoid homomorphism; `IsUnit.tensorPow`.
* `Op.conjTranspose_tensorPow_mul_self`, `Op.tensorPow_mul_conjTranspose_self`,
  `Op.tensorPow_mem_unitaryGroup`: powers of isometries, co-isometries and unitaries.
* `Op.tensorPow_apply`, `Op.tensorPow_apply_finFunctionFinEquiv`: the entry formula in digit
  coordinates, without any nonzero-dimension assumption.
* `Op.tensorPow_diagonal`, `Op.trace_tensorPow`: diagonal operators and traces.
* `Matrix.IsHermitian.tensorPow`, `Matrix.PosSemidef.tensorPow`, `Matrix.PosDef.tensorPow`.
* `Op.tensorPow_castDim`, `Op.reindex_finCongr_tensorPow`: transport of the single-site dimension
  along an equality `a = b`.
* `Op.continuous_tensorPow`, together with `Op.continuous_tensor` and `Op.continuous_castDim`.
* `Quantum.Operators.DensityOp.tensorPowGen_toOp`: the underlying operator of the state tensor power
  `ρ.tensorPowGen n` is `Op.tensorPow ρ.toOp n`.

The power is the tensor product of the constant family (`Op.tensorPow_eq_tensorFamily`, in
`TensorFamily.lean`). The behaviour under permutations of the copies
(`Op.permutationRepresentation_conj_tensorPow`, `Op.commute_tensorPow_permutationRepresentation`)
is in `SymmetricSubspace.lean`, next to the permutation representation.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

variable {d : ℕ}

/-! ## The definition and its recursion -/

/-- The `n`-fold tensor power `M^{⊗n} = M ⊗ M ⊗ ⋯ ⊗ M` of `M : Op d`, an operator on `d ^ n`
dimensions. `M^{⊗0}` is the identity on the one-dimensional register and
`M^{⊗(n+1)} = M ⊗ M^{⊗n}`, the new copy being the first (high-digit) tensor factor. -/
def Op.tensorPow (M : Op d) (n : ℕ) : Op (d ^ n) :=
  match n with
  | 0 => 1
  | n + 1 => Op.castDim (pow_succ' d n).symm (Op.tensor M (Op.tensorPow M n))

@[simp] theorem Op.tensorPow_zero (M : Op d) : Op.tensorPow M 0 = 1 := rfl

/-- The defining recursion: the new copy is the first tensor factor. -/
theorem Op.tensorPow_succ (M : Op d) (n : ℕ) :
    Op.tensorPow M (n + 1) = Op.castDim (pow_succ' d n).symm (Op.tensor M (Op.tensorPow M n)) :=
  rfl

/-! ## Digit coordinates -/

/-- Peeling the **high** digit: in `Fin (d * d ^ n)` the index `finFunctionFinEquiv f` of a digit
string `f : Fin (n + 1) → Fin d` splits into its top digit `f (Fin.last n)` and the lower digits
`Fin.init f`. -/
theorem finProdFinEquiv_symm_cast_finFunctionFinEquiv {n : ℕ} (f : Fin (n + 1) → Fin d)
    (h : d ^ (n + 1) = d * d ^ n) :
    finProdFinEquiv.symm (Fin.cast h (finFunctionFinEquiv f)) =
      (f (Fin.last n), finFunctionFinEquiv (Fin.init f)) := by
  rw [Equiv.symm_apply_eq, Fin.ext_iff, Fin.val_cast, finProdFinEquiv_apply_val,
    finFunctionFinEquiv_apply, finFunctionFinEquiv_apply, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.init]
  ring

/-- Peeling the **low** digit: in `Fin (d ^ n * d)` the index `finFunctionFinEquiv f` of a digit
string `f : Fin (n + 1) → Fin d` splits into the higher digits `Fin.tail f` and its bottom digit
`f 0`. -/
theorem finProdFinEquiv_symm_cast_finFunctionFinEquiv' {n : ℕ} (f : Fin (n + 1) → Fin d)
    (h : d ^ (n + 1) = d ^ n * d) :
    finProdFinEquiv.symm (Fin.cast h (finFunctionFinEquiv f)) =
      (finFunctionFinEquiv (Fin.tail f), f 0) := by
  rw [Equiv.symm_apply_eq, Fin.ext_iff, Fin.val_cast, finProdFinEquiv_apply_val,
    finFunctionFinEquiv_apply, finFunctionFinEquiv_apply, Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Fin.tail]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Entry formula.** In digit coordinates the entries of `M^{⊗n}` are the products of the
single-copy entries, digit by digit. No nonzero-dimension assumption is needed: for `d = 0` and
`n > 0` there are no digit strings. -/
@[simp] theorem Op.tensorPow_apply_finFunctionFinEquiv (M : Op d) {n : ℕ} (f g : Fin n → Fin d) :
    Op.tensorPow M n (finFunctionFinEquiv f) (finFunctionFinEquiv g) = ∏ k, M (f k) (g k) := by
  induction n with
  | zero => simp [Subsingleton.elim f g]
  | succ n ih =>
    rw [Op.tensorPow_succ, Op.castDim_apply]
    simp only [Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply]
    rw [finProdFinEquiv_symm_cast_finFunctionFinEquiv f,
      finProdFinEquiv_symm_cast_finFunctionFinEquiv g, ih, Fin.prod_univ_castSucc, mul_comm]
    rfl

/-- The entry formula at arbitrary indices, read through the digits `finFunctionFinEquiv.symm`. -/
theorem Op.tensorPow_apply (M : Op d) (n : ℕ) (i j : Fin (d ^ n)) :
    Op.tensorPow M n i j =
      ∏ k, M (finFunctionFinEquiv.symm i k) (finFunctionFinEquiv.symm j k) := by
  rw [← Op.tensorPow_apply_finFunctionFinEquiv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Two operators on `d ^ n` dimensions are equal once their entries agree in digit coordinates. -/
theorem Op.ext_finFunctionFinEquiv {n : ℕ} {A B : Op (d ^ n)}
    (h : ∀ f g : Fin n → Fin d, A (finFunctionFinEquiv f) (finFunctionFinEquiv g) =
      B (finFunctionFinEquiv f) (finFunctionFinEquiv g)) : A = B := by
  ext i j
  simpa using h (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j)

/-- The **mirrored recursion**: the new copy may equally be taken as the last (low-digit) tensor
factor. This uses that all copies are equal. -/
theorem Op.tensorPow_succ' (M : Op d) (n : ℕ) :
    Op.tensorPow M (n + 1) = Op.castDim (pow_succ d n).symm (Op.tensor (Op.tensorPow M n) M) := by
  refine Op.ext_finFunctionFinEquiv fun f g => ?_
  rw [Op.tensorPow_apply_finFunctionFinEquiv, Op.castDim_apply]
  simp only [Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply]
  rw [finProdFinEquiv_symm_cast_finFunctionFinEquiv' f,
    finProdFinEquiv_symm_cast_finFunctionFinEquiv' g, Op.tensorPow_apply_finFunctionFinEquiv,
    Fin.prod_univ_succ, mul_comm]
  rfl

/-- The first power is the operator itself, up to the cast `d = d ^ 1`. -/
theorem Op.tensorPow_one (M : Op d) : Op.tensorPow M 1 = Op.castDim (pow_one d).symm M := by
  refine Op.ext_finFunctionFinEquiv fun f g => ?_
  rw [Op.tensorPow_apply_finFunctionFinEquiv, Fin.prod_univ_one, Op.castDim_apply]
  congr 1 <;> exact Fin.ext (by simp)

/-! ## Algebraic laws -/

/-- The power of the identity is the identity. -/
@[simp] theorem Op.one_tensorPow (n : ℕ) : Op.tensorPow (1 : Op d) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Op.tensorPow_succ, ih, Op.tensor_one, Op.castDim_one]

/-- The power is multiplicative: `(A B)^{⊗n} = A^{⊗n} B^{⊗n}`. -/
theorem Op.mul_tensorPow (A B : Op d) (n : ℕ) :
    Op.tensorPow (A * B) n = Op.tensorPow A n * Op.tensorPow B n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Op.tensorPow_succ, Op.tensorPow_succ, Op.tensorPow_succ, ih,
      ← Op.tensor_mul, Op.castDim_mul]

/-- The power commutes with the adjoint: `(M^{⊗n})ᴴ = (Mᴴ)^{⊗n}`. -/
@[simp] theorem Op.conjTranspose_tensorPow (M : Op d) (n : ℕ) :
    (Op.tensorPow M n)ᴴ = Op.tensorPow Mᴴ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Op.tensorPow_succ, Op.tensorPow_succ, Op.castDim_conjTranspose,
      Op.tensor_conjTranspose, ih]

/-- The power commutes with the transpose: `(M^{⊗n})ᵀ = (Mᵀ)^{⊗n}`. -/
theorem Op.transpose_tensorPow (M : Op d) (n : ℕ) :
    (Op.tensorPow M n)ᵀ = Op.tensorPow Mᵀ n := by
  refine Op.ext_finFunctionFinEquiv fun f g => ?_
  simp [transpose_apply]

/-- Scalars are raised to the power: `(c M)^{⊗n} = cⁿ M^{⊗n}`. -/
theorem Op.smul_tensorPow (c : ℂ) (M : Op d) (n : ℕ) :
    Op.tensorPow (c • M) n = c ^ n • Op.tensorPow M n := by
  refine Op.ext_finFunctionFinEquiv fun f g => ?_
  simp [Finset.prod_mul_distrib]

/-- A positive power of the zero operator vanishes. -/
theorem Op.zero_tensorPow {n : ℕ} (hn : n ≠ 0) : Op.tensorPow (0 : Op d) n = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine Op.ext_finFunctionFinEquiv fun f g => ?_
  simp

/-- The power of an isometry `Wᴴ W = 1` is an isometry. -/
theorem Op.conjTranspose_tensorPow_mul_self {W : Op d} (hW : Wᴴ * W = 1) (n : ℕ) :
    (Op.tensorPow W n)ᴴ * Op.tensorPow W n = 1 := by
  rw [Op.conjTranspose_tensorPow, ← Op.mul_tensorPow, hW, Op.one_tensorPow]

/-- The power of a co-isometry `W Wᴴ = 1` is a co-isometry. -/
theorem Op.tensorPow_mul_conjTranspose_self {W : Op d} (hW : W * Wᴴ = 1) (n : ℕ) :
    Op.tensorPow W n * (Op.tensorPow W n)ᴴ = 1 := by
  rw [Op.conjTranspose_tensorPow, ← Op.mul_tensorPow, hW, Op.one_tensorPow]

/-- The power as a monoid homomorphism `Op d →* Op (d ^ n)`. -/
@[simps]
def Op.tensorPowMonoidHom (d n : ℕ) : Op d →* Op (d ^ n) where
  toFun M := Op.tensorPow M n
  map_one' := Op.one_tensorPow n
  map_mul' A B := Op.mul_tensorPow A B n

/-- The power of an invertible operator is invertible. -/
theorem _root_.IsUnit.tensorPow {M : Op d} (hM : IsUnit M) (n : ℕ) : IsUnit (Op.tensorPow M n) :=
  hM.map (Op.tensorPowMonoidHom d n)

/-- The power of a unitary is unitary. -/
theorem Op.tensorPow_mem_unitaryGroup {U : Op d} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (n : ℕ) : Op.tensorPow U n ∈ Matrix.unitaryGroup (Fin (d ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at hU ⊢
  exact Op.tensorPow_mul_conjTranspose_self hU n

/-! ## Diagonal operators and traces -/

/-- The power of a diagonal operator is diagonal, with the products of the single-copy diagonal
entries along the digits. -/
theorem Op.tensorPow_diagonal (v : Fin d → ℂ) (n : ℕ) :
    Op.tensorPow (Matrix.diagonal v) n =
      Matrix.diagonal fun J : Fin (d ^ n) => ∏ k, v (finFunctionFinEquiv.symm J k) := by
  refine Op.ext_finFunctionFinEquiv fun f g => ?_
  simp only [Op.tensorPow_apply_finFunctionFinEquiv, diagonal_apply, Equiv.symm_apply_apply,
    finFunctionFinEquiv.injective.eq_iff]
  by_cases hfg : f = g
  · subst hfg; simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp hfg
    rw [if_neg hfg]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- The trace of a power is the power of the trace. -/
@[simp] theorem Op.trace_tensorPow (M : Op d) (n : ℕ) :
    (Op.tensorPow M n).trace = M.trace ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Op.tensorPow_succ, Op.castDim_trace, Op.trace_tensor, ih, pow_succ']

/-! ## Positivity -/

/-- The power of a Hermitian operator is Hermitian. -/
theorem _root_.Matrix.IsHermitian.tensorPow {M : Op d} (hM : M.IsHermitian) (n : ℕ) :
    (Op.tensorPow M n).IsHermitian := by
  rw [IsHermitian, Op.conjTranspose_tensorPow, hM.eq]

/-- The power of a positive-semidefinite operator is positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.tensorPow {M : Op d} (hM : M.PosSemidef) (n : ℕ) :
    (Op.tensorPow M n).PosSemidef := by
  induction n with
  | zero => exact PosSemidef.one
  | succ n ih =>
    rw [Op.tensorPow_succ, Op.castDim_eq_reindex_finCongr]
    exact ((hM.kronecker ih).submatrix finProdFinEquiv.symm).submatrix _

/-- The power of a positive-definite operator is positive definite. -/
theorem _root_.Matrix.PosDef.tensorPow {M : Op d} (hM : M.PosDef) (n : ℕ) :
    (Op.tensorPow M n).PosDef :=
  (hM.posSemidef.tensorPow n).posDef_iff_isUnit.mpr (hM.isUnit.tensorPow n)

/-! ## Transport of the single-site dimension -/

/-- Casting the single-site operator along `a = b` casts its power along `a ^ n = b ^ n`. -/
theorem Op.tensorPow_castDim {a b : ℕ} (h : a = b) (X : Op a) (n : ℕ) :
    Op.tensorPow (Op.castDim h X) n = Op.castDim (congrArg (· ^ n) h) (Op.tensorPow X n) := by
  subst h; rfl

/-- Relabelling along a numeric cast `finCongr` commutes with the power (the same statement in
`Matrix.reindex` form). -/
theorem Op.reindex_finCongr_tensorPow {a b n : ℕ} (h : a = b) (X : Op a) :
    Matrix.reindex (finCongr (congrArg (· ^ n) h)) (finCongr (congrArg (· ^ n) h))
        (Op.tensorPow X n) =
      Op.tensorPow (Matrix.reindex (finCongr h) (finCongr h) X) n := by
  subst h; simp

/-! ## Continuity -/

/-- A dimension cast is continuous. -/
theorem Op.continuous_castDim {n m : ℕ} (h : n = m) : Continuous (Op.castDim h : Op n → Op m) := by
  subst h; exact continuous_id

/-- The Kronecker product of operators is jointly continuous. -/
theorem Op.continuous_tensor {n m : ℕ} : Continuous fun p : Op n × Op m => Op.tensor p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply]
  exact ((continuous_apply_apply _ _).comp continuous_fst).mul
    ((continuous_apply_apply _ _).comp continuous_snd)

/-- The power `M ↦ M^{⊗n}` is continuous. -/
theorem Op.continuous_tensorPow (n : ℕ) : Continuous fun M : Op d => Op.tensorPow M n := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    simp only [Op.tensorPow_succ]
    exact (Op.continuous_castDim _).comp (Op.continuous_tensor.comp (continuous_id.prodMk ih))

end Quantum.TensorProducts

namespace Quantum.Operators

open Quantum.TensorProducts

/-- The underlying operator of the state tensor power `ρ.tensorPowGen n` is the operator tensor
power of `ρ`. -/
theorem DensityOp.tensorPowGen_toOp {d : ℕ} [NeZero d] (ρ : DensityOp d) (n : ℕ) :
    (ρ.tensorPowGen n).toOp = Op.tensorPow ρ.toOp n := by
  induction n with
  | zero =>
    rw [Op.tensorPow_zero, DensityOp.tensorPowGen, densityOp_castDim_toOp]
    ext i j
    obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
    simp [Op.castDim_apply, DensityOp.trivial]
  | succ n ih =>
    rw [DensityOp.tensorPowGen, densityOp_castDim_toOp, Op.tensorPow_succ, ← ih]
    rfl

end Quantum.Operators

end
