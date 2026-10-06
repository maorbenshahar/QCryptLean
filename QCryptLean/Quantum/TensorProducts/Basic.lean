import QCryptLean.Quantum.Operators.BraKet.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Matrix.Order  -- For PosSemidef.kronecker

namespace Quantum.TensorProducts

open Quantum.Operators
open scoped Matrix BigOperators ComplexConjugate ComplexOrder TensorProduct Kronecker
open Matrix

noncomputable section

/-!
# Type-Safe Quantum Mechanics - Tensor Products (HMul Foundation)

This module defines tensor products of quantum states and operators,
built on the HMul-primary foundation from `BraKet/Basic.lean`.

## Key Definitions:
- `⊗` (Ket.tensor, NormKet.tensor, Op.tensor): Unified tensor product notation
  - Works for kets, normalized kets, and operators (Kronecker product)
  - Type inference determines which tensor product to use
- Tensor products of unitary and density operators
- `tensorUnitary`: tensor a unitary with identity on an equal-dimensional ancilla
- `tensor_conj_transpose_mul_self_of_conj_transpose_mul_self`: tensoring
  preserves the left unitary equation.

The calculus properties (linearity, distributivity) are in `PartialTrace.lean`.
-/

/-- Complex conjugation distributes over an `if` expression whose false branch
is zero. -/
lemma star_ite_zero {b : Prop} [Decidable b] (a : ℂ) :
    star (if b then a else 0) = if b then star a else 0 := by
  split_ifs <;> simp

-- ============================================================================
-- Section 15: Tensor Product Definitions
-- ============================================================================

/-- Tensor product of kets -/
def Ket.tensor {n m : ℕ} (ψ : Ket n) (φ : Ket m) : Ket (n * m) :=
  ⟨fun k =>
    let ⟨i, j⟩ := finProdFinEquiv.symm k
    ψ.vec i * φ.vec j⟩

/-- Tensor product of bras -/
def Bra.tensor {n m : ℕ} (β₁ : Bra n) (β₂ : Bra m) : Bra (n * m) :=
  ⟨fun k =>
    let ⟨i, j⟩ := finProdFinEquiv.symm k
    β₁.vec i * β₂.vec j⟩

/-- Tensor product of operators (Kronecker product) -/
def Op.tensor {n m : ℕ} (A : Op n) (B : Op m) : Op (n * m) :=
  reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)  -- Uses Matrix.kronecker (⊗ₖ)

-- Unified tensor product notation ⊗ (works for Ket, Bra, Op)
-- Note: NormKet tensor notation is defined below after the needed calculus lemmas.
infixl:70 " ⊗ " => Ket.tensor
infixl:70 " ⊗ " => Bra.tensor
infixl:70 " ⊗ " => Op.tensor

/-- Entry of a Kronecker product (`Op.tensor`) decomposes via `finProdFinEquiv`. The two
coordinates of `finProdFinEquiv.symm i` are definitionally `i.divNat` and `i.modNat`,
so this is also the entry formula in that presentation. -/
lemma Op_tensor_apply_finProd {n m : ℕ} (A : Op n) (B : Op m) (i j : Fin (n * m)) :
    (Op.tensor A B) i j =
      A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      B (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  simp only [Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply]

-- ============================================================================
-- Bra Tensor Properties
-- ============================================================================

/-- Dag distributes over tensor: (ψ ⊗ φ).dag = ψ.dag ⊗ φ.dag -/
@[simp]
theorem Ket.dag_tensor {n m : ℕ} (ψ : Ket n) (φ : Ket m) :
    (ψ ⊗ φ).dag = ψ.dag ⊗ φ.dag := by
  ext k
  unfold Ket.dag Ket.tensor Bra.tensor
  simp only [starRingEnd_apply, star_mul']

-- ============================================================================
-- Kronecker Product Lemmas (Physics Properties)
-- ============================================================================

/-- Physics: Conjugate transpose distributes over tensor product: (A⊗B)† = A†⊗B† -/
@[simp]
theorem Op.tensor_conjTranspose {n m : ℕ} (A : Op n) (B : Op m) :
    (A ⊗ B)† = A† ⊗ B† := by
  -- Proof strategy: Use properties of reindex and kronecker
  -- (reindex e f (A ⊗ₖ B))† = reindex e f ((A ⊗ₖ B)†) = reindex e f (A† ⊗ₖ B†)
  unfold Op.tensor
  simp only [conjTranspose_reindex, conjTranspose_kronecker]

/-- Physics: Tensor product preserves matrix multiplication: (A⊗B)(C⊗D) = (AC)⊗(BD) -/
@[simp]
theorem Op.tensor_mul {n m : ℕ} (A C : Op n) (B D : Op m) :
    (A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D) := by
  unfold Op.tensor
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, kroneckerMap_apply]
  -- Convert sum over Fin(n*m) to sum over Fin n × Fin m
  trans (∑ k : Fin n × Fin m,
          (A (finProdFinEquiv.symm i).1 k.1 * B (finProdFinEquiv.symm i).2 k.2) *
          (C k.1 (finProdFinEquiv.symm j).1 * D k.2 (finProdFinEquiv.symm j).2))
  · apply Fintype.sum_equiv finProdFinEquiv.symm
    intro k; simp [finProdFinEquiv]
  -- Split into double sum and rearrange: (a*b)*(c*d) = (a*c)*(b*d)
  rw [Fintype.sum_prod_type]
  trans (∑ a : Fin n, ∑ b : Fin m,
          (A (finProdFinEquiv.symm i).1 a * C a (finProdFinEquiv.symm j).1) *
          (B (finProdFinEquiv.symm i).2 b * D b (finProdFinEquiv.symm j).2))
  · congr 1; ext a; congr 1; ext b; ring
  -- Factor: ∑_{a,b} f(a)*g(b) = (∑_a f(a))*(∑_b g(b))
  rw [Finset.sum_mul_sum]

/-- Physics: Identity tensor product: I⊗I = I -/
@[simp]
theorem Op.tensor_one {n m : ℕ} :
    (1 : Op n) ⊗ (1 : Op m) = 1 := by
  -- Proof: 1 ⊗ 1 = I_{n*m}
  -- Use Mathlib's one_kronecker_one and submatrix_one_equiv
  unfold Op.tensor
  rw [Matrix.one_kronecker_one]
  -- submatrix of identity with equivalence is identity
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm

/-- Operators of the form `A ⊗ 1` and `1 ⊗ B` commute. -/
lemma Op.tensor_one_mul_one_tensor_comm {d : ℕ} (A B : Op d) :
    Op.tensor A (1 : Op d) * Op.tensor (1 : Op d) B =
      Op.tensor (1 : Op d) B * Op.tensor A (1 : Op d) := by
  rw [Op.tensor_mul, Op.tensor_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul, Matrix.mul_one]

/-- Tensoring a unitary with identity is unitary. -/
def tensorUnitary {d : ℕ} (U : UnitaryOp d) : UnitaryOp (d * d) :=
  ⟨Op.tensor U.toOp (1 : Op d), by
    rw [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, U.unitary_left,
      Matrix.one_mul, Op.tensor_one], by
    rw [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, U.unitary_right,
      Matrix.one_mul, Op.tensor_one]⟩

/-- The tensor product preserves the left unitary equation `A† * A = 1`. -/
lemma tensor_conj_transpose_mul_self_of_conj_transpose_mul_self {n m : ℕ}
    (A : Op n) (B : Op m) (hA : A† * A = 1) (hB : B† * B = 1) :
    (Op.tensor A B)† * Op.tensor A B = 1 := by
  rw [Op.tensor_conjTranspose, Op.tensor_mul, hA, hB, Op.tensor_one]

/-- Physics: Trace factorizes over tensor product: Tr(A⊗B) = Tr(A)·Tr(B) -/
@[simp]
theorem Op.trace_tensor {n m : ℕ} (A : Op n) (B : Op m) :
    (A ⊗ B).trace = A.trace * B.trace := by
  unfold Op.tensor trace
  simp only [Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  -- Convert sum over Fin(n*m) to sum over Fin n × Fin m
  trans (∑ p : Fin n × Fin m, (A ⊗ₖ B) p p)
  · apply Fintype.sum_equiv finProdFinEquiv.symm
    intro i; simp [finProdFinEquiv]
  -- Unfold kronecker at diagonal: (A ⊗ₖ B)[(i,j), (i,j)] = A[i,i] * B[j,j]
  simp only [kroneckerMap_apply]
  -- Factor: ∑_{i,j} A[i,i] * B[j,j] = (∑_i A[i,i]) * (∑_j B[j,j])
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Physics: Tensor product of positive semidefinite operators is positive semidefinite.

Uses `Matrix.PosSemidef.kronecker` from Mathlib to show that the Kronecker product
of PSD matrices is PSD, then uses `posSemidef_submatrix_equiv` to transfer to
the reindexed form used by `Op.tensor`. -/
theorem Op.tensor_posSemidef {n m : ℕ} (A : Op n) (B : Op m)
    (hAH : A.IsHermitian) (hBH : B.IsHermitian)
    (hA : ∀ x, 0 ≤ (quadraticForm A x).re) (hB : ∀ y, 0 ≤ (quadraticForm B y).re) :
    ∀ z : Fin (n * m) → ℂ, 0 ≤ (quadraticForm (A ⊗ B) z).re := by
  -- Convert our quadraticForm condition to Matrix.PosSemidef
  have hPA : A.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · exact hAH
    · intro x
      rw [Complex.nonneg_iff]
      constructor
      · exact hA x
      · -- Show imaginary part is 0 using Hermitian property
        simp only [dotProduct, mulVec, Pi.star_apply]
        have herm : ∀ i j, star (A i j) = A j i := fun i j => congr_fun₂ hAH j i
        have h_conj : conj (∑ i, star (x i) * (∑ j, A i j * x j)) =
                       ∑ i, star (x i) * (∑ j, A i j * x j) := by
          simp only [map_sum, map_mul, starRingEnd_apply, star_star]
          conv_lhs => arg 2; ext i; arg 2; arg 2; ext j; rw [herm]
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1; ext j; congr 1; ext i; ring
        simp only [Complex.ext_iff, Complex.conj_re, Complex.conj_im] at h_conj
        linarith [h_conj.2]
  have hPB : B.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · exact hBH
    · intro x
      rw [Complex.nonneg_iff]
      constructor
      · exact hB x
      · simp only [dotProduct, mulVec, Pi.star_apply]
        have herm : ∀ i j, star (B i j) = B j i := fun i j => congr_fun₂ hBH j i
        have h_conj : conj (∑ i, star (x i) * (∑ j, B i j * x j)) =
                       ∑ i, star (x i) * (∑ j, B i j * x j) := by
          simp only [map_sum, map_mul, starRingEnd_apply, star_star]
          conv_lhs => arg 2; ext i; arg 2; arg 2; ext j; rw [herm]
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1; ext j; congr 1; ext i; ring
        simp only [Complex.ext_iff, Complex.conj_re, Complex.conj_im] at h_conj
        linarith [h_conj.2]
  -- Use PosSemidef.kronecker: Kronecker product of PSD matrices is PSD
  have hKron : (A ⊗ₖ B).PosSemidef := hPA.kronecker hPB
  -- Use posSemidef_submatrix_equiv: reindexing preserves PSD
  have hTensor : (A ⊗ B).PosSemidef := by
    unfold Op.tensor
    rw [reindex_apply]
    exact (posSemidef_submatrix_equiv finProdFinEquiv.symm).mpr hKron
  -- Convert back to quadraticForm condition
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hTensor
  intro z
  have h := hTensor.2 z
  rw [Complex.nonneg_iff] at h
  exact h.1

end  -- noncomputable section
end Quantum.TensorProducts

-- DensityOp extensions must be in the same namespace as DensityOp for dot notation
noncomputable section
namespace Quantum.Operators

open Quantum.TensorProducts
open scoped Matrix BigOperators ComplexConjugate ComplexOrder TensorProduct Kronecker
open Matrix

/-- Tensor product of density operators is a density operator -/
def DensityOp.tensor {n m : ℕ} (ρ : DensityOp n) (σ : DensityOp m) : DensityOp (n * m) :=
  ⟨⟨⟨ρ.toOp ⊗ σ.toOp, by
    -- Physics proof: (ρ⊗σ)† = ρ†⊗σ† = ρ⊗σ (using Hermiticity of ρ and σ)
    unfold IsHermitian
    calc (ρ.toOp ⊗ σ.toOp)†
        = ρ.toOp† ⊗ σ.toOp† := by rw [Op.tensor_conjTranspose]
      _ = ρ.toOp ⊗ σ.toOp := by
          rw [show ρ.toOp† = ρ.toOp from ρ.toPosSemidefOp.toHermitianOp.isHermitian]
          rw [show σ.toOp† = σ.toOp from σ.toPosSemidefOp.toHermitianOp.isHermitian]
    ⟩, by
    -- Physics proof: ρ⊗σ is positive semidefinite because both ρ and σ are
    exact Op.tensor_posSemidef ρ.toOp σ.toOp
      ρ.toPosSemidefOp.toHermitianOp.isHermitian σ.toPosSemidefOp.toHermitianOp.isHermitian
      ρ.toPosSemidefOp.pos_semidef σ.toPosSemidefOp.pos_semidef
    ⟩, by
    -- Physics proof: Tr(ρ⊗σ) = Tr(ρ)·Tr(σ) = 1·1 = 1
    calc (ρ.toOp ⊗ σ.toOp).trace
        = ρ.toOp.trace * σ.toOp.trace := by rw [Op.trace_tensor]
      _ = 1 * 1 := by rw [ρ.trace_one, σ.trace_one]
      _ = 1 := by ring
    ⟩

/-- The trivial 1×1 density operator (identity on dimension 1).
    This is the unique density operator on a 1-dimensional space. -/
def DensityOp.trivial : DensityOp 1 :=
  ⟨⟨⟨!![1], by
    unfold IsHermitian Matrix.conjTranspose
    ext i j
    fin_cases i; fin_cases j; simp [Matrix.of_apply]
  ⟩, by
    intro x
    simp only [quadraticForm, Matrix.mulVec, Matrix.of_apply, dotProduct,
               Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Pi.star_apply]
    -- Simplify ![![1]] 0 0 to 1
    have h_entry : ![![(1 : ℂ)]] 0 0 = 1 := rfl
    simp only [h_entry, one_mul]
    -- Goal: 0 ≤ (star (x 0) * x 0).re
    -- Directly compute: (star z * z).re = |z|² ≥ 0
    have h : (star (x 0) * x 0).re = Complex.normSq (x 0) := by
      simp only [Complex.mul_re, star, Complex.normSq_apply]
      ring
    rw [h]
    exact Complex.normSq_nonneg _
  ⟩, by
    simp only [Matrix.trace, Matrix.diag, Finset.univ_unique, Fin.default_eq_zero,
               Finset.sum_singleton]
    rfl
  ⟩

/-- n-fold tensor power of a density operator: ρ^⊗n (general dimension).
    For the i.i.d. error model, this represents n independent copies
    of the same single-copy state. -/
noncomputable def DensityOp.tensorPowGen {d : ℕ} [NeZero d] (ρ : DensityOp d) (n : ℕ) :
    DensityOp (d ^ n) :=
  match n with
  | 0 => DensityOp.castDim (by simp : 1 = d ^ 0) DensityOp.trivial
  | k + 1 => DensityOp.castDim (by ring : d * d ^ k = d ^ (k + 1)) (ρ.tensor (ρ.tensorPowGen k))

/-- n-fold tensor power of a density operator: ρ^⊗n.
    For the i.i.d. error model in BB84, this represents n independent copies
    of the same single-pair state (dimension 4 = 2 qubits). -/
noncomputable def DensityOp.tensorPow (ρ : DensityOp 4) (n : ℕ) : DensityOp (4 ^ n) :=
  ρ.tensorPowGen n

-- ============================================================================
-- Tensor Purity Lemmas
-- ============================================================================

/-- The trivial 1×1 density operator is pure -/
theorem DensityOp.trivial_IsPure : DensityOp.trivial.IsPure := by
  unfold DensityOp.IsPure DensityOp.trivial
  ext i j
  fin_cases i; fin_cases j
  simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
             Matrix.of_apply]
  norm_num

/-- Tensor product of pure density operators is pure -/
theorem DensityOp.tensor_IsPure {n m : ℕ} (ρ : DensityOp n) (σ : DensityOp m)
    (hρ : ρ.IsPure) (hσ : σ.IsPure) : (ρ.tensor σ).IsPure := by
  unfold DensityOp.IsPure at *
  -- (ρ.tensor σ).toOp = ρ.toOp ⊗ σ.toOp by definition
  have h_tensor_toOp : (ρ.tensor σ).toOp = ρ.toOp ⊗ σ.toOp := rfl
  rw [h_tensor_toOp]
  -- (ρ.toOp ⊗ σ.toOp) * (ρ.toOp ⊗ σ.toOp) = (ρ.toOp * ρ.toOp) ⊗ (σ.toOp * σ.toOp)
  rw [Op.tensor_mul]
  -- = ρ.toOp ⊗ σ.toOp using hρ and hσ
  rw [hρ, hσ]

/-- Cast preserves purity (dimension casting doesn't change the underlying operator) -/
theorem DensityOp.castDim_IsPure {n m : ℕ} (h : n = m) (ρ : DensityOp n) (hρ : ρ.IsPure) :
    (DensityOp.castDim h ρ).IsPure := by
  subst h
  exact hρ

/-- Tensor power of a pure state is pure (general dimension) -/
theorem DensityOp.tensorPowGen_IsPure {d : ℕ} [NeZero d] (n : ℕ) [NeZero (d ^ n)]
    (ρ : DensityOp d) (hρ : ρ.IsPure) : (ρ.tensorPowGen n).IsPure := by
  induction n with
  | zero =>
    -- Base case: tensorPowGen 0 = castDim trivial
    simp only [DensityOp.tensorPowGen]
    apply DensityOp.castDim_IsPure
    exact DensityOp.trivial_IsPure
  | succ k ih =>
    -- Inductive case: tensorPowGen (k+1) = castDim (ρ.tensor (ρ.tensorPowGen k))
    simp only [DensityOp.tensorPowGen]
    apply DensityOp.castDim_IsPure
    haveI : NeZero (d ^ k) := ⟨pow_ne_zero k (NeZero.ne d)⟩
    apply DensityOp.tensor_IsPure
    · exact hρ
    · exact ih

/-- Tensor power of a pure state is pure (dimension 4, for BB84) -/
theorem DensityOp.tensorPow_IsPure (n : ℕ) [NeZero (4 ^ n)]
    (ρ : DensityOp 4) (hρ : ρ.IsPure) : (ρ.tensorPow n).IsPure := by
  unfold DensityOp.tensorPow
  haveI : NeZero 4 := ⟨by norm_num⟩
  exact DensityOp.tensorPowGen_IsPure n ρ hρ

end Quantum.Operators
end -- noncomputable section

noncomputable section
namespace Quantum.TensorProducts

open Quantum.Operators
open scoped Matrix BigOperators ComplexConjugate ComplexOrder TensorProduct Kronecker
open Matrix

-- ============================================================================
-- Physics Notation for Multi-Qubit States
-- ============================================================================

/-!
## Multi-Qubit State Notation


Usage: These expand to tensor products via ⊗
-/


-- ============================================================================
-- General Tensor Product Notation (for arbitrary kets/bras)
-- ============================================================================

/-!
## General Tensor Product Notation

Uses ToKet type class and macros for flexible notation that accepts both Kets and Bras
with any number of comma-separated arguments:
- `|x, y⟩`, `|x, y, z⟩`, `|x, y, z, w⟩`, ... converts all to Kets, then tensors
- `⟨x, y|`, `⟨x, y, z|`, ... converts to Kets, tensors, then dags

This allows mixing Kets and Bras: `|ket, bra⟩` will dag the bra to make it a ket.
-/

-- ToKet instance for ℕ - allows natural number literals 0, 1 in qubit notation
instance instToKetNat2 : ToKet ℕ 2 where
  toKet n := stdKet 2 ⟨n % 2, Nat.mod_lt n (by decide)⟩

-- Syntax for tensor ket: |x, y, z, ...⟩
syntax (name := tensorKet) "|" term,+ "⟩" : term

-- Macro expansion for tensor ket
macro_rules
  | `(| $x:term, $xs:term,* ⟩) => do
    let mut result ← `(ToKet.toKet $x)
    for x in xs.getElems do
      result ← `($result ⊗ ToKet.toKet $x)
    return result

-- Syntax for tensor bra: ⟨x, y, z, ...|
syntax (name := tensorBra) "⟨" term,+ "|" : term

-- Macro expansion for tensor bra
set_option quotPrecheck false in
macro_rules
  | `(⟨ $x:term, $xs:term,* |) => do
    let mut result ← `(ToKet.toKet $x)
    for x in xs.getElems do
      result ← `($result ⊗ ToKet.toKet $x)
    `(Ket.dag $result)

-- ============================================================================
-- NormKet Tensor Notation
-- ============================================================================

/-!
## NormKet Tensor Product Notation

- `‖x, y, ...⟩` → tensor product of NormKets via `ToNormKet.toNormKet`

Examples:
- `‖ψ, φ⟩` tensors two NormKet variables
- `‖ψ, 0⟩` tensors ψ with qubit |0⟩ (uses ToNormKet ℕ 2 instance)

Single-state notation (`‖i:n⟩`, `‖0⟩`, `‖1⟩`) is defined in `BraKet/Basic.lean`.
-/

-- ToNormKet instance for Fin 2 - allows ‖ψ, 0⟩ and ‖ψ, 1⟩ notation for qubits
instance instToNormKetFin2 : ToNormKet (Fin 2) 2 where
  toNormKet i := stdNormKet 2 i

-- ToNormKet instance for ℕ - allows natural number literals 0, 1 in qubit notation
instance instToNormKetNat2 : ToNormKet ℕ 2 where
  toNormKet n := stdNormKet 2 ⟨n % 2, Nat.mod_lt n (by decide)⟩

-- Syntax for tensor NormKet: ‖x, y, z, ...⟩
syntax (name := tensorNormKet) "‖" term,+ "⟩" : term

-- Macro expansion for tensor NormKet
macro_rules
  | `(‖ $x:term, $xs:term,* ⟩) => do
    let mut result ← `(ToNormKet.toNormKet $x)
    for x in xs.getElems do
      result ← `($result ⊗ ToNormKet.toNormKet $x)
    return result


end Quantum.TensorProducts

end  -- noncomputable section

namespace Quantum.TensorProducts

open Quantum.Operators

/-- Conjugate transpose distributes over Op.castDim -/
lemma Op.castDim_conjTranspose {n m : ℕ} (h : n = m) (A : Op n) :
    (Op.castDim h A)† = Op.castDim h A† := by
  subst h; rfl

/-- Op.castDim preserves multiplication -/
lemma Op.castDim_mul {n m : ℕ} (h : n = m) (A B : Op n) :
    Op.castDim h A * Op.castDim h B = Op.castDim h (A * B) := by
  subst h; rfl

/-- Op.castDim preserves identity -/
lemma Op.castDim_one {n m : ℕ} (h : n = m) :
    Op.castDim h (1 : Op n) = (1 : Op m) := by
  subst h; rfl

/-- Helper: castDim for operators preserves scalar multiplication -/
lemma Op.castDim_smul {n m : ℕ} (h : n = m) (c : ℂ) (A : Op n) :
    Op.castDim h (c • A) = c • Op.castDim h A := by
  subst h; rfl

end Quantum.TensorProducts

namespace Quantum.Operators

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

/-- Operator casting preserves addition. -/
lemma Op.castDim_add {n m : ℕ} (h : n = m) (A B : Op n) :
    Op.castDim h (A + B) = Op.castDim h A + Op.castDim h B := by
  subst h
  rfl

/-- The linear equivalence induced by casting equal operator dimensions. -/
noncomputable def Op.castDimLinear {n m : ℕ} (h : n = m) :
    Op n →ₗ[ℂ] Op m where
  toFun := Op.castDim h
  map_add' := by
    intro A B
    exact Op.castDim_add h A B
  map_smul' := by
    intro c A
    exact Quantum.TensorProducts.Op.castDim_smul h c A

end Quantum.Operators
