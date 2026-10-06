import QCryptLean.Quantum.Operators.Types
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Bra-Ket Basics — multiplication instances, adjoints, normalized kets, computational basis

This module defines the `HMul` instances that make `*` the primary notation for
ket/bra outer products, inner products, operator actions, and scalar products.
It also records adjoint, normalization, and computational-basis infrastructure
used by tensor-product and projector modules.

## Main definitions
- `Ket.dag`, `Bra.dag`: adjoints for kets and bras.
- `NormKet`: normalized ket subtype.
- `stdKet`, `stdNormKet`: computational-basis kets.

## Main statements
- `ketbra_mul_ketbra`: product of two rank-one operators.
- `op_mul_ketbra`, `ketbra_mul_op`, `braop_mul_ket`: associativity between
  operator actions and bra-ket products.
- `one_op_mul_ket`: the identity operator acts trivially on a ket.
- `stdKet_braket`: computational-basis inner products.
- `Ket.inner_self_re_nonneg`: nonnegativity of a ket's self-inner product.
- `operator_action_in_bra_ket`: replacing an operator action inside a bra-ket
  matrix element.
-/

namespace Quantum.Operators

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

-- ============================================================================
-- Section 1: HMul Instances (Primary Definitions)
-- ============================================================================

/-- HMul: Ket × Bra → Op (outer product |ψ⟩⟨φ|) -/
instance instHMulKetBra {n : ℕ} : HMul (Ket n) (Bra n) (Op n) where
  hMul ψ φ := Matrix.of fun i j => ψ.vec i * φ.vec j

/-- HMul: Bra × Ket → ℂ (inner product ⟨φ|ψ⟩) -/
instance instHMulBraKet {n : ℕ} : HMul (Bra n) (Ket n) ℂ where
  hMul φ ψ := ∑ i, φ.vec i * ψ.vec i

/-- HMul: Op × Ket → Ket (operator action A|ψ⟩) -/
instance instHMulOpKet {n : ℕ} : HMul (Op n) (Ket n) (Ket n) where
  hMul A ψ := ⟨A.mulVec ψ.vec⟩

/-- HMul: Bra × Op → Bra (bra action ⟨φ|A) -/
instance instHMulBraOp {n : ℕ} : HMul (Bra n) (Op n) (Bra n) where
  hMul φ A := ⟨fun j => ∑ i, φ.vec i * A i j⟩

/-- HMul: UnitaryOp × Ket → Ket (unitary action on kets) -/
instance instHMulUnitaryOpKet {n : ℕ} : HMul (UnitaryOp n) (Ket n) (Ket n) where
  hMul U ψ := ⟨U.toOp.mulVec ψ.vec⟩

-- Note: UnitaryOp × NormKet → NormKet instance is defined after NormKet (Section 10)

-- ============================================================================
-- Section 2: Expansion Lemmas (for proofs that need to unfold *)
-- ============================================================================

/-- Expand ψ * φ (Ket × Bra) -/
@[simp] lemma ket_mul_bra_apply {n : ℕ} (ψ : Ket n) (φ : Bra n) (i j : Fin n) :
    (ψ * φ : Op n) i j = ψ.vec i * φ.vec j := rfl

/-- Expand φ * ψ (Bra × Ket) to sum form.
    Note: NOT @[simp] to allow algebraic simp lemmas (bra_mul_smul_ket, etc.)
    to simplify structure before unfolding to sums. -/
lemma bra_mul_ket_eq {n : ℕ} (φ : Bra n) (ψ : Ket n) :
    (φ * ψ : ℂ) = ∑ i, φ.vec i * ψ.vec i := rfl

/-- Expand A * ψ (Op × Ket) -/
@[simp] lemma op_mul_ket_vec {n : ℕ} (A : Op n) (ψ : Ket n) :
    (A * ψ : Ket n).vec = A.mulVec ψ.vec := rfl

/-- Expand φ * A (Bra × Op) -/
@[simp] lemma bra_mul_op_vec {n : ℕ} (φ : Bra n) (A : Op n) (j : Fin n) :
    (φ * A : Bra n).vec j = ∑ i, φ.vec i * A i j := rfl

-- ============================================================================
-- Section 3: Scalar Multiplication (uses SMul • notation)
-- ============================================================================

-- Note: We use SMul (•) for scalar multiplication to align with Mathlib conventions
-- This makes all standard simplification lemmas work automatically
-- Scalar multiplication remains commutative: c • X for all quantum objects X

-- Component-level SMul is handled by Mathlib's Pi.smul_apply and smul_eq_mul

-- ============================================================================
-- Section 4: Basic Algebraic Properties
-- ============================================================================

-- Note: Scalar commutativity is built into SMul (c • X is the standard form)

/-- The identity operator acts trivially on a ket: `(1 : Op n) * ψ = ψ`. -/
@[simp] theorem one_op_mul_ket {n : ℕ} (ψ : Ket n) : (1 : Op n) * ψ = ψ := by
  ext i
  simp only [op_mul_ket_vec, Matrix.one_mulVec]

-- ============================================================================
-- Section 5: Associativity Laws
-- ============================================================================

/-- Op * (Ket * Bra) = (Op * Ket) * Bra -/
@[simp]
theorem op_mul_ketbra {n : ℕ} (A : Op n) (ψ : Ket n) (φ : Bra n) :
    A * (ψ * φ) = (A * ψ) * φ := by
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, op_mul_ket_vec, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  congr 1
  ext k
  ring

/-- (Ket * Bra) * Op = Ket * (Bra * Op) -/
@[simp]
theorem ketbra_mul_op {n : ℕ} (ψ : Ket n) (φ : Bra n) (A : Op n) :
    (ψ * φ) * A = ψ * (φ * A) := by
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, bra_mul_op_vec]
  rw [Finset.mul_sum]
  congr 1
  ext k
  ring

/-- (Bra * Op) * Ket = Bra * (Op * Ket) -/
@[simp]
theorem braop_mul_ket {n : ℕ} (φ : Bra n) (A : Op n) (ψ : Ket n) :
    (φ * A) * ψ = φ * (A * ψ) := by
  simp only [bra_mul_ket_eq, bra_mul_op_vec, op_mul_ket_vec, Matrix.mulVec, dotProduct]
  conv_lhs =>
    arg 2; ext j
    rw [Finset.sum_mul]
  conv_rhs =>
    arg 2; ext i
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  ring

-- ============================================================================
-- Section 6: Bra-Ketbra Multiplication
-- ============================================================================

/-- Bra * (Ket * Bra) = (Bra * Ket) * Bra
    Fundamental: ⟨φ|(|χ⟩⟨ξ|) = ⟨φ|χ⟩⟨ξ| -/
@[simp]
theorem bra_mul_ketbra {n : ℕ} (φ : Bra n) (χ : Ket n) (ξ : Bra n) :
    φ * (χ * ξ) = (φ * χ) • ξ := by
  ext j
  simp only [bra_mul_op_vec, ket_mul_bra_apply, bra_mul_ket_eq]
  trans (∑ x, (φ.vec x * χ.vec x) * ξ.vec j)
  · congr 1; funext k; ring
  rw [← Finset.sum_mul]
  rfl

-- ============================================================================
-- Section 7: Scalar Distribution
-- ============================================================================

/-- Helper: (c • ψ).vec = c • ψ.vec -/
@[simp]
lemma Ket.smul_vec {n : ℕ} (c : ℂ) (ψ : Ket n) : (c • ψ).vec = c • ψ.vec := rfl

/-- Helper: (c • φ).vec = c • φ.vec for Bra -/
@[simp]
lemma Bra.smul_vec {n : ℕ} (c : ℂ) (φ : Bra n) : (c • φ).vec = c • φ.vec := rfl

/-- (c • A) * ψ = c • (A * ψ) -/
@[simp]
theorem smul_op_mul_ket {n : ℕ} (c : ℂ) (A : Op n) (ψ : Ket n) :
    (c • A) * ψ = c • (A * ψ) := by
  ext i
  simp only [op_mul_ket_vec, Ket.smul_vec, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]

/-- A * (c • ψ) = c • (A * ψ) -/
@[simp]
theorem op_mul_smul_ket {n : ℕ} (A : Op n) (c : ℂ) (ψ : Ket n) :
    A * (c • ψ) = c • (A * ψ) := by
  ext i
  simp only [op_mul_ket_vec, Ket.smul_vec,
             Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext j
  ring

/-- (c • ψ) * φ = c • (ψ * φ) -/
@[simp]
theorem smul_ket_mul_bra {n : ℕ} (c : ℂ) (ψ : Ket n) (φ : Bra n) :
    (c • ψ) * φ = c • (ψ * φ) := by
  ext i j
  simp only [ket_mul_bra_apply, Ket.smul_vec, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- ψ * (c • φ) = c • (ψ * φ) -/
@[simp]
theorem ket_mul_smul_bra {n : ℕ} (ψ : Ket n) (c : ℂ) (φ : Bra n) :
    ψ * (c • φ) = c • (ψ * φ) := by
  ext i j
  simp only [ket_mul_bra_apply, Matrix.smul_apply, Bra.smul_vec, Pi.smul_apply, smul_eq_mul]
  ring

/-- (c • φ) * ψ = c • (φ * ψ) -/
@[simp]
theorem smul_bra_mul_ket {n : ℕ} (c : ℂ) (φ : Bra n) (ψ : Ket n) :
    (c • φ) * ψ = c • (φ * ψ) := by
  simp only [bra_mul_ket_eq, Bra.smul_vec, Pi.smul_apply, smul_eq_mul]
  trans (∑ i, c * (φ.vec i * ψ.vec i))
  · congr 1; ext i; ring
  rw [← Finset.mul_sum]

/-- φ * (c • ψ) = c • (φ * ψ) -/
@[simp]
theorem bra_mul_smul_ket {n : ℕ} (φ : Bra n) (c : ℂ) (ψ : Ket n) :
    φ * (c • ψ) = c • (φ * ψ) := by
  simp only [bra_mul_ket_eq, Ket.smul_vec, Pi.smul_apply, smul_eq_mul]
  trans (∑ i, φ.vec i * (c * ψ.vec i))
  · rfl
  trans (∑ i, c * (φ.vec i * ψ.vec i))
  · congr 1; ext i; ring
  rw [← Finset.mul_sum]

/-- (⟨ψ| + ⟨φ|)|χ⟩ = ⟨ψ|χ⟩ + ⟨φ|χ⟩ (left distributivity) -/
@[simp]
theorem bra_add_mul_ket {n : ℕ} (ψ φ : Bra n) (χ : Ket n) :
    (ψ + φ) * χ = ψ * χ + φ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (ψ + φ).vec i = ψ.vec i + φ.vec i from rfl, add_mul]
  rw [Finset.sum_add_distrib]

/-- ⟨ψ|(|φ⟩ + |χ⟩) = ⟨ψ|φ⟩ + ⟨ψ|χ⟩ (right distributivity) -/
@[simp]
theorem bra_mul_add_ket {n : ℕ} (ψ : Bra n) (φ χ : Ket n) :
    ψ * (φ + χ) = ψ * φ + ψ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (φ + χ).vec i = φ.vec i + χ.vec i from rfl, mul_add]
  rw [Finset.sum_add_distrib]

/-- (⟨ψ| - ⟨φ|)|χ⟩ = ⟨ψ|χ⟩ - ⟨φ|χ⟩ (left distributivity for subtraction) -/
@[simp]
theorem bra_sub_mul_ket {n : ℕ} (ψ φ : Bra n) (χ : Ket n) :
    (ψ - φ) * χ = ψ * χ - φ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (ψ - φ).vec i = ψ.vec i - φ.vec i from rfl, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- ⟨ψ|(|φ⟩ - |χ⟩) = ⟨ψ|φ⟩ - ⟨ψ|χ⟩ (right distributivity for subtraction) -/
@[simp]
theorem bra_mul_sub_ket {n : ℕ} (ψ : Bra n) (φ χ : Ket n) :
    ψ * (φ - χ) = ψ * φ - ψ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (φ - χ).vec i = φ.vec i - χ.vec i from rfl, mul_sub]
  rw [Finset.sum_sub_distrib]

-- ============================================================================
-- Section 8: Scalar-Scalar Multiplication
-- ============================================================================

-- Note: (c₁ * c₂) • A = c₁ • (c₂ • A) follows from smul_smul in Mathlib

-- ============================================================================
-- Section 9: Ketbra-Ketbra Multiplication (Derived)
-- ============================================================================

/-- Physics: (|ψ⟩⟨φ|)(|χ⟩⟨ξ|) = ⟨φ|χ⟩ • |ψ⟩⟨ξ|

    Direct proof by matrix calculation.
-/
@[simp]
theorem ketbra_mul_ketbra {n : ℕ} (ψ χ : Ket n) (φ ξ : Bra n) :
    (ψ * φ) * (χ * ξ) = (φ * χ) • (ψ * ξ) := by
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, bra_mul_ket_eq, Matrix.smul_apply, smul_eq_mul]
  trans (∑ x, (φ.vec x * χ.vec x) * (ψ.vec i * ξ.vec j))
  · congr 1; funext x; ring
  · rw [← Finset.sum_mul]

/-- Zero ket times any bra is zero matrix -/
@[simp]
lemma zero_ket_mul_bra {n : ℕ} (φ : Bra n) : (0 : Ket n) * φ = 0 := by
  ext i j; simp [ket_mul_bra_apply]

/-- Zero bra component -/
@[simp]
lemma Bra.zero_vec {n : ℕ} (j : Fin n) : (0 : Bra n).vec j = 0 := rfl

/-- Any ket times zero bra is zero matrix -/
@[simp]
lemma ket_mul_zero_bra {n : ℕ} (ψ : Ket n) : ψ * (0 : Bra n) = 0 := by
  ext i j; simp [ket_mul_bra_apply]

/-- Ket addition at component level -/
@[simp]
lemma Ket.add_vec {n : ℕ} (ψ φ : Ket n) (i : Fin n) : (ψ + φ).vec i = ψ.vec i + φ.vec i := rfl

/-- Bra addition at component level -/
@[simp]
lemma Bra.add_vec {n : ℕ} (ψ φ : Bra n) (i : Fin n) : (ψ + φ).vec i = ψ.vec i + φ.vec i := rfl

/-- Bra subtraction at component level -/
@[simp]
lemma Bra.sub_vec {n : ℕ} (ψ φ : Bra n) (i : Fin n) : (ψ - φ).vec i = ψ.vec i - φ.vec i := rfl

/-- Bra negation at component level -/
@[simp]
lemma Bra.neg_vec {n : ℕ} (φ : Bra n) (i : Fin n) : (-φ).vec i = -φ.vec i := rfl

/-- Ket subtraction at component level -/
@[simp]
lemma Ket.sub_vec {n : ℕ} (ψ φ : Ket n) (i : Fin n) : (ψ - φ).vec i = ψ.vec i - φ.vec i := rfl

/-- Ket negation at component level -/
@[simp]
lemma Ket.neg_vec {n : ℕ} (ψ : Ket n) (i : Fin n) : (-ψ).vec i = -ψ.vec i := rfl

/-- Ket minus zero: |ψ⟩ - 0 = |ψ⟩ -/
@[simp]
lemma Ket.sub_zero {n : ℕ} (ψ : Ket n) : ψ - 0 = ψ := by
  ext i; simp [Ket.sub_vec]

/-- Zero minus ket: 0 - |ψ⟩ = -|ψ⟩ -/
@[simp]
lemma Ket.zero_sub {n : ℕ} (ψ : Ket n) : 0 - ψ = -ψ := by
  ext i; simp [Ket.sub_vec, Ket.neg_vec]

/-- Negation as scalar: -|ψ⟩ = (-1) • |ψ⟩ -/
@[simp]
lemma Ket.neg_eq_smul {n : ℕ} (ψ : Ket n) : -ψ = (-1 : ℂ) • ψ := by
  ext i; simp [Ket.neg_vec]

/-- Subtraction as addition with negation: |ψ⟩ - |φ⟩ = |ψ⟩ + (-1) • |φ⟩ -/
@[simp]
lemma Ket.sub_eq_add_neg_smul {n : ℕ} (ψ φ : Ket n) : ψ - φ = ψ + (-1 : ℂ) • φ := by
  ext i
  simp only [Ket.sub_vec, Ket.add_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul, neg_one_mul]
  ring

/-- Physics: |ψ⟩⟨φ| acting on |χ⟩ gives ⟨φ|χ⟩·|ψ⟩ -/
@[simp]
theorem ketbra_mul_ket {n : ℕ} (ψ χ : Ket n) (φ : Bra n) :
    (ψ * φ) * χ = (φ * χ) • ψ := by
  ext i
  simp only [op_mul_ket_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul,
             bra_mul_ket_eq, ket_mul_bra_apply, Matrix.mulVec, dotProduct]
  trans (ψ.vec i * ∑ x, φ.vec x * χ.vec x)
  · rw [Finset.mul_sum]; congr 1; funext x; ring
  · ring

/-- Physics: Addition of operators distributes over ket multiplication -/
@[simp]
theorem add_op_mul_ket {n : ℕ} (A B : Op n) (ψ : Ket n) :
    (A + B) * ψ = A * ψ + B * ψ := by
  ext i
  simp only [op_mul_ket_vec, Ket.add_vec, Matrix.add_apply, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]; congr 1; funext j; ring

/-- Physics: Subtraction of operators distributes over ket multiplication -/
@[simp]
theorem sub_op_mul_ket {n : ℕ} (A B : Op n) (ψ : Ket n) :
    (A - B) * ψ = A * ψ - B * ψ := by
  ext i
  simp only [op_mul_ket_vec, Ket.sub_vec, Matrix.sub_apply, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]; congr 1; funext j; ring

/-- Physics: A(|ψ⟩ + |φ⟩) = A|ψ⟩ + A|φ⟩ (right linearity of operator action) -/
@[simp]
theorem Op_mul_add_ket {n : ℕ} (A : Op n) (ψ φ : Ket n) :
    A * (ψ + φ) = A * ψ + A * φ := by
  ext i
  simp only [op_mul_ket_vec, Ket.add_vec, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]; congr 1; funext j; ring

/-- Expand U * ψ (UnitaryOp × Ket) -/
@[simp] lemma UnitaryOp_mul_ket_vec {n : ℕ} (U : UnitaryOp n) (ψ : Ket n) :
    (U * ψ : Ket n).vec = U.toOp.mulVec ψ.vec := rfl

/-- Physics: U(|ψ⟩ + |φ⟩) = U|ψ⟩ + U|φ⟩ (linearity of unitary action on kets) -/
@[simp]
theorem UnitaryOp_mul_add_ket {n : ℕ} (U : UnitaryOp n) (ψ φ : Ket n) :
    U * (ψ + φ) = U * ψ + U * φ := by
  ext i
  simp only [UnitaryOp_mul_ket_vec, Ket.add_vec, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]; congr 1; funext j; ring

/-- Physics: U(c|ψ⟩) = c(U|ψ⟩) (scalar compatibility of unitary action) -/
@[simp]
theorem UnitaryOp_mul_smul_ket {n : ℕ} (U : UnitaryOp n) (c : ℂ) (ψ : Ket n) :
    U * (c • ψ) = c • (U * ψ) := by
  ext i
  simp only [UnitaryOp_mul_ket_vec, Ket.smul_vec, Matrix.mulVec, dotProduct,
             Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]; congr 1; funext j; ring

-- ============================================================================
-- Section 10: Dagger Operations
-- ============================================================================

/-- Dagger: |ψ⟩ ↦ ⟨ψ| -/
def Ket.dag {n : ℕ} (ψ : Ket n) : Bra n :=
  ⟨fun i => conj (ψ.vec i)⟩

/-- Dagger: ⟨ψ| ↦ |ψ⟩ -/
def Bra.dag {n : ℕ} (φ : Bra n) : Ket n :=
  ⟨fun i => conj (φ.vec i)⟩

/-- Physics: ⟨ψ|† = |ψ⟩ (dagger involution for bras) -/
@[simp]
theorem Bra.dag_dag {n : ℕ} (φ : Bra n) : φ.dag.dag = φ := by
  ext i
  simp only [Ket.dag, Bra.dag]
  exact star_star (φ.vec i)

/-- Physics: |ψ⟩† = ⟨ψ| (dagger involution for kets) -/
@[simp]
theorem Ket.dag_dag {n : ℕ} (ψ : Ket n) : ψ.dag.dag = ψ := by
  ext i
  simp only [Ket.dag, Bra.dag]
  exact star_star (ψ.vec i)

/-- Expand ψ.dag.vec -/
@[simp] lemma Ket.dag_vec {n : ℕ} (ψ : Ket n) (i : Fin n) :
    ψ.dag.vec i = conj (ψ.vec i) := rfl

/-- Expand φ.dag.vec -/
@[simp] lemma Bra.dag_vec {n : ℕ} (φ : Bra n) (i : Fin n) :
    φ.dag.vec i = conj (φ.vec i) := rfl

/-- Inner product of two ket sums expands as the double sum of the component inner products:
`⟨∑ᵢ fᵢ | ∑ⱼ gⱼ⟩ = ∑ᵢ ∑ⱼ ⟨fᵢ|gⱼ⟩`. -/
lemma sum_ket_dag_mul_sum_ket {D : ℕ} {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → Ket D) (g : κ → Ket D) :
    ((⟨∑ i ∈ s, (f i).vec⟩ : Ket D).dag * (⟨∑ j ∈ t, (g j).vec⟩ : Ket D) : ℂ)
      = ∑ i ∈ s, ∑ j ∈ t, ((f i).dag * (g j) : ℂ) := by
  simp only [bra_mul_ket_eq, Ket.dag_vec, Finset.sum_apply, map_sum]
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_mul_sum s t
    (fun i => (starRingEnd ℂ) ((f i).vec k)) (fun j => (g j).vec k))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

/-- Physics: (c|ψ⟩)† = c*⟨ψ| (conjugate-linearity of dagger) -/
@[simp]
theorem Ket.dag_smul {n : ℕ} (c : ℂ) (ψ : Ket n) : (c • ψ).dag = star c • ψ.dag := by
  ext i
  simp only [Ket.dag, Ket.smul_vec, Pi.smul_apply, Bra.smul_vec, starRingEnd_apply,
             smul_eq_mul, star_mul']

/-- Physics: (|ψ⟩ + |φ⟩)† = ⟨ψ| + ⟨φ| (linearity of dagger for addition) -/
@[simp]
theorem Ket.dag_add {n : ℕ} (ψ φ : Ket n) : (ψ + φ).dag = ψ.dag + φ.dag := by
  ext i
  simp only [Ket.dag, Ket.add_vec, map_add, Bra.add_vec]

/-- Physics: (|ψ⟩ - |φ⟩)† = ⟨ψ| - ⟨φ| (linearity of dagger for subtraction) -/
@[simp]
theorem Ket.dag_sub {n : ℕ} (ψ φ : Ket n) : (ψ - φ).dag = ψ.dag - φ.dag := by
  ext i
  simp only [Ket.dag_vec, Ket.sub_vec, Bra.sub_vec, map_sub]

/-- Convert dag of subtraction to addition with negation: (|ψ⟩ - |φ⟩)† = ⟨ψ| + (-1) • ⟨φ| -/
@[simp]
theorem Ket.dag_sub_eq_add_neg_smul {n : ℕ} (ψ φ : Ket n) :
    (ψ - φ).dag = ψ.dag + (-1 : ℂ) • φ.dag := by
  ext i
  simp only [Ket.dag_vec, Ket.sub_vec, Bra.add_vec, Bra.smul_vec, Pi.smul_apply, smul_eq_mul,
             neg_one_mul, map_sub]
  ring

-- ============================================================================
-- Section 11: Inner Product and Normalization
-- ============================================================================

/-- Inner product of two kets ⟨φ|ψ⟩ (via HMul: φ.dag * ψ) -/
def Ket.inner {n : ℕ} (φ ψ : Ket n) : ℂ := φ.dag * ψ

/-- Physics: ⟨φ|ψ⟩ = conj(⟨ψ|φ⟩) (conjugate symmetry of inner product) -/
theorem Ket.inner_conj {n : ℕ} (φ ψ : Ket n) : Ket.inner φ ψ = star (Ket.inner ψ φ) := by
  unfold Ket.inner
  simp only [bra_mul_ket_eq, Ket.dag_vec]
  rw [star_sum]
  congr 1; ext i
  simp only [starRingEnd_apply, star_mul', star_star]
  ring

/-- The real part of the inner product of a ket with itself is nonnegative. -/
theorem Ket.inner_self_re_nonneg {n : ℕ} (ψ : Ket n) :
    0 ≤ (ψ.dag * ψ).re := by
  rw [bra_mul_ket_eq, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [Ket.dag_vec, starRingEnd_apply]
  simpa [Complex.normSq_apply, Complex.mul_re] using Complex.normSq_nonneg (ψ.vec i)

/-- Predicate: a ket is normalized, i.e., ⟨ψ|ψ⟩ = 1 -/
def Ket.IsNormalized {n : ℕ} (ψ : Ket n) : Prop := ψ.dag * ψ = 1

/-- Real-valued inner product: Re⟨φ|ψ⟩ (utility function) -/
def Ket.realInner {n : ℕ} (φ ψ : Ket n) : ℝ := (Ket.inner φ ψ).re

/-- Squared norm of a ket (utility function) -/
def Ket.normSq {n : ℕ} (ψ : Ket n) : ℝ := Ket.realInner ψ ψ

/-- A normalized ket (pure quantum state) -/
structure NormKet (n : ℕ) extends Ket n where
  normalized : toKet.IsNormalized

instance {n : ℕ} : Coe (NormKet n) (Ket n) where
  coe := NormKet.toKet

/-- HMul: UnitaryOp × NormKet → NormKet (unitary action preserves normalization)
    Physics: Unitary operators preserve the norm of quantum states: ‖U|ψ⟩‖ = ‖|ψ⟩‖ -/
instance instHMulUnitaryOpNormKet {n : ℕ} : HMul (UnitaryOp n) (NormKet n) (NormKet n) where
  hMul U ψ := ⟨⟨U.toOp.mulVec ψ.vec⟩, by
    unfold Ket.IsNormalized
    simp only [bra_mul_ket_eq, Ket.dag, starRingEnd_apply]
    rw [show (∑ i, star ((U.toOp *ᵥ ψ.vec) i) * (U.toOp *ᵥ ψ.vec) i) =
             dotProduct (star (U.toOp *ᵥ ψ.vec)) (U.toOp *ᵥ ψ.vec) by
      unfold dotProduct; rfl]
    rw [U.preserves_inner]
    rw [show dotProduct (star ψ.vec) ψ.vec =
             ∑ i, star (ψ.vec i) * ψ.vec i by
      unfold dotProduct; rfl]
    exact ψ.normalized⟩

/-- Connection: (U * ψ).toKet = U * ψ.toKet for UnitaryOp acting on NormKet -/
@[simp]
theorem UnitaryOp_mul_NormKet_toKet {n : ℕ} (U : UnitaryOp n) (ψ : NormKet n) :
    (U * ψ).toKet = U * ψ.toKet := rfl

-- ============================================================================
-- Section 12: Standard Basis Kets
-- ============================================================================

/-- Standard basis ket |i⟩ in n-dimensional space -/
def stdKet (n : ℕ) (i : Fin n) : Ket n :=
  ⟨fun j => if i = j then 1 else 0⟩

/-- Standard basis ket component -/
@[simp] theorem stdKet_apply {n : ℕ} (i j : Fin n) :
    (stdKet n i).vec j = if i = j then 1 else 0 := rfl

/-- Standard basis inner product: ⟨i|j⟩ = δᵢⱼ -/
@[simp] theorem stdKet_braket (n : ℕ) (i j : Fin n) :
    (stdKet n i).dag * (stdKet n j) = if i = j then 1 else 0 := by
  simp only [bra_mul_ket_eq, Ket.dag_vec, stdKet_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd (Finset.mem_univ i) h
  · simp only [h, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hi : i = k
    · subst hi; simp [Ne.symm h]
    · simp [hi]

-- ============================================================================
-- Specialized braket lemmas (direct evaluation without `if`)
-- ============================================================================

/-- ⟨i|i⟩ = 1 for any basis state -/
@[simp] theorem stdKet_braket_self {n : ℕ} (i : Fin n) :
    (stdKet n i).dag * (stdKet n i) = 1 := by simp only [stdKet_braket, ↓reduceIte]

/-- ⟨0|0⟩ = 1 using Fin coercion -/
@[simp] theorem stdKet_braket_0_0 {n : ℕ} [NeZero n] :
    (stdKet n (0 : Fin n)).dag * (stdKet n (0 : Fin n)) = 1 := stdKet_braket_self 0

/-- ⟨1|1⟩ = 1 using Fin coercion -/
@[simp] theorem stdKet_braket_1_1 {n : ℕ} [Fact (1 < n)] :
    (stdKet n (1 : Fin n)).dag * (stdKet n (1 : Fin n)) = 1 := stdKet_braket_self 1

/-- ⟨0|1⟩ = 0 using Fin coercion -/
@[simp] theorem stdKet_braket_0_1 {n : ℕ} [Fact (1 < n)] :
    (stdKet n (0 : Fin n)).dag * (stdKet n (1 : Fin n)) = 0 := by
  simp only [stdKet_braket]
  have h : (0 : Fin n) ≠ 1 := Fin.ne_of_val_ne (by simp; have := Fact.out (p := 1 < n); omega)
  simp [h]

/-- ⟨1|0⟩ = 0 using Fin coercion -/
@[simp] theorem stdKet_braket_1_0 {n : ℕ} [Fact (1 < n)] :
    (stdKet n (1 : Fin n)).dag * (stdKet n (0 : Fin n)) = 0 := by
  simp only [stdKet_braket]
  have h : (1 : Fin n) ≠ 0 := Fin.ne_of_val_ne (by simp; have := Fact.out (p := 1 < n); omega)
  simp [h]

/-- ⟨i|j⟩ = 0 when i ≠ j -/
theorem stdKet_braket_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (stdKet n i).dag * (stdKet n j) = 0 := by simp only [stdKet_braket, h, ↓reduceIte]

/-- Standard basis kets are normalized: ⟨i|i⟩ = 1 -/
@[simp] theorem stdKet_IsNormalized {n : ℕ} (i : Fin n) :
    (stdKet n i).IsNormalized := stdKet_braket_self i

/-- Standard basis kets have norm squared 1 (utility lemma) -/
@[simp] theorem stdKet_normSq {n : ℕ} (i : Fin n) :
    (stdKet n i).normSq = 1 := by
  unfold Ket.normSq Ket.realInner Ket.inner
  simp only [stdKet_braket_self, Complex.one_re]

/-- Standard normalized ket: |i⟩ as a NormKet -/
def stdNormKet (n : ℕ) (i : Fin n) : NormKet n :=
  ⟨stdKet n i, stdKet_IsNormalized i⟩

/-- Connection: stdNormKet as Ket equals stdKet -/
@[simp]
theorem stdNormKet_toKet (n : ℕ) (i : Fin n) :
    (stdNormKet n i).toKet = stdKet n i := rfl

-- ============================================================================
-- Section 13: Type Classes for Flexible Bra-Ket Notation
-- ============================================================================

/-- Type class for things that can be converted to a Bra.
    - Ket n → Bra n via .dag
    - Bra n → Bra n via identity -/
class ToBra (α : Type*) (n : outParam ℕ) where
  toBra : α → Bra n

/-- Type class for things that can be converted to a Ket.
    - Ket n → Ket n via identity
    - Bra n → Ket n via .dag -/
class ToKet (α : Type*) (n : outParam ℕ) where
  toKet : α → Ket n

-- Instances for Ket
instance instToKetKet {n : ℕ} : ToKet (Ket n) n where
  toKet := id

instance instToBraKet {n : ℕ} : ToBra (Ket n) n where
  toBra := Ket.dag

-- Instances for Bra
instance instToBraBra {n : ℕ} : ToBra (Bra n) n where
  toBra := id

instance instToKetBra {n : ℕ} : ToKet (Bra n) n where
  toKet := Bra.dag

-- Simp lemmas to reduce type class applications
@[simp] theorem ToKet.toKet_ket {n : ℕ} (ψ : Ket n) : ToKet.toKet ψ = ψ := rfl
@[simp] theorem ToBra.toBra_bra {n : ℕ} (β : Bra n) : ToBra.toBra β = β := rfl
@[simp] theorem ToKet.toKet_bra {n : ℕ} (β : Bra n) : ToKet.toKet β = β.dag := rfl
@[simp] theorem ToBra.toBra_ket {n : ℕ} (ψ : Ket n) : ToBra.toBra ψ = ψ.dag := rfl

/-- Type class for things that can be converted to a NormKet.
    Used by the ‖x, y, ...⟩ tensor product notation. -/
class ToNormKet (α : Type*) (n : outParam ℕ) where
  toNormKet : α → NormKet n

-- Instance for NormKet (identity)
instance instToNormKetNormKet {n : ℕ} : ToNormKet (NormKet n) n where
  toNormKet := id

@[simp]
theorem ToNormKet.toNormKet_normket {n : ℕ} (ψ : NormKet n) : ToNormKet.toNormKet ψ = ψ := rfl

-- ============================================================================
-- Section 14: Standard Basis Notation
-- ============================================================================

-- Qubit notation (specific, higher priority)
notation "|0⟩" => stdKet 2 0
notation "|1⟩" => stdKet 2 1

set_option quotPrecheck false in
notation "⟨0|" => Ket.dag (stdKet 2 0)

set_option quotPrecheck false in
notation "⟨1|" => Ket.dag (stdKet 2 1)

-- General notation: |i:n⟩ creates stdKet n i
notation "|" i ":" n "⟩" => stdKet n i

-- General bra notation: ⟨x| converts x to Bra (dags Kets, keeps Bras)
set_option quotPrecheck false in
notation "⟨" x "|" => ToBra.toBra x

-- General ket notation: |x⟩ converts x to Ket (keeps Kets, dags Bras)
notation "|" x "⟩" => ToKet.toKet x

-- NormKet notation: ‖i:n⟩ creates stdNormKet n i
notation "‖" i ":" n "⟩" => stdNormKet n i

-- Qubit shorthand for NormKets (dimension 2)
notation "‖0⟩" => stdNormKet 2 0
notation "‖1⟩" => stdNormKet 2 1

-- ============================================================================
-- Section 15: Operator Dagger Lemmas
-- ============================================================================

/-- Dagger distributes over operator addition -/
@[simp]
theorem Op.dag_add {n : ℕ} (A B : Op n) : (A + B)† = A† + B† :=
  Matrix.conjTranspose_add A B

/-- Dagger distributes over operator subtraction -/
@[simp]
theorem Op.dag_sub {n : ℕ} (A B : Op n) : (A - B)† = A† - B† :=
  Matrix.conjTranspose_sub A B

/-- Dagger of scalar times operator -/
@[simp]
theorem Op.dag_smul {n : ℕ} (c : ℂ) (A : Op n) : (c • A)† = star c • A† :=
  Matrix.conjTranspose_smul c A

-- ============================================================================
-- Section 16: Inner Product and Hermitian Operator Properties
-- ============================================================================

/-- Inner product of two vectors: ⟨v|w⟩ = Σᵢ v̄ᵢ wᵢ -/
def innerProduct {n : ℕ} (v w : Fin n → ℂ) : ℂ :=
  ∑ i, star (v i) * w i

/-- A Hermitian operator may be moved from a ket to the corresponding bra. -/
lemma Ket.dag_op_mul_of_isHermitian {n : ℕ} (M : Op n) (hM : M.IsHermitian)
    (ψ : Ket n) :
    (M * ψ).dag = ψ.dag * M := by
  ext j
  simp only [Ket.dag_vec, bra_mul_op_vec, op_mul_ket_vec, Matrix.mulVec, dotProduct,
    map_sum, map_mul]
  congr 1
  ext i
  change star (M j i) * star (ψ.vec i) = star (ψ.vec i) * M i j
  rw [hM.apply i j, mul_comm]

/-- Hermitian operator inner product symmetry: `⟨ψ|M|φ⟩ = ⟨Mψ|φ⟩`. -/
theorem hermitian_inner_product_left {n : ℕ} (M : Op n) (hM : M.IsHermitian)
    (ψ φ : Ket n) :
    ψ.dag * M * φ = innerProduct (M.mulVec ψ.vec) φ.vec := by
  rw [← Ket.dag_op_mul_of_isHermitian M hM ψ]
  unfold innerProduct
  simp only [bra_mul_ket_eq, Ket.dag_vec, op_mul_ket_vec, starRingEnd_apply]

/-- If `M|φ⟩ = |ψ_result⟩`, then all bra matrix elements against them agree. -/
theorem operator_action_in_bra_ket {n : ℕ} (M : Op n) (χ φ ψ_result : Ket n)
    (h_apply : M.mulVec φ.vec = ψ_result.vec) :
    χ.dag * M * φ = χ.dag * ψ_result := by
  rw [braop_mul_ket]
  congr
  ext i
  exact congrFun h_apply i

end  -- noncomputable section

end Quantum.Operators
