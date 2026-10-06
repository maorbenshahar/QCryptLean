import QCryptLean.Quantum.Tactic.QISimpBasic
import QCryptLean.Quantum.TensorProducts.PartialTrace

/-!
# Quantum Gates — Pauli, Hadamard, phase, CNOT, SWAP, unitarity proofs

Standard single- and two-qubit quantum gates with their actions on basis states
and algebraic properties (unitarity, Hermiticity, anticommutation).

## Main definitions
- `pauliX`, `pauliY`, `pauliZ`: Pauli gates (notations `X`, `Y`, `Z`)
- `hadamard`, `phaseS`, `phaseT`, `gateI`: Single-qubit gates
- `cnot`, `swap`, `cz`: Two-qubit gates

## Main statements
- `pauliX_unitary`, `pauliY_unitary`, `pauliZ_unitary`: Unitarity proofs
- `pauliXZ_anticommute`: Pauli anticommutation relation
- `hadamard_ket0`, `hadamard_ket1`: `H|0⟩ = |+⟩` and `H|1⟩ = |−⟩`
- `hadamard_hermitian`, `hadamard_transpose`, `hadamard_sq`, `hadamard_unitary`: the Hadamard
  gate is a real symmetric unitary involution
- `hadamard_conj_pauliX`, `hadamard_conj_pauliZ`, `hadamard_conj_pauliY`: conjugation by `H`
  exchanges `X` and `Z` and negates `Y`
-/

namespace Quantum.Gates

open Quantum.Operators
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

-- ============================================================================
-- Single-Qubit Gate Definitions
-- ============================================================================

/-- Pauli X gate (NOT gate): |0⟩ ↔ |1⟩ -/
def pauliX : Op 2 := |1⟩ * ⟨0| + |0⟩ * ⟨1|

/-- Pauli Y gate -/
def pauliY : Op 2 := Complex.I • (|1⟩ * ⟨0|) - Complex.I • (|0⟩ * ⟨1|)

/-- Pauli Z gate (phase flip): |0⟩ → |0⟩, |1⟩ → -|1⟩ -/
def pauliZ : Op 2 := |0⟩ * ⟨0| - |1⟩ * ⟨1|

/-- Hadamard gate: Creates superpositions -/
def hadamard : Op 2 :=
  ((1 : ℂ) / (Real.sqrt 2 : ℂ)) • (|0⟩ * ⟨0| + |0⟩ * ⟨1| + |1⟩ * ⟨0| - |1⟩ * ⟨1|)

/-- Phase gate (S gate): |0⟩ → |0⟩, |1⟩ → i|1⟩ -/
def phaseS : Op 2 := |0⟩ * ⟨0| + Complex.I • (|1⟩ * ⟨1|)

/-- T gate (π/8 gate) -/
def phaseT : Op 2 :=
  |0⟩ * ⟨0| + Complex.exp (Complex.I * (Real.pi / 4)) • (|1⟩ * ⟨1|)
/-- Identity gate -/
def gateI : Op 2 := |0⟩ * ⟨0| + |1⟩ * ⟨1|

-- Gate notation
notation "X" => pauliX
notation "Y" => pauliY
notation "Z" => pauliZ
notation "H" => hadamard
notation "S_gate" => phaseS  -- Avoid conflict with ℕ → ℕ successor
notation "T_gate" => phaseT


-- ============================================================================
-- Two-Qubit Gates
-- ============================================================================

/-- CNOT gate (Controlled-NOT): Flips target if control is |1⟩
    |00⟩ → |00⟩, |01⟩ → |01⟩, |10⟩ → |11⟩, |11⟩ → |10⟩ -/
def cnot : Op 4 :=
  |0,0⟩ * ⟨0,0| +  |0,1⟩ * ⟨0,1| +
  |1,1⟩ * ⟨1,0| + |1,0⟩ * ⟨1,1|

/-- SWAP gate: Swaps two qubits
    |00⟩ → |00⟩, |01⟩ → |10⟩, |10⟩ → |01⟩, |11⟩ → |11⟩ -/
def swap : Op 4 :=
  |0,0⟩ * ⟨0,0| + |1,0⟩ * ⟨0,1| +
  |0,1⟩ * ⟨1,0| + |1,1⟩ * ⟨1,1|

/-- Controlled-Z gate: Applies phase if both qubits are |1⟩
    |00⟩ → |00⟩, |01⟩ → |01⟩, |10⟩ → |10⟩, |11⟩ → -|11⟩ -/
def cz : Op 4 :=
  |0,0⟩ * ⟨0,0| + |0,1⟩ * ⟨0,1| +
  |1,0⟩ * ⟨1,0| - |1,1⟩ * ⟨1,1|

-- Notation for two-qubit gates
notation "CNOT" => cnot
notation "SWAP" => swap
notation "CZ" => cz

-- ============================================================================
-- Gate Actions on Basis States
-- ============================================================================

/-- Identity gate maps |0⟩ to |0⟩ -/
@[simp]
theorem gateI_ket0 : gateI * |0⟩ = |0⟩ := by
  unfold gateI
  simp

/-- Identity gate maps |1⟩ to |1⟩ -/
@[simp]
theorem gateI_ket1 : gateI * |1⟩ = |1⟩ := by
  unfold gateI
  simp

/-- Pauli X maps |0⟩ to |1⟩ -/
@[simp]
theorem X_ket0 : X * |0⟩ = |1⟩ := by
  unfold pauliX
  simp

/-- Pauli X maps |1⟩ to |0⟩ -/
@[simp]
theorem X_ket1 : X * |1⟩ = |0⟩ := by
  unfold pauliX
  simp

/-- Pauli Z maps |0⟩ to |0⟩ -/
@[simp]
theorem Z_ket0 : Z * |0⟩ = |0⟩ := by
  unfold pauliZ
  simp

/-- Pauli Z maps |1⟩ to -|1⟩ -/
@[simp]
theorem Z_ket1 : Z * |1⟩ = (-1 : ℂ) • |1⟩ := by
  unfold pauliZ
  simp


/-- Pauli Y maps |0⟩ to i|1⟩ -/
@[simp]
theorem Y_ket0 : Y * |0⟩ = Complex.I • |1⟩ := by
  unfold pauliY
  simp [smul_op_mul_ket]



/-- Pauli Y maps |1⟩ to -i|0⟩ -/
@[simp]
theorem Y_ket1 : Y * |1⟩ = (-Complex.I) • |0⟩ := by
  unfold pauliY
  simp [smul_op_mul_ket]


-- ============================================================================
-- Gate Unitarity (Physics: U†U = UU† = 1)
-- ============================================================================

/-- Pauli X is unitary: X†X = 1 -/
@[simp]
theorem pauliX_unitary : X† * X = (1 : Op 2) := by
  unfold pauliX
  qisimp_basic

/-- Pauli Z is unitary: Z†Z = 1 -/
@[simp]
theorem pauliZ_unitary : Z† * Z = (1 : Op 2) := by
  unfold pauliZ
  qisimp_basic

/-- Pauli Y is unitary: Y†Y = 1 -/
@[simp]
theorem pauliY_unitary : Y† * Y = (1 : Op 2) := by
  unfold pauliY
  qisimp_basic

/-- Pauli X is Hermitian: X† = X -/
@[simp]
theorem pauliX_hermitian : X† = X := by
  unfold pauliX
  qisimp_basic
  abel

/-- Pauli Z is Hermitian: Z† = Z -/
@[simp]
theorem pauliZ_hermitian : Z† = Z := by
  unfold pauliZ
  qisimp_basic

/-- Pauli X squares to identity: X * X = 1 -/
@[simp]
theorem pauliX_sq : X * X = (1 : Op 2) := by
  unfold pauliX
  qisimp_basic

/-- Pauli Z squares to identity: Z * Z = 1 -/
@[simp]
theorem pauliZ_sq : Z * Z = (1 : Op 2) := by
  unfold pauliZ
  qisimp_basic

/-- XZ anticommutation: X * Z = -(Z * X).
    This is the fundamental anticommutation relation of Pauli matrices. -/
@[simp]
theorem pauliXZ_anticommute : X * Z = -(Z * X) := by
  unfold pauliX pauliZ
  qisimp_basic
  abel

/-- ZX anticommutation: Z * X = -(X * Z).
    Equivalent form of the anticommutation relation. -/
theorem pauliZX_anticommute : Z * X = -(X * Z) := by
  unfold pauliX pauliZ
  qisimp_basic
  abel

-- ============================================================================
-- The Hadamard Gate
-- ============================================================================

/-- The Hadamard gate maps `|0⟩` to `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
@[simp]
theorem hadamard_ket0 : hadamard * |0⟩ = (1 / Real.sqrt 2 : ℂ) • (|0⟩ + |1⟩) := by
  unfold hadamard
  simp [smul_op_mul_ket]

/-- The Hadamard gate maps `|1⟩` to `|−⟩ = (|0⟩ − |1⟩)/√2`. -/
@[simp]
theorem hadamard_ket1 : hadamard * |1⟩ = (1 / Real.sqrt 2 : ℂ) • (|0⟩ - |1⟩) := by
  unfold hadamard
  simp [smul_op_mul_ket]

/-- The Hadamard gate is Hermitian: `H† = H`. -/
theorem hadamard_hermitian : hadamard† = hadamard := by
  unfold hadamard
  qisimp_basic
  abel

/-- The Hadamard gate is symmetric: `Hᵀ = H`. It is a real matrix, so this is the same
statement as `hadamard_hermitian`. -/
theorem hadamard_transpose : hadamardᵀ = hadamard := by
  unfold hadamard
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, ket_mul_bra_apply, Ket.dag]

/-- The Hadamard gate is an involution: `H * H = 1`. -/
theorem hadamard_sq : hadamard * hadamard = (1 : Op 2) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_two, ket_mul_bra_apply, Ket.dag] <;>
    field_simp <;> ring_nf <;> simp [h2]

/-- The Hadamard gate is unitary: `H† * H = 1`. -/
theorem hadamard_unitary : hadamard† * hadamard = (1 : Op 2) := by
  rw [hadamard_hermitian, hadamard_sq]

/-- Conjugation by the Hadamard gate turns the bit flip into the phase flip: `H X H = Z`. -/
theorem hadamard_conj_pauliX : hadamard * pauliX * hadamard = pauliZ := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hadamard, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> rw [h2]

/-- Conjugation by the Hadamard gate turns the phase flip into the bit flip: `H Z H = X`. -/
theorem hadamard_conj_pauliZ : hadamard * pauliZ * hadamard = pauliX := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hadamard, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> rw [h2]

/-- Conjugation by the Hadamard gate negates `Y`: `H Y H = −Y`. -/
theorem hadamard_conj_pauliY : hadamard * pauliY * hadamard = -pauliY := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hadamard, pauliY, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;>
    simp [h2]

-- ============================================================================
-- Explicit Matrix Forms
-- ============================================================================

/-! The single-qubit gates as explicit `!![…]` arrays, and the Kronecker product of two explicit
`2×2` matrices. Finite computations rewrite with these once and then evaluate products of explicit
matrices as a whole, instead of unfolding the Dirac-notation definitions entry by entry. -/

/-- The Pauli `X` gate as an explicit matrix. -/
theorem pauliX_eq_matrix : pauliX = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, ket_mul_bra_apply, stdKet_apply]

/-- The Pauli `Y` gate as an explicit matrix. -/
theorem pauliY_eq_matrix : pauliY = !![0, -Complex.I; Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, ket_mul_bra_apply, stdKet_apply]

/-- The Pauli `Z` gate as an explicit matrix. -/
theorem pauliZ_eq_matrix : pauliZ = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, ket_mul_bra_apply, stdKet_apply]

/-- The Hadamard gate as an explicit matrix: `H = (√2)⁻¹ • !![1, 1; 1, -1]`. -/
theorem hadamard_eq_matrix : hadamard = (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1] := by
  rw [hadamard, one_div]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ket_mul_bra_apply, stdKet_apply]

/-- The Kronecker product `Op.tensor` of two explicit `2×2` matrices, as an explicit `4×4`
matrix: the pair `(a, b)` sits at index `2a + b` (the `finProdFinEquiv` convention). Each entry
holds by definitional unfolding of `Op.tensor`. -/
theorem _root_.Quantum.TensorProducts.Op.tensor_fin_two_eq_matrix (a b c d e f g h : ℂ) :
    Quantum.TensorProducts.Op.tensor !![a, b; c, d] !![e, f; g, h] =
      !![a * e, a * f, b * e, b * f;
         a * g, a * h, b * g, b * h;
         c * e, c * f, d * e, d * f;
         c * g, c * h, d * g, d * h] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end -- noncomputable section

end Quantum.Gates
