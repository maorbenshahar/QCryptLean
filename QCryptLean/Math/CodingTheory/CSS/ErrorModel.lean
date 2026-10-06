import QCryptLean.Math.CodingTheory.LinearCodes
import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.Gates
import QCryptLean.Quantum.TensorProducts.Basic

/-!
# CSS Pauli error model

Pauli errors on n qubits (`PauliError`) and their unitary operator representation,
the ground layer the CSS code structure and correction theorems build on.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Gates Math.CodingTheory

noncomputable section

namespace Math.CodingTheory.CSS


/-!
# Pauli Error Model — error patterns, weights, operator construction, unitarity

Pauli errors on n qubits specified by X and Z bit-pattern vectors. Each qubit
independently receives an X error (bit flip), Z error (phase flip), both, or neither.

## Main definitions
- `PauliError`: Pauli error specified by X and Z bit vectors
- `PauliError.xWeight`, `PauliError.zWeight`: Hamming weight of error patterns
- `PauliError.toOp`: error operator as a unitary on (ℂ²)^⊗n
- `singleQubitPauli`: single-qubit Pauli from X/Z bits

## Main statements
- `PauliError.toOp_unitary`: Pauli error operators are unitary
-/

/-- Specification of a Pauli error on n qubits.
    xPattern i = 1 means qubit i has an X error.
    zPattern i = 1 means qubit i has a Z error. -/
structure PauliError (n : ℕ) where
  xPattern : Fin n → ZMod 2
  zPattern : Fin n → ZMod 2

/-- Number of X (bit flip) errors -/
def PauliError.xWeight {n : ℕ} (e : PauliError n) : ℕ :=
  hammingWeight e.xPattern

/-- Number of Z (phase flip) errors -/
def PauliError.zWeight {n : ℕ} (e : PauliError n) : ℕ :=
  hammingWeight e.zPattern

/-- The identity (no error) -/
def PauliError.identity (n : ℕ) : PauliError n :=
  ⟨fun _ => 0, fun _ => 0⟩

/-- Identity error has zero weight -/
theorem PauliError.identity_xWeight (n : ℕ) : (PauliError.identity n).xWeight = 0 := by
  simp [identity, xWeight, hammingWeight]

theorem PauliError.identity_zWeight (n : ℕ) : (PauliError.identity n).zWeight = 0 := by
  simp [identity, zWeight, hammingWeight]

/-- Single-qubit Pauli operator X^a Z^b where a, b ∈ {0, 1}.
    - (0, 0) → I
    - (1, 0) → X
    - (0, 1) → Z
    - (1, 1) → XZ

    Using direct pattern matching on ZMod 2 for definitional reduction after fin_cases. -/
def singleQubitPauli (a b : ZMod 2) : Op 2 :=
  match a, b with
  | 0, 0 => 1
  | 0, 1 => Z
  | 1, 0 => X
  | 1, 1 => X * Z

/-- XZ is unitary: (XZ)† (XZ) = I -/
private lemma XZ_unitary : (X * Z)† * (X * Z) = (1 : Op 2) := by
  -- (XZ)† = Z† X† = ZX (since X, Z are Hermitian)
  -- ZX * XZ = Z(XX)Z = ZZ = I (since X² = Z² = I)
  calc (X * Z)† * (X * Z)
      = Z† * X† * (X * Z) := by rw [Matrix.conjTranspose_mul]
    _ = Z * X * (X * Z) := by rw [pauliX_hermitian, pauliZ_hermitian]
    _ = Z * (X * X * Z) := by rw [mul_assoc, mul_assoc]
    _ = Z * (1 * Z) := by rw [pauliX_sq]
    _ = Z * Z := by rw [one_mul]
    _ = 1 := pauliZ_sq

/-- Single-qubit Pauli operators are unitary -/
lemma singleQubitPauli_unitary (a b : ZMod 2) :
    (singleQubitPauli a b)† * (singleQubitPauli a b) = (1 : Op 2) := by
  unfold singleQubitPauli
  -- Case split on a and b (each is 0 or 1 in ZMod 2)
  fin_cases a <;> fin_cases b
  · -- a = 0, b = 0: Identity
    simp
  · -- a = 0, b = 1: Z
    exact pauliZ_unitary
  · -- a = 1, b = 0: X
    exact pauliX_unitary
  · -- a = 1, b = 1: XZ
    exact XZ_unitary

-- Concrete values for singleQubitPauli
@[simp] lemma singleQubitPauli_00 : singleQubitPauli 0 0 = (1 : Op 2) := by
  unfold singleQubitPauli
  rfl

@[simp] lemma singleQubitPauli_01 : singleQubitPauli 0 1 = Z := by
  unfold singleQubitPauli
  rfl

@[simp] lemma singleQubitPauli_10 : singleQubitPauli 1 0 = X := by
  unfold singleQubitPauli
  rfl

@[simp] lemma singleQubitPauli_11 : singleQubitPauli 1 1 = X * Z := by
  unfold singleQubitPauli
  rfl

/-- Multiplication of single-qubit Pauli operators.
    (X^a Z^b)(X^c Z^d) = (-1)^{bc} X^{a+c} Z^{b+d}
    where the phase comes from moving Z past X: ZX = -XZ

    This is a fundamental algebraic identity in Pauli theory.
    The proof requires:
    1. 16-case analysis on ZMod 2 variables (a, b, c, d ∈ {0, 1})
    2. For each case, reducing the ite conditions (ZMod 2 arithmetic)
    3. Then using Pauli algebra lemmas (pauliX_sq, pauliZ_sq, pauliZX_anticommute)

    Key identities by case (a,b,c,d):
    - (0,0,_,_): I * _ = _, trivial
    - (0,1,0,1): Z * Z = I
    - (0,1,1,0): Z * X = -XZ (anticommutation)
    - (0,1,1,1): Z * XZ = -X
    - (1,0,1,0): X * X = I
    - (1,0,1,1): X * XZ = Z
    - (1,1,0,1): XZ * Z = X
    - (1,1,1,0): XZ * X = -Z (anticommutation)
    - (1,1,1,1): XZ * XZ = -I -/
-- The proof uses pattern matching directly to ensure ZMod 2 values reduce
lemma singleQubitPauli_mul (a b c d : ZMod 2) :
    singleQubitPauli a b * singleQubitPauli c d =
    (if b * c = 1 then -1 else 1 : ℂ) • singleQubitPauli (a + c) (b + d) := by
  match a, b, c, d with
  -- I * I = I
  | 0, 0, 0, 0 => simp only [singleQubitPauli, mul_one, one_smul,
      show (0 : ZMod 2) * 0 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (0 : ZMod 2) + 0 = 0 by decide]
  -- I * Z = Z
  | 0, 0, 0, 1 => simp only [singleQubitPauli, one_mul, one_smul,
      show (0 : ZMod 2) * 0 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (0 : ZMod 2) + 0 = 0 by decide, show (0 : ZMod 2) + 1 = 1 by decide]
  -- I * X = X
  | 0, 0, 1, 0 => simp only [singleQubitPauli, one_mul, one_smul,
      show (0 : ZMod 2) * 1 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (0 : ZMod 2) + 1 = 1 by decide, show (0 : ZMod 2) + 0 = 0 by decide]
  -- I * XZ = XZ
  | 0, 0, 1, 1 => simp only [singleQubitPauli, one_mul, one_smul,
      show (0 : ZMod 2) * 1 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (0 : ZMod 2) + 1 = 1 by decide]
  -- Z * I = Z
  | 0, 1, 0, 0 => simp only [singleQubitPauli, mul_one, one_smul,
      show (1 : ZMod 2) * 0 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (0 : ZMod 2) + 0 = 0 by decide, show (1 : ZMod 2) + 0 = 1 by decide]
  -- Z * Z = I (using Z² = I)
  | 0, 1, 0, 1 => simp only [singleQubitPauli, pauliZ_sq, one_smul,
      show (1 : ZMod 2) * 0 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (0 : ZMod 2) + 0 = 0 by decide, show (1 : ZMod 2) + 1 = 0 by decide]
  -- Z * X = -XZ (anticommutation)
  | 0, 1, 1, 0 => simp only [singleQubitPauli, pauliZX_anticommute, neg_one_smul,
      show (1 : ZMod 2) * 1 = 1 by decide, ite_true,
      show (0 : ZMod 2) + 1 = 1 by decide, show (1 : ZMod 2) + 0 = 1 by decide]
  -- Z * XZ = -X
  | 0, 1, 1, 1 =>
      simp only [singleQubitPauli, neg_one_smul,
        show (1 : ZMod 2) * 1 = 1 by decide, ite_true,
        show (0 : ZMod 2) + 1 = 1 by decide,
        show (1 : ZMod 2) + 1 = 0 by decide]
      calc Z * (X * Z) = (Z * X) * Z := by rw [mul_assoc]
        _ = (-(X * Z)) * Z := by rw [pauliZX_anticommute]
        _ = -(X * Z * Z) := by rw [neg_mul]
        _ = -(X * (Z * Z)) := by rw [mul_assoc]
        _ = -(X * 1) := by rw [pauliZ_sq]
        _ = -X := by rw [mul_one]
  -- X * I = X
  | 1, 0, 0, 0 => simp only [singleQubitPauli, mul_one, one_smul,
      show (0 : ZMod 2) * 0 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (1 : ZMod 2) + 0 = 1 by decide, show (0 : ZMod 2) + 0 = 0 by decide]
  -- X * Z = XZ
  | 1, 0, 0, 1 => simp only [singleQubitPauli, one_smul,
      show (0 : ZMod 2) * 0 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (1 : ZMod 2) + 0 = 1 by decide, show (0 : ZMod 2) + 1 = 1 by decide]
  -- X * X = I (using X² = I)
  | 1, 0, 1, 0 => simp only [singleQubitPauli, pauliX_sq, one_smul,
      show (0 : ZMod 2) * 1 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (1 : ZMod 2) + 1 = 0 by decide, show (0 : ZMod 2) + 0 = 0 by decide]
  -- X * XZ = Z
  | 1, 0, 1, 1 =>
      simp only [singleQubitPauli, one_smul,
        show (0 : ZMod 2) * 1 = 0 by decide,
        show (0 : ZMod 2) ≠ 1 by decide, ite_false,
        show (1 : ZMod 2) + 1 = 0 by decide,
        show (0 : ZMod 2) + 1 = 1 by decide]
      calc X * (X * Z) = (X * X) * Z := by rw [mul_assoc]
        _ = 1 * Z := by rw [pauliX_sq]
        _ = Z := by rw [one_mul]
  -- XZ * I = XZ
  | 1, 1, 0, 0 => simp only [singleQubitPauli, mul_one, one_smul,
      show (1 : ZMod 2) * 0 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide, ite_false,
      show (1 : ZMod 2) + 0 = 1 by decide]
  -- XZ * Z = X (using ZZ = I)
  | 1, 1, 0, 1 =>
      simp only [singleQubitPauli, one_smul,
        show (1 : ZMod 2) * 0 = 0 by decide,
        show (0 : ZMod 2) ≠ 1 by decide, ite_false,
        show (1 : ZMod 2) + 0 = 1 by decide,
        show (1 : ZMod 2) + 1 = 0 by decide]
      calc X * Z * Z = X * (Z * Z) := by rw [mul_assoc]
        _ = X * 1 := by rw [pauliZ_sq]
        _ = X := by rw [mul_one]
  -- XZ * X = -Z (anticommutation, XX = I)
  | 1, 1, 1, 0 =>
      simp only [singleQubitPauli, neg_one_smul,
        show (1 : ZMod 2) * 1 = 1 by decide, ite_true,
        show (1 : ZMod 2) + 1 = 0 by decide,
        show (1 : ZMod 2) + 0 = 1 by decide]
      calc X * Z * X = X * (Z * X) := by rw [mul_assoc]
        _ = X * (-(X * Z)) := by rw [pauliZX_anticommute]
        _ = -(X * (X * Z)) := by rw [mul_neg]
        _ = -((X * X) * Z) := by rw [mul_assoc]
        _ = -(1 * Z) := by rw [pauliX_sq]
        _ = -Z := by rw [one_mul]
  -- XZ * XZ = -I (ZX = -XZ, XX = I, ZZ = I)
  | 1, 1, 1, 1 =>
      simp only [singleQubitPauli, neg_one_smul,
        show (1 : ZMod 2) * 1 = 1 by decide, ite_true,
        show (1 : ZMod 2) + 1 = 0 by decide]
      calc X * Z * (X * Z) = X * (Z * (X * Z)) := by rw [mul_assoc]
        _ = X * ((Z * X) * Z) := by rw [mul_assoc]
        _ = X * (Z * X) * Z := by rw [← mul_assoc]
        _ = X * (-(X * Z)) * Z := by rw [pauliZX_anticommute]
        _ = -(X * (X * Z)) * Z := by rw [mul_neg]
        _ = -((X * X) * Z) * Z := by rw [mul_assoc]
        _ = -(1 * Z) * Z := by rw [pauliX_sq]
        _ = -(Z * Z) := by rw [one_mul, neg_mul]
        _ = -(1 : Op 2) := by rw [pauliZ_sq]

/-- The operator corresponding to a Pauli error on n qubits.
    This is the tensor product ⊗ᵢ (Xᵢ^{xᵢ} Zᵢ^{zᵢ}).

    For now, we define this recursively. The base case n=0 gives
    a 1×1 identity, and the inductive case tensors the next qubit. -/
def PauliError.toOp {n : ℕ} (e : PauliError n) : Op (2 ^ n) :=
  match n with
  | 0 => 1  -- 1×1 identity matrix
  | k + 1 =>
    -- Split: first qubit ⊗ remaining qubits
    let firstQubit : Op 2 := singleQubitPauli (e.xPattern 0) (e.zPattern 0)
    let restError : PauliError k := ⟨e.xPattern ∘ Fin.succ, e.zPattern ∘ Fin.succ⟩
    -- Tensor product with dimension cast
    let tensorOp : Op (2 * 2^k) := firstQubit ⊗ restError.toOp
    -- Cast dimension: 2 * 2^k = 2^(k+1)
    Op.castDim (by ring : 2 * 2^k = 2^(k+1)) tensorOp

/-- Pauli error operators are unitary: E† E = I.
    Proof by induction on n using the tensor product structure. -/
theorem PauliError.toOp_unitary {n : ℕ} (e : PauliError n) : e.toOp† * e.toOp = 1 := by
  match n with
  | 0 =>
    -- Base case: 1×1 identity
    simp only [toOp]
    simp
  | k + 1 =>
    -- Inductive case: (P ⊗ E')† * (P ⊗ E') = (P† ⊗ E'†) * (P ⊗ E') = (P†P) ⊗ (E'†E') = I ⊗ I = I
    simp only [toOp]
    let firstQubit := singleQubitPauli (e.xPattern 0) (e.zPattern 0)
    let restError : PauliError k := ⟨e.xPattern ∘ Fin.succ, e.zPattern ∘ Fin.succ⟩
    let h : 2 * 2^k = 2^(k+1) := by ring
    -- Rewrite using castDim properties
    calc (Op.castDim h (firstQubit ⊗ restError.toOp))† *
         (Op.castDim h (firstQubit ⊗ restError.toOp))
        = Op.castDim h (firstQubit ⊗ restError.toOp)† *
          Op.castDim h (firstQubit ⊗ restError.toOp) := by rw [Op.castDim_conjTranspose]
      _ = Op.castDim h ((firstQubit ⊗ restError.toOp)† *
          (firstQubit ⊗ restError.toOp)) := by rw [Op.castDim_mul]
      _ = Op.castDim h ((firstQubit† ⊗ restError.toOp†) *
          (firstQubit ⊗ restError.toOp)) := by rw [Op.tensor_conjTranspose]
      _ = Op.castDim h ((firstQubit† * firstQubit) ⊗
          (restError.toOp† * restError.toOp)) := by rw [Op.tensor_mul]
      _ = Op.castDim h ((1 : Op 2) ⊗ (1 : Op (2^k))) := by
            rw [singleQubitPauli_unitary, restError.toOp_unitary]
      _ = Op.castDim h 1 := by rw [Op.tensor_one]
      _ = 1 := Op.castDim_one h


end Math.CodingTheory.CSS
