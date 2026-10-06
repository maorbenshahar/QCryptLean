import QCryptLean.Quantum.Operators.BraKet.Projector

/-!
# Basic Quantum Tactics — qisimp_basic for bra-ket simplification

Automation for simplifying bra-ket expressions that do not require tensor
product-specific lemmas.

## Main definitions
- qisimp_basic (tactic macro): simp tactic for scalar, dagger, bra-ket, and qubit basis
  calculations.
-/

open Quantum.Operators

/-- Basic simplification tactic for quantum information proofs.
    Expands products, applies completeness relations, and simplifies complex arithmetic.
    Uses SMul (•) notation for all scalar multiplication. -/
macro "qisimp_basic" : tactic =>
  `(tactic| (
    simp (config := { decide := true }) [
      -- Scalar multiplication
      Op.dag_smul, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub, smul_add,
      -- Conjugate transpose
      Op.dag_sub, Op.dag_add, ket_mul_bra_conjTranspose, stdKet_dag_dag,
      -- Products
      sub_mul, mul_sub, add_mul, mul_add, ketbra_mul_ketbra, ketbra_mul_ket,
      add_op_mul_ket, sub_op_mul_ket, smul_op_mul_ket,
      -- Inner products (brakets)
      stdKet_braket, bra_mul_smul_ket, bra_mul_add_ket,
      -- Complex arithmetic
      Complex.star_def, Complex.conj_I, Complex.I_mul_I, mul_neg, neg_mul,
      neg_neg, neg_one_smul, one_smul, neg_smul,
      -- Zero/one simplification
      zero_mul, mul_zero, zero_smul, smul_zero, zero_add, add_zero, zero_sub, sub_zero,
      mul_one, one_mul, zero_ket_mul_bra, ket_mul_zero_bra,
      -- Ket arithmetic
      Ket.add_vec, Ket.sub_vec, Ket.smul_vec, Ket.neg_vec,
      Ket.sub_zero, Ket.zero_sub,
      -- Negation and subtraction
      sub_neg_eq_add, neg_add, add_neg_cancel_right, add_neg_cancel_left,
      -- Completeness (dimension 2 for qubits)
      completeness_2
    ]
  ))
