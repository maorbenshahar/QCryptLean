import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.Tactic.QISimpBasic
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.TensorProducts.PartialTrace
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.Gates

/-!
# Quantum Tactics — `qisimp` for bra-ket simplification

Automation for simplifying bra-ket expressions involving dagger, scalar
multiplication, addition, tensor products, and standard basis inner products.

## Main definitions
- `qisimp`: Multi-stage simp tactic for quantum inner product calculations
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Gates

/-- Extended qisimp tactic that includes tensor product lemmas.
    Strategy:
    0. Convert subtraction to addition with negation (ψ - φ → ψ + (-1)•φ)
    1. Handle dagger of smul/add/tensor (and convert dag of subtraction)
    2. Pull out scalars from brakets
    3. Distribute brakets over addition
    4. Apply tensor factorization (must be AFTER distribution!)
    5. Evaluate inner products with stdKet_braket
    6. Reduce Fin comparisons and if-then-else
    7. Simplify arithmetic -/
macro "qisimp" : tactic =>
  `(tactic| (
    -- Stage 0: Convert subtraction to addition with negation
    try simp only [Ket.sub_eq_add_neg_smul]
    -- Stage 1: Handle dagger of smul/add/tensor and convert dag of subtraction
    try simp only [Ket.dag_smul, Ket.dag_add, Ket.dag_sub_eq_add_neg_smul, Ket.dag_tensor]
    -- Stage 1b: Convert any remaining subtraction (after dag is applied)
    try simp only [Ket.sub_eq_add_neg_smul]
    -- Stage 2: Pull out scalars from brakets
    try simp only [bra_mul_smul_ket, smul_bra_mul_ket]
    -- Stage 3: Distribute brakets over addition
    try simp only [bra_mul_add_ket, bra_add_mul_ket]
    -- Stage 4: Tensor factorization (after distribution exposes tensor structure)
    try simp only [bra_tensor_mul_ket_tensor]
    -- Stage 5: Evaluate brakets
    try simp only [stdKet_braket]
    -- Stage 6: Reduce Fin comparisons to Nat and simplify
    try simp only [↓reduceIte, smul_eq_mul, mul_one]
    -- Stage 7: Evaluate Nat comparisons
    try norm_num
  ))
