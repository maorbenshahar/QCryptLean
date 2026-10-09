import QCryptLean
import Batteries.Tactic.Lint.Simp

/-!
# Quantum simp normal forms

Negation and subtraction retain their additive forms. Simp extracts scalars, contracts zero
and identity actions, and evaluates product tensors. Product and tensor expansion over sums,
rank-one reassociation and general tensor algebra require explicit lemmas. The critical-pair checks
compare the resulting normal forms.
-/

open Quantum.Operators
open scoped QuantumDirac QuantumAdjoint QuantumTensor

-- The extra zero forces a simplification while the guard checks the resulting syntax.
example {n : Type*} (ψ : Ket n) (P : Ket n → Prop) (h : P (-ψ + 0)) : P (-ψ) := by
  simp at h
  guard_hyp h :ₛ P (-ψ)
  assumption

-- Instance projections may differ while their operation data agree definitionally.
example {n : Type*} (ψ : Ket n) (P : Ket n → Prop) (h : P ((-1 : ℂ) • ψ)) : P (-ψ) := by
  fail_if_success guard_hyp h : P (-ψ)
  simp at h
  guard_hyp h : P (-ψ)
  assumption

-- Negative scalar multiplication uses the same normal form as negation.
example {n : Type*} (ψ : Ket n) (P : Ket n → Prop) (h : P (((-1 : ℂ) • ψ) + 0)) :
    P (-ψ) := by
  simp at h
  guard_hyp h : P (-ψ)
  assumption

example {n : Type*} (ψ φ : Ket n) (P : Ket n → Prop) (h : P ((ψ - φ) + 0)) :
    P (ψ - φ) := by
  simp at h
  guard_hyp h :ₛ P (ψ - φ)
  assumption

example {n : Type*} (ψ φ : Ket n) (P : Bra n → Prop) (h : P ((ψ - φ).dag)) :
    P (ψ.dag - φ.dag) := by
  simp at h
  guard_hyp h :ₛ P (ψ.dag - φ.dag)
  assumption

-- Explicit scalar/negation and subtraction/dagger rewrites give the same additive expressions.
example {n : Type*} (ψ : Ket n) : (-1 : ℂ) • ψ = -ψ := by
  simp

example {n : Type*} (ψ φ : Ket n) : ψ + (-1 : ℂ) • φ = ψ - φ := by
  ext i
  simp [sub_eq_add_neg]

example {n : Type*} (ψ φ : Ket n) : (ψ - φ).dag = ψ.dag - φ.dag := by simp

example {n : Type*} (ψ φ : Ket n) : (ψ - φ).dag = ψ.dag - φ.dag := by
  rw [sub_eq_add_neg, Ket.dag_add, Ket.dag_neg, sub_eq_add_neg]

example {n : Type*} (A : Op n) : (A†)† = A := by simp

example {n : Type*} (ψ : Ket n) : ψ.dag.dag = ψ := by simp

example {n : Type*} (β : Bra n) : β.dag.dag = β := by simp

-- Involution runs before propagation through a compound ket.
example {n m : Type*} (ψ : Ket n) (φ : Ket m) : (ψ ⊗ φ).dag.dag = ψ ⊗ φ := by
  simp

example {n m : Type*} (A : Op n) (B : Op m) : ((A ⊗ B)†)† = A ⊗ B := by simp

-- Product tensors expose their natural component entries.
example {X Y : Type*} (ψ : Ket X) (φ : Ket Y) (x : X) (y : Y) :
    (ψ ⊗ φ).vec (x, y) = ψ.vec x * φ.vec y := rfl

example {X Y : Type*} (A : Op X) (B : Op Y) : (A ⊗ B)† = A† ⊗ B† :=
  Matrix.conjTranspose_kronecker A B

example {X : Type*} [Fintype X] [DecidableEq X] (ψ : Ket X) : (1 : Op X) * ψ = ψ := by simp

example {X : Type*} [Fintype X] (ψ : Ket X) : (0 : Op X) * ψ = 0 := by simp

example {X : Type*} (ψ : Ket X) : ψ * (0 : Bra X) = (0 : Op X) := by simp

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``Quantum.Operators.Ket.dag_dag, ``Quantum.Operators.Bra.dag_dag,
      ``Quantum.Operators.Ket.dag_add, ``Quantum.Operators.Bra.dag_add,
      ``Quantum.Operators.Ket.dag_sub, ``Quantum.Operators.Bra.dag_sub,
      ``Quantum.Operators.Ket.dag_smul, ``Quantum.Operators.Bra.dag_smul,
      ``Quantum.Operators.ToKet.toKet_ket, ``Quantum.Operators.ToBra.toBra_bra] do
    unless ← Batteries.Tactic.Lint.isSimpTheorem name do
      throwError "Missing simp attribute: {name}"
    if let some message ← Batteries.Tactic.Lint.simpNF.test name then
      logError m!"{name}: {message}"
