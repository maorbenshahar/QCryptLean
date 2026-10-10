import QCryptLeanTest.Notation.Dirac
import QCryptLeanTest.Notation.Adjoint
import QCryptLeanTest.Notation.Tensor

/-!
# Quantum scope lifetime and compatibility with Mathlib notation

The imports open all three quantum scopes in their own modules. None is inherited here.
-/

open Quantum.Operators  

open Lean Elab Command in
run_cmd do
  for name in [`QuantumDirac.tensorKet, `QuantumDirac.tensorBra] do
    unless (← getEnv).contains name do
      throwError "Missing named parser: {name}"

open Lean Elab Command in
run_cmd do
  for source in ["|0⟩", "|1⟩", "⟨0|", "⟨1|",
      "|ψ⟩", "⟨ψ|", "|ψ, φ⟩", "⟨ψ, φ|",
      "A†", "A ⊗ B",
      "⟨ 0 |", "⟨ 1 |"] do
    unless (Parser.runParserCategory (← getEnv) `term "id x").isOk do
      throwError "Ordinary-term positive control failed"
    if (Parser.runParserCategory (← getEnv) `term source).isOk then
      throwError "Unexpected term syntax: {source}"

section

open scoped QuantumDirac

example : |0, 1⟩ = Ket.kronecker (stdKet (0 : Fin 2)) (stdKet (1 : Fin 2)) := rfl

open Lean Elab Command in
run_cmd do
  for source in ["|0⟩", "|1⟩", "⟨0|", "⟨1|",
      "|ψ⟩", "⟨ψ|", "|ψ, φ⟩", "⟨ψ, φ|",
      "⟨ 0 |", "⟨ 1 |"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

end

open Lean Elab Command in
run_cmd do
  for source in ["|0⟩", "|1⟩", "⟨0|", "⟨1|",
      "|ψ⟩", "⟨ψ|", "|ψ, φ⟩", "⟨ψ, φ|",
      "⟨ 0 |", "⟨ 1 |"] do
    unless (Parser.runParserCategory (← getEnv) `term "id x").isOk do
      throwError "Ordinary-term positive control failed"
    if (Parser.runParserCategory (← getEnv) `term source).isOk then
      throwError "Unexpected term syntax: {source}"

section

open scoped QuantumAdjoint

example {n : ℕ} (A : Op (Fin n)) : A† = Matrix.conjTranspose A := rfl

open Lean Elab Command in
run_cmd do
  for source in ["A†"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

end

open Lean Elab Command in
run_cmd do
  for source in ["A†"] do
    unless (Parser.runParserCategory (← getEnv) `term "id x").isOk do
      throwError "Ordinary-term positive control failed"
    if (Parser.runParserCategory (← getEnv) `term source).isOk then
      throwError "Unexpected term syntax: {source}"

section

open scoped QuantumTensor

example {n m : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) : ψ ⊗ φ = Ket.kronecker ψ φ := rfl

open Lean Elab Command in
run_cmd do
  for source in ["A ⊗ B"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

end

open Lean Elab Command in
run_cmd do
  for source in ["A ⊗ B"] do
    unless (Parser.runParserCategory (← getEnv) `term "id x").isOk do
      throwError "Ordinary-term positive control failed"
    if (Parser.runParserCategory (← getEnv) `term source).isOk then
      throwError "Unexpected term syntax: {source}"

open scoped QuantumDirac in
example : |1⟩ = stdKet (1 : Fin 2) := rfl

open scoped QuantumDirac in
open Lean Elab Command in
run_cmd do
  for source in ["|1⟩"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

open Lean Elab Command in
run_cmd do
  for source in ["|1⟩"] do
    unless (Parser.runParserCategory (← getEnv) `term "id x").isOk do
      throwError "Ordinary-term positive control failed"
    if (Parser.runParserCategory (← getEnv) `term source).isOk then
      throwError "Unexpected term syntax: {source}"

section

variable {n m : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) (β : Bra (Fin n)) (γ : Bra (Fin m))
    (A : Op (Fin n)) (B : Op (Fin m))

/-- info: stdKet 0 : Ket (Fin 2) -/
#guard_msgs in
#check stdKet (0 : Fin 2)

/-- info: stdKet 1 : Ket (Fin 2) -/
#guard_msgs in
#check stdKet (1 : Fin 2)

/-- info: (stdKet 0).dag : Bra (Fin 2) -/
#guard_msgs in
#check Ket.dag (stdKet (0 : Fin 2))

/-- info: (stdKet 1).dag : Bra (Fin 2) -/
#guard_msgs in
#check Ket.dag (stdKet (1 : Fin 2))

/-- info: ToBra.toBra ψ : Bra (Fin n) -/
#guard_msgs in
#check ToBra.toBra ψ

/-- info: ToBra.toBra β : Bra (Fin n) -/
#guard_msgs in
#check ToBra.toBra β

/-- info: ToKet.toKet ψ : Ket (Fin n) -/
#guard_msgs in
#check ToKet.toKet ψ

/-- info: ψ.kronecker φ : Ket (Fin n × Fin m) -/
#guard_msgs in
#check Ket.kronecker ψ φ

/-- info: β.kronecker γ : Bra (Fin n × Fin m) -/
#guard_msgs in
#check Bra.kronecker β γ

/-- info: Matrix.kronecker A B : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ -/
#guard_msgs in
#check Matrix.kronecker A B

/-- info: Matrix.conjTranspose A : Matrix (Fin n) (Fin n) ℂ -/
#guard_msgs in
#check Matrix.conjTranspose A

end

section

open scoped QuantumDirac

variable {n m : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) (β : Bra (Fin n)) (γ : Bra (Fin m))
    (A : Op (Fin n)) (B : Op (Fin m))

/-- info: stdKet 0 : Ket (Fin 2) -/
#guard_msgs in
#check stdKet (0 : Fin 2)

/-- info: stdKet 1 : Ket (Fin 2) -/
#guard_msgs in
#check stdKet (1 : Fin 2)

/-- info: (stdKet 0).dag : Bra (Fin 2) -/
#guard_msgs in
#check Ket.dag (stdKet (0 : Fin 2))

/-- info: (stdKet 1).dag : Bra (Fin 2) -/
#guard_msgs in
#check Ket.dag (stdKet (1 : Fin 2))

/-- info: ⟨ψ| : Bra (Fin n) -/
#guard_msgs in
#check ToBra.toBra ψ

/-- info: ⟨β| : Bra (Fin n) -/
#guard_msgs in
#check ToBra.toBra β

/-- info: ToKet.toKet ψ : Ket (Fin n) -/
#guard_msgs in
#check ToKet.toKet ψ

end

section

open scoped QuantumTensor

variable {n m : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) (β : Bra (Fin n)) (γ : Bra (Fin m))
    (A : Op (Fin n)) (B : Op (Fin m))

/-- info: ψ ⊗ φ : Ket (Fin n × Fin m) -/
#guard_msgs in
#check Ket.kronecker ψ φ

/-- info: β ⊗ γ : Bra (Fin n × Fin m) -/
#guard_msgs in
#check Bra.kronecker β γ

/-- info: A ⊗ B : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ -/
#guard_msgs in
#check Matrix.kronecker A B

end

section

open scoped QuantumAdjoint

variable {n m : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) (β : Bra (Fin n)) (γ : Bra (Fin m))
    (A : Op (Fin n)) (B : Op (Fin m))

/-- info: A† : Matrix (Fin n) (Fin n) ℂ -/
#guard_msgs in
#check Matrix.conjTranspose A

end

section

open scoped Matrix TensorProduct Kronecker InnerProduct
open scoped QuantumDirac QuantumAdjoint QuantumTensor

example {n : ℕ} (A : Op (Fin n)) : A† = Aᴴ := rfl

example {n m : ℕ} (A : Op (Fin n)) (B : Op (Fin m)) :
    A ⊗ B = A ⊗ₖ B := rfl

example (x y : ℂ) : (x ⊗ₜ[ℂ] y : ℂ ⊗ ℂ) = TensorProduct.tmul ℂ x y := rfl

example (f : ℂ →L[ℂ] ℂ) : f† = ContinuousLinearMap.adjoint f := rfl

example : |0, 1⟩ = (|0⟩ ⊗ |1⟩ : Ket (Fin 2 × Fin 2)) := rfl

example : ⟨0, 1| = (|0⟩ ⊗ |1⟩ : Ket (Fin 2 × Fin 2)).dag := rfl

example {n : ℕ} (A : Op (Fin n)) : (A†)† = A := Matrix.conjTranspose_conjTranspose A

example {n : ℕ} (_A : Op (Fin n)) : True := by
  fail_if_success exact (let _ : Op (Fin n) := _A††; True.intro)
  exact (let _ : Op (Fin n) := (_A†)†; True.intro)

end
