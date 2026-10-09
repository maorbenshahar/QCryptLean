import QCryptLean

/-!
# Tensor notation isolation
-/

open Quantum.Operators 

open scoped QuantumTensor

example (X Y Z H R S : ℕ) : X + Y + Z + H + R + S = X + Y + Z + H + R + S := rfl

example (S_gate T_gate CNOT SWAP CZ : ℕ) :
    S_gate + T_gate + CNOT + SWAP + CZ = S_gate + T_gate + CNOT + SWAP + CZ := rfl

example (f : ℕ → Option ℕ) (x alt : ℕ) : Option ℕ := do
  let some y ← pure (f x) | pure alt
  pure y

example (f : ℕ → Option (Option ℕ)) (x : ℕ) (alt : Option ℕ) : Option ℕ := do
  let some y ← f x | alt
  pure y

example (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | n + 1 => f n

example : Set ℕ := {x : ℕ | x < 3}

example (a b : ℕ) : ℕ × ℕ := ⟨a, b⟩

example {n m : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) : ψ ⊗ φ = Ket.kronecker ψ φ := rfl

example {n m : ℕ} (β : Bra (Fin n)) (γ : Bra (Fin m)) : β ⊗ γ = Bra.kronecker β γ := rfl

example {n m : ℕ} (A : Op (Fin n)) (B : Op (Fin m)) : A ⊗ B = Matrix.kronecker A B := rfl

example {n m : ℕ} (ψ : NormKet (Fin n)) (φ : NormKet (Fin m)) :
    (NormKet.kronecker ψ φ).toKet = ψ.toKet ⊗ φ.toKet := rfl

example {n m : ℕ} (_ψ : NormKet (Fin n)) (_φ : NormKet (Fin m)) : True := by
  fail_if_success exact (let _ : NormKet (Fin n × Fin m) := _ψ ⊗ _φ; True.intro)
  trivial

section

open scoped QuantumDirac QuantumAdjoint

open Lean Elab Command in
run_cmd do
  for source in ["|0⟩", "|1⟩", "⟨0|", "⟨1|",
      "|ψ⟩", "⟨ψ|", "|ψ, φ⟩", "⟨ψ, φ|",
      "A†",
      "⟨ 0 |", "⟨ 1 |"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

end

open Lean Elab Command in
run_cmd do
  for source in ["A ⊗ B"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

open Lean Elab Command in
run_cmd do
  for source in ["|0⟩", "|1⟩", "⟨0|", "⟨1|",
      "|ψ⟩", "⟨ψ|", "|ψ, φ⟩", "⟨ψ, φ|",
      "A†",
      "⟨ 0 |", "⟨ 1 |"] do
    unless (Parser.runParserCategory (← getEnv) `term "id x").isOk do
      throwError "Ordinary-term positive control failed"
    if (Parser.runParserCategory (← getEnv) `term source).isOk then
      throwError "Unexpected term syntax: {source}"

-- Tensor binds at precedence 100; multiplication is 70 and scalar multiplication is 73.
example {n m : ℕ} (A : Op (Fin n × Fin m)) (B : Op (Fin n)) (C : Op (Fin m)) :
    A * B ⊗ C = A * Matrix.kronecker B C := rfl

example {n m : ℕ} (A : Op (Fin n)) (B : Op (Fin m)) (C : Op (Fin n × Fin m)) :
    A ⊗ B * C = Matrix.kronecker A B * C := rfl

example {n m : ℕ} (c : ℂ) (A : Op (Fin n)) (B : Op (Fin m)) :
    c • A ⊗ B = c • Matrix.kronecker A B := rfl

example {n m : ℕ} (c : ℂ) (ψ : Ket (Fin n)) (φ : Ket (Fin m)) :
    c • ψ ⊗ φ = c • Ket.kronecker ψ φ := rfl

example {n m : ℕ} (c : ℂ) (β : Bra (Fin n)) (γ : Bra (Fin m)) :
    c • β ⊗ γ = c • Bra.kronecker β γ := rfl

example {n m : ℕ} (A : Op (Fin n)) (B : Op (Fin m)) (k : ℕ) :
    A ⊗ B ^ k = (Matrix.kronecker A B) ^ k := rfl

example {n m : ℕ} (A : Op (Fin n)) (B : Op (Fin m)) : -A ⊗ B = -(Matrix.kronecker A B) := rfl

example {n m k : ℕ} (A : Op (Fin n)) (B : Op (Fin m)) (C : Op (Fin k)) :
    A ⊗ B ⊗ C = Matrix.kronecker (Matrix.kronecker A B) C := rfl

-- Quantum and Mathlib tensor notation agree on scalar precedence when both scopes are open.
open scoped TensorProduct QuantumTensor in
example {n m : ℕ} (c : ℂ) (A : Op (Fin n)) (B : Op (Fin m)) :
    c • A ⊗ B = c • Matrix.kronecker A B := rfl
