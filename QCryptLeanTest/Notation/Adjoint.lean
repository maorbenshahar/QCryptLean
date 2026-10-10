import QCryptLean

/-!
# Adjoint notation isolation
-/

open Quantum.Operators 

open scoped QuantumAdjoint

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

example {n : ℕ} (A : Op (Fin n)) : A† = Matrix.conjTranspose A := rfl

example {n : ℕ} (U : UnitaryOp (Fin n)) :
    ((star U : UnitaryOp (Fin n)) : Op (Fin n)) = (U : Op (Fin n))† := rfl

example {n : ℕ} (_U : UnitaryOp (Fin n)) : True := by
  fail_if_success exact (let _ : UnitaryOp (Fin n) := _U†; True.intro)
  trivial

section

open scoped QuantumDirac QuantumTensor

open Lean Elab Command in
run_cmd do
  for source in ["|0⟩", "|1⟩", "⟨0|", "⟨1|",
      "|ψ⟩", "⟨ψ|", "|ψ, φ⟩", "⟨ψ, φ|",
      "A ⊗ B",
      "⟨ 0 |", "⟨ 1 |"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

end

open Lean Elab Command in
run_cmd do
  for source in ["A†"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

open Lean Elab Command in
run_cmd do
  for source in ["|0⟩", "|1⟩", "⟨0|", "⟨1|",
      "|ψ⟩", "⟨ψ|", "|ψ, φ⟩", "⟨ψ, φ|",
      "A ⊗ B",
      "⟨ 0 |", "⟨ 1 |"] do
    unless (Parser.runParserCategory (← getEnv) `term "id x").isOk do
      throwError "Ordinary-term positive control failed"
    if (Parser.runParserCategory (← getEnv) `term source).isOk then
      throwError "Unexpected term syntax: {source}"
