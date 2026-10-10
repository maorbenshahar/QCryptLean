import QCryptLean

/-!
# Quantum notation isolation
-/

open Quantum.Operators  

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

section

open scoped QuantumDirac QuantumAdjoint QuantumTensor

open Lean Elab Command in
run_cmd do
  for source in ["|0⟩", "|1⟩", "⟨0|", "⟨1|",
      "|ψ⟩", "⟨ψ|", "|ψ, φ⟩", "⟨ψ, φ|",
      "A†", "A ⊗ B",
      "⟨ 0 |", "⟨ 1 |"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

end

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
