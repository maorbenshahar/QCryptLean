import QCryptLean

/-!
# Dirac notation without tensor or adjoint notation
-/

open Quantum.Operators 
open scoped QuantumDirac

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

example : | 0 ⟩ = stdKet (0 : Fin 2) := rfl

example : |0 ⟩ = stdKet (0 : Fin 2) := rfl

example : | 1 ⟩ = stdKet (1 : Fin 2) := rfl

example : ⟨ 0 | = (stdKet (0 : Fin 2)).dag := rfl

example : ⟨ 1 | = (stdKet (1 : Fin 2)).dag := rfl

example {n : ℕ} (ψ : Ket (Fin n)) : id |ψ⟩ = ψ := rfl

example {n m : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) : id |ψ, φ⟩ = Ket.kronecker ψ φ := rfl

example : id | 0 ⟩ = stdKet (0 : Fin 2) := rfl

example : id |0, 1⟩ = Ket.kronecker (stdKet (0 : Fin 2)) (stdKet (1 : Fin 2)) := rfl

example (x : ℤ) : |x| = |x| := rfl

example (f : ℕ → ℕ) (s : Set ℕ) : Set ℕ := {f x | x ∈ s}

example : |0⟩ = stdKet (0 : Fin 2) := rfl

example : |1⟩ = stdKet (1 : Fin 2) := rfl

example : ⟨0| = (stdKet (0 : Fin 2)).dag := rfl

example : ⟨1| = (stdKet (1 : Fin 2)).dag := rfl

example {n : ℕ} (ψ : Ket (Fin n)) : |ψ⟩ = ψ := rfl

example {n : ℕ} (β : Bra (Fin n)) : | β ⟩ = β.dag := rfl

example {n : ℕ} (ψ : Ket (Fin n)) : ⟨ ψ | = ψ.dag := rfl

example {n : ℕ} (β : Bra (Fin n)) : ⟨β| = β := rfl

example : | 0, 1 ⟩ = Ket.kronecker (stdKet (0 : Fin 2)) (stdKet (1 : Fin 2)) := rfl

example : ⟨ 1, 0 | = (Ket.kronecker (stdKet (1 : Fin 2)) (stdKet (0 : Fin 2))).dag := rfl

example {n m : ℕ} (ψ : Ket (Fin n)) (β : Bra (Fin m)) : |ψ, β⟩ = Ket.kronecker ψ β.dag := rfl

example {n m : ℕ} (ψ : Ket (Fin n)) (β : Bra (Fin m)) : ⟨ψ, β| = (Ket.kronecker ψ β.dag).dag := rfl

example {n m k : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) (χ : Ket (Fin k)) :
    (|ψ, φ, χ⟩ : Ket ((Fin n × Fin m) × Fin k)) = Ket.kronecker (Ket.kronecker ψ φ) χ := rfl

example {n m k : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) (χ : Ket (Fin k)) :
    (⟨ψ, φ, χ| : Bra ((Fin n × Fin m) × Fin k)) = (Ket.kronecker (Ket.kronecker ψ φ) χ).dag := rfl

example {n m : ℕ} (ψ : Ket (Fin n)) (φ : Ket (Fin m)) :
    |(ψ + ψ), (φ + φ)⟩ = Ket.kronecker (ψ + ψ) (φ + φ) := rfl

example : |stdKet (2 : Fin 3), 1⟩ = Ket.kronecker (stdKet (2 : Fin 3)) (stdKet (1 : Fin 2)) := rfl

example : (|0, 1⟩ : Ket (Fin 2 × Fin 2)).vec (0, 1) = 1 := by
  norm_num [Ket.kronecker, stdKet]

example : (|1, 0⟩ : Ket (Fin 2 × Fin 2)).vec (1, 0) = 1 := by
  norm_num [Ket.kronecker, stdKet]

example : (|1, 0, 1⟩ : Ket ((Fin 2 × Fin 2) × Fin 2)).vec ((1, 0), 1) = 1 := by
  norm_num [Ket.kronecker, stdKet]

example : (⟨1, 0, 1| : Bra ((Fin 2 × Fin 2) × Fin 2)).vec ((1, 0), 1) = 1 := by
  norm_num [Ket.kronecker, stdKet, Ket.dag]

example : (|stdKet (1 : Fin 2), stdKet (2 : Fin 3), stdKet (3 : Fin 5)⟩ :
    Ket ((Fin 2 × Fin 3) × Fin 5)).vec ((1, 2), 3) = 1 := by
  norm_num [Ket.kronecker, stdKet]

example : (⟨stdKet (1 : Fin 2), stdKet (2 : Fin 3), stdKet (3 : Fin 5)| :
    Bra ((Fin 2 × Fin 3) × Fin 5)).vec ((1, 2), 3) = 1 := by
  norm_num [Ket.kronecker, stdKet, Ket.dag]

example : True := by
  fail_if_success exact (let _ : Ket (Fin 2) := |2⟩; True.intro)
  fail_if_success exact (let _ : Bra (Fin 2) := ⟨2|; True.intro)
  fail_if_success exact (let _ : Ket (Fin 4) := |(2 : ℕ), 0⟩; True.intro)
  fail_if_success exact (let _ : Bra (Fin 4) := ⟨0, (2 : ℕ)|; True.intro)
  fail_if_success exact (let _ := (inferInstance : ToKet ℕ (Fin 2)); True.intro)
  trivial

/-- error: Only 0 and 1 are qubit labels; use stdKet (i : Fin n) for other basis states -/
#guard_msgs in
#check |2, 0⟩

/-- error: Only 0 and 1 are qubit labels; use stdKet (i : Fin n) for other basis states -/
#guard_msgs in
#check |0, 2⟩

/-- error: Only 0 and 1 are qubit labels; use stdKet (i : Fin n) for other basis states -/
#guard_msgs in
#check ⟨2, 0|

/-- error: Only 0 and 1 are qubit labels; use stdKet (i : Fin n) for other basis states -/
#guard_msgs in
#check ⟨0, 1, 37|

/-- error: Only 0 and 1 are qubit labels; use stdKet (i : Fin n) for other basis states -/
#guard_msgs in
#check |2⟩

/-- error: Only 0 and 1 are qubit labels; use stdKet (i : Fin n) for other basis states -/
#guard_msgs in
#check | 2 ⟩

/-- error: Only 0 and 1 are qubit labels; use stdKet (i : Fin n) for other basis states -/
#guard_msgs in
#check ⟨ 2 |

open Lean Elab Command in
run_cmd do
  unless (← getEnv).contains `Quantum.Operators.ToKet do
    throwError "Conversion API positive control failed"
  for name in [`Quantum.Operators.ToNormKet, `Quantum.Operators.instToNormKetNormKet,
      `Quantum.Operators.ToNormKet.toNormKet_normket, `Quantum.Operators.instToNormKetFin2] do
    if (← getEnv).contains name then
      throwError "Unused normalized-ket conversion API remains: {name}"

open Lean Elab Command in
run_cmd do
  for source in ["|0⟩", "|1⟩", "⟨0|", "⟨1|",
      "|ψ⟩", "⟨ψ|", "|ψ, φ⟩", "⟨ψ, φ|",
      "| 0 ⟩", "| 1 ⟩", "⟨ 0 |", "⟨ 1 |",
      "|stdKet (2 : Fin 3), 0⟩"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

section

open scoped QuantumAdjoint QuantumTensor

open Lean Elab Command in
run_cmd do
  for source in ["A†", "A ⊗ B"] do
    unless (Parser.runParserCategory (← getEnv) `term source).isOk do
      throwError "Expected term syntax: {source}"

end

open Lean Elab Command in
run_cmd do
  for source in ["A†", "A ⊗ B"] do
    unless (Parser.runParserCategory (← getEnv) `term "id x").isOk do
      throwError "Ordinary-term positive control failed"
    if (Parser.runParserCategory (← getEnv) `term source).isOk then
      throwError "Unexpected term syntax: {source}"

open Lean Elab Command in
run_cmd do
  for (source, control) in [
      ("|0:2⟩", "stdKet (0 : Fin 2)"),
      ("‖0⟩", "stdNormKet (0 : Fin 2)"),
      ("‖1⟩", "stdNormKet (1 : Fin 2)"),
      ("‖0:2⟩", "stdNormKet (0 : Fin 2)"),
      ("‖ψ, φ⟩", "NormKet.kronecker ψ φ"),
      ("|ψ,⟩", "|ψ, φ⟩"),
      ("⟨ψ,|", "⟨ψ, φ|")] do
    unless (Parser.runParserCategory (← getEnv) `term control).isOk do
      throwError "Positive control failed: {control}"
    if (Parser.runParserCategory (← getEnv) `term source).isOk then
      throwError "Removed or malformed syntax parsed: {source}"
