import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.Symmetry.Covariance
import QCryptLean.Math.LinearAlgebra.PermutationMatrix

/-!
# Signal-register permutation channel — round-permutation conjugation on `Op (d^n)`

The `d`-generic unitary-conjugation channel implementing a round permutation on an
`n`-fold tensor register `Op (d^n)`: the construction and its two structural lemmas
mention no BB84 or QKD-protocol object. It is consumed by the BB84 finite-size engine's
signal-register conjugations, outcome-string relabelings and transcript/output corrections.

## Main definitions
- `permuteSignalLinear`: unitary conjugation by a round permutation on `Op (4^n)`.

## Main statements
- `permuteSignalLinear_isCPTP`: signal permutation conjugation is CPTP.
- `permuteSignal_after_sigma`: signal permutation composition law.
-/

open Equiv

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Symmetry

/-!
## Signal-register permutation channel
-/

/-- Unitary conjugation by the permutation representation on `Op (4^n)`.

`ρ ↦ U_π · ρ · U_π†` where `U_π = permutationRepresentation 4 n π`
(`U_π|i⟩ = |i ∘ π⁻¹⟩` on the `n` tensor factors).

**It permutes the rounds of the JOINT `A ⊗ B` pair register**, not one party's half: the `n` tensor
factors of `Op (4^n)` are the `signalDim = 4`-dimensional Alice⊗Bob qubit pairs of the `n`
rounds — `roundGroupEquiv 2 2 n : Fin (4^n) ≃ Fin (2^n · 2^n)`
is the regrouping that separates the
interleaved per-round pairs into the `Aⁿ`/`Bⁿ` blocks. That the SAME `π` is applied to both halves
is what makes the symmetrization LOCC-implementable and is what the sources specify: Renner's
"Alice and Bob both permute the order of their `N` subsystems according to `π`"
(arXiv:quant-ph/0512258v2, `main.tex:1800-1801`) and CKR's "both Alice and Bob permute
their inputs according to a permutation `π̄` chosen at random by one party and communicated to the
other" (arXiv:0809.3019, `main.tex:452-455`) — one party draws `π`, announces it, both
apply it locally.

In the symmetrized BB84 channels this map sits **innermost**, on the diamond-norm input, ahead of
the attack slot (`bb84SymSiftedRealChannelDirect_withPEAnnounce`); `π` is announced in
the output. That is what makes the fixed prefix/parity PE and X-test selectors read a uniformly
random round subset relative to the input. -/
noncomputable def permuteSignalLinear (n : ℕ) [NeZero n]
    [NeZero (4 ^ n)]
    (π : Equiv.Perm (Fin n)) :
    Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n) where
  toFun ρ :=
    Math.RepresentationTheory.permutationRepresentation 4 n π * ρ *
      (Math.RepresentationTheory.permutationRepresentation 4 n π)ᴴ
  map_add' a b := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- `permuteSignalLinear` is CPTP because it is unitary conjugation. -/
theorem permuteSignalLinear_isCPTP (n : ℕ) [NeZero n]
    [NeZero (4 ^ n)]
    (π : Equiv.Perm (Fin n)) :
    IsCPTP (⇑(permuteSignalLinear n π)) := by
  change IsCPTP
    (fun ρ : Op (4 ^ n) =>
      Math.RepresentationTheory.permutationRepresentation 4 n π * ρ *
        (Math.RepresentationTheory.permutationRepresentation 4 n π)ᴴ)
  apply isCPTP_unitary_conjugation
  exact (Math.RepresentationTheory.permutationRepresentation_unitary 4 n π).1

/-- Applying `permuteSignalLinear π` after conjugation by `U_σ` is the same
as applying `permuteSignalLinear (π * σ)`. -/
lemma permuteSignal_after_sigma
    (n : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (π σ : Equiv.Perm (Fin n)) (ρ : Op (4 ^ n)) :
    permuteSignalLinear n π
      (Math.RepresentationTheory.permutationRepresentation 4 n σ * ρ *
        (Math.RepresentationTheory.permutationRepresentation 4 n σ)ᴴ) =
      permuteSignalLinear n (π * σ) ρ := by
  simp only [permuteSignalLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Matrix.mul_assoc]
  rw [← Matrix.mul_assoc]
  rw [Math.RepresentationTheory.permutationRepresentation_mul]
  rw [Matrix.mul_assoc]
  congr 1
  rw [← Matrix.conjTranspose_mul, Math.RepresentationTheory.permutationRepresentation_mul]

end Quantum.Symmetry

end -- noncomputable section
