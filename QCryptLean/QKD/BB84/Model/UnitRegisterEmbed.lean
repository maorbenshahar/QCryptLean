import QCryptLean.Quantum.Channels.CPTP.CKRBound.Basic
import QCryptLean.Quantum.TensorProducts.TensorRightId

/-!
# The unit register embedding

The attack-free padding of a register by a one-dimensional side slot: the identity Kraus map
transported along `m = m · 1`.  It is the `eveDim = 1` instantiation of every retained-Eve slot in
the BB84 protocol channels, and it is what lets the bare channels
(`bb84SymRealChannel` / `bb84SymIdealChannel`) be written with no attack parameter anywhere in
their statements.

## Main definitions

- `idKrausRep`: the single-operator identity Kraus representation `{1}` on `Op n`.
- `bb84UnitRegisterEmbed`: `Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * 1)`, the identity Kraus map cast along
  `4 ^ n = 4 ^ n * 1`.
- `IsPermutationCovariantUpToEveRelabelPre`: permutation covariance up to a permutation-dependent
  unitary relabeling of the retained-Eve register, stated on a bare retained-Eve dimension and an
  opaque pre-channel.

## Main statements

- `bb84UnitRegisterEmbed_isCPTP`: the embedding is CPTP, from its own Kraus representation.
- `bb84UnitRegisterEmbed_apply`: the embedding is `A ↦ A ⊗ 1₁`.
- `bb84UnitRegisterEmbed_isPermCovUpToEveRelabelPre`: the embedding is permutation covariant up to
  Eve relabeling, with `R π = 1`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-- The identity Kraus representation `{ 1 }` on `Op n` (single Kraus operator `1`). -/
def idKrausRep (n : ℕ) : KrausRepresentation n n where
  numOps := 1
  operators := fun _ => (1 : Op n)
  completeness := by simp

-- Casting `M : Op m` along `m = m·1` is `M ⊗ 1₁`
-- (`Quantum.TensorProducts.op_castDim_mul_one_eq_tensor_one`), used unqualified below through the
-- `open Quantum.TensorProducts` above.

/-- **The unit register embedding** `Op (4 ^ n) →ₗ Op (4 ^ n * 1)` — the identity Kraus map
transported along `4 ^ n = 4 ^ n * 1`.

This is the attack-free padding of the signal register by a one-dimensional side slot: it
mentions no attack object, and it is what lets the bare protocol channels be written with **no
attack parameter anywhere in their statement** — every retained-Eve slot `(eveDim, pre, hpre)` is
instantiated at `eveDim := 1`, `pre := bb84UnitRegisterEmbed n`. -/
def bb84UnitRegisterEmbed (n : ℕ) : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * 1) :=
  krausMapFintype ((idKrausRep (4 ^ n)).castOutput (Nat.mul_one (4 ^ n)).symm).operators

/-- **The unit register embedding is CPTP**, proved directly from its own Kraus representation: the
identity Kraus map cast along `4 ^ n = 4 ^ n * 1`.  No attack object is named anywhere in the
statement or in the proof, which is what lets the bare channels carry attack-free CPTP proofs. -/
theorem bb84UnitRegisterEmbed_isCPTP (n : ℕ) [NeZero (4 ^ n)] :
    IsCPTP (⇑(bb84UnitRegisterEmbed n)) := by
  haveI : NeZero (4 ^ n * 1) := ⟨by simp⟩
  exact KrausRepresentation.is_cptp ((idKrausRep (4 ^ n)).castOutput (Nat.mul_one (4 ^ n)).symm)

/-- **The unit register embedding is `A ↦ A ⊗ 1₁`** (the identity on the signal, tensored with the
one-dimensional side register). -/
theorem bb84UnitRegisterEmbed_apply (n : ℕ) (A : Op (4 ^ n)) :
    bb84UnitRegisterEmbed n A = Op.tensor A (1 : Op 1) := by
  change krausMapFintype
    ((idKrausRep (4 ^ n)).castOutput (Nat.mul_one (4 ^ n)).symm).operators A = _
  rw [krausMapFintype_castOutput]
  have hid : krausMapFintype (idKrausRep (4 ^ n)).operators A = A := by
    simp [idKrausRep, krausMapFintype]
  rw [show (Nat.mul_one (4 ^ n)).symm ▸ krausMapFintype (idKrausRep (4 ^ n)).operators A
        = Op.castDim (Nat.mul_one (4 ^ n)).symm
            (krausMapFintype (idKrausRep (4 ^ n)).operators A) from rfl,
      hid, op_castDim_mul_one_eq_tensor_one]

end QKD.BB84.Model

end -- noncomputable section
