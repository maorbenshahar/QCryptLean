import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Dimensions of flagged two-key registers

`QKD.keyedFlagOutDim ℓ Dinner` is the dimension of two key factors with `2 ^ ℓ` basis values
each, a two-dimensional accept/abort flag, and a retained factor of dimension `Dinner`:

`K_A ⊗ K_B ⊗ (flag ⊗ retained)`, of dimension `2 ^ ℓ · 2 ^ ℓ · (2 · Dinner)`.

The retained factor may include public data and other residual registers. These arithmetic
definitions impose no protocol or classicality condition. The output dimension is positive
when `Dinner` is positive; the module also supplies nonemptiness of a pair of `2 ^ n`-dimensional
signal registers.

Flag-block identities and the key-replacement channel are defined in
`QCryptLean.QKD.KeyedOutputRegister.FlagBlocks` and
`QCryptLean.QKD.KeyedOutputRegister.KeyReplacement`.
-/

namespace QKD

/-! ## The flagged two-key output register -/

/-- The dimension of two `ℓ`-bit key registers, an accept/abort flag and a retained factor
of dimension `Dinner`. -/
@[reducible] def keyedFlagOutDim (ℓ Dinner : ℕ) : ℕ := 2 ^ ℓ * 2 ^ ℓ * (2 * Dinner)

/-- A flagged two-key output register with a positive-dimensional retained factor is nonempty. -/
theorem keyedFlagOutDim_pos {ℓ Dinner : ℕ} (h : 0 < Dinner) : 0 < keyedFlagOutDim ℓ Dinner :=
  Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos ℓ) (Nat.two_pow_pos ℓ))
    (Nat.mul_pos (by norm_num) h)

/-- A nonzero-dimensional retained factor gives a nonzero-dimensional flagged two-key register. -/
instance instNeZeroKeyedFlagOutDim (ℓ Dinner : ℕ) [NeZero Dinner] :
    NeZero (keyedFlagOutDim ℓ Dinner) :=
  ⟨(keyedFlagOutDim_pos (NeZero.pos Dinner)).ne'⟩

/-- Enlarging the retained factor on the right multiplies the register dimension:
`keyedFlagOutDim ℓ (D · E) = keyedFlagOutDim ℓ D · E`. -/
theorem keyedFlagOutDim_mul_right (ℓ D E : ℕ) :
    keyedFlagOutDim ℓ (D * E) = keyedFlagOutDim ℓ D * E := by
  simp only [keyedFlagOutDim]; ring

/-! ## The two-party signal register -/

/-- The joint signal register of two `2 ^ n`-dimensional laboratories is
nonzero-dimensional. -/
instance instNeZeroSignalPairDim (n : ℕ) : NeZero (2 ^ n * 2 ^ n) :=
  ⟨(Nat.mul_pos (Nat.two_pow_pos n) (Nat.two_pow_pos n)).ne'⟩

end QKD
