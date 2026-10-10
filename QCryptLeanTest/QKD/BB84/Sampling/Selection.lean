import QCryptLean.QKD.BB84.Sampling.Selection
import Mathlib.Util.AssertNoSorry

/-!
# BB84 fixed-quota selection test

This test retains the concrete zero-round, mismatch, and packed-mask probes and checks the
selector's core laws and definitions.
-/

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-! ## Definition-level probes -/

/-- With no rounds and zero quotas, the explicit selector succeeds. -/
theorem select_zero_isSome :
    (select 0 0 0 (defaultRawControl 0)).isSome = true := by
  simp [select, HasQuotas, zOrder, xOrder, matchedOrder]

/-- An explicit one-round Z/X mismatch has no available Z-key round. -/
def oneMismatchControl : RawControl 1 :=
  let a : Fin 1 → Basis := fun _ => Basis.z
  let b : Fin 1 → Basis := fun _ => Basis.x
  ⟨a, b, increasingShuffle a b⟩

/-- Requesting one key round from the explicit mismatch control aborts. -/
theorem select_oneMismatch_none :
    select 1 0 0 oneMismatchControl = none := by
  simp [select, HasQuotas, zOrder, matchedOrder, oneMismatchControl, Matched]

/-- Packed roles have masks `(false,false)`, `(true,false)`, and `(true,true)`. -/
theorem packed_masks_at_roles :
    (packedPESel (packedRoleEquiv 1 1 1 (Sum.inl (Sum.inl (0 : Fin 1)))),
        packedXSel (packedRoleEquiv 1 1 1 (Sum.inl (Sum.inl (0 : Fin 1))))) =
      (false, false) ∧
    (packedPESel (packedRoleEquiv 1 1 1 (Sum.inl (Sum.inr (0 : Fin 1)))),
        packedXSel (packedRoleEquiv 1 1 1 (Sum.inl (Sum.inr (0 : Fin 1))))) =
      (true, false) ∧
    (packedPESel (packedRoleEquiv 1 1 1 (Sum.inr (0 : Fin 1))),
        packedXSel (packedRoleEquiv 1 1 1 (Sum.inr (0 : Fin 1)))) =
      (true, true) := by
  decide

end QKD.BB84.Sampling

