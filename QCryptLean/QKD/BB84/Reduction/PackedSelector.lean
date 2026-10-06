import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.Engine.EntropyFloor.SiftedRoundFactorizationReferee

-- The single over-long line in this file is the import path of the parametric selector cell
-- above; it is one unbreakable module name.  No prose or expression line is over budget.

/-!
# The packed key/Z-test/X-test selector meets the parametric interface

The measure-first experiment keeps `nK + mZ + mX` sifted rounds and assigns them the three roles
**in that order**: the first `nK` are key rounds, the next `mZ` are Z-basis test rounds and the
last `mX` are X-basis test rounds.  `Sampling.packedPESel` is the resulting
parameter-estimation mask (`true` on a test round) and `Sampling.packedXSel` the X-test mask.

The retained general-`m` analysis of `QCryptLean.QKD.BB84.SelectionData` instead
identifies test rounds through a *sorted* coordinate `bb84PERoundIdx`, and its key-round count
`bb84KeyRoundCount n m = n - m` is stated for an abstract selector.  This module is the
arithmetic dictionary between the two presentations:

* `packedPESel_keyCount` — the packed mask really has `n - m` key rounds, so the parametric
  count hypothesis `bb84KeyCount` holds here rather than being assumed;
* `packedZTestSampleSize`, `packedXTestSampleSize` — the two realised test-block sizes are `mZ` and
  `mX`, which is what the finite-key budgets read as their sample sizes.

No quota equality `mZ = mX` is assumed anywhere, and nothing here is a physical or security claim:
these are finite `ℕ`-arithmetic and `Fin`-indexing facts about the explicit packed mask.
-/

noncomputable section

namespace QKD.BB84.Reduction
open TypedLOCC

open QKD.BB84.Engine

/-- The packed Z-key/Z-test/X-test mask has exactly the required parametric key count.

This is the finite threshold count for the explicit packed selector; no equality between the Z
and X test quotas is assumed. -/
theorem packedPESel_keyCount (nK mZ mX : ℕ) :
    QKD.BB84.Engine.bb84KeyCount
      (nK + mZ + mX) (mZ + mX)
      (@Sampling.packedPESel nK mZ mX) := by
  change Fintype.card {i : Fin (nK + mZ + mX) // Sampling.packedPESel i = false} = _
  rw [Sampling.card_packedPESel_eq_false]
  simp only [bb84KeyRoundCount]
  omega

/-- The Z-test block of the packed selector has cardinality `mZ`. -/
theorem packedZTestSampleSize (nK mZ mX : ℕ) :
    bb84SiftedZTestSampleSize
      (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX) = mZ := by
  classical
  let e : Fin mZ ≃
      {i : Fin (nK + mZ + mX) //
        Sampling.packedPESel i = true ∧ Sampling.packedXSel i = false} := {
    toFun z := ⟨⟨nK + z.val, by omega⟩, by
      simp [Sampling.packedPESel, Sampling.packedXSel]
      ⟩
    invFun i := ⟨i.1.val - nK, by
      have hlo : nK ≤ i.1.val := by
        simpa [Sampling.packedPESel] using i.2.1
      have hhi : ¬nK + mZ ≤ i.1.val := by
        simpa [Sampling.packedXSel] using i.2.2
      omega⟩
    left_inv z := by
      apply Fin.ext
      simp
    right_inv i := by
      apply Subtype.ext
      apply Fin.ext
      have hlo : nK ≤ i.1.val := by
        simpa [Sampling.packedPESel] using i.2.1
      simp
      omega }
  unfold bb84SiftedZTestSampleSize
  rw [← Fintype.card_subtype]
  calc
    _ = Fintype.card (Fin mZ) := Fintype.card_congr e.symm
    _ = mZ := Fintype.card_fin mZ

/-- The X-test block of the packed selector has cardinality `mX`. -/
theorem packedXTestSampleSize (nK mZ mX : ℕ) :
    bb84SiftedXTestSampleSize
      (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX) = mX := by
  classical
  let e : Fin mX ≃
      {i : Fin (nK + mZ + mX) //
        Sampling.packedPESel i = true ∧ Sampling.packedXSel i = true} := {
    toFun x := ⟨⟨nK + mZ + x.val, by omega⟩, by
      simp [Sampling.packedPESel, Sampling.packedXSel]
      omega⟩
    invFun i := ⟨i.1.val - (nK + mZ), by
      have hlo : nK + mZ ≤ i.1.val := by
        simpa [Sampling.packedXSel] using i.2.2
      omega⟩
    left_inv x := by
      apply Fin.ext
      simp
    right_inv i := by
      apply Subtype.ext
      apply Fin.ext
      have hlo : nK + mZ ≤ i.1.val := by
        simpa [Sampling.packedXSel] using i.2.2
      simp
      omega }
  unfold bb84SiftedXTestSampleSize
  rw [← Fintype.card_subtype]
  calc
    _ = Fintype.card (Fin mX) := Fintype.card_congr e.symm
    _ = mX := Fintype.card_fin mX

end QKD.BB84.Reduction
