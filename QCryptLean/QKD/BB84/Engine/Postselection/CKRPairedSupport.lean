import QCryptLean.QKD.BB84.Engine.EntropyFloor.PostMeasurementCQ
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired

/-!
# BB84 CKR paired support — polynomial dimension

The BB84 specialization of the generic paired-CKR rank bound: `bb84PolyDim` identified with the
paired symmetric-subspace dimension, giving a rank bound on the BB84 paired de Finetti state.

## Main results

* `bb84PolyDim_eq_ckr_paired_choose` — `bb84PolyDim n` in the parenthesization the generic
  paired CKR lemmas use.
* `bb84_pairedDeFinettiState_rank_le_polyDim` — the BB84 paired de Finetti state has rank at
  most `bb84PolyDim n`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Quantum.Metrics Math.ClassicalEntropy
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-- The BB84 polynomial dimension in the parenthesization used by the generic
paired CKR lemmas. -/
lemma bb84PolyDim_eq_ckr_paired_choose (n : ℕ) :
    bb84PolyDim n =
      Nat.choose (n + (signalDim ^ 2 - 1)) (signalDim ^ 2 - 1) := by
  rfl

/-- The BB84 paired de Finetti state has rank at most `bb84PolyDim n`. -/
lemma bb84_pairedDeFinettiState_rank_le_polyDim
    (n : ℕ) [NeZero n] :
    Matrix.rank (pairedDeFinettiState signalDim n).toOp ≤ bb84PolyDim n := by
  rw [bb84PolyDim_eq_ckr_paired_choose n]
  have h := pairedDeFinettiState_rank_le_polyDim signalDim n
  refine h.trans (le_of_eq ?_)
  norm_num

end QKD.BB84.Engine

end -- noncomputable section
