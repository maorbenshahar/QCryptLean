import QCryptLean.InfoTheory.DeFinetti.FullRank
import QCryptLean.InfoTheory.DeFinetti.Support
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Mixture

/-!
# CKR Full Rank — open-positive support, positive definiteness, rank of the de Finetti state

This module connects the general open-positive full-rank theorem for
tensor-power de Finetti integrals to the CKR Hilbert-Schmidt mixture measure.

## Main definitions
- This file defines no new data structures.

## Main statements
- `ckrMixtureMeasure_isOpenPosMeasure`: the CKR mixture measure has open-positive support.
- `ckrDeFinettiState_toOp_posDef`: the CKR de Finetti state is positive definite.
- `Quantum.Channels.ckrDeFinettiState_rank_toOp_of_openPosIntegral`: the CKR de Finetti state has
full rank.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The CKR Hilbert-Schmidt mixture measure has open-positive support on density operators. -/
theorem ckrMixtureMeasure_isOpenPosMeasure
    (d : ℕ) [NeZero d] :
    (ckrMixtureMeasure d).measure.IsOpenPosMeasure := by
  haveI : NeZero (d * d) := ⟨mul_ne_zero (NeZero.ne d) (NeZero.ne d)⟩
  unfold ckrMixtureMeasure
  exact InfoTheory.DeFinetti.partialTraceBDensityMeasure_deFinetti_haarMeasure_isOpenPos d

/-- The CKR de Finetti state is positive definite, via the open-positive
tensor-power integral. -/
theorem ckrDeFinettiState_toOp_posDef
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    (ckrDeFinettiState d n).toOp.PosDef := by
  have hμ_open : (ckrMixtureMeasure d).measure.IsOpenPosMeasure :=
    ckrMixtureMeasure_isOpenPosMeasure d
  have hμ_pd :
      (integralTensorPower n (ckrMixtureMeasure d)).toOp.PosDef :=
    InfoTheory.DeFinetti.integralTensorPower_toOp_posDef_of_isOpenPosMeasure
      (n := n) (ckrMixtureMeasure d) hμ_open
  simpa [integralTensorPower_ckrMixtureMeasure_eq d n] using hμ_pd

/-- The CKR de Finetti state has full rank, via the open-positive tensor-power integral. -/
theorem ckrDeFinettiState_rank_toOp_of_openPosIntegral
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    Matrix.rank (ckrDeFinettiState d n).toOp = d ^ n := by
  have hμ_open : (ckrMixtureMeasure d).measure.IsOpenPosMeasure :=
    ckrMixtureMeasure_isOpenPosMeasure d
  have hμ_rank :
      Matrix.rank (integralTensorPower n (ckrMixtureMeasure d)).toOp = d ^ n :=
    InfoTheory.DeFinetti.integralTensorPower_rank_toOp_eq_full_of_isOpenPosMeasure
      (n := n) (ckrMixtureMeasure d) hμ_open
  simpa [integralTensorPower_ckrMixtureMeasure_eq d n] using hμ_rank

end Quantum.Channels

end
