import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Mixed
import QCryptLean.InfoTheory.DeFinetti.Theorem.TensorPowerPushforward

/-!
# CKR Hilbert-Schmidt mixture representation

This module packages the CKR reference state as a de Finetti tensor-power
mixture.  The measure is the `Tr_B` pushforward of the pure-state Haar measure
on `d*d`-dimensional purifications.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The CKR de Finetti measure on `DensityOp d`: `Tr_B` pushforward of the pure-state
Haar measure on `d*d`-dimensional purifications. The defining equality
`integralTensorPower n (ckrMixtureMeasure d) = ckrDeFinettiState d n` is
`integralTensorPower_ckrMixtureMeasure_eq`. -/
noncomputable def ckrMixtureMeasure (d : ℕ) [NeZero d] : DensityMeasure d :=
  partialTraceBDensityMeasure (deFinetti_haarMeasure (d * d))

/-- The integral of tensor powers against `ckrMixtureMeasure` recovers the CKR
de Finetti reference state. -/
theorem integralTensorPower_ckrMixtureMeasure_eq
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    integralTensorPower n (ckrMixtureMeasure d) = ckrDeFinettiState d n := by
  haveI : NeZero ((d * d) ^ n) := ⟨pow_ne_zero n (NeZero.ne (d * d))⟩
  unfold ckrMixtureMeasure
  calc
    integralTensorPower n (partialTraceBDensityMeasure (deFinetti_haarMeasure (d * d)))
        = DensityOp.partialTraceB
            (densityOp_reindex (interleavingEquiv d n).symm
              (integralTensorPower n (deFinetti_haarMeasure (d * d)))) :=
            integralTensorPower_partialTraceBDensityMeasure (d := d) (k := n)
              (deFinetti_haarMeasure (d * d))
    _ = ckrDeFinettiState d n := by
      rw [← pairedDeFinettiState_eq_haar_integral_paired (d := d) (n := n)]
      rfl

/-- The CKR Hilbert-Schmidt reference state is a mixture of tensor powers of
single-system density operators. -/
theorem exists_densityMeasure_integralTensorPower_eq_ckrDeFinettiState
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)] :
    ∃ μ : DensityMeasure d,
      integralTensorPower n μ = ckrDeFinettiState d n :=
  ⟨ckrMixtureMeasure d, integralTensorPower_ckrMixtureMeasure_eq d n⟩

end Quantum.Channels

end
