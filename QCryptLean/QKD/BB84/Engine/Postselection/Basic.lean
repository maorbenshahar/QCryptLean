import QCryptLean.Quantum.Symmetry.Covariance
import QCryptLean.Quantum.Channels.CPTP.CKRBound.CovarianceBundles
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PostselectionBound
import QCryptLean.InfoTheory.VonNeumannEntropy.FannesInequality.PureState
import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.Engine.Budgets.SmoothEntropyBound
import QCryptLean.InfoTheory.QuantumLHL.Main
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeySmoothing
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PostMeasurementCQ

/-!
# The canonical BB84 CKR de Finetti purification

The canonical purification of the CKR (Christandl-König-Renner) de Finetti state used by the BB84
postselection reduction.

## Main definitions and results

* `bb84SymCKRDeFinettiPurification` — the canonical BB84 CKR de Finetti purification.
* `bb84SymCKRDeFinettiPurification_isPurification` — it is a CKR de Finetti purification: pure,
  with `signalDim ^ n` marginal `ckrDeFinettiState signalDim n`.

## References

Renner (2008) "Security of Quantum Key Distribution"; Christandl-König-Renner (2009)
"Postselection technique".
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Quantum.Symmetry InfoTheory.DeFinetti
open QKD.BB84.Engine InfoTheory.VonNeumannEntropy Math.ClassicalEntropy
open InfoTheory.SmoothMinEntropy
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

-- `ckr_security_reduction_exact` (CKR security reduction at the exact symmetric-subspace
-- dimension) lives in `QCryptLean.Quantum.Channels.CPTP.CKRBound.PostselectionBound`
-- (imported above; still under this namespace): it is channel-agnostic and carries no BB84
-- content.

/-- The canonical CKR de Finetti purification for BB84 postselection.

Concretely, `purificationDensityOp (ckrDeFinettiState signalDim n)`:
the square-root-vectorization purification of the CKR de Finetti state on
`Op (signalDim ^ n)`, living on `Op (signalDim ^ n * signalDim ^ n)`.
Its partial trace over the reference register recovers `ckrDeFinettiState signalDim n`. -/
noncomputable def bb84SymCKRDeFinettiPurification (n : ℕ) [NeZero n]
    [NeZero (signalDim ^ n)] :
    DensityOp ((signalDim ^ n) * (signalDim ^ n)) :=
  InfoTheory.DeFinetti.purificationDensityOp
    (Quantum.Channels.ckrDeFinettiState signalDim n)

/-- `bb84SymCKRDeFinettiPurification n` is a CKR de Finetti purification:
    it is pure and its `signalDim ^ n` marginal equals `ckrDeFinettiState signalDim n`. -/
theorem bb84SymCKRDeFinettiPurification_isPurification (n : ℕ) [NeZero n]
    [NeZero (signalDim ^ n)] :
    IsCKRDeFinettiPurification (bb84SymCKRDeFinettiPurification n) :=
  ⟨InfoTheory.DeFinetti.purificationDensityOp_isPure _,
   InfoTheory.DeFinetti.purificationDensityOp_partialTraceB _⟩

end QKD.BB84.Engine

end
