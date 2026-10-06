import QCryptLean.Quantum.Symmetry.SignalPermutation
import QCryptLean.QKD.BB84.Model.AttackIntegrability
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Mixture
import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity
import QCryptLean.Quantum.Symmetry.AttackSymmetrization
import QCryptLean.InfoTheory.DeFinetti.Theorem.UnequalInterleaving
import QCryptLean.InfoTheory.QuantumLHL.Main
import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyExtractor
import QCryptLean.InfoTheory.QuantumLHL.SeedKeySmoothing
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired

/-!
# The good-rate set for parameter estimation

The set of de Finetti components whose per-component bit- and phase-flip error rates both lie
within the PE acceptance window.

## Main definitions

* `componentAliceBobMarginal` — the per-component single-round Alice–Bob marginal classifier
  (the identity on the component); moved here from
  `QKD.BB84.Engine.ParameterEstimation.PEConcentration` because it is the model math `goodRateSet`
  is stated on, not Engine-specific analysis (its continuity/measurability lemmas stay in
  `PEConcentration`, which now imports this module for the definition).
* `goodRateSet` — de Finetti components with acceptable induced bit and phase error rates.

## References

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024, Lemma 9 Eq. 44.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open InfoTheory.QuantumLHL InfoTheory.SmoothMinEntropy
open Math.ClassicalEntropy
open Quantum.Symmetry
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace QKD.BB84.Model

/-- The per-IID-component single-round Alice–Bob marginal of a de Finetti
component `σ` under the per-round PE POVM (Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024,
arXiv:2403.11851, Lemma 9 Eq.44).

For a single-round BB84 de Finetti component `σ : DensityOp signalDim`, the
per-round PE POVM `{Γⱼ}` (the Bell-basis bit-flip and phase-flip projectors) acts
on the single round, so the component's *own* Alice–Bob marginal against which the
per-round Born statistic `Tr(Γⱼ σ)` is measured is `σ` itself.  This is an
attack-independent per-component classifier: a covariant
mixture can carry a bad *average* while every per-component statistic stays good,
so the PE classifier must be keyed to the per-component marginal, not the average.

Explicit definition (the identity on the component), no `Classical.choose`. -/
def componentAliceBobMarginal (σ : DensityOp signalDim) : DensityOp signalDim :=
  σ

@[simp] theorem componentAliceBobMarginal_eq (σ : DensityOp signalDim) :
    componentAliceBobMarginal σ = σ := rfl

/-- The "good σ" set for PE parameters `Q, δ`:
the set of de Finetti components whose **per-component** single-round marginal
`componentAliceBobMarginal σ` (Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024, Lemma 9 Eq.44 — the
component's own Alice–Bob marginal against which the per-round Born statistic `Tr(Γⱼ σ)` is
measured) has bit-flip and phase-flip error rates both ≤ Q + δ.

The classifier is keyed to the **per-component** marginal, not to any attack-averaged
first-round marginal: a covariant mixture (apply `X^{⊗n}` w.p. `f`, identity
otherwise) can carry a bad average while every per-component statistic stays good,
so the average-keyed classifier fails for the clean-majority covariant mixture.
The membership predicate therefore mentions no attack object and no block length. -/
def goodRateSet
    (Q δ : ℝ) :
    Set (DensityOp signalDim) :=
  {σ |
    bitFlipErrorRate_single (componentAliceBobMarginal σ) ≤ Q + δ ∧
    phaseFlipErrorRate_single (componentAliceBobMarginal σ) ≤ Q + δ}

end QKD.BB84.Model

end -- noncomputable section
