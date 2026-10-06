import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.Quantum.Symmetry.Covariance
import QCryptLean.Quantum.Channels.CPTP.CKRBound.CovarianceBundles
import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.InfoTheory.DeFinetti.Measure
import QCryptLean.Math.Concentration.Serfling
import QCryptLean.Math.Probability.SamplingConcentration
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.TensorProducts.ProjectiveConditioning

/-!
# The per-component single-round Alice–Bob marginal for BB84 parameter estimation

The parameter-estimation classifier of Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024,
arXiv:2403.11851, Lemma 9 Eq. 44) is keyed to the per-IID-component Born statistic `Tr(Γⱼ σ)`,
where `σ` is a de Finetti component's *own* single-round Alice–Bob state and `Γⱼ` is the per-round
PE POVM element — not an attack-averaged marginal.  A covariant mixture can carry a bad average
while every per-component statistic stays good, so the classifier must be keyed to the
per-component marginal.

In the BB84 instantiation a de Finetti component `σ` is already the single-round Alice–Bob signal
state on `DensityOp signalDim`, and the per-round PE POVM elements are the Bell-basis bit-flip and
phase-flip projectors, so the component's own marginal under the PE POVM is `σ` itself.

## Main definitions

- `QKD.BB84.Model.componentAliceBobMarginal` (moved to
  `QKD.BB84.Model.ProtocolPair`, imported here): the per-component single-round Alice–Bob marginal
  classifier (the identity on the component). It lives with the model math `goodRateSet` is stated
  on, not in the Engine analysis layer; only its continuity/measurability proofs stay here.

## Main results

- `QKD.BB84.Engine.componentAliceBobMarginal_continuous`,
  `QKD.BB84.Engine.componentAliceBobMarginal_measurable`: continuity and measurability.
- `QKD.BB84.Engine.tensorPowGen_preChannel_continuous`: feeding a component's tensor power
  through a fixed linear map is continuous in the component.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851), Lemma 9 Eq. 44;
Renner 2005, §6.4.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.DeFinetti
open QKD.BB84.Engine
open QKD.BB84.Model
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ComplexOrder ENNReal

noncomputable section

namespace QKD.BB84.Engine

/-- Feeding the tensor-power operator of a component through a fixed linear map is continuous
in the component.

Indexed by a bare retained-Eve dimension and an opaque pre-channel rather than by an attack
object; continuity is pure finite-dimensional linearity, so no CPTP hypothesis is needed. -/
lemma tensorPowGen_preChannel_continuous
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    {eveDim : ℕ} [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) :
    Continuous (fun σ : DensityOp signalDim => pre (σ.tensorPowGen n).toOp) :=
  pre.continuous_of_finiteDimensional.comp
    (InfoTheory.DeFinetti.continuous_tensorPowGen_toOp (d := signalDim) (n := n))

-- `componentAliceBobMarginal` now lives in `QKD.BB84.Model.ProtocolPair` (imported above): it is
-- the model math `goodRateSet` is stated on, not Engine-specific analysis. Only the
-- continuity/measurability proofs about it stay here.

/-- The per-component single-round marginal classifier is continuous. -/
lemma componentAliceBobMarginal_continuous :
    Continuous (componentAliceBobMarginal) := by
  simpa [componentAliceBobMarginal] using continuous_id

/-- The per-component single-round marginal classifier is measurable. -/
lemma componentAliceBobMarginal_measurable :
    Measurable (componentAliceBobMarginal) := by
  simpa [componentAliceBobMarginal] using measurable_id

open Math.Probability.SamplingConcentration Math.Concentration.Serfling

end QKD.BB84.Engine

end -- noncomputable section
