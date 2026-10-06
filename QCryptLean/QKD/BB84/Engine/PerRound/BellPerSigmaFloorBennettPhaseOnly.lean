/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.EntropyFloor.BellFloorChain
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledPerSigmaFloor
import QCryptLean.QKD.BB84.Engine.Postselection.BellReduction
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.PhaseOnlyPivot

/-!
# The `bellWembed`-pullback of the Bell phase-only good set

The `φ ↦ Tr_B (Wembed φ)`-pullback of the phase-only good-rate set `goodRateSetPhaseOnly Q (2δ)`
is closed and measurable — the Carathéodory input the finite decomposition
`integralRestrict_eq_finite_subConvexCombination` needs at the migrated pivot.

`goodRateSet Q δ ⊆ goodRateSetPhaseOnly Q δ`, strictly: the good set grows under the migration
from `goodRateSet Q (2δ)` to `goodRateSetPhaseOnly Q (2δ)` (`PhaseOnlyPivot.lean`), which is the
burden the phase-only pivot moves onto the good branch.

## Main results

- `QKD.BB84.Engine.bb84_bell_goodPreimagePhaseOnly_isClosed`
- `QKD.BB84.Engine.bb84_bell_goodPreimagePhaseOnly_measurableSet`

## Relation to the literature

The phase-only restriction is **not** in the cited literature.  Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand *each* small — the ancestor of the phase-only conjunction, not authority for
dropping the bit ball.  What licenses it here is
`QKD.BB84.Engine.bb84ComponentAliceZRate_ge_phaseOnly_of_good`.

References: Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`),
`\label{lem:rtbound}` (`main.tex:10487`), §3.1, §6.5; Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`), `\label{lem:groupPurification}`
(`main.tex:354`), `\label{eq:boundingsmoothedmin}` (`main.tex:1380`), `\label{eq:splittingoffV}`
(`main.tex:1393`), §V.C (`main.tex:909`, `:913`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- The pullback of a closed good-rate set under `φ ↦ Tr_B (Wembed φ)` is closed: the continuity
half of `bb84_bell_goodPreimagePhaseOnly_isClosed`, with the good set abstract. -/
lemma bb84_bell_goodPreimage_isClosed_ofClosed {B : Set (DensityOp signalDim)}
    (hB : IsClosed B) :
    IsClosed ((fun φ : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ)) ⁻¹' B) := by
  have hbell : Continuous (fun φ : DensityOp 4 => bellWembed φ) := by
    rw [continuous_induced_rng]
    exact (continuous_const.matrix_mul continuous_induced_dom).matrix_mul continuous_const
  exact hB.preimage (InfoTheory.DeFinetti.partialTraceB_continuous_general.comp hbell)

/-- The `φ ↦ Tr_B (Wembed φ)`-pullback of the PHASE-ONLY good-rate set is closed.

`goodRateSetPhaseOnly` is a single `≤`-sublevel set of the continuous
`phaseFlipErrorRate_single ∘ componentAliceBobMarginal`, hence closed, and both
`bellWembed` and `DensityOp.partialTraceB` are continuous.

This is the Carathéodory input of the finite decomposition
`integralRestrict_eq_finite_subConvexCombination` at the migrated pivot; the un-doubled analogue is
`bb84_pairedHaar_goodSetPhaseOnly_isClosed` (`PhaseOnlyPivot.lean`). -/
lemma bb84_bell_goodPreimagePhaseOnly_isClosed (Q δ : ℝ) :
    IsClosed ((fun φ : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ)) ⁻¹'
      (goodRateSetPhaseOnly Q (2 * δ))) := by
  have hphase : Continuous (fun σ : DensityOp signalDim =>
      phaseFlipErrorRate_single (componentAliceBobMarginal σ)) :=
    phaseFlipErrorRate_single_continuous.comp componentAliceBobMarginal_continuous
  exact bb84_bell_goodPreimage_isClosed_ofClosed (isClosed_le hphase continuous_const)

/-- The Bell phase-only good-preimage set is measurable. -/
lemma bb84_bell_goodPreimagePhaseOnly_measurableSet (Q δ : ℝ) :
    MeasurableSet ((fun φ : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ)) ⁻¹'
      (goodRateSetPhaseOnly Q (2 * δ))) :=
  (bb84_bell_goodPreimagePhaseOnly_isClosed Q δ).measurableSet

/-- The Bell phase-only good-preimage set at a free phase-error deviation is measurable.

The window/deviation split: the accept-test **window** stays `δ` (it fixes the accept masses), while
the **deviation** `dev` sets the pivot
`goodRateSetPhaseOnly Q (δ + dev)` whose preimage feeds the Dev Bell accept split.  The incumbent
`2δ` form (`bb84_bell_goodPreimagePhaseOnly_measurableSet`) is the case `dev = δ`; the proof is the
same sublevel-set closedness, since `goodRateSetPhaseOnly Q (δ + dev)` is a `≤`-sublevel set of
the same continuous phase rate. -/
lemma bb84_bell_goodPreimagePhaseOnly_measurableSetDev (Q δ dev : ℝ) :
    MeasurableSet ((fun φ : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ)) ⁻¹'
      (goodRateSetPhaseOnly Q (δ + dev))) := by
  have hphase : Continuous (fun σ : DensityOp signalDim =>
      phaseFlipErrorRate_single (componentAliceBobMarginal σ)) :=
    phaseFlipErrorRate_single_continuous.comp componentAliceBobMarginal_continuous
  exact (bb84_bell_goodPreimage_isClosed_ofClosed
    (isClosed_le hphase continuous_const)).measurableSet

end QKD.BB84.Engine

end -- noncomputable section
