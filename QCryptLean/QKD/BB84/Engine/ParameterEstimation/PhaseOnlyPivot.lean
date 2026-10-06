/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledPerSigmaFamily

/-!
# The phase-only pivot set and the `hmXZ`-free accept split

A split-test bad-branch bound quantified over `goodRateSet` carries a hypothesis
`hmXZ : m_X ≤ m_Z`: the pivot set `goodRateSet` is a **conjunction** of a bit-error ball and a
phase-error ball, so its complement is a **disjunction**, and a bit-bad component is caught only
by the Z-subsample, whose exponent is `m_Z`-shaped; `hmXZ` weakens that down to the single
`m_X`-shaped conclusion.

This module replaces the pivot set by the phase ball alone.  The bit arm of the disjunction then
does not exist, the exponent is `m_X` outright, and `hmXZ` is not needed.

## Direction of the change

`goodRateSet Q δ ⊆ goodRateSetPhaseOnly Q δ`, so the good set grows and the bad set shrinks.  The
bad branch then integrates a nonnegative integrand over a smaller domain, so the tail side is
strictly easier; the burden that moves is the good branch, where the entropy floor must hold on
the larger set — it does, since `bb84ComponentAliceZRate_ge_phaseOnly_of_good` binds only
`hbound : Q + 2δ ≤ 1/2` and the phase bound.

## Relation to the literature

No paper in the cited literature runs a phase-only pivot set.  Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand each small — that is the ancestor of the two-basis **conjunction**, not
authority for dropping the bit ball.  Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(arXiv:2403.11851, `main.tex` §V.C, App. B, Lemma 9 Eq. 44) supply the per-component
accept-mass bound the rungs below cite.  The comparator
(arXiv:2311.01600, `adaptivepaper.tex:206`, `:537` `\label{eq:acceptancetest}`, `:642`
`\label{eq:confinterval}`, `:1320` `\label{lemma:concentration}`) runs one statistic on all `m`
test rounds and carries the full `m` in its exponent, never a per-basis `min`.  The phase-only
pivot set here is our own, not transcribed from a source.

## Main definitions

- `QKD.BB84.Engine.goodRateSetPhaseOnly`: `goodRateSet` with the bit-error conjunct deleted.

## Main results

- `QKD.BB84.Engine.goodRateSetPhaseOnly_compl_phaseRate_lt`: complement membership yields a single
  inequality, not a disjunction.
- `QKD.BB84.Engine.goodRateSet_subset_goodRateSetPhaseOnly` /
  `QKD.BB84.Engine.goodRateSetPhaseOnly_compl_subset_goodRateSet_compl`: the inclusion.
- `QKD.BB84.Engine.bb84_pairedHaar_goodSetPhaseOnly_isClosed`: the Carathéodory input for the
  migrated pivot set.
- `QKD.BB84.Engine.bb84_onComponent_localPhaseBad_le_klChernoff_exact`: the per-σ bad-branch bound
  at the exact KL-Chernoff exponent, without `hmXZ`.

## Window and deviation

The `Dev` twins (`bb84_pairedHaar_goodSetPhaseOnly_isClosedDev`,
`bb84_onComponent_localPhaseBad_le_klChernoff_exactDev`) free the phase-error **deviation** `dev`
from the accept-test **window** `δ`: the pivot reads `goodRateSetPhaseOnly Q (δ + dev)` and the
KL-Chernoff exponent edge is `klBer (Q+δ) (Q+δ+dev)`, while the accept probability stays keyed to
the window `δ`.  The `2δ` forms in the Main results list are the case `dev = δ` (the window
half-width charged twice, once as window and once as deviation).  Reference: Nahar et al. 2024
(arXiv:2403.11851) Lemma 9 Eq. 44, §V.C.
-/

-- The paired-Haar per-σ family wiring states Bochner integrability of `Op`-valued block maps;
-- as in `AcceptSplit.lean` / `PerSigmaFamily.lean`, this uses the Frobenius norm.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## 1. The phase-only pivot set -/

/-- **The phase-only good-rate set.**

`goodRateSet Q δ` (`ProtocolChannelsPair/Basic/Core.lean`) with the `bitFlipErrorRate_single`
conjunct deleted: the de Finetti components whose per-component single-round marginal
`componentAliceBobMarginal σ` has phase-flip error rate `≤ Q + δ`, with no constraint on the
bit-flip rate.

Keyed to the **per-component** marginal for the same reason as `goodRateSet`: a covariant mixture
(apply `X^{⊗n}` w.p. `f`, identity otherwise) carries a bad average while every per-component
statistic stays good, so an average-keyed classifier fails for the clean-majority covariant
mixture.  The membership predicate mentions no attack object and no block length.

This is a larger set than `goodRateSet Q δ` (`goodRateSet_subset_goodRateSetPhaseOnly`), and the
inclusion is strict.  `bitFlipProjector = |β₀₁⟩⟨β₀₁| + |β₁₁⟩⟨β₁₁|` and `phaseFlipProjector =
|β₁₀⟩⟨β₁₀| + |β₁₁⟩⟨β₁₁|` (`QCryptLean/QKD/BB84/Engine/ErrorModel.lean`), so the Bell
component `|β₀₁⟩⟨β₀₁|` has bit-flip rate `1` and phase-flip rate `0`: it lies in
`goodRateSetPhaseOnly 0 0` and not in `goodRateSet 0 0`.  On components whose two rates coincide,
the two sets agree; the honest pair is one of them (`bb84HonestPauliChannel`: bit and phase flips
each with probability `Q`, never both).  The enlargement bites exactly on the bit-heavy components
that the standard row's entropy floor never reads.

Reference for the per-component statistic: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(arXiv:2403.11851) Lemma 9 Eq. 44.  The phase-only restriction itself is not from the literature —
see the module docstring. -/
def goodRateSetPhaseOnly
    (Q δ : ℝ) :
    Set (DensityOp signalDim) :=
  {σ | phaseFlipErrorRate_single (componentAliceBobMarginal σ) ≤ Q + δ}

/-- Measurability of the phase-only good-rate set. -/
theorem goodRateSetPhaseOnly_measurableSet
    (Q δ : ℝ) :
    MeasurableSet (goodRateSetPhaseOnly Q δ) := by
  simpa [goodRateSetPhaseOnly] using
    ((phaseFlipErrorRate_single_measurable.comp
        componentAliceBobMarginal_measurable).le' measurable_const)

/-- **Outside `goodRateSetPhaseOnly`, the phase-flip rate exceeds `Q + δ`.**

This is a *single* inequality, not a disjunction of a bit- and a phase-error bound — which is
why `hmXZ` is absent from every rung below. -/
theorem goodRateSetPhaseOnly_compl_phaseRate_lt
    (Q δ : ℝ) {σ : DensityOp signalDim}
    (hσ : σ ∈ (goodRateSetPhaseOnly Q δ)ᶜ) :
    Q + δ < phaseFlipErrorRate_single (componentAliceBobMarginal σ) := by
  have hnot : ¬ (phaseFlipErrorRate_single (componentAliceBobMarginal σ) ≤ Q + δ) := by
    simpa [goodRateSetPhaseOnly] using hσ
  exact lt_of_not_ge hnot

/-- **The good set grows**: `goodRateSet Q δ ⊆ goodRateSetPhaseOnly Q δ`, by projecting the
conjunction onto its phase component.

No `0 ≤ δ` side condition is needed: the two sets are taken at the same margin and the inclusion
is a projection, not a threshold comparison. -/
theorem goodRateSet_subset_goodRateSetPhaseOnly
    (Q δ : ℝ) :
    goodRateSet Q δ ⊆ goodRateSetPhaseOnly Q δ := fun _ hσ => hσ.2

/-- **The bad set shrinks**: `(goodRateSetPhaseOnly Q δ)ᶜ ⊆ (goodRateSet Q δ)ᶜ`.

Complement direction of `goodRateSet_subset_goodRateSetPhaseOnly`. -/
theorem goodRateSetPhaseOnly_compl_subset_goodRateSet_compl
    (Q δ : ℝ) :
    (goodRateSetPhaseOnly Q δ)ᶜ ⊆ (goodRateSet Q δ)ᶜ :=
  Set.compl_subset_compl.mpr (goodRateSet_subset_goodRateSetPhaseOnly Q δ)

/-! ## 1b. Strictness of the inclusion -/

/-- The `Tr_B`-pullback of the phase-only good-rate set at the deviation-scoped radius `δ + dev` —
the Carathéodory input of the floor chain at the free phase-error deviation (the window `δ` stays
the protocol's; only the deviation moves).  The `2δ` form
`bb84_pairedHaar_goodSetPhaseOnly_isClosed` is the special case `dev = δ`. -/
theorem bb84_pairedHaar_goodSetPhaseOnly_isClosedDev (Q δ dev : ℝ) :
    IsClosed ((DensityOp.partialTraceB :
        DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
      (goodRateSetPhaseOnly Q (δ + dev))) := by
  have hphase : Continuous (fun σ : DensityOp signalDim =>
      phaseFlipErrorRate_single (componentAliceBobMarginal σ)) :=
    phaseFlipErrorRate_single_continuous.comp componentAliceBobMarginal_continuous
  have hgood : IsClosed (goodRateSetPhaseOnly Q (δ + dev)) := isClosed_le hphase continuous_const
  exact hgood.preimage InfoTheory.DeFinetti.partialTraceB_continuous_general

/-- The `Tr_B`-pullback of the phase-only good-rate set is closed — the Carathéodory input of the
finite decomposition `integralRestrict_eq_finite_subConvexCombination`, at the migrated pivot set.

`goodRateSetPhaseOnly` is a single `≤`-sublevel set of the continuous
`phaseFlipErrorRate_single ∘ componentAliceBobMarginal`, hence closed, and
`DensityOp.partialTraceB` is continuous. -/
theorem bb84_pairedHaar_goodSetPhaseOnly_isClosed (Q δ : ℝ) :
    IsClosed ((DensityOp.partialTraceB :
        DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
      (goodRateSetPhaseOnly Q (2 * δ))) := by
  rw [show (2:ℝ) * δ = δ + δ from by ring]
  exact bb84_pairedHaar_goodSetPhaseOnly_isClosedDev Q δ δ

/-! ## 2. The per-arm bad-branch concentration, without `hmXZ` -/

/-- **The exact-KL-exponent bad-branch bound on the phase-only pivot at a free deviation, without
`hmXZ`.**

The window/deviation split of `klAcceptTailPhaseOnlyDev` (`KLAcceptTailPhaseOnlyGeneral.lean`):
the accept-test **window** stays `δ` (the pass threshold `Q + δ` of
`bb84_siftedLocal_le_phaseBinomialPassSum`), while the **deviation** `dev` sets the pivot edge
`Q + δ + dev` and hence the KL exponent edge.  The `2δ` form
(`bb84_onComponent_localPhaseBad_le_klChernoff_exact`) is the case `dev = δ`.

Only the positive deviation is needed, through the pivot edge `Q + δ < Q + δ + dev`.

References: Renner (2005) §5; Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851)
Lemma 9 Eq. 44. -/
theorem bb84_onComponent_localPhaseBad_le_klChernoff_exactDev
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ) (hdev : 0 < dev)
    (σ : DensityOp signalDim) (hσ : σ ∈ (goodRateSetPhaseOnly Q (δ + dev))ᶜ) :
    bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ ≤
      Real.exp (-(bb84SiftedXTestSampleSize peSel xSel : ℝ) *
        Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev)) := by
  classical
  have hQedge : Q + δ < Q + δ + dev := by linarith
  have hphase := goodRateSetPhaseOnly_compl_phaseRate_lt Q (δ + dev) hσ
  rw [componentAliceBobMarginal_eq] at hphase
  -- `Q + (δ + dev)` is `Q + δ + dev` up to association, not definitionally.
  have hphase' : Q + δ + dev < phaseFlipErrorRate_single σ := by linarith
  have hbounds := phaseFlipErrorRate_single_bounds σ
  refine (bb84_siftedLocal_le_phaseBinomialPassSum peSel xSel Q δ σ).trans ?_
  exact Math.Concentration.BinomialKLChernoff.binomialPassSum_le_klChernoff
    (bb84SiftedXTestSampleSize peSel xSel) Q δ (Q + δ + dev) (phaseFlipErrorRate_single σ)
    hQedge hphase'.le hbounds.1 hbounds.2 (lt_of_lt_of_le hphase' hbounds.2)

/-- **The exact-KL-exponent bad-branch bound on the phase-only pivot, without `hmXZ`.**

Conclusion `exp(−m_X · klBer (Q+δ) (Q+2δ))`: with the bit branch gone, the exact-KL exponent is
exactly what `binomialPassSum_le_klChernoff` returns on the X-subsample, with no `m_Z → m_X`
weakening step needed.

The positive window supplies the deviation between `Q + δ` and `Q + 2δ`.

References: Renner (2005) §5; Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851)
Lemma 9 Eq. 44. -/
theorem bb84_onComponent_localPhaseBad_le_klChernoff_exact
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hδ : 0 < δ)
    (σ : DensityOp signalDim) (hσ : σ ∈ (goodRateSetPhaseOnly Q (2 * δ))ᶜ) :
    bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ ≤
      Real.exp (-(bb84SiftedXTestSampleSize peSel xSel : ℝ) *
        Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + 2 * δ)) := by
  -- the Dev twin at `dev = δ`, with the `2δ` edges read back off the result
  have h := bb84_onComponent_localPhaseBad_le_klChernoff_exactDev (n := n) peSel xSel Q δ δ hδ
    σ (by rw [show (2:ℝ) * δ = δ + δ from by ring] at hσ; exact hσ)
  rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring] at h

/-! ## 3. The two halves of the accept split, at the phase-only pivot -/

end QKD.BB84.Engine

end -- noncomputable section
