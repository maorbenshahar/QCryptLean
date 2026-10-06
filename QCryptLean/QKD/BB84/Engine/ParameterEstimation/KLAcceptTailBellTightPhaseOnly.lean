/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.KLAcceptTailBellTight
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.KLAcceptTailPhaseOnly
import QCryptLean.QKD.BB84.Engine.PerRound.BellPerSigmaFloorBennettPhaseOnly

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-!
# The Bell accept split at the phase-only pivot

The accept-tail interface of the Bell chain and its accept-split bad-branch bound, at the
phase-only pivot `(goodRateSetPhaseOnly Q (2δ))ᶜ` in place of `(goodRateSet Q (2δ))ᶜ`.

The free-deviation variants `IsBellSourceAcceptTailCapPhaseOnlyDev` and
`bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev` take the pivot at
`goodRateSetPhaseOnly Q (δ + dev)`: the accept-test **window** stays `δ` (protocol), while the
**deviation** `dev` sets the pivot the entropy floor is charged at (Nahar et al. 2024,
`arXiv:2403.11851`, Lemma 9 Eq. 44, §V.C); the `2δ` forms are the case `dev = δ`.

The interface is pointwise: it carries no measure, no Bochner integrability side condition and no
register width — it reads `bb84SiftedLocalAcceptProbabilityOnComponent` alone.
Since `goodRateSet Q r ⊆ goodRateSetPhaseOnly Q r`, the phase-bad complement is contained in
the two-error complement. A uniform cap on the two-error complement therefore restricts to
the phase-bad complement. Both halves of the accept split use the same phase-only pivot.

The identity `bb84UnitRegisterEmbed_localAcceptMass_eq_onComponent` holds for every component,
so the accepted mass equals the source mass on either phase-bad set.

## Relation to the literature

The phase-only pivot is not in the cited literature; it is licensed by
`QKD.BB84.Engine.bb84ComponentAliceZRate_ge_phaseOnly_of_good`.  Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand *each* small — the ancestor of the phase-only conjunction, not authority for
dropping the bit ball.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) App. B,
`\label{eq:tausplit}` (`main.tex:1356`–`:1361`) through `\label{eq:boundingsmoothedmin}`
(`main.tex:1380`–`:1387`), Lemma 9 Eq. 44; Renner 2005 (`arXiv:quant-ph/0512258v2`) §5, §6.5.
-/
/-! ## 1. The phase-only accept-tail interface of the Bell chain -/

/-- **The accept-tail interface of the Bell chain, at the phase-only pivot.**

`IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E` says the source accept mass of every
**phase**-rate-bad component is at most `E`.

The phase-bad complement is contained in the two-error complement, because
`goodRateSet Q (2 * δ) ⊆ goodRateSetPhaseOnly Q (2 * δ)`. A uniform source cap on the two-error
complement restricts to this interface with the same `E`.

The instance at the realised-X-subsample KL exponent is
`bb84_bellSourceAcceptTailCapPhaseOnly_klTailPhaseOnly` (`BellAcceptTailCapPhaseOnly.lean`).

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`), Lemma 9 Eq. 44; Renner 2005 (`arXiv:quant-ph/0512258v2`) §5, §6.5. -/
def IsBellSourceAcceptTailCapPhaseOnly {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ E : ℝ) : Prop :=
  ∀ σ : DensityOp signalDim, σ ∈ (goodRateSetPhaseOnly Q (2 * δ))ᶜ →
    bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ ≤ E

/-- **The Bell accept-tail interface at the phase-only pivot, at a free phase-error deviation.**

The window/deviation split: the accept-test **window** stays `δ` (it fixes the accept mass
`bb84SiftedLocalAcceptProbabilityOnComponent … Q δ …`), while the
**deviation** `dev` sets the bad set the cap is quantified over,
`(goodRateSetPhaseOnly Q (δ + dev))ᶜ`.  The `2δ` form
(`IsBellSourceAcceptTailCapPhaseOnly`) is the case `dev = δ`.  It is the hypothesis the Dev Bell
accept-split rung below consumes; the instance at the realised-X-subsample KL exponent is
`bb84_bellSourceAcceptTailCapPhaseOnly_klTailPhaseOnlyDev` (`BellAcceptTailCapPhaseOnly.lean`).

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, §V.C; Renner 2005
(`arXiv:quant-ph/0512258v2`) §5, §6.5. -/
def IsBellSourceAcceptTailCapPhaseOnlyDev {n : ℕ} (peSel xSel : Fin n → Bool)
    (Q δ dev E : ℝ) : Prop :=
  ∀ σ : DensityOp signalDim, σ ∈ (goodRateSetPhaseOnly Q (δ + dev))ᶜ →
    bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ ≤ E

/-- The `dev = δ` interface bridge `IsBellSourceAcceptTailCapPhaseOnly → …Dev`: at `dev = δ` the
two quantification domains agree after the `δ + δ = 2 * δ` rewrite (not defeq). -/
theorem isBellSourceAcceptTailCapPhaseOnlyDev_of_isBellSourceAcceptTailCapPhaseOnly
    {n : ℕ} {peSel xSel : Fin n → Bool} {Q δ E : ℝ}
    (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E) :
    IsBellSourceAcceptTailCapPhaseOnlyDev peSel xSel Q δ δ E := by
  intro σ hσ
  rw [show (δ : ℝ) + δ = 2 * δ from by ring] at hσ
  exact hCap σ hσ

/-! ## 2. The Bell accept split at the phase-only pivot -/

/-- **The Bell accept-split bad-branch bound at an abstract phase-only source cap, at a free
phase-error deviation.**

The accept-test window `δ` fixes the accept masses, while the deviation `dev` moves the
pivot to `goodRateSetPhaseOnly Q (δ + dev)` and hence the cap `hCap` and the bad branch.  The
`2δ` form (`bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCap`) is
the case `dev = δ`. The component accepted mass equals the source mass by
`bb84UnitRegisterEmbed_localAcceptMass_eq_onComponent`, so the phase-bad half costs `E`.

References: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, App. B
`\label{eq:tausplit}` (`main.tex:1356`–`:1361`); Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ)
    (E : ℝ) (hE0 : 0 ≤ E) (hCap : IsBellSourceAcceptTailCapPhaseOnlyDev peSel xSel Q δ dev E) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (1 * (signalDim ^ n)) =>
            ∫ φ in ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
                  (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
              ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
                  (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
                (bellWembed φ)).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure 4).measure :
            Op (1 * (signalDim ^ n))).trace).re
      ≤ E := by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hμP : MeasureTheory.IsProbabilityMeasure (deFinetti_haarMeasure 4).measure :=
    (deFinetti_haarMeasure 4).isProbability
  -- The `Sᶜ` pointwise cap at the ABSTRACT phase-only source cap, on the widened bad set.
  have hbadB : ∀ φ ∈ ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
        (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
      ∑ x : Fin n → Fin signalDim,
        ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
            peSel xSel Q δ
          (bellWembed φ)).stateMap x).toOp.trace.re ≤ E := by
    intro φ hφ
    have hσbad : DensityOp.partialTraceB (bellWembed φ) ∈
        (goodRateSetPhaseOnly Q (δ + dev))ᶜ := hφ
    rw [bb84_pairedHaarPerSigmaFamily_weightRe_eq_preLocalAcceptMass 1
      (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ (bellWembed φ)]
    rw [bb84UnitRegisterEmbed_localAcceptMass_eq_onComponent]
    exact hCap (DensityOp.partialTraceB (bellWembed φ)) hσbad
  have hbase := InfoTheory.SmoothMinEntropy.traceSetIntegral_le_of_pointwise_weight_bounds
    (f := fun φ : DensityOp 4 =>
      bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
          peSel xSel Q δ (bellWembed φ))
    (bb84_bellF_blocks_integrable peSel xSel Q δ)
    ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
      (goodRateSetPhaseOnly Q (δ + dev)))
    (bb84_bell_goodPreimagePhaseOnly_measurableSetDev Q δ dev)
    E hE0 hbadB
  linarith only [hbase]

/-- **The Bell accept-split bad-branch bound at an abstract phase-only source cap.**

The good set is the phase-only preimage
`S = (φ ↦ Tr_B (bellWembed φ))⁻¹'(goodRateSetPhaseOnly Q (2δ))`. If every phase-rate-bad
component’s source accept mass is at most `E`, the accept mass carried over `Sᶜ` is at most `E`.
The component accept mass equals the source mass. The assumptions on the window and exponent
belong to the source cap.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`) through `\label{eq:boundingsmoothedmin}` (`main.tex:1380`–`:1387`);
Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCap
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (E : ℝ) (hE0 : 0 ≤ E) (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (1 * (signalDim ^ n)) =>
            ∫ φ in ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
                  (goodRateSetPhaseOnly Q (2 * δ)))ᶜ,
              ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
                  (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
                (bellWembed φ)).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure 4).measure :
            Op (1 * (signalDim ^ n))).trace).re
      ≤ E := by
  -- the `dev = δ` instance of the Dev rung; the marker converts via the interface bridge.
  have h := bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev peSel xSel
    Q δ δ E hE0 (isBellSourceAcceptTailCapPhaseOnlyDev_of_isBellSourceAcceptTailCapPhaseOnly hCap)
  rwa [show (δ : ℝ) + δ = 2 * δ from by ring] at h

end QKD.BB84.Engine

end -- noncomputable section
