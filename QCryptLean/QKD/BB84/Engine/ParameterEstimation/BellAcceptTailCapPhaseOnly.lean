/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.KLAcceptTailBellTightPhaseOnly
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.KLAcceptTailPhaseOnlyGeneral

/-!
# The Bell accept split at the realised-X-subsample KL tail, on the phase-only pivot

The instance of `IsBellSourceAcceptTailCapPhaseOnly` at
`klAcceptTailPhaseOnly peSel xSel Q δ = exp(−m_X · klBer (Q+δ) (Q+2δ))`, and the general-`m`
labelled bad-branch rung on the `m`-sized announced-PE label register.

On the phase-only pivot the failing statistic is a single phase inequality
(`goodRateSetPhaseOnly_compl_phaseRate_lt`), so the per-component bound
`bb84_onComponent_localPhaseBad_le_klChernoff_exact` (`PhaseOnlyPivot.lean`) lands directly on
the realised X-subsample with no bit arm and no selector pin. Its conclusion is
`klAcceptTailPhaseOnly peSel xSel Q δ` unfolded, so the interface instance is that lemma applied
pointwise.

## `m_X = 0` is covered, not excluded

There the tail is `1`; the improved security budget exceeds two and the channel-distance bound
applies. The exact accept-tail interface itself requires only a positive phase-error deviation.

## Relation to the literature

The phase-only pivot is not in the cited literature; it is licensed by
`QKD.BB84.Engine.bb84ComponentAliceZRate_ge_phaseOnly_of_good`. Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand each small — the ancestor of the phase-only conjunction, not authority for
dropping the bit ball.

## Window and deviation

The `Dev` declarations of this module (`bb84_bellSourceAcceptTailCapPhaseOnly_klTailPhaseOnlyDev`
in §1, `bb84_bellPeLabelledRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev`) free
the phase-error **deviation** `dev` from the accept-test **window** `δ`: the pivot reads
`goodRateSetPhaseOnly Q (δ + dev)`, the tail is
`klAcceptTailPhaseOnlyDev peSel xSel Q δ dev = exp(−m_X · klBer (Q+δ) (Q+δ+dev))`, and the window
`δ` keeps only its protocol role; the `2δ` forms are the case `dev = δ`.  This is the window and
deviation split of Nahar et al. 2024 (arXiv:2403.11851) Lemma 9 Eq. 44, §V.C.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44 (the
per-component accept-mass bound at the subsample the statistic is measured on), App. B
`\label{eq:tausplit}` (`main.tex:1356`–`:1361`), §V.C (`main.tex:909`, `:913`, `:970`); Renner 2005
(`arXiv:quant-ph/0512258v2`) §5, §6.5.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## 1. The interface instance at the free phase-error deviation

The window `δ` is the accept test's half-width (protocol, completeness side); the deviation `dev`
is the gap between the window edge `Q + δ` and where the entropy floor is charged, `Q + δ + dev`
(soundness side).  Here `dev` enters only through the pivot `goodRateSetPhaseOnly Q (δ + dev)`
and the KL exponent; the window `δ` is untouched, exactly as in Nahar et al. (arXiv:2403.11851)
Lemma 9 Eq. 44 with the deviation split of §V.C. -/

/-- **The Bell chain meets its phase-only accept-tail interface at the realised-`m_X` KL tail
widened by the free deviation `dev`, at arbitrary selectors.**  The incumbent 2δ form
`bb84_bellSourceAcceptTailCapPhaseOnly_klTailPhaseOnly` (§1b below) is the case `dev = δ`.

`bb84_onComponent_localPhaseBad_le_klChernoff_exactDev` (`PhaseOnlyPivot.lean`) caps a
component in the widened bad set `(goodRateSetPhaseOnly Q (δ + dev))ᶜ` — the pivot of the
deviation-scoped chain, not the accept window, which stays `δ` — at
`exp(−m_X · klBer (Q+δ) (Q+δ+dev))`, i.e. `klAcceptTailPhaseOnlyDev peSel xSel Q δ dev`
unfolded.  As in §1b the interface is pointwise, so the instance is that lemma with the quantifier
reintroduced; no exponent conversion happens anywhere in this proof.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, §V.C (window/deviation split),
App. B `\label{eq:tausplit}` (`main.tex:1356`–`:1361`); Renner 2005
(`arXiv:quant-ph/0512258v2`) §5. -/
theorem bb84_bellSourceAcceptTailCapPhaseOnly_klTailPhaseOnlyDev
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ) (hdev : 0 < dev) :
    IsBellSourceAcceptTailCapPhaseOnlyDev peSel xSel Q δ dev
      (klAcceptTailPhaseOnlyDev peSel xSel Q δ dev) :=
  fun σ hσ =>
    bb84_onComponent_localPhaseBad_le_klChernoff_exactDev peSel xSel Q δ dev hdev
      σ hσ

/-! ## 1b. The interface instance at the realised X-subsample -/

/-- **The Bell chain meets its phase-only accept-tail interface at the realised-`m_X` KL tail**, at
arbitrary selectors.

`bb84_onComponent_localPhaseBad_le_klChernoff_exact` (`PhaseOnlyPivot.lean`) caps a
phase-rate-bad component's source accept mass at `exp(−m_X · klBer (Q+δ) (Q+2δ))`, which is
`klAcceptTailPhaseOnly peSel xSel Q δ` unfolded.  The interface is pointwise, so the instance is
that lemma with the quantifier reintroduced — no exponent conversion happens anywhere in this
proof.  The proof is the `dev = δ` case of
`bb84_bellSourceAcceptTailCapPhaseOnly_klTailPhaseOnlyDev` (§1): its marker at `dev = δ` is this
marker after the `δ + δ = 2 * δ` rewrite, and the tail is read back with
`klAcceptTailPhaseOnlyDev_self`.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, App. B `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`); Renner 2005 (`arXiv:quant-ph/0512258v2`) §5. -/
theorem bb84_bellSourceAcceptTailCapPhaseOnly_klTailPhaseOnly
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hδ : 0 < δ) :
    IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ
      (klAcceptTailPhaseOnly peSel xSel Q δ) := by
  -- the Dev twin at `dev = δ`; its marker is this marker after the `δ + δ = 2 * δ` rewrite
  have h := bb84_bellSourceAcceptTailCapPhaseOnly_klTailPhaseOnlyDev peSel xSel Q δ δ hδ
  rw [klAcceptTailPhaseOnlyDev_self] at h
  exact fun σ hσ => h σ (by rw [show (2:ℝ) * δ = δ + δ from by ring] at hσ; exact hσ)

/-! ## 2. The labelled bad-branch rung on the `m`-sized PE label register -/

/-- **The general-`m` labelled Bell accept-split bad-branch bound at an abstract phase-only source
cap.**

`tr (label block ⊗ M) = tr M`, entrywise under the set integral
(`trace_setIntegral_tensorLeftKernel_blocks_eq`), so attaching the general-`m` PE label leaves the
bad-branch trace unchanged and the `m`-free base rung
`bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCap` applies verbatim.  The
defeq that makes the transport typecheck is `bb84PELabelledPairedHaarPerSigmaFamily`'s own body
(`PELabelledPerSigmaFamily.lean`): it is
`(bb84PairedHaarPerSigmaFamily …).tensorLeftKernel (bb84PELabelKernel (m := m) peSel)`.

The positive deviation and exponent arithmetic enter only when constructing the source cap.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`) through `\label{eq:boundingsmoothedmin}` (`main.tex:1380`–`:1387`), and
`main.tex:909`, `:913` for the general-`m` split; Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem bb84_bellPeLabelledRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCap
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (E : ℝ) (hE0 : 0 ≤ E) (hCap : IsBellSourceAcceptTailCapPhaseOnly peSel xSel Q δ E) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
              (1 * (signalDim ^ n))) =>
            ∫ φ in ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
                  (goodRateSetPhaseOnly Q (2 * δ)))ᶜ,
              ((bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
                (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
                (bellWembed φ)).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure 4).measure :
          Op (signalDim ^ (n - bb84KeyRoundCount n m) *
            (1 * (signalDim ^ n)))).trace).re ≤
      E := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hsame : ∀ x : Fin n → Fin signalDim,
      (Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
            (1 * (signalDim ^ n))) =>
          ∫ φ in ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
                (goodRateSetPhaseOnly Q (2 * δ)))ᶜ,
            ((bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
              (bellWembed φ)).stateMap x).toOp i j
            ∂(deFinetti_haarMeasure 4).measure :
        Op (signalDim ^ (n - bb84KeyRoundCount n m) *
          (1 * (signalDim ^ n)))).trace =
      (Matrix.of fun i j : Fin (1 * (signalDim ^ n)) =>
          ∫ φ in ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
                (goodRateSetPhaseOnly Q (2 * δ)))ᶜ,
            ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
                (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
              (bellWembed φ)).stateMap x).toOp i j
            ∂(deFinetti_haarMeasure 4).measure :
        Op (1 * (signalDim ^ n))).trace := fun x =>
    trace_setIntegral_tensorLeftKernel_blocks_eq
      (fun φ : DensityOp 4 =>
        bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
            peSel xSel Q δ (bellWembed φ))
      (bb84PELabelKernel (m := m) peSel)
      (bb84PELabelKernel_matrix_trace (m := m) peSel) _ x
  simp_rw [hsame]
  exact bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCap peSel xSel Q δ E hE0
    hCap

/-! ## 2b. The labelled bad-branch rung at the free phase-error deviation

The Dev analogue of §2: the pivot preimage moves from `goodRateSetPhaseOnly Q (2 * δ)` to
`goodRateSetPhaseOnly Q (δ + dev)` — the entropy-charge point of the deviation-scoped chain —
while the accept window `δ` and the label transport are unchanged.
The base rung consumed is
`bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev`
(`KLAcceptTailBellTightPhaseOnly.lean`), so the source cap is the Dev predicate. -/

/-- **The Dev analogue of
`bb84_bellPeLabelledRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCap`**: the
general-`m` labelled Bell accept-split bad-branch bound at an abstract phase-only source cap on
the widened bad set `(goodRateSetPhaseOnly Q (δ + dev))ᶜ`.

Same transport as §2: `tr (label block ⊗ M) = tr M`, entrywise under the set integral
(`trace_setIntegral_tensorLeftKernel_blocks_eq`), so attaching the general-`m` PE label leaves
the bad-branch trace unchanged and the Dev base rung
`bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev` applies verbatim.
The pivot of the integration domain is `δ + dev`; the accept window stays `δ`.

The positive deviation and exponent arithmetic enter only when constructing the source cap.

References: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, §V.C (window/deviation
split), App. B, `\label{eq:tausplit}` (`main.tex:1356`–`:1361`) through
`\label{eq:boundingsmoothedmin}` (`main.tex:1380`–`:1387`), and `main.tex:909`, `:913` for the
general-`m` split; Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem bb84_bellPeLabelledRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ)
    (E : ℝ) (hE0 : 0 ≤ E)
    (hCap : IsBellSourceAcceptTailCapPhaseOnlyDev peSel xSel Q δ dev E) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
              (1 * (signalDim ^ n))) =>
            ∫ φ in ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
                  (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
              ((bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
                (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
                (bellWembed φ)).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure 4).measure :
          Op (signalDim ^ (n - bb84KeyRoundCount n m) *
            (1 * (signalDim ^ n)))).trace).re ≤
      E := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hsame : ∀ x : Fin n → Fin signalDim,
      (Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
            (1 * (signalDim ^ n))) =>
          ∫ φ in ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
                (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
            ((bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
              (bellWembed φ)).stateMap x).toOp i j
            ∂(deFinetti_haarMeasure 4).measure :
        Op (signalDim ^ (n - bb84KeyRoundCount n m) *
          (1 * (signalDim ^ n)))).trace =
      (Matrix.of fun i j : Fin (1 * (signalDim ^ n)) =>
          ∫ φ in ((fun φ' : DensityOp 4 => DensityOp.partialTraceB (bellWembed φ')) ⁻¹'
                (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
            ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
                (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
              (bellWembed φ)).stateMap x).toOp i j
            ∂(deFinetti_haarMeasure 4).measure :
        Op (1 * (signalDim ^ n))).trace := fun x =>
    trace_setIntegral_tensorLeftKernel_blocks_eq
      (fun φ : DensityOp 4 =>
        bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
            peSel xSel Q δ (bellWembed φ))
      (bb84PELabelKernel (m := m) peSel)
      (bb84PELabelKernel_matrix_trace (m := m) peSel) _ x
  simp_rw [hsame]
  exact bb84_bellRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev peSel xSel Q δ
    dev E hE0 hCap

end QKD.BB84.Engine

end -- noncomputable section
