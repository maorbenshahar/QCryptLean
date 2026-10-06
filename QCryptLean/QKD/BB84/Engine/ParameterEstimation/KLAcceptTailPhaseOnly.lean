/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett
import QCryptLean.QKD.BB84.Engine.InnerBudget.InnerBudgetPinned
import QCryptLean.Quantum.Channels.CPTP.DiamondNormAncilla
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.PhaseOnlyPivot

-- The paired-Haar per-σ family wiring states Bochner integrability of `Op`-valued block maps;
-- as in `PhaseOnlyPivot.lean`, this uses the Frobenius norm.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-!
# Exact-KL accept splits at the phase-only pivot

The source accept mass over the complement of `goodRateSetPhaseOnly Q (δ + dev)` is bounded by
`exp(-m_X * klBer (Q + δ) (Q + δ + dev))`. The protocol window is `δ`; the deviation `dev`
sets the phase-error edge. Setting `dev = δ` gives the pivot `goodRateSetPhaseOnly Q (2 * δ)`.

For an arbitrary CPTP pre-channel and `c ≥ 0`, componentwise domination
`acceptedMass ≤ c * sourceMass`
transfers a source cap `T` to phase-bad mass `c * T`.
The choice `c = 2` permits factor-two domination. At the unit register embedding, the accepted
mass equals the source accept mass on every component
(`bb84UnitRegisterEmbed_localAcceptMass_eq_onComponent`), giving the phase-bad bound `T`.
Adjoining the announced-PE label preserves these bounds because its kernel has unit trace.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851), Lemma 9 Eq. 44,
§V.C and Appendix B; Renner 2005 (arXiv:quant-ph/0512258v2), §5 and §6.5.
-/

/-! ## 1. The exact-KL source cap at a free phase-error deviation -/

/-- **C3 at the exact KL exponent on the phase-only pivot at a free deviation, integral form —
against any `DensityMeasure`.**

The window/deviation split: the accept-test **window** stays `δ` (it is in the integrand
`bb84SiftedLocalAcceptProbabilityOnComponent … Q δ …`, fixed by the protocol), while the
**deviation** `dev` sets the pivot `goodRateSetPhaseOnly Q (δ + dev)` and the exponent edge
`klBer (Q+δ) (Q+δ+dev)`.  The `2δ` form
(`bb84_integral_onComponent_localPhaseBadBranch_le_klChernoff_exact_anyMeasure`) is the case
`dev = δ`; the mechanism is pointwise
(`bb84_onComponent_localPhaseBad_le_klChernoff_exactDev`, `PhaseOnlyPivot.lean`), so the integral
follows by integrating over the probability measure.

References: Renner 2005 §5; Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44. -/
theorem bb84_integral_onComponent_localPhaseBadBranch_le_klChernoff_exact_anyMeasureDev
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ) (hdev : 0 < dev)
    (μ : InfoTheory.DeFinetti.DensityMeasure signalDim) :
    (∫ σ in (goodRateSetPhaseOnly Q (δ + dev))ᶜ,
        bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ ∂μ.measure) ≤
      Real.exp (-(bb84SiftedXTestSampleSize peSel xSel : ℝ) *
        Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev)) := by
  have hPerσ :
      ∀ σ : DensityOp signalDim, σ ∈ (goodRateSetPhaseOnly Q (δ + dev))ᶜ →
        bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ ≤
          Real.exp (-(bb84SiftedXTestSampleSize peSel xSel : ℝ) *
            Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev)) :=
    fun σ hσ =>
      bb84_onComponent_localPhaseBad_le_klChernoff_exactDev peSel xSel Q δ dev hdev
        σ hσ
  haveI hProb : MeasureTheory.IsProbabilityMeasure μ.measure := μ.isProbability
  have hInt : MeasureTheory.Integrable
      (bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ) μ.measure := by
    have hAE := (bb84SiftedLocalAcceptProbabilityOnComponent_continuous n peSel xSel Q
      δ).aestronglyMeasurable (μ := μ.measure)
    apply MeasureTheory.Integrable.of_bound hAE 1
    filter_upwards with σ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (bb84SiftedLocalAcceptProbabilityOnComponent_nonneg n peSel xSel Q δ σ)]
    exact bb84SiftedLocalAcceptProbabilityOnComponent_le_one n peSel xSel Q δ σ
  have hMeas : MeasurableSet ((goodRateSetPhaseOnly Q (δ + dev))ᶜ) :=
    (goodRateSetPhaseOnly_measurableSet Q (δ + dev)).compl
  have hConstInt :
      MeasureTheory.IntegrableOn
        (fun _ => Real.exp (-(bb84SiftedXTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev)))
        ((goodRateSetPhaseOnly Q (δ + dev))ᶜ) μ.measure :=
    MeasureTheory.integrableOn_const
  have hmono :=
    MeasureTheory.setIntegral_mono_on hInt.integrableOn hConstInt hMeas hPerσ
  rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hmono
  refine hmono.trans ?_
  exact mul_le_of_le_one_left (Real.exp_pos _).le MeasureTheory.measureReal_le_one

/-! ## 2. The exact-KL source cap at the phase-only pivot -/

/-- **C3 at the exact KL exponent on the phase-only pivot, integral form — against any
`DensityMeasure`.**

The `μ`-integral of the accept mass over `(goodRateSetPhaseOnly Q (2δ))ᶜ` is at most
`exp(−m_X · klBer (Q+δ) (Q+2δ))` for **any** `DensityMeasure μ`: the `dev = δ`
corollary of `bb84_integral_onComponent_localPhaseBadBranch_le_klChernoff_exact_anyMeasureDev`.

References: Renner 2005 §5; Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44. -/
theorem bb84_integral_onComponent_localPhaseBadBranch_le_klChernoff_exact_anyMeasure
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hδ : 0 < δ)
    (μ : InfoTheory.DeFinetti.DensityMeasure signalDim) :
    (∫ σ in (goodRateSetPhaseOnly Q (2 * δ))ᶜ,
        bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ ∂μ.measure) ≤
      Real.exp (-(bb84SiftedXTestSampleSize peSel xSel : ℝ) *
        Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + 2 * δ)) := by
  have h := bb84_integral_onComponent_localPhaseBadBranch_le_klChernoff_exact_anyMeasureDev
    peSel xSel Q δ δ hδ μ
  -- Read the `dev = δ` instance back in the `2δ` shape.
  rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring,
    show (δ:ℝ) + δ = 2 * δ from by ring] at h

/-! ## 3. The `Sᶜ` half of the accept split at an ABSTRACT source cap, phase-only pivot -/

/-- A componentwise bound `acceptedMass ≤ c * sourceMass` transfers a source cap `T` to
phase-bad mass at most `c * T`, for an arbitrary CPTP pre-channel and retained Eve register.
The Haar pushforward turns the block-entry integral into the CKR source integral. -/
theorem bb84_rhoEtilde_phaseBadBranch_traceNorm_le_ofSourceCap_of_goodSet {n : ℕ} [NeZero n]
    [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (goodSet : Set (DensityOp signalDim)) (hgoodMeas : MeasurableSet goodSet)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ goodSetᶜ,
      bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ σ ≤
        c * bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in goodSetᶜ,
        bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ
        ∂(Quantum.Channels.ckrMixtureMeasure signalDim).measure) ≤ T) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (eveDim * (signalDim ^ n)) =>
            ∫ ψ in ((DensityOp.partialTraceB :
                  DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                goodSet)ᶜ,
              ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
            Op (eveDim * (signalDim ^ n))).trace).re
      ≤ c * T := by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hNd : NeZero (signalDim * signalDim) := ⟨by norm_num⟩
  set μ16 := (deFinetti_haarMeasure (signalDim * signalDim)).measure with hμ16
  set ckr := Quantum.Channels.ckrMixtureMeasure signalDim with hckr
  haveI hckrProb : MeasureTheory.IsProbabilityMeasure ckr.measure := ckr.isProbability
  set S : Set (DensityOp signalDim) := goodSetᶜ with hS
  have hSmeas : MeasurableSet S := hgoodMeas.compl
  set Spaired : Set (DensityOp (signalDim * signalDim)) :=
    ((DensityOp.partialTraceB :
        DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
      goodSet)ᶜ with hSpaired
  have hSpairedMeas : MeasurableSet Spaired :=
    (partialTraceB_measurable hgoodMeas).compl
  have hmapeq : MeasureTheory.Measure.map
      (DensityOp.partialTraceB :
        DensityOp (signalDim * signalDim) → DensityOp signalDim) μ16 = ckr.measure := by
    rw [hckr, hμ16]; rfl
  -- Entry-eval continuous linear map `M ↦ M i j` ⇒ block-entry integrability.
  let entryCLM : Fin (eveDim * (signalDim ^ n)) →
      Fin (eveDim * (signalDim ^ n)) →
      (Op (eveDim * (signalDim ^ n)) →L[ℝ] ℂ) := fun i j =>
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hblockInt : ∀ x : Fin n → Fin signalDim,
      MeasureTheory.Integrable
        (fun ψ => ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp)
            μ16 :=
    bb84_f_blocks_integrable eveDim pre hpre peSel xSel Q δ
  have hentInt : ∀ (x : Fin n → Fin signalDim)
      (i : Fin (eveDim * (signalDim ^ n))),
      MeasureTheory.IntegrableOn
        (fun ψ => ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp
            i i)
        Spaired μ16 :=
    fun x i => ((entryCLM i i).integrable_comp (hblockInt x)).integrableOn
  -- (1) The per-ψ block reduction: the summed filtered trace is the attacked accept mass of the
  -- AB-marginal `Tr_B ψ`.
  have hsumψ : ∀ ψ : DensityOp (signalDim * signalDim),
      (∑ x : Fin n → Fin signalDim,
          ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap
              x).toOp.trace.re)
        = bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ
            (DensityOp.partialTraceB ψ) := by
    intro ψ
    have hτpt : (densityOp_reindex (interleavingEquiv signalDim n).symm
          (ψ.tensorPowGen n)).partialTraceB = (DensityOp.partialTraceB ψ).tensorPowGen n :=
      (partialTraceB_tensorPow_eq ψ).symm
    have hbridge : ∀ x : Fin n → Fin signalDim,
        partialTraceB
            ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp
          = ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
              (bb84SiftedPostMeasurementCQState eveDim pre hpre peSel xSel
                (densityOp_reindex (interleavingEquiv signalDim n).symm
                  (ψ.tensorPowGen n)).partialTraceB)).stateMap x).toOp := by
      intro x
      exact bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq peSel xSel Q δ
        ((bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
          (densityOp_reindex (interleavingEquiv signalDim n).symm
            (ψ.tensorPowGen n))).toCQState)
        (bb84SiftedPostMeasurementCQState eveDim pre hpre peSel xSel
          (densityOp_reindex (interleavingEquiv signalDim n).symm
            (ψ.tensorPowGen n)).partialTraceB)
        (fun ω' => bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned
          eveDim pre hpre peSel xSel
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)) ω') x
    unfold bb84SiftedPreLocalAcceptMass SubDensityOp.trace
    apply Finset.sum_congr rfl
    intro x _
    rw [show ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp.trace
          = (partialTraceB
              ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap
                  x).toOp).trace
        from (trace_partialTraceB _).symm, hbridge x, hτpt]
  have hcont : Continuous
      (bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ) := by
    have hpost : Continuous (fun σ : DensityOp signalDim =>
        cptpDensityOp pre hpre (σ.tensorPowGen n)) := by
      rw [continuous_induced_rng]
      exact tensorPowGen_preChannel_continuous pre
    have hmarg := DensityOp.continuous_toOp.comp
      (partialTraceB_continuous_general.comp hpost)
    change Continuous (fun σ => bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ σ)
    simp_rw [bb84SiftedPreLocalAcceptMass_eq_sum_quadForm]
    refine continuous_finset_sum _ (fun ω _ => ?_)
    split_ifs
    · simp_rw [← trace_ketbra_mul]
      exact Complex.continuous_re.comp (continuous_const.mul hmarg).matrix_trace
    · exact continuous_const
  -- (2) Reduce the entry-integral trace sum to the `S`-restricted attacked accept-mass integral.
  have hreduce :
      (∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (eveDim * (signalDim ^ n)) =>
            ∫ ψ in Spaired,
              ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
                  ∂μ16 :
            Op (eveDim * (signalDim ^ n))).trace).re)
        = ∫ σ in S, bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ σ ∂ckr.measure := by
    have hperx : ∀ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (eveDim * (signalDim ^ n)) =>
            ∫ ψ in Spaired,
              ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
                  ∂μ16 :
            Op (eveDim * (signalDim ^ n))).trace).re =
          ∫ ψ in Spaired,
            ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap
                x).toOp.trace.re ∂μ16 := by
      intro x
      rw [Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.of_apply]
      rw [← MeasureTheory.integral_finset_sum _ (fun i _ => hentInt x i), ← Complex.reCLM_apply,
        ← ContinuousLinearMap.integral_comp_comm Complex.reCLM
          (MeasureTheory.integrable_finset_sum _ (fun i _ => hentInt x i))]
      refine MeasureTheory.setIntegral_congr_fun hSpairedMeas (fun ψ _ => ?_)
      simp only [Complex.reCLM_apply, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
    rw [Finset.sum_congr rfl (fun x _ => hperx x)]
    have htrInt : ∀ x : Fin n → Fin signalDim,
        MeasureTheory.IntegrableOn
          (fun ψ => ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap
              x).toOp.trace.re)
          Spaired μ16 := by
      intro x
      have heq : (fun ψ =>
            ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap
                x).toOp.trace.re)
          = fun ψ =>
            ∑ i, (((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp
                i i).re := by
        funext ψ; simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
      rw [heq]
      exact MeasureTheory.integrable_finset_sum _ fun i _ =>
        Complex.reCLM.integrable_comp (hentInt x i)
    rw [← MeasureTheory.integral_finset_sum _ (fun x _ => htrInt x),
      MeasureTheory.setIntegral_congr_fun hSpairedMeas (fun ψ _ => hsumψ ψ),
      show Spaired = (DensityOp.partialTraceB :
            DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹' S by
        rw [hSpaired, hS, Set.preimage_compl],
      ← MeasureTheory.setIntegral_map hSmeas hcont.aestronglyMeasurable
        partialTraceB_measurable.aemeasurable, hmapeq]
  rw [hreduce]
  have hsource := bb84SiftedLocalAcceptProbabilityOnComponent_continuous n peSel xSel Q δ
  have hmono := MeasureTheory.setIntegral_mono_on
    (hcont.integrable_of_compactSpace (μ := ckr.measure)).integrableOn
    ((continuous_const.mul hsource).integrable_of_compactSpace
      (μ := ckr.measure)).integrableOn hSmeas hdom
  simp only [Pi.mul_apply] at hmono
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left hcap hc)

/-- **The `Sᶜ` half at an abstract source cap, phase-only pivot.**

The pivot is the phase-only good-rate set `goodRateSetPhaseOnly Q (2δ)`; the cap is over its
complement against the CKR mixture measure.  Corollary of
`bb84_rhoEtilde_phaseBadBranch_traceNorm_le_ofSourceCap_of_goodSet` at `goodSet =
goodRateSetPhaseOnly Q (2δ)`.

References: Nahar et al. 2024 (arXiv:2403.11851) main.tex:1364–:1372; Renner 2005 §6.5. -/
theorem bb84_rhoEtilde_phaseBadBranch_traceNorm_le_ofSourceCap {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ (goodRateSetPhaseOnly Q (2 * δ))ᶜ,
      bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ σ ≤
        c * bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in (goodRateSetPhaseOnly Q (2 * δ))ᶜ,
        bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ
        ∂(Quantum.Channels.ckrMixtureMeasure signalDim).measure) ≤ T) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (eveDim * (signalDim ^ n)) =>
            ∫ ψ in ((DensityOp.partialTraceB :
                  DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                (goodRateSetPhaseOnly Q (2 * δ)))ᶜ,
              ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
            Op (eveDim * (signalDim ^ n))).trace).re
      ≤ c * T := by
  refine bb84_rhoEtilde_phaseBadBranch_traceNorm_le_ofSourceCap_of_goodSet eveDim pre hpre peSel
    xSel Q δ (goodRateSetPhaseOnly Q (2 * δ))
    (goodRateSetPhaseOnly_measurableSet Q (2 * δ)) c hc hdom T hcap

/-- The phase-bad mass at a free deviation is bounded by `c * T` under componentwise domination.
The window `δ` fixes acceptance; the deviation `dev` sets `goodRateSetPhaseOnly Q (δ + dev)`. -/
theorem bb84_rhoEtilde_phaseBadBranch_traceNorm_le_ofSourceCapDev {n : ℕ} [NeZero n]
    [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ (goodRateSetPhaseOnly Q (δ + dev))ᶜ,
      bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ σ ≤
        c * bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in (goodRateSetPhaseOnly Q (δ + dev))ᶜ,
        bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ
        ∂(Quantum.Channels.ckrMixtureMeasure signalDim).measure) ≤ T) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (eveDim * (signalDim ^ n)) =>
            ∫ ψ in ((DensityOp.partialTraceB :
                  DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
              ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
            Op (eveDim * (signalDim ^ n))).trace).re
      ≤ c * T := by
  exact bb84_rhoEtilde_phaseBadBranch_traceNorm_le_ofSourceCap_of_goodSet eveDim pre hpre peSel
    xSel Q δ (goodRateSetPhaseOnly Q (δ + dev))
    (goodRateSetPhaseOnly_measurableSet Q (δ + dev)) c hc hdom T hcap

/-! ## 5. The PE-labelled accept split at an abstract source cap, phase-only pivot -/

/-- **The general-`m` PE-labelled accept split at an abstract source cap, phase-only pivot.**

`tr (label block ⊗ M) = tr M`, entrywise under the set integral, so the PE-labelled bad-branch trace
is the unlabelled one and `bb84_rhoEtilde_phaseBadBranch_traceNorm_le_ofSourceCap`
applies verbatim.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B; Renner 2005
(`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem bb84_peLabelledRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCap
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ (goodRateSetPhaseOnly Q (2 * δ))ᶜ,
      bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ σ ≤
        c * bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in (goodRateSetPhaseOnly Q (2 * δ))ᶜ,
        bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ
        ∂(Quantum.Channels.ckrMixtureMeasure signalDim).measure) ≤ T) :
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
              (eveDim * (signalDim ^ n))) =>
            ∫ ψ in ((DensityOp.partialTraceB :
                    DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                  (goodRateSetPhaseOnly Q (2 * δ)))ᶜ,
              ((bb84PELabelledPairedHaarPerSigmaFamily (m := m)
                eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
          Op (signalDim ^ (n - bb84KeyRoundCount n m) *
            (eveDim * (signalDim ^ n)))).trace).re ≤
      c * T := by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hsame : ∀ x : Fin n → Fin signalDim,
      (Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
            (eveDim * (signalDim ^ n))) =>
          ∫ ψ in ((DensityOp.partialTraceB :
                  DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                (goodRateSetPhaseOnly Q (2 * δ)))ᶜ,
            ((bb84PELabelledPairedHaarPerSigmaFamily (m := m)
              eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
            ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
        Op (signalDim ^ (n - bb84KeyRoundCount n m) *
          (eveDim * (signalDim ^ n)))).trace =
      (Matrix.of fun i j : Fin (eveDim * (signalDim ^ n)) =>
          ∫ ψ in ((DensityOp.partialTraceB :
                  DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                (goodRateSetPhaseOnly Q (2 * δ)))ᶜ,
            ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
            ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
        Op (eveDim * (signalDim ^ n))).trace := fun x =>
    trace_setIntegral_tensorLeftKernel_blocks_eq
      (fun ψ => bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ)
      (bb84PELabelKernel (m := m) peSel)
      (bb84PELabelKernel_matrix_trace (m := m) peSel) _ x
  simp_rw [hsame]
  exact bb84_rhoEtilde_phaseBadBranch_traceNorm_le_ofSourceCap
    eveDim pre hpre peSel xSel Q δ c hc hdom T hcap

/-- Adjoining the PE label preserves the bad-mass bound `c * T` at a free deviation.
Each label block has trace one, so the labelled bad-branch trace equals the unlabelled trace. -/
theorem bb84_peLabelledRhoEtilde_acceptSplit_phaseBadBranch_traceNorm_le_ofSourceCapDev
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ (goodRateSetPhaseOnly Q (δ + dev))ᶜ,
      bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ σ ≤
        c * bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in (goodRateSetPhaseOnly Q (δ + dev))ᶜ,
        bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ
        ∂(Quantum.Channels.ckrMixtureMeasure signalDim).measure) ≤ T) :
    ∑ x : Fin n → Fin signalDim,
        ((Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
              (eveDim * (signalDim ^ n))) =>
            ∫ ψ in ((DensityOp.partialTraceB :
                    DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                  (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
              ((bb84PELabelledPairedHaarPerSigmaFamily (m := m)
                eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
          Op (signalDim ^ (n - bb84KeyRoundCount n m) *
            (eveDim * (signalDim ^ n)))).trace).re ≤
      c * T := by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hsame : ∀ x : Fin n → Fin signalDim,
      (Matrix.of fun i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) *
            (eveDim * (signalDim ^ n))) =>
          ∫ ψ in ((DensityOp.partialTraceB :
                  DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
            ((bb84PELabelledPairedHaarPerSigmaFamily (m := m)
              eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
            ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
        Op (signalDim ^ (n - bb84KeyRoundCount n m) *
          (eveDim * (signalDim ^ n)))).trace =
      (Matrix.of fun i j : Fin (eveDim * (signalDim ^ n)) =>
          ∫ ψ in ((DensityOp.partialTraceB :
                  DensityOp (signalDim * signalDim) → DensityOp signalDim) ⁻¹'
                (goodRateSetPhaseOnly Q (δ + dev)))ᶜ,
            ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
            ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure :
        Op (eveDim * (signalDim ^ n))).trace := fun x =>
    trace_setIntegral_tensorLeftKernel_blocks_eq
      (fun ψ => bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ)
      (bb84PELabelKernel (m := m) peSel)
      (bb84PELabelKernel_matrix_trace (m := m) peSel) _ x
  simp_rw [hsame]
  exact bb84_rhoEtilde_phaseBadBranch_traceNorm_le_ofSourceCapDev
    eveDim pre hpre peSel xSel Q δ dev c hc hdom T hcap

end QKD.BB84.Engine

end -- noncomputable section
