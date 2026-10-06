import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AcceptSplit

/-!
# The genuine-LOCC de Finetti mixture and its two analytic data

The `Eⁿ`-marginal de Finetti reference `bb84EnVRhoEtilde` and two analytic facts about it: the
Nahar et al. B13 integral split `bb84_rhoEtilde_eq_haar_integral_blocks` (its entries are the
paired-Haar block integral of the per-σ family) and the accept-weight trace-out identity
`bb84_rhoEtilde_acceptWeight_eq_ckrMixture` (tracing out the purifier does not change the accepted
weight).

Each declaration here reads the fail-closed LOCC two-basis test
`bb84SiftedLocalPETestPassed` evaluated after the local `H ⊗ H` sift `bb84SiftedRotation`.

Together with `bb84PairedHaarPerSigmaFamily`, `bb84_f_blocks_integrable`,
`bb84PairedHaarPerSigmaFamily_blocks_continuous`
(`AcceptSplit.lean`), these are the analytic data of the coarsening assembler
`smoothMinEntropy_coarsen_ge_of_deFinetti_postFilter_ownMarginal_heavyFloor`
(`InfoTheory/SmoothMinEntropy/Mixture/FinitePostFilterFloorCoarsen.lean`).

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B main.tex:1341–:1413
(Appendix B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}`
(main.tex:1356–:1362), the Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed
min-entropy bound `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting
step `\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413); Renner 2005
(arXiv:quant-ph/0512258v2) §6.5; Christandl–König–Renner 2009 (PRL 102, 020504) main.tex:268–:401
(\emph{Main Result}: Theorem `\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}`
:319–:328). -/

-- The paired-Haar per-σ family wiring states Bochner integrability of `Op`-valued block maps;
-- as in `PerSigmaFamily.lean`/`AcceptSplit.lean`, this uses the Frobenius norm on matrices.
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

private local instance {n : ℕ} : ContinuousENorm (Op n) :=
  SeminormedAddGroup.toContinuousENorm

/-! ## 1. The `Eⁿ`-marginal de Finetti reference `bb84EnVRhoEtilde` -/

/-- **The `Eⁿ`-marginal de Finetti reference state `bb84EnVRhoEtilde` (Nahar et al. B13).**

The sifted / fail-closed-local-PE-filtered τ-side pipeline run on the `Eⁿ`-only CKR purification
`pairedDeFinettiState signalDim n` (register `Aⁿ ⊗ Eⁿ`, `dimR = 4ⁿ`), so the quantum register
is `eveDim·4ⁿ` (Eve's ancilla tensored with the per-round-IID purifier `Eⁿ`).

Built from the LOCC sift `bb84SiftedRotation` and the fail-closed two-basis filter
`bb84PostMeasurementCQSiftedLocalPEPassFilter`; the τ-side pipeline
`bb84SiftedTauPostMeasurementNormalizedCQState` is the same one the per-σ family
`bb84PairedHaarPerSigmaFamily` (`AcceptSplit.lean`) runs on the per-σ inputs, instantiated at the
paired de Finetti state instead. -/
noncomputable def bb84EnVRhoEtilde {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    CQState (Fin n → Fin signalDim) (eveDim * (signalDim ^ n)) :=
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI : NeZero (eveDim * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
    (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
      (pairedDeFinettiState signalDim n)).toCQState

/-! ## 2. The Nahar et al. B13 integral split (the assembler's `hf_lin`) -/

/-- **`bb84EnVRhoEtilde` is the paired-Haar block integral of the per-σ family (Nahar et al. B13).**

Each register-block entry of the `Eⁿ`-marginal de Finetti reference `bb84EnVRhoEtilde` is the
Bochner integral over the paired Haar measure of the corresponding entry of the per-σ family
`bb84PairedHaarPerSigmaFamily`.  This is the `hf_lin` argument of the coarsening assembler
`smoothMinEntropy_coarsen_ge_of_deFinetti_postFilter_ownMarginal_heavyFloor`
(`InfoTheory/SmoothMinEntropy/Mixture/FinitePostFilterFloorCoarsen.lean`).

The proof case-splits on the PE test `bb84SiftedLocalPETestPassed` (a `Bool` function of `ω`
alone), and on the accepting branch factors the whole pipeline through a fixed ℂ-linear functional
`L` of the input operator (sift conjugation, linear attack channel, τ-block embedding), commuted
past the Bochner integral by `ContinuousLinearMap.integral_comp_comm` against
`pairedDeFinettiState_eq_haar_integral_paired` (`Reference/Mixed.lean`) +
`densityOp_reindex_integralTensorPower_toOp`.

References: Nahar et al. 2024 (arXiv:2403.11851) App. B `\label{eq:tausplit}` (main.tex:1356–:1362).
-/
theorem bb84_rhoEtilde_eq_haar_integral_blocks {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∀ (x : Fin n → Fin signalDim)
      (i j : Fin (eveDim * (signalDim ^ n))),
      ((bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ).stateMap x).toOp i j =
        ∫ ψ : DensityOp (signalDim * signalDim),
          ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
          ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure := by
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI : NeZero (signalDim * signalDim) := ⟨by norm_num⟩
  intro x i j
  by_cases hpe : bb84SiftedLocalPETestPassed peSel xSel δ Q x
  · -- Accepting branch: the pipeline reads each input block-entry through a fixed ℂ-linear
    -- functional `L` of the input operator (sift rotation, linear attack channel, τ-embedding).
    let L : Op (signalDim ^ n * signalDim ^ n) →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun M =>
            (Op.tensor (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
                  (1 : Op (signalDim ^ n))
                * mapTensorId pre M
                * (Op.tensor
                    (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
                    (1 : Op (signalDim ^ n)))ᴴ)
              (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
                (dimR := signalDim ^ n) (bb84OutcomeIndex x) i)
              (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
                (dimR := signalDim ^ n) (bb84OutcomeIndex x) j)
          map_add' := by
            intro M N
            simp only [mapTensorId_add_basic, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
          map_smul' := by
            intro c M
            simp only [mapTensorId_smul_basic, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.smul_apply, RingHom.id_apply] }
    -- On the accepting branch the fail-closed filter keeps the τ-conditioned block unchanged.
    have hstate : ∀ (τ : DensityOp (signalDim ^ n * signalDim ^ n)),
        (bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
            (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
              τ).toCQState).stateMap x =
          bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel τ x := by
      intro τ
      change (if bb84SiftedLocalPETestPassed peSel xSel δ Q x then
          (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
              τ).toCQState.stateMap x
        else (0 : SubDensityOp _)) = _
      rw [if_pos hpe]
      rfl
    -- Each input block-entry is read by `L`.
    have hgen : ∀ (τ : DensityOp (signalDim ^ n * signalDim ^ n)),
        ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
            (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
              τ).toCQState).stateMap x).toOp i j = L τ.toOp := by
      intro τ
      rw [hstate τ]
      rfl
    -- The paired de Finetti input is the paired-Haar Bochner integral of the per-σ inputs.
    have hint : MeasureTheory.Integrable
        (fun ψ : DensityOp (signalDim * signalDim) =>
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp)
        (deFinetti_haarMeasure (signalDim * signalDim)).measure :=
      integrable_reindexed_tensorPowGen_toOp (d := signalDim) (n := n)
        (deFinetti_haarMeasure (signalDim * signalDim))
    have hpaired : (pairedDeFinettiState signalDim n).toOp =
        ∫ ψ : DensityOp (signalDim * signalDim),
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp
          ∂(deFinetti_haarMeasure (signalDim * signalDim)).measure := by
      rw [pairedDeFinettiState_eq_haar_integral_paired signalDim n,
        densityOp_reindex_integralTensorPower_toOp]
    -- Compose: read the entry of `bb84EnVRhoEtilde` through `L`, commute `L` with the Bochner
    -- integral.
    rw [show ((bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ).stateMap x).toOp i j =
          L (pairedDeFinettiState signalDim n).toOp from
        hgen (pairedDeFinettiState signalDim n)]
    rw [hpaired]
    refine (L.integral_comp_comm hint).symm.trans ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ψ => ?_))
    exact (show ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i
        j =
        L (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp from
      hgen (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n))).symm
  · -- Rejecting branch: the fail-closed filter zeros the block on both sides.
    have hLHS : ((bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ).stateMap x).toOp i j = 0 := by
      change ((if bb84SiftedLocalPETestPassed peSel xSel δ Q x then
          (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
            (pairedDeFinettiState signalDim n)).toCQState.stateMap x
        else (0 : SubDensityOp _)).toOp) i j = 0
      rw [if_neg hpe]
      rfl
    rw [hLHS]
    refine (MeasureTheory.integral_eq_zero_of_ae
      (Filter.Eventually.of_forall (fun ψ => ?_))).symm
    change ((if bb84SiftedLocalPETestPassed peSel xSel δ Q x then
        (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
          (densityOp_reindex (interleavingEquiv signalDim n).symm
            (ψ.tensorPowGen n))).toCQState.stateMap x
      else (0 : SubDensityOp _)).toOp) i j = 0
    rw [if_neg hpe]
    rfl

/-! ## 3. The accept-weight trace-out identity -/

/-- **Accept-weight trace-out invariance.**

The accept event reads only the classical announced-outcome string, so tracing out the `Eⁿ` purifier
does not change the accepted weight: the total accepted weight of the `Eⁿ`-marginal reference
`bb84EnVRhoEtilde` equals the accepted weight of the physical accept state
`bb84SiftedLocalPEAcceptedPostMeasurementCQState` on the `ckrMixtureMeasure` de Finetti source.

This identifies the total weight of `bb84EnVRhoEtilde` with the physical acceptance probability.

Proved via `integralTensorPower_ckrMixtureMeasure_eq`, which identifies the de Finetti source with
`ckrDeFinettiState`, itself `(pairedDeFinettiState _ n).partialTraceB` by definition (no purity is
used); the blockwise bridge
`bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned`
transports each τ block, and
`bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq`
lifts the blockwise identity through the fail-closed filter.

References: Nahar et al. 2024 (arXiv:2403.11851) App. B `\label{eq:tausplit}` (main.tex:1356–:1362).
-/
theorem bb84_rhoEtilde_acceptWeight_eq_ckrMixture {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∑ x : Fin n → Fin signalDim,
        ((bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ).stateMap x).trace =
      ∑ ω : Fin n → Fin signalDim,
        ((bb84SiftedLocalPEAcceptedPostMeasurementCQState eveDim pre hpre peSel xSel
            (Quantum.Channels.ckrMixtureMeasure signalDim) Q δ).stateMap ω).trace := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hN' : NeZero (eveDim * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  -- `integralTensorPower n ckrMixtureMeasure = ckrDeFinettiState` (Nahar et al. B13).
  have hμ : InfoTheory.DeFinetti.integralTensorPower n
        (Quantum.Channels.ckrMixtureMeasure signalDim) =
      Quantum.Channels.ckrDeFinettiState signalDim n :=
    Quantum.Channels.integralTensorPower_ckrMixtureMeasure_eq signalDim n
  -- Per-block trace-out-`Eⁿ` identity, lifted through the fail-closed PE filter.  Uses only the
  -- marginal `(pairedDeFinettiState).partialTraceB = ckrDeFinettiState`, which holds by definition
  -- (`ckrDeFinettiState d n := (pairedDeFinettiState d n).partialTraceB`); no purity is needed.
  have hpt : ∀ ω : Fin n → Fin signalDim,
      Quantum.TensorProducts.partialTraceB
          (((bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ).stateMap ω).toOp) =
        ((bb84SiftedLocalPEAcceptedPostMeasurementCQState eveDim pre hpre peSel xSel
            (Quantum.Channels.ckrMixtureMeasure signalDim) Q δ).stateMap ω).toOp := by
    intro ω
    have hblocks : ∀ ω' : Fin n → Fin signalDim,
        Quantum.TensorProducts.partialTraceB
            ((bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
                (pairedDeFinettiState signalDim n)).toCQState.stateMap ω').toOp =
          ((bb84SiftedPostMeasurementCQState eveDim pre hpre peSel xSel
              (InfoTheory.DeFinetti.integralTensorPower n
                (Quantum.Channels.ckrMixtureMeasure signalDim))).stateMap ω').toOp := by
      intro ω'
      rw [hμ]
      exact bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned eveDim pre hpre
          peSel
        xSel (pairedDeFinettiState signalDim n) ω'
    exact bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq
      peSel xSel Q δ _ _ hblocks ω
  apply Finset.sum_congr rfl
  intro ω _
  unfold SubDensityOp.trace
  rw [← Quantum.TensorProducts.trace_partialTraceB
        (((bb84EnVRhoEtilde eveDim pre hpre peSel xSel Q δ).stateMap ω).toOp), hpt ω]

end QKD.BB84.Engine

end
