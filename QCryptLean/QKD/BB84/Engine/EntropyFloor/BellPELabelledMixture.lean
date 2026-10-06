import QCryptLean.QKD.BB84.Engine.EntropyFloor.BellFloorChain
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledPerSigmaFloor

-- The de Finetti coarsening assembler states Bochner integrability of `Op`-valued block maps; as in
-- `PerSigmaFamily.lean` / `AcceptSplit.lean`, this uses the Frobenius norm on matrices.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/-!
# The analytic data of the Bell de Finetti mixture floor

The fail-closed-LOCC-two-basis-PE analogues of the CKR post-filter-floor coarsening-assembler
inputs of `BellHaarIntegral.lean` and `BellFloorChain.lean`, at the **Bell**
de Finetti measure `deFinetti_haarMeasure 4` and the Bell-doubled source `ψ = bellWembed φ`:

* `bb84_bellPairedHaarPerSigmaFamily_blocks_continuous` and `bb84_bellF_blocks_integrable` — the
  assembler's `hcont` and `h_int`, the CKR data precomposed with the continuous fixed-matrix
  conjugation `bellWembed φ = W·φ·Wᴴ`;
* `bb84_siftedLocalPE_blocks_eq_integral_of_toOp_eq_integral` — the assembler's `hf_lin` in
  **source-generic** form: whenever the τ-side input is a Bochner integral of inputs, every filtered
  block entry is the corresponding integral.  Fed `bb84BellPairedDeFinettiState_eq_haar_integral`
  on the Bell chain;
* `bb84_pairedHaarPerSigmaFamily_weightRe_eq_preLocalAcceptMass` — each filtered block's total
  trace is the pre-channel accept mass of the Alice–Bob marginal.

## Why the bad branch is pointwise here and not a pushforward

The pushforward of `deFinetti_haarMeasure 4` under `φ ↦ Tr_B (bellWembed φ)` is **not**
`ckrMixtureMeasure signalDim`, so the route of integrating the source cap against a pushed-forward
measure (available on the CKR side) is unavailable on the Bell side.
`InfoTheory.SmoothMinEntropy.traceSetIntegral_le_of_pointwise_weight_bounds` integrates the
pointwise cap against the probability measure directly, so no measure identity is needed.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`), App. B — the
accept-block mixture split `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`) through the smoothed min-entropy bound
`\label{eq:boundingsmoothedmin}` (`main.tex:1380`–`:1387`) — and `main.tex:1428`
`\label{lemma:infsmoothedmin}`; Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5;
Christandl–König–Renner 2009 (`arXiv:0809.3019`) `main.tex:268`–`:401` (\emph{Main Result}: the
Post-Selection Theorem `\label{thm:main}` :291–:301, the substate-extraction Lemma
`\label{lem:extractpart}` :319–:328). -/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy
open InfoTheory.DeFinetti Quantum.Symmetry Math.ClassicalEntropy
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## 1. Continuity and integrability of the Bell per-σ family -/

/-- The Bell-doubling embedding `φ ↦ W·φ·Wᴴ` is continuous: a fixed two-sided matrix product. -/
theorem bellWembed_continuous : Continuous (fun φ : DensityOp 4 => bellWembed φ) := by
  rw [continuous_induced_rng]
  exact (continuous_const.matrix_mul continuous_induced_dom).matrix_mul continuous_const

/-- **`hcont` (Bell).**  Each register block of the per-σ family at the Bell-doubled source is
continuous in the single-pair state `φ`: the CKR block continuity
(`bb84PairedHaarPerSigmaFamily_blocks_continuous`) precomposed with `bellWembed_continuous`. -/
theorem bb84_bellPairedHaarPerSigmaFamily_blocks_continuous {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∀ x : Fin n → Fin signalDim,
      Continuous
        (fun φ : DensityOp 4 =>
          ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
            (bellWembed φ)).stateMap x).toOp) := by
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  intro x
  exact (bb84PairedHaarPerSigmaFamily_blocks_continuous  1 (bb84UnitRegisterEmbed n)
      (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
    x).comp bellWembed_continuous

/-- **`h_int` (Bell).**  Each register block of the per-σ family at the Bell-doubled source is
Bochner-integrable against `deFinetti_haarMeasure 4`: it is continuous on the compact state space
and the Haar measure is a probability measure. -/
theorem bb84_bellF_blocks_integrable {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∀ x : Fin n → Fin signalDim,
      MeasureTheory.Integrable
        (fun φ : DensityOp 4 =>
          ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
            (bellWembed φ)).stateMap x).toOp)
        (deFinetti_haarMeasure 4).measure := by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI : MeasureTheory.IsProbabilityMeasure (deFinetti_haarMeasure 4).measure :=
    (deFinetti_haarMeasure 4).isProbability
  intro x
  exact (bb84_bellPairedHaarPerSigmaFamily_blocks_continuous peSel xSel Q δ
      x).integrable_of_compactSpace

/-! ## 2. The filtered mixture integral -/

/-- **The filtered block entries commute with a Bochner integral over the τ-side input.**

If the τ-side input `τ₀` is the `μ`-Bochner integral of a family of inputs `τ a`, then every
local-PE-filtered block entry of the τ-side pipeline at `τ₀` is the `μ`-integral of the
corresponding entry at `τ a`.  This is the assembler's `hf_lin` with the de Finetti representation
left abstract.

On the accepting branch the pipeline reads each block entry through a **fixed** ℂ-linear functional
`L` of the input operator (the sift conjugation, the linear pre-channel `pre`, τ-block embedding),
which commutes past the integral by `ContinuousLinearMap.integral_comp_comm`; on the rejecting
branch the fail-closed filter zeroes both sides.

`bb84_rhoEtilde_eq_haar_integral_blocks` is the CKR instance (at
`pairedDeFinettiState_eq_haar_integral_paired`); the Bell chain feeds
`bb84BellPairedDeFinettiState_eq_haar_integral`.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, the accept-block mixture split
`\label{eq:tausplit}` (`main.tex:1356`–`:1361`). -/
theorem bb84_siftedLocalPE_blocks_eq_integral_of_toOp_eq_integral {n : ℕ} [NeZero n]
    [NeZero (4 ^ n)] (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (τ₀ : DensityOp (signalDim ^ n * signalDim ^ n))
    (τ : α → DensityOp (signalDim ^ n * signalDim ^ n))
    (hint : MeasureTheory.Integrable (fun a => (τ a).toOp) μ)
    (hτ₀ : τ₀.toOp = ∫ a, (τ a).toOp ∂μ) :
    ∀ (x : Fin n → Fin signalDim) (i j : Fin (eveDim * (signalDim ^ n))),
      ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
          (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
            τ₀).toCQState).stateMap x).toOp i j =
        ∫ a, ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
            (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
              (τ a)).toCQState).stateMap x).toOp i j ∂μ := by
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  intro x i j
  by_cases hpe : bb84SiftedLocalPETestPassed peSel xSel δ Q x
  · -- Accepting branch: read each input block entry through the fixed ℂ-linear functional `L`.
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
    have hgen : ∀ (σ : DensityOp (signalDim ^ n * signalDim ^ n)),
        ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
            (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
              σ).toCQState).stateMap x).toOp i j = L σ.toOp := by
      intro σ
      have hstate : (bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
          (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
            σ).toCQState).stateMap x =
          bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel σ x := by
        change (if bb84SiftedLocalPETestPassed peSel xSel δ Q x then
            (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
                σ).toCQState.stateMap x
          else (0 : SubDensityOp _)) = _
        rw [if_pos hpe]
        rfl
      rw [hstate]
      rfl
    rw [hgen τ₀, hτ₀, ← L.integral_comp_comm hint]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun a => (hgen (τ a)).symm))
  · -- Rejecting branch: the fail-closed filter zeroes the block on both sides.
    have hzero : ∀ (σ : DensityOp (signalDim ^ n * signalDim ^ n)),
        ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
            (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
              σ).toCQState).stateMap x).toOp i j = 0 := by
      intro σ
      change ((if bb84SiftedLocalPETestPassed peSel xSel δ Q x then
          (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
              σ).toCQState.stateMap x
        else (0 : SubDensityOp _)).toOp) i j = 0
      rw [if_neg hpe]
      rfl
    rw [hzero τ₀]
    exact (MeasureTheory.integral_eq_zero_of_ae
      (Filter.Eventually.of_forall (fun a => hzero (τ a)))).symm

/-- **The interleaved Bell-doubled tensor power is Haar-integrable.**

`φ ↦ (bellWembed φ)^{⊗n}(interleaved)` is the image of the continuous map `φ ↦ φ^{⊗n}` on the
compact state space under the fixed continuous linear map `M ↦ rdx(W^{⊗n}·M·(W^{⊗n})ᴴ)`
(`bellWembed_tensorPow_eq_Wconj`), hence integrable against the probability measure
`deFinetti_haarMeasure 4`.  This is the `hint` argument the Bell instance of
`bb84_siftedLocalPE_blocks_eq_integral_of_toOp_eq_integral` needs. -/
theorem bb84_bellWembed_reindexedTensorPow_integrable {n : ℕ} [NeZero n] [NeZero (4 ^ n)] :
    MeasureTheory.Integrable
      (fun φ : DensityOp 4 =>
        (densityOp_reindex (interleavingEquiv signalDim n).symm
          ((bellWembed φ).tensorPowGen n)).toOp)
      (deFinetti_haarMeasure 4).measure := by
  haveI : MeasureTheory.IsProbabilityMeasure (deFinetti_haarMeasure 4).measure :=
    (deFinetti_haarMeasure 4).isProbability
  have htint : MeasureTheory.Integrable
      (fun φ : DensityOp 4 => (φ.tensorPowGen n).toOp) (deFinetti_haarMeasure 4).measure :=
    continuous_tensorPowGen_toOp.integrable_of_compactSpace
  let Lw : Op (4 ^ n) →L[ℂ] Op (4 ^ n * 4 ^ n) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M =>
          Matrix.reindex (interleavingEquiv 4 n).symm (interleavingEquiv 4 n).symm
            (bellDoublingIsometryPow n * M * (bellDoublingIsometryPow n)ᴴ)
        map_add' := by
          intro M N
          ext p q
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
            Matrix.add_apply]
        map_smul' := by
          intro c M
          ext p q
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.reindex_apply,
            Matrix.submatrix_apply, Matrix.smul_apply, RingHom.id_apply] }
  have hintegrand : ∀ φ : DensityOp 4,
      (densityOp_reindex (interleavingEquiv signalDim n).symm
          ((bellWembed φ).tensorPowGen n)).toOp = Lw ((φ.tensorPowGen n).toOp) := by
    intro φ
    change Matrix.reindex (interleavingEquiv 4 n).symm (interleavingEquiv 4 n).symm
        ((bellWembed φ).tensorPowGen n).toOp = _
    rw [bellWembed_tensorPow_eq_Wconj]
    rfl
  have heq : (fun φ : DensityOp 4 =>
        (densityOp_reindex (interleavingEquiv signalDim n).symm
          ((bellWembed φ).tensorPowGen n)).toOp)
      = fun φ => Lw ((φ.tensorPowGen n).toOp) := funext hintegrand
  rw [heq]
  exact Lw.integrable_comp htint

/-! ## 4. The accept-split bad branch -/

/-- **The per-σ block weight is the pre-channel accept mass of the Alice–Bob marginal.**

`∑_x tr (f ψ)_x = bb84SiftedPreLocalAcceptMass eveDim pre hpre … (Tr_B ψ)`: each filtered block's
trace is the trace of its `Eⁿ`-marginal
(`bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq` fed
`bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned`), and the marginal of
the interleaved paired power is `(Tr_B ψ)^{⊗n}` (`partialTraceB_tensorPow_eq`).

Named extraction of the `hsumψ` step used by the Bell accept-split chain, which reads it at
`ψ = bellWembed φ`. -/
theorem bb84_pairedHaarPerSigmaFamily_weightRe_eq_preLocalAcceptMass {n : ℕ} [NeZero n]
    [NeZero (4 ^ n)] (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (ψ : DensityOp (signalDim * signalDim)) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    (∑ x : Fin n → Fin signalDim,
        ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp.trace.re)
      = bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ (DensityOp.partialTraceB ψ) :=
          by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
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
            ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp).trace
      from (trace_partialTraceB _).symm, hbridge x, hτpt]

end QKD.BB84.Engine

end -- noncomputable section
