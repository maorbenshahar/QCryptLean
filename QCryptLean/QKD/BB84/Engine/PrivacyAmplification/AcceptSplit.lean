import QCryptLean.QKD.BB84.Engine.EntropyFloor.EnVDecompositionReferee
import QCryptLean.QKD.BB84.Engine.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.BadBranchConcentration
import QCryptLean.Math.Concentration.DisjointSelectedBinomialPassSum

-- The paired-Haar per-σ family wiring states Bochner integrability of `Op`-valued block maps;
-- as in `PerSigmaFamily.lean`/`FinitePostFilterFloor.lean`, this uses the Frobenius norm.
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

/-!
# The genuine-LOCC pure-paired-Haar per-σ family and its accept mass

The per-component family and accept mass use the fail-closed LOCC two-basis accept event
`bb84SiftedLocalPETestPassed`, applied after the local `H ⊗ H` sift `bb84SiftedRotation`.

## Main definitions

- `bb84PairedHaarPerSigmaFamily`: the pure-paired-Haar per-σ family `f ψ`.
- `bb84SiftedTensorState`: the `n`-round sifted tensor vector, the `ω`-block outer product's square
  root.
- `bb84SiftedPreLocalAcceptMass`: the accept mass of a de Finetti component through a bare
  CPTP pre-channel.

## Main results

- `bb84_f_blocks_integrable`, `bb84PairedHaarPerSigmaFamily_blocks_continuous`: block
  integrability and continuity of the per-σ family in the de Finetti component `ψ`.
- `siftedTensorState_quadForm_eq_prod_born`: the sifted tensor vector's quadratic form against
  `σ^{⊗n}` factors over rounds into a product of single-round Born weights.
- `bb84SiftedPreLocalAcceptMass_eq_sum_quadForm`: the accept mass as the accept-filtered sum of the
  pre-channel's Alice–Bob marginal Born values against the sifted tensor vectors.
- `bb84UnitRegisterEmbed_localAcceptMass_eq_onComponent`: at the bare unit register embedding the
  accept mass **is** the per-component accept mass.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B main.tex:1341–:1413
(Appendix B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}`
(main.tex:1356–:1362), the Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed
min-entropy bound `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting
step `\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413), and
arXiv:2403.11851, `main.tex:909` (general test-set size `m`), `:913` (`n_key = n − m`),
`:970` in `\label{sec:plots}` (`m = 0.05n`); Renner 2005 (arXiv:quant-ph/0512258v2) §6.5;
Christandl–König–Renner 2009 (PRL 102, 020504) main.tex:268–:401 (\emph{Main Result}: Theorem
`\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328). -/

/-! ## 1. The pure-paired-Haar per-σ family -/

/-- **The pure-paired-Haar per-σ family `f ψ`.**

The sifted / fail-closed-local-PE-filtered τ-pipeline applied to the `n`-fold tensor power of the
**pure** paired state `ψ` on `A⊗E = ℂ⁴⊗ℂ⁴`, reindexed to the `Aⁿ⊗Eⁿ` register the pipeline consumes.

The genuine-LOCC counterpart of the referee per-σ family, with the LOCC sift
`bb84SiftedRotation` and the fail-closed two-basis filter
`bb84PostMeasurementCQSiftedLocalPEPassFilter` in place of the referee Bell rotation and
Bell-joint filter.

References: Nahar et al. 2024 (arXiv:2403.11851) App. B `\label{eq:tausplit}` (main.tex:1356–:1362).
-/
noncomputable def bb84PairedHaarPerSigmaFamily {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    CQState (Fin n → Fin signalDim) (eveDim * (signalDim ^ n)) :=
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI : NeZero (signalDim * signalDim) := ⟨by norm_num⟩
  bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
    (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
      (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n))).toCQState

/-- **Block integrability of the paired-Haar family `f`.**

Each register block `ψ ↦ ((f ψ).stateMap x).toOp` is Bochner-integrable against the paired Haar
measure: on the accepting branch the block entry is a fixed finite linear combination of entries of
the reindexed tensor power (`integrable_tensorPow_entry`), on the rejecting branch it vanishes. -/
theorem bb84_f_blocks_integrable {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∀ x : Fin n → Fin signalDim,
      MeasureTheory.Integrable
        (fun ψ : DensityOp (signalDim * signalDim) =>
          ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp)
        (deFinetti_haarMeasure (signalDim * signalDim)).measure := by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hSig2 : NeZero ((signalDim * signalDim) ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  haveI hμ : MeasureTheory.IsProbabilityMeasure
      (deFinetti_haarMeasure (signalDim * signalDim)).measure :=
    (deFinetti_haarMeasure (signalDim * signalDim)).isProbability
  have h_input_entry : ∀ p q : Fin (signalDim ^ n * signalDim ^ n),
      MeasureTheory.Integrable
        (fun ψ : DensityOp (signalDim * signalDim) =>
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp p q)
        (deFinetti_haarMeasure (signalDim * signalDim)).measure := by
    intro p q
    have hrw : (fun ψ : DensityOp (signalDim * signalDim) =>
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp p q) =
        fun ψ : DensityOp (signalDim * signalDim) =>
          (ψ.tensorPowGen n).toOp ((interleavingEquiv signalDim n) p)
            ((interleavingEquiv signalDim n) q) := by
      funext ψ
      simp [densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hrw]
    exact InfoTheory.DeFinetti.integrable_tensorPow_entry n _ _
      (deFinetti_haarMeasure (signalDim * signalDim))
  have h_tau_entry : ∀ r s : Fin (4 ^ n * eveDim * signalDim ^ n),
      MeasureTheory.Integrable
        (fun ψ : DensityOp (signalDim * signalDim) =>
          mapTensorId pre
            (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp r s)
        (deFinetti_haarMeasure (signalDim * signalDim)).measure := by
    intro r s
    simp only [mapTensorId, Matrix.of_apply]
    exact MeasureTheory.integrable_finset_sum _ fun i' _ =>
      MeasureTheory.integrable_finset_sum _ fun j' _ => (h_input_entry _ _).const_mul _
  intro x
  refine matrix_integrable_of_entry_integrable (fun i j => ?_)
  by_cases hpass : bb84SiftedLocalPETestPassed peSel xSel δ Q x = true
  · have heq : (fun ψ : DensityOp (signalDim * signalDim) =>
          ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j) =
        fun ψ : DensityOp (signalDim * signalDim) =>
          (Op.tensor (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
                (1 : Op (signalDim ^ n)) *
              mapTensorId pre
                (densityOp_reindex (interleavingEquiv signalDim n).symm
                  (ψ.tensorPowGen n)).toOp *
              (Op.tensor (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
                (1 : Op (signalDim ^ n)))ᴴ)
            (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
              (dimR := signalDim ^ n) (bb84OutcomeIndex x) i)
            (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
              (dimR := signalDim ^ n) (bb84OutcomeIndex x) j) := by
      funext ψ
      simp only [bb84PairedHaarPerSigmaFamily, bb84PostMeasurementCQSiftedLocalPEPassFilter,
        hpass, if_true, bb84SiftedTauPostMeasurementNormalizedCQState,
        bb84SiftedTauEveRefConditioned, bb84SiftedTauPreOutputDensity,
        densityOpUnitaryConj_toOp, Matrix.submatrix_apply]
      rfl
    rw [heq]
    set U := Op.tensor (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
      (1 : Op (signalDim ^ n)) with hU
    set ei := bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
      (dimR := signalDim ^ n) (bb84OutcomeIndex x) i with hei
    set ej := bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
      (dimR := signalDim ^ n) (bb84OutcomeIndex x) j with hej
    have hentry : ∀ ψ : DensityOp (signalDim * signalDim),
        (U * mapTensorId pre
              (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp *
            Uᴴ) ei ej =
          ∑ s, ∑ r, U ei r *
            mapTensorId pre
              (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp r s *
            Uᴴ s ej := by
      intro ψ
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl ?_
      intro s _
      rw [Matrix.mul_apply, Finset.sum_mul]
    simp_rw [hentry]
    exact MeasureTheory.integrable_finset_sum _ fun s _ =>
      MeasureTheory.integrable_finset_sum _ fun r _ =>
        ((h_tau_entry r s).const_mul _).mul_const _
  · have hfail : bb84SiftedLocalPETestPassed peSel xSel δ Q x = false := Bool.eq_false_iff.mpr hpass
    have heq : (fun ψ : DensityOp (signalDim * signalDim) =>
          ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j) =
        fun _ : DensityOp (signalDim * signalDim) => (0 : ℂ) := by
      funext ψ
      simp only [bb84PairedHaarPerSigmaFamily, bb84PostMeasurementCQSiftedLocalPEPassFilter,
        hfail, Bool.false_eq_true, if_false]
      rfl
    rw [heq]
    exact MeasureTheory.integrable_const 0

/-- **Continuity of the paired-Haar family blocks.**

Each register block `ψ ↦ ((f ψ).stateMap x).toOp` is continuous in the pure paired state `ψ`:
the sift/attack/condition/filter pipeline reads each block entry as a fixed finite linear
functional of the continuous tensor-power entries.  This is the continuity input the generic finite
Carathéodory decomposition needs. -/
theorem bb84PairedHaarPerSigmaFamily_blocks_continuous {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    ∀ x : Fin n → Fin signalDim,
      Continuous
        (fun ψ : DensityOp (signalDim * signalDim) =>
          ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp) := by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have h_input_entry : ∀ p q : Fin (signalDim ^ n * signalDim ^ n),
      Continuous (fun ψ : DensityOp (signalDim * signalDim) =>
        (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp p q) := by
    intro p q
    have hrw : (fun ψ : DensityOp (signalDim * signalDim) =>
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp p q) =
        fun ψ : DensityOp (signalDim * signalDim) =>
          (ψ.tensorPowGen n).toOp ((interleavingEquiv signalDim n) p)
            ((interleavingEquiv signalDim n) q) := by
      funext ψ
      simp [densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hrw]
    exact InfoTheory.DeFinetti.PureState.continuous_tensorPowGen_entry _ _
  have h_tau_entry : ∀ r s : Fin (4 ^ n * eveDim * signalDim ^ n),
      Continuous (fun ψ : DensityOp (signalDim * signalDim) =>
        mapTensorId pre
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp r s) :=
              by
    intro r s
    simp only [mapTensorId, Matrix.of_apply]
    exact continuous_finset_sum _ fun i' _ =>
      continuous_finset_sum _ fun j' _ => continuous_const.mul (h_input_entry _ _)
  intro x
  refine continuous_matrix (fun i j => ?_)
  by_cases hpass : bb84SiftedLocalPETestPassed peSel xSel δ Q x = true
  · have heq : (fun ψ : DensityOp (signalDim * signalDim) =>
          ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j) =
        fun ψ : DensityOp (signalDim * signalDim) =>
          (Op.tensor (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
                (1 : Op (signalDim ^ n)) *
              mapTensorId pre
                (densityOp_reindex (interleavingEquiv signalDim n).symm
                  (ψ.tensorPowGen n)).toOp *
              (Op.tensor (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
                (1 : Op (signalDim ^ n)))ᴴ)
            (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
              (dimR := signalDim ^ n) (bb84OutcomeIndex x) i)
            (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
              (dimR := signalDim ^ n) (bb84OutcomeIndex x) j) := by
      funext ψ
      simp only [bb84PairedHaarPerSigmaFamily, bb84PostMeasurementCQSiftedLocalPEPassFilter,
        hpass, if_true, bb84SiftedTauPostMeasurementNormalizedCQState,
        bb84SiftedTauEveRefConditioned, bb84SiftedTauPreOutputDensity,
        densityOpUnitaryConj_toOp, Matrix.submatrix_apply]
      rfl
    rw [heq]
    set U := Op.tensor (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
      (1 : Op (signalDim ^ n)) with hU
    set ei := bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
      (dimR := signalDim ^ n) (bb84OutcomeIndex x) i with hei
    set ej := bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
      (dimR := signalDim ^ n) (bb84OutcomeIndex x) j with hej
    have hentry : ∀ ψ : DensityOp (signalDim * signalDim),
        (U * mapTensorId pre
              (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp *
            Uᴴ) ei ej =
          ∑ s, ∑ r, U ei r *
            mapTensorId pre
              (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp r s *
            Uᴴ s ej := by
      intro ψ
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl ?_
      intro s _
      rw [Matrix.mul_apply, Finset.sum_mul]
    simp_rw [hentry]
    exact continuous_finset_sum _ fun s _ =>
      continuous_finset_sum _ fun r _ =>
        (continuous_const.mul (h_tau_entry r s)).mul continuous_const
  · have hfail : bb84SiftedLocalPETestPassed peSel xSel δ Q x = false := Bool.eq_false_iff.mpr hpass
    have heq : (fun ψ : DensityOp (signalDim * signalDim) =>
          ((bb84PairedHaarPerSigmaFamily eveDim pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j) =
        fun _ : DensityOp (signalDim * signalDim) => (0 : ℂ) := by
      funext ψ
      simp only [bb84PairedHaarPerSigmaFamily, bb84PostMeasurementCQSiftedLocalPEPassFilter,
        hfail, Bool.false_eq_true, if_false]
      rfl
    rw [heq]
    exact continuous_const

/-! ## 2. The accepting set -/

/-! ## 3. The attacked accept mass of a de Finetti component

The genuine-LOCC counterparts of the referee's sifted tensor vector
`|w_ω⟩ = (bb84SiftedRotation peSel xSel)ᴴ |ωIdx⟩`, the identification of an outcome block
trace with the Born value `⟨w_ω| ρ_AB |w_ω⟩`, and the per-string Born factorization over the
rounds.  These carry the LOCAL `H ⊗ H` sift where the referee objects carry the Bell rotation. -/

/-- **The `n`-round sifted tensor vector.**

`|w_ω⟩ = (bb84SiftedRotation n peSel xSel)ᴴ |ωIdx⟩`, entry
`(|w_ω⟩)_idx = ∏_a conj((H⊗H or 1)_{ω a, idx_a})`, the product vector `tensorFamilyVec` of the
conjugated round rows: the round factor is the `H ⊗ H` row on a PE∧X-designated round and the
standard basis vector `e_{ω a}` elsewhere.  Explicit; no `Classical.choose`. -/
def bb84SiftedTensorState {n : ℕ} (peSel xSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) : Ket (signalDim ^ n) :=
  ⟨tensorFamilyVec fun a x => star (bb84SiftedSinglePairOp (peSel a) (xSel a) (ω a) x)⟩

/-- **Design identity, row form.**  The `ωIdx` row of the sift unitary is the conjugate of the
sifted tensor vector. -/
lemma bb84SiftedRotation_row_eq_conj_tensorState {n : ℕ}
    (peSel xSel : Fin n → Bool) (ω : Fin n → Fin signalDim)
    (l : Fin (signalDim ^ n)) :
    bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) l =
      (starRingEnd ℂ) ((bb84SiftedTensorState peSel xSel ω).vec l) := by
  simp only [bb84SiftedRotation, tensorFamily_apply, bb84SiftedTensorState,
    tensorFamilyVec_apply, map_prod,
    show (@finFunctionFinEquiv signalDim n).symm (bb84OutcomeIndex ω) = ω from
      finFunctionFinEquiv_symm_bb84OutcomeIndex ω]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [starRingEnd_apply, star_star]

/-- **Design identity, quadratic-form version.**  The `(ωIdx, ωIdx)` diagonal entry of the
sift-conjugated operator is the Born value of `|w_ω⟩`. -/
lemma bb84SiftedRotation_conj_diag_eq_quadForm {n : ℕ}
    (peSel xSel : Fin n → Bool) (ω : Fin n → Fin signalDim)
    (M : Op (signalDim ^ n)) :
    (bb84SiftedRotation n peSel xSel * M * (bb84SiftedRotation n peSel xSel)ᴴ)
        (bb84OutcomeIndex ω) (bb84OutcomeIndex ω) =
      ((bb84SiftedTensorState peSel xSel ω).dag * M *
        (bb84SiftedTensorState peSel xSel ω) : ℂ) := by
  rw [bra_mul_ket_eq, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_apply, bra_mul_op_vec, Matrix.conjTranspose_apply,
    bb84SiftedRotation_row_eq_conj_tensorState peSel xSel ω k, starRingEnd_apply, star_star]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [bb84SiftedRotation_row_eq_conj_tensorState peSel xSel ω l, Ket.dag_vec]

/-- **Outcome-block trace = Born value of the pre-channel's Alice–Bob marginal.**

Pushing the sift `bb84SiftedRotation peSel xSel ⊗ 1_E` through the Eve partial trace turns the
`ω`-block trace of the post-measurement CQ state into the Born value
`⟨w_ω| ρ_AB |w_ω⟩.re`, where `ρ_AB = Tr_E (pre ρ)`.

At `pre := attackChannelLinear atk` the marginal `(cptpDensityOp pre hpre ρ).partialTraceB` is
`atk.aliceBobState ρ`. -/
theorem bb84SiftedEveConditioned_trace_eq_quadForm {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (4 ^ n)) (ω : Fin n → Fin signalDim) :
    (bb84SiftedEveConditioned eveDim pre
        hpre peSel xSel ρ ω).trace =
      ((bb84SiftedTensorState peSel xSel ω).dag *
          ((cptpDensityOp pre hpre ρ).partialTraceB).toOp *
        (bb84SiftedTensorState peSel xSel ω) : ℂ).re := by
  set ρAB := ((cptpDensityOp pre hpre ρ).partialTraceB).toOp with hρAB
  -- (A) Push the sift through the Eve partial trace.
  have hPT : partialTraceB (bb84SiftedRotatedPreOutput eveDim pre
        hpre peSel xSel ρ).toOp =
      bb84SiftedRotation n peSel xSel * ρAB * (bb84SiftedRotation n peSel xSel)ᴴ := by
    rw [bb84SiftedRotatedPreOutput, densityOpUnitaryConj_toOp,
      InfoTheory.VonNeumannEntropy.partialTraceB_tensor_conj (bb84SiftedRotation n peSel xSel)
        (1 : Op eveDim) ((cptpDensityOp pre hpre ρ).toOp)
        (by rw [Matrix.conjTranspose_one, Matrix.one_mul])]
    congr 2
  -- (B) The block trace is the AB-diagonal of the pushed-through marginal.
  have h1 : (bb84SiftedEveConditioned eveDim pre
        hpre peSel xSel ρ ω).trace =
      ∑ a : Fin eveDim, ((bb84SiftedRotatedPreOutput eveDim pre
          hpre peSel xSel ρ).toOp
        (bb84OutcomeEveEmbedding (eveDim := eveDim) (bb84OutcomeIndex ω) a)
        (bb84OutcomeEveEmbedding (eveDim := eveDim) (bb84OutcomeIndex ω) a)).re := by
    simp only [bb84SiftedEveConditioned, SubDensityOp.trace, trace_re_submatrix_eq_sum_diag_re]
  have h2 : (bb84SiftedEveConditioned eveDim pre
        hpre peSel xSel ρ ω).trace =
      ((bb84SiftedRotation n peSel xSel * ρAB * (bb84SiftedRotation n peSel xSel)ᴴ)
        (bb84OutcomeIndex ω) (bb84OutcomeIndex ω)).re := by
    rw [h1, ← hPT]
    simp only [partialTraceB, Matrix.of_apply, Complex.re_sum, bb84OutcomeEveEmbedding]
  -- (C) The design identity.
  rw [h2, bb84SiftedRotation_conj_diag_eq_quadForm peSel xSel ω ρAB]

/-- A density operator's computational diagonal entry is real. -/
private lemma densityOp_diag_ofReal (ρ : DensityOp signalDim) (k : Fin signalDim) :
    ρ.toOp k k = ↑((ρ.toOp k k).re) := by
  refine Complex.ext (by rw [Complex.ofReal_re]) ?_
  rw [Complex.ofReal_im]
  have hH : ρ.toOp k k = (starRingEnd ℂ) (ρ.toOp k k) := by
    have hherm := (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).isHermitian
    have hkk := congrFun (congrFun hherm k) k
    rw [Matrix.conjTranspose_apply] at hkk
    exact hkk.symm
  exact Complex.conj_eq_iff_im.mp hH.symm

/-- **Per-round double-sum collapse.**  The per-round double sum of the sifted vector against
`σ` is the single-round Born weight `bb84SiftedBorn`: on a PE∧X round it is the computational
diagonal of `H⊗H · σ · H⊗H` (`bb84XBasisConjugate`), elsewhere the computational diagonal of `σ`. -/
private lemma sifted_perRound_double_sum (peSel xSel : Bool) (σ : DensityOp signalDim)
    (k : Fin signalDim) :
    (∑ x : Fin signalDim, ∑ y : Fin signalDim,
      (starRingEnd ℂ) (star (bb84SiftedSinglePairOp peSel xSel k x)) * σ.toOp x y *
        star (bb84SiftedSinglePairOp peSel xSel k y)) =
      ↑(bb84SiftedBorn peSel xSel σ k) := by
  have hconj : ∀ z : ℂ, (starRingEnd ℂ) (star z) = z := fun z => by
    rw [starRingEnd_apply, star_star]
  simp only [hconj]
  by_cases h : (peSel && xSel) = true
  · -- X-test round: the `H ⊗ H` conjugate's computational diagonal.
    have hU : bb84SiftedSinglePairOp peSel xSel = bb84HadamardPair := by
      unfold bb84SiftedSinglePairOp; rw [if_pos h]
    have hquad : (∑ x : Fin signalDim, ∑ y : Fin signalDim,
          bb84HadamardPair k x * σ.toOp x y * star (bb84HadamardPair k y)) =
        (bb84HadamardPair * σ.toOp * bb84HadamardPair) k k := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have hH : star (bb84HadamardPair k y) = bb84HadamardPair y k := by
        have := congrFun (congrFun bb84HadamardPair_hermitian y) k
        rw [Matrix.conjTranspose_apply] at this
        exact this
      rw [hH]
    rw [hU, hquad, bb84SiftedBorn]
    rw [if_pos h]
    exact densityOp_diag_ofReal (bb84XBasisConjugate σ) k
  · -- Z-test or key round: the unrotated computational diagonal.
    have hU : bb84SiftedSinglePairOp peSel xSel = (1 : Op signalDim) := by
      unfold bb84SiftedSinglePairOp; rw [if_neg h]
    have hcollapse : (∑ x : Fin signalDim, ∑ y : Fin signalDim,
          (1 : Op signalDim) k x * σ.toOp x y * star ((1 : Op signalDim) k y)) =
        σ.toOp k k := by
      simp only [Matrix.one_apply]
      rw [Finset.sum_eq_single k]
      · rw [Finset.sum_eq_single k]
        · simp
        · intro y _ hy; simp [Ne.symm hy]
        · intro hk; exact absurd (Finset.mem_univ k) hk
      · intro x _ hx; simp [Ne.symm hx]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [hU, hcollapse, bb84SiftedBorn, if_neg h]
    exact densityOp_diag_ofReal σ k

/-- **Per-string Born factorization.**

The quadratic form of the sifted tensor vector against `σ^{⊗n}` factors over the rounds into the
product of single-round Born weights:
`⟨w_ω| σ^{⊗n} |w_ω⟩ = ∏_i bb84SiftedBorn (peSel i) (xSel i) σ (ω i)`: the vector is a
product vector and `σ^{⊗n}` a product operator (`tensorFamily_mulVec`,
`dotProduct_tensorFamilyVec`), and each round factor is `sifted_perRound_double_sum`. -/
theorem siftedTensorState_quadForm_eq_prod_born {n : ℕ} [NeZero n]
    [NeZero (signalDim ^ n)]
    (peSel xSel : Fin n → Bool) (σ : DensityOp signalDim)
    (ω : Fin n → Fin signalDim) :
    ((bb84SiftedTensorState peSel xSel ω).dag * (σ.tensorPowGen n).toOp *
        (bb84SiftedTensorState peSel xSel ω) : ℂ) =
      ↑(∏ i : Fin n, bb84SiftedBorn (peSel i) (xSel i) σ (ω i)) := by
  have hquad : ∀ {m : ℕ} (ψ : Ket m) (M : Op m),
      (ψ.dag * M * ψ : ℂ) = star ψ.vec ⬝ᵥ (M *ᵥ ψ.vec) := fun ψ M => by
    rw [braop_mul_ket]; rfl
  rw [hquad, DensityOp.tensorPowGen_toOp_eq_tensorFamily, Complex.ofReal_prod]
  simp only [bb84SiftedTensorState, tensorFamily_mulVec, star_tensorFamilyVec,
    dotProduct_tensorFamilyVec]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← sifted_perRound_double_sum (peSel a) (xSel a) σ (ω a)]
  simp only [dotProduct, mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, mul_assoc]

/-! ## 4. The unit-register accept-mass identity -/

/-- **The accept mass of a de Finetti component `σ`, through a bare CPTP pre-channel.**

The total weight retained by the fail-closed LOCC two-basis filter on the post-measurement CQ
state of the `n`-fold tensor power `σ^{⊗n}` fed through `pre`.  At `pre := attackChannelLinear atk`
this is the attacked accept mass.  The genuine-LOCC counterpart of the referee
quantity `(bb84SiftedAcceptOp n peSel Q δ · aliceBobState(σ^{⊗n})).trace.re`. -/
noncomputable def bb84SiftedPreLocalAcceptMass {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp signalDim) : ℝ :=
  ∑ ω : Fin n → Fin signalDim,
    ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
        (bb84SiftedPostMeasurementCQState eveDim pre hpre peSel xSel (σ.tensorPowGen n))).stateMap
            ω).trace

/-- The accept mass as the accept-filtered sum of the Born values of the pre-channel's
Alice–Bob marginal against the sifted tensor vectors. -/
theorem bb84SiftedPreLocalAcceptMass_eq_sum_quadForm {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp signalDim) :
    bb84SiftedPreLocalAcceptMass eveDim pre hpre peSel xSel Q δ σ =
      ∑ ω : Fin n → Fin signalDim,
        if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then
          ((bb84SiftedTensorState peSel xSel ω).dag *
              ((cptpDensityOp pre hpre (σ.tensorPowGen n)).partialTraceB).toOp *
              (bb84SiftedTensorState peSel xSel ω) : ℂ).re
        else 0 := by
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  simp only [bb84PostMeasurementCQSiftedLocalPEPassFilter, bb84SiftedPostMeasurementCQState]
  split_ifs with h
  · exact bb84SiftedEveConditioned_trace_eq_quadForm eveDim pre hpre peSel xSel
      (σ.tensorPowGen n) ω
  · show SubDensityOp.trace (0 : SubDensityOp eveDim) = 0
    unfold SubDensityOp.trace
    simp only [Matrix.trace,
      show (0 : SubDensityOp eveDim).toPosSemidefOp.toOp = 0 from rfl,
      Matrix.diag_zero, Pi.zero_apply, Complex.zero_re, Finset.sum_const_zero]

/-- **At the unit register embedding the Alice–Bob marginal is the input itself.**  `eveDim = 1`
and the pre-channel is `ρ ↦ ρ ⊗ 1₁`, so `Tr_E(ρ ⊗ 1₁) = (Tr 1₁)·ρ = ρ`. -/
private lemma bb84UnitRegisterEmbed_partialTraceB_toOp (n : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (ρ : DensityOp (4 ^ n)) :
    ((cptpDensityOp (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
        ρ).partialTraceB).toOp = ρ.toOp := by
  have hpt : ((cptpDensityOp (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
        ρ).partialTraceB).toOp =
      Quantum.TensorProducts.partialTraceB
        (cptpDensityOp (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) ρ).toOp := rfl
  rw [hpt, cptpDensityOp_toOp, bb84UnitRegisterEmbed_apply, partialTraceB_tensor_op]
  simp

/-- **At the unit register embedding the accept mass IS the per-component accept mass.**

The one-dimensional side register leaves the Alice–Bob marginal equal to the source `σ^{⊗n}`
(`bb84UnitRegisterEmbed_partialTraceB_toOp`), and the per-string Born factorization
(`siftedTensorState_quadForm_eq_prod_born`) turns each accepted Born value into the product of
the per-round Born weights — which is exactly the summand of
`bb84SiftedLocalAcceptProbabilityOnComponent`.

This is the bridge between the CQ-state accept mass that the paired-Haar family carries and the
scalar accept mass the split-test concentration bounds are stated for. -/
theorem bb84UnitRegisterEmbed_localAcceptMass_eq_onComponent (n : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (σ : DensityOp signalDim) :
    bb84SiftedPreLocalAcceptMass 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel
        xSel Q δ σ =
      bb84SiftedLocalAcceptProbabilityOnComponent n peSel xSel Q δ σ := by
  haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  rw [bb84SiftedPreLocalAcceptMass_eq_sum_quadForm,
    bb84SiftedLocalAcceptProbabilityOnComponent]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  split_ifs with h
  · rw [bb84UnitRegisterEmbed_partialTraceB_toOp n (σ.tensorPowGen n),
      siftedTensorState_quadForm_eq_prod_born peSel xSel σ ω, Complex.ofReal_re]
  · rfl

end QKD.BB84.Engine

end
