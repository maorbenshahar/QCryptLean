import QCryptLean.InfoTheory.Postselection.RawKeyMeasurement
import QCryptLean.InfoTheory.Postselection.Lift
import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized

/-!
# Bounds for the accepted branch of a QKD protocol

`RawKeyMeasurement.badBranchBlockOp_weight_le_of_pAcc_le` integrates the accept-test bound.
`RawKeyMeasurement.referenceSecrecy_le_mixCQ_En_weight` bounds secrecy by total accepted weight.
The latter assumes completely positive idempotent acceptance and agreement of abort outputs;
these assumptions do not assert that acceptance is a projector sandwich.

References: Nahar et al., arXiv:2403.11851, Appendix B proving Theorem 3,
`eq:tausplit` (main.tex:1356–1362) and the bad-branch bound (main.tex:1366–1372).
-/

open Equiv

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts MeasureTheory
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.Postselection

private local instance {n : ℕ} : ContinuousENorm (Op n) :=
  SeminormedAddGroup.toContinuousENorm

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-- An almost-everywhere accept-test bound controls the total bad-branch block weight. -/
theorem RawKeyMeasurement.badBranchBlockOp_weight_le_of_pAcc_le
    (M : RawKeyMeasurement dA dB n)
    (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (Sσhat : Set (DensityOp (dA * dB)))
    (haeSσhat : ∀ᵐ σ ∂μ.measure, σ ∈ Sσhat)
    (goodSet : Set (DensityOp (dA * dB))) (hMeas : MeasurableSet goodSet)
    (εAT : ℝ) (hεAT : 0 ≤ εAT)
    (hacc : ∀ σ ∈ Sσhat \ goodSet, M.pAcc σ ≤ εAT) :
    ∑ x, (badBranchBlockOp μ M.rawKeyCQ goodSet x).trace.re ≤ εAT := by
  haveI : MeasureTheory.IsProbabilityMeasure μ.measure := μ.isProbability
  change ∑ x, (goodBranchBlockOp μ M.rawKeyCQ goodSetᶜ x).trace.re ≤ εAT
  rw [sum_goodBranchBlockOp_trace_re_eq_setIntegral μ M.rawKeyCQ goodSetᶜ h_int]
  -- `\label{eq:condS}` caps `pAcc` on `goodSetᶜ ∩ Sσhat`; `Sσhatᶜ` is μ-null
  have hae : ∀ᵐ σ ∂μ.measure, σ ∈ goodSetᶜ → M.pAcc σ ≤ εAT :=
    haeSσhat.mono fun σ hσ hgood => hacc σ (⟨hσ, hgood⟩ : σ ∈ Sσhat \ goodSet)
  have hpAcc_int : MeasureTheory.Integrable (fun σ : DensityOp (dA * dB) => M.pAcc σ)
      (μ.measure.restrict goodSetᶜ) := by
    simp only [RawKeyMeasurement.pAcc]
    exact MeasureTheory.integrable_finsetSum Finset.univ
      (fun x _ => block_trace_integrable M.rawKeyCQ (μ.measure.restrict goodSetᶜ)
        (fun x => (h_int x).restrict) x)
  calc ∫ σ in goodSetᶜ, M.pAcc σ ∂μ.measure
      ≤ ∫ σ in goodSetᶜ, εAT ∂μ.measure :=
        MeasureTheory.setIntegral_mono_on_ae hpAcc_int
          (integrable_const (εAT : ℝ)).integrableOn hMeas.compl hae
    _ = μ.measure.real goodSetᶜ * εAT := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    _ ≤ 1 * εAT := mul_le_mul_of_nonneg_right measureReal_le_one hεAT
    _ = εAT := by norm_num

/-- An accepted mixture heavier than the outside-set bound has a component in the good set. -/
lemma RawKeyMeasurement.inter_nonempty_of_lt_mixCQ_En_weight
    (M : RawKeyMeasurement dA dB n) (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (P goodSet : Set (DensityOp (dA * dB))) (ε : ℝ)
    (hμ : ∀ᵐ σ ∂μ.measure, σ ∈ P)
    (hacc : ∀ σ ∈ P \ goodSet, M.pAcc σ ≤ ε)
    (hmass : ε < ∑ x, ((M.mixCQ_En μ h_int).stateMap x).trace) :
    (goodSet ∩ P).Nonempty := by
  haveI := μ.isProbability
  by_contra hne
  have hae : ∀ᵐ σ ∂μ.measure, M.pAcc σ ≤ ε :=
    hμ.mono fun σ hσ => hacc σ ⟨hσ, fun hg => hne ⟨σ, hg, hσ⟩⟩
  have hi : MeasureTheory.Integrable M.pAcc μ.measure :=
    MeasureTheory.integrable_finsetSum Finset.univ
      (fun x _ => block_trace_integrable M.rawKeyCQ μ.measure h_int x)
  have hle : ∫ σ, M.pAcc σ ∂μ.measure ≤ ε := by
    simpa using integral_mono_ae hi (integrable_const ε) hae
  rw [← M.mixCQ_En_weight_eq μ h_int] at hle
  exact (not_le_of_gt hmass) hle

/-- The accepted real output on the de Finetti purification has the integrated IID accept mass. -/
lemma RawKeyMeasurement.re_trace_acceptReal_mixturePurification_eq_integral_pAcc
    (M : RawKeyMeasurement dA dB n) (μ : DensityMeasure (dA * dB)) (l' : ℕ)
    (hpAcc_sem : ∀ σ : DensityOp (dA * dB),
      (M.toProtocol.acceptProj (M.toProtocol.variantReal l'
        (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
          (σ.tensorPowGen n).toOp))).trace.re = M.pAcc σ) :
    haveI := M.toProtocol.keyDim_neZero
    haveI := M.toProtocol.annDim_neZero
    let Xhat := Matrix.reindex
      (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) ((dA * dB) ^ n))
      (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) ((dA * dB) ^ n))
      (deFinettiMixturePurification dA dB n μ).toOp
    (mapTensorId M.toProtocol.acceptProj
      (mapTensorId (M.toProtocol.variantReal l') Xhat)).trace.re =
        ∫ σ, M.pAcc σ ∂μ.measure := by
  haveI := M.toProtocol.keyDim_neZero
  haveI := M.toProtocol.annDim_neZero
  dsimp only
  set Xhat := Matrix.reindex
    (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) ((dA * dB) ^ n))
    (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) ((dA * dB) ^ n))
    (deFinettiMixturePurification dA dB n μ).toOp with hXhat
  haveI : MeasureTheory.IsProbabilityMeasure μ.measure := μ.isProbability
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero (dA ^ n * dB ^ n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (pow_pos (NeZero.pos dA) n)
      (pow_pos (NeZero.pos dB) n))⟩
  -- `Ψ := Ω_acc ∘ r ∘ reindex`: on the tensor power it is exactly `hpAcc_sem`'s integrand
  let Ψ : Op ((dA * dB) ^ n) →ₗ[ℂ] Op (M.toProtocol.keyDim * M.toProtocol.annDim) :=
    LinearMap.comp M.toProtocol.acceptProj
      (LinearMap.comp (M.toProtocol.variantReal l')
        (Matrix.reindexLinearEquiv ℂ ℂ (roundGroupEquiv dA dB n)
          (roundGroupEquiv dA dB n)).toLinearMap)
  have hΨ : ∀ Y : Op ((dA * dB) ^ n), Ψ Y = M.toProtocol.acceptProj
      (M.toProtocol.variantReal l'
        (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n) Y)) :=
    fun Y => rfl
  -- the round-regrouped B-marginal of the purification is the round-regrouped mixture
  have h2 : partialTraceB Xhat = Matrix.reindex (roundGroupEquiv dA dB n)
      (roundGroupEquiv dA dB n) (integralTensorPower n μ).toOp := by
    rw [hXhat, partialTraceB_reindex_finProdCongrExt]
    congr 1
    exact congrArg (fun d : DensityOp ((dA * dB) ^ n) => d.toOp)
      (deFinettiMixturePurification_partialTraceB dA dB n μ)
  -- `Tr U = Tr (Ψ (partialTraceB Xhat))`: trace through `mapTensorId` and the B-marginal
  rw [trace_mapTensorId, partialTraceB_mapTensorId, h2,
    ← hΨ, integralTensorPower_map]
  -- the mixture is the Bochner integral of the tensor powers; push `Ψ` and the real trace
  -- through the integral (`integral_comp_comm` for continuous linear maps)
  have hintΨ : MeasureTheory.Integrable
      (fun σ : DensityOp (dA * dB) => Ψ ((σ.tensorPowGen n).toOp)) μ.measure :=
    ((LinearMap.continuous_of_finiteDimensional Ψ).comp
      continuous_tensorPowGen_toOp).integrable_of_compactSpace
  have htre : (∫ σ : DensityOp (dA * dB), Ψ ((σ.tensorPowGen n).toOp) ∂μ.measure).trace.re
      = ∫ σ : DensityOp (dA * dB), (Ψ ((σ.tensorPowGen n).toOp)).trace.re ∂μ.measure :=
    ((Complex.reCLM.comp
      (Matrix.traceLinearMap (Fin (M.toProtocol.keyDim * M.toProtocol.annDim))
        ℝ ℂ).toContinuousLinearMap).integral_comp_comm hintΨ).symm
  rw [htre]
  simp only [hΨ, hpAcc_sem]
/-- Half the trace norm of the reference difference is at most the mixture's accepted weight.
The proof factors through the two positive accepted outputs, applies the trace-norm triangle
bound, and identifies their common trace with the integrated IID acceptance probability. -/
theorem RawKeyMeasurement.referenceSecrecy_le_mixCQ_En_weight
    (M : RawKeyMeasurement dA dB n)
    (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ) (l' : ℕ)
    (hΩ_cp : letI := M.toProtocol.keyDim_neZero; letI := M.toProtocol.annDim_neZero
      IsCompletelyPositive (n := M.toProtocol.keyDim * M.toProtocol.annDim)
        (m := M.toProtocol.keyDim * M.toProtocol.annDim) ⇑M.toProtocol.acceptProj)
    (hpAcc_sem : ∀ σ : DensityOp (dA * dB),
      (M.toProtocol.acceptProj
        (M.toProtocol.variantReal l'
          (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
            (σ.tensorPowGen n).toOp))).trace.re
        = M.pAcc σ) :
    referenceSecrecy M.toProtocol l' μ
      ≤ ∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ_En μ h_int).stateMap x).trace := by
  haveI := M.toProtocol.keyDim_neZero
  haveI := M.toProtocol.annDim_neZero
  haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos M.toProtocol.keyDim_neZero.pos
      M.toProtocol.annDim_neZero.pos)⟩
  haveI : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  -- the round-regrouped purification and the two accept-branch pieces
  set Xhat := Matrix.reindex (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) ((dA * dB) ^ n))
      (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) ((dA * dB) ^ n))
      (deFinettiMixturePurification dA dB n μ).toOp with hXhat
  set U := mapTensorId (k := (dA * dB) ^ n) M.toProtocol.acceptProj
      (mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.variantReal l') Xhat) with hUdef
  set V := mapTensorId (k := (dA * dB) ^ n) M.toProtocol.acceptProj
      (mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.variantIdeal l') Xhat)
  -- The trace-norm argument factors as `U - V`: the subtraction sits inside `mapTensorId Ω`;
  -- distribute it with `mapTensorId_sub`.
  have hfactor : mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
      (deFinettiMixturePurification dA dB n μ).toOp = U - V := by
    have h := PMQKDProtocol.mapTensorId_roundDifferenceMap_eq_acceptProj_sub
      M.toProtocol l' ((dA * dB) ^ n)
      (deFinettiMixturePurification dA dB n μ).toOp
    rw [mapTensorId_sub] at h
    exact h
  -- Complete positivity preserves both accepted output cones.
  have hXhat_psd : Xhat.PosSemidef :=
    Matrix.PosSemidef.reindex
      (posSemidefOp_implies_mathlib (deFinettiMixturePurification dA dB n μ).toPosSemidefOp)
      (Equiv.finProdCongrExt (roundGroupEquiv dA dB n) ((dA * dB) ^ n))
  have hU_psd : U.PosSemidef :=
    mapTensorId_posSemidef M.toProtocol.acceptProj
      (mapTensorId (M.toProtocol.variantReal l') Xhat)
      (mapTensorId_posSemidef (M.toProtocol.variantReal l') Xhat hXhat_psd
        (M.toProtocol.variantReal_isCPTP l').2.1) hΩ_cp
  have hV_psd : V.PosSemidef :=
    mapTensorId_posSemidef M.toProtocol.acceptProj
      (mapTensorId (M.toProtocol.variantIdeal l') Xhat)
      (mapTensorId_posSemidef (M.toProtocol.variantIdeal l') Xhat hXhat_psd
        (M.toProtocol.variantIdeal_isCPTP l').2.1) hΩ_cp
  have hUtrace : U.trace.re = ∫ σ, M.pAcc σ ∂μ.measure :=
    M.re_trace_acceptReal_mixturePurification_eq_integral_pAcc μ l' hpAcc_sem
  have hVtrace : V.trace.re = ∫ σ, M.pAcc σ ∂μ.measure :=
    (M.toProtocol.re_trace_acceptIdeal_eq_re_trace_acceptReal l'
      (deFinettiMixturePurification dA dB n μ).toOp).trans hUtrace
  calc referenceSecrecy M.toProtocol l' μ
      = (1 / 2 : ℝ) * traceNorm (U - V) := by
        unfold referenceSecrecy PMQKDProtocol.referenceDifference
        rw [hfactor]
    _ ≤ (1 / 2 : ℝ) * ((Matrix.trace U).re + (Matrix.trace V).re) :=
        mul_le_mul_of_nonneg_left (traceNorm_sub_le_of_posSemidef hU_psd hV_psd)
          (by norm_num)
    _ = ∫ σ : DensityOp (dA * dB), M.pAcc σ ∂μ.measure := by
        rw [hUtrace, hVtrace]
        ring
    _ = ∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ_En μ h_int).stateMap x).trace :=
        (M.mixCQ_En_weight_eq μ h_int).symm

end InfoTheory.Postselection
