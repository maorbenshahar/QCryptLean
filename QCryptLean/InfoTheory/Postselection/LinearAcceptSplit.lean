import QCryptLean.InfoTheory.Postselection.RawKeyMeasurementDischarge
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyAcceptSplit

/-!
# Linear accepted-state postselection bounds

Good-branch smooth entropy floors pass to the register-extended mixture. Linear accepted-state
decompositions combine these floors with `hashingError` and the actual trace-gap smoothing
charges.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Quantum.Metrics MeasureTheory
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

namespace RawKeyMeasurement

variable (M : RawKeyMeasurement dA dB n)

/-! ## `hMixFloor` linear good-branch glue (Nahar et al. App. B, main.tex:1364–:1372 (unlabeled; the
Hoeffding accept-radius bound `≤ \epsAT` on the complement)/(B16)/(B17)) -/

/-- A common extended component floor yields one dominated good branch with the same
smoothing radius and an additive register penalty, including an infinite floor. -/
theorem registerExtendedMixtureFloor_linear_le_add
    (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (hcont : ∀ x : Fin M.toProtocol.rawKeyDim,
      Continuous (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp))
    (goodSet Pset : Set (DensityOp (dA * dB)))
    (hClosed : IsClosed goodSet) (hP_closed : IsClosed Pset) (hP_ae : ∀ᵐ σ ∂μ.measure, σ ∈ Pset)
    (K : ENNReal) (εbar εAT : ℝ) (hεbar_nonneg : 0 ≤ εbar)
    (h_badBranch_traceNorm :
      ∑ x : Fin M.toProtocol.rawKeyDim,
          ((Matrix.of fun i j : Fin M.condDim =>
              ∫ σ in goodSetᶜ, ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure :
              Op M.condDim).trace).re ≤ εAT)
    (hf_smoothFloor : ∀ σ ∈ goodSet, σ ∈ Pset →
      K ≤ smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE) :
    ∃ ρ_good_ext : CQState (Fin M.toProtocol.rawKeyDim) M.mixCondDim,
      (∀ x : Fin M.toProtocol.rawKeyDim,
        opLe (ρ_good_ext.stateMap x).toOp ((M.mixCQ μ h_int).stateMap x).toOp) ∧
      (∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ μ h_int).stateMap x).trace) -
          (∑ x : Fin M.toProtocol.rawKeyDim, (ρ_good_ext.stateMap x).trace) ≤ εAT ∧
      K ≤ smoothMinEntropy εbar ρ_good_ext M.mixRef +
        ENNReal.ofReal (2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ)) := by
  have : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  set g := deFinettiPrefactor (dA ^ 2 * dB ^ 2) n
  obtain ⟨ρ_good, hgood_eq, hle, hgap⟩ :=
    exists_goodBranchCQState_of_integrable_traceNormBound_subNormalized
      μ (M.mixCQ_En μ h_int) M.rawKeyCQ goodSet hClosed.measurableSet h_int
      (M.mixCQ_En_hf_lin μ h_int) h_badBranch_traceNorm
  obtain ⟨N, p, ψ, hp_nonneg, hp_sum_le, hψ_mem, hψ_memP, hdecomp⟩ :=
    integralRestrict_eq_finite_subConvexCombination μ M.rawKeyCQ goodSet
      hClosed.measurableSet hClosed hcont Pset hP_closed hP_ae
  have hmix : ∀ x : Fin M.toProtocol.rawKeyDim, (ρ_good.stateMap x).toOp =
      ∑ z, (p z : ℂ) • ((M.rawKeyCQ (ψ z)).stateMap x).toOp := by
    intro x
    ext i j
    rw [hgood_eq x]
    simp only [goodBranchBlockOp, Matrix.of_apply]
    rw [hdecomp x i j, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
  have hfloor : K ≤ smoothMinEntropy εbar ρ_good M.sigmaE := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hf : ∀ z, ENNReal.ofReal (r : ℝ) ≤
        smoothMinEntropy εbar (M.rawKeyCQ (ψ z)) M.sigmaE := by
      intro z
      simpa only [ENNReal.ofReal_coe_nnreal] using
        hr.le.trans (hf_smoothFloor (ψ z) (hψ_mem z) (hψ_memP z))
    simpa only [ENNReal.ofReal_coe_nnreal] using
      smoothMinEntropy_subMixture_ge_inf_component εbar hεbar_nonneg
        p hp_nonneg hp_sum_le (fun z => M.rawKeyCQ (ψ z)) ρ_good hmix M.sigmaE r hf
  have hCpsd : ((1 / (g : ℂ)) • (1 : Op g)).PosSemidef := by
    rw [← toSubDensityOp_maxMixed_toOp_eq g]
    exact posSemidefOp_implies_mathlib
      (DensityOp.toSubDensityOp (DensityOp.maxMixed g)).toPosSemidefOp
  have htr : ∀ (ρ : CQState (Fin M.toProtocol.rawKeyDim) M.condDim)
      (x : Fin M.toProtocol.rawKeyDim), ((ρ.tensorMaxMixed g).stateMap x).trace =
        (ρ.stateMap x).trace := by
    intro ρ x
    simp [CQState.tensorMaxMixed, SubDensityOp.tensorMaxMixed_trace]
  refine ⟨ρ_good.tensorMaxMixed g, ?_, ?_, ?_⟩
  · intro x
    change opLe ((ρ_good.tensorMaxMixed g).stateMap x).toOp
      (((M.mixCQ_En μ h_int).tensorMaxMixed g).stateMap x).toOp
    rw [CQState.tensorMaxMixed_stateMap_toOp, CQState.tensorMaxMixed_stateMap_toOp]
    exact opLe_tensor_psd (ρ_good.stateMap x).isHermitian
      (posSemidefOp_implies_mathlib ((M.mixCQ_En μ h_int).stateMap x).toPosSemidefOp)
      hCpsd hCpsd.isHermitian (hle x) (fun _ => le_rfl)
  · change (∑ x, (((M.mixCQ_En μ h_int).tensorMaxMixed g).stateMap x).trace) -
        (∑ x, ((ρ_good.tensorMaxMixed g).stateMap x).trace) ≤ εAT
    simpa only [htr] using hgap
  · have hext := smoothMinEntropy_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius
      (ρ_good.tensorMaxMixed g) ρ_good M.sigmaE
      (CQState.tensorMaxMixed_partialTraceB g ρ_good) εbar
    have h := hfloor.trans hext
    simp only [mul_div_assoc] at h
    exact h

/-- A completed signed floor holds on a dominated good branch, with bad-branch weight charged
only to the trace gap and with no positive retained-weight premise. -/
theorem registerExtendedMixtureFloor_linear
    (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (hcont : ∀ x : Fin M.toProtocol.rawKeyDim,
      Continuous (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp))
    (goodSet Pset : Set (DensityOp (dA * dB)))
    (hClosed : IsClosed goodSet) (hP_closed : IsClosed Pset) (hP_ae : ∀ᵐ σ ∂μ.measure, σ ∈ Pset)
    (k εbar εAT : ℝ) (hεbar_nonneg : 0 ≤ εbar)
    (h_badBranch_traceNorm :
      ∑ x : Fin M.toProtocol.rawKeyDim,
          ((Matrix.of fun i j : Fin M.condDim =>
              ∫ σ in goodSetᶜ, ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure :
              Op M.condDim).trace).re ≤ εAT)
    (hf_smoothFloor : ∀ σ ∈ goodSet, σ ∈ Pset →
      ENNReal.ofReal k ≤ smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE) :
    ∃ ρ_good_ext : CQState (Fin M.toProtocol.rawKeyDim) M.mixCondDim,
      (∀ x : Fin M.toProtocol.rawKeyDim,
        opLe (ρ_good_ext.stateMap x).toOp ((M.mixCQ μ h_int).stateMap x).toOp) ∧
      (∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ μ h_int).stateMap x).trace) -
          (∑ x : Fin M.toProtocol.rawKeyDim, (ρ_good_ext.stateMap x).trace) ≤ εAT ∧
      ENNReal.ofReal (k - 2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ)) ≤
        smoothMinEntropy εbar ρ_good_ext M.mixRef := by
  obtain ⟨ρ_good_ext, hle, hgap, hfloor⟩ := M.registerExtendedMixtureFloor_linear_le_add
    μ h_int hcont goodSet Pset hClosed hP_closed hP_ae (ENNReal.ofReal k) εbar εAT
    hεbar_nonneg h_badBranch_traceNorm hf_smoothFloor
  refine ⟨ρ_good_ext, hle, hgap, ?_⟩
  have hp : 0 ≤ 2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ) := by
    apply mul_nonneg (by norm_num)
    exact Real.logb_nonneg (by norm_num)
      (by exact_mod_cast deFinettiPrefactor_pos (dA ^ 2 * dB ^ 2) n)
  rw [ENNReal.ofReal_sub k hp]
  exact tsub_le_iff_right.mpr hfloor


/-- A component signed smooth floor `k` yields a dominated good branch on the extended register
with floor `k - 2 * logb 2 g` and trace gap at most `εAT`. -/
theorem registerExtendedMixtureFloorReal_linear
    (μ : DensityMeasure (dA * dB)) (h_int : M.Integrable μ)
    (hcont : ∀ x : Fin M.toProtocol.rawKeyDim,
      Continuous (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp))
    (goodSet Pset : Set (DensityOp (dA * dB))) (hMeas : MeasurableSet goodSet)
    (hClosed : IsClosed goodSet) (hP_closed : IsClosed Pset) (hP_ae : ∀ᵐ σ ∂μ.measure, σ ∈ Pset)
    (k εbar εAT : ℝ) (hεbar_nonneg : 0 ≤ εbar)
    (h_subNorm_linear : 2 * εbar + εAT <
      ∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ_En μ h_int).stateMap x).trace)
    (h_badBranch_traceNorm :
      ∑ x : Fin M.toProtocol.rawKeyDim,
          ((Matrix.of fun i j : Fin M.condDim =>
              ∫ σ in goodSetᶜ, ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure :
              Op M.condDim).trace).re
        ≤ εAT)
    (hf_smoothFloor : ∀ σ ∈ goodSet, σ ∈ Pset →
      k ≤ smoothMinEntropyReal εbar (M.rawKeyCQ σ) M.sigmaE) :
    ∃ ρ_good_ext : CQState (Fin M.toProtocol.rawKeyDim) M.mixCondDim,
      (∀ x : Fin M.toProtocol.rawKeyDim,
        opLe (ρ_good_ext.stateMap x).toOp ((M.mixCQ μ h_int).stateMap x).toOp) ∧
      (∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ μ h_int).stateMap x).trace)
          - (∑ x : Fin M.toProtocol.rawKeyDim, (ρ_good_ext.stateMap x).trace) ≤ εAT ∧
      k - 2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ)
        ≤ smoothMinEntropyReal εbar ρ_good_ext M.mixRef := by
  have : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  have := M.condDim_neZero
  have := M.toProtocol.rawKeyDim_neZero
  have : Nonempty (Fin M.toProtocol.rawKeyDim) := ⟨(0 : Fin M.toProtocol.rawKeyDim)⟩
  set g := deFinettiPrefactor (dA ^ 2 * dB ^ 2) n with hg
  obtain ⟨ρ_good, hle, hgap, hfloor⟩ :=
  smoothMinEntropyReal_ge_goodBranch_of_deFinetti_postFilter_finiteSmoothFloor_subNormalized_linear
      μ (M.mixCQ_En μ h_int) M.rawKeyCQ M.sigmaE M.sigmaE_posDef h_int
      (M.mixCQ_En_hf_lin μ h_int) hcont goodSet hMeas hClosed Pset hP_closed hP_ae
      k εbar εAT hεbar_nonneg h_subNorm_linear
      h_badBranch_traceNorm hf_smoothFloor
  have hCpsd : ((1 / (g : ℂ)) • (1 : Op g)).PosSemidef := by
    rw [← toSubDensityOp_maxMixed_toOp_eq g]
    exact posSemidefOp_implies_mathlib
      (DensityOp.toSubDensityOp (DensityOp.maxMixed g)).toPosSemidefOp
  have htr : ∀ (ρ : CQState (Fin M.toProtocol.rawKeyDim) M.condDim)
      (x : Fin M.toProtocol.rawKeyDim), ((ρ.tensorMaxMixed g).stateMap x).trace
        = (ρ.stateMap x).trace := by
    intro ρ x
    simp [CQState.tensorMaxMixed, SubDensityOp.tensorMaxMixed_trace]
  refine ⟨ρ_good.tensorMaxMixed g, ?_, ?_, ?_⟩
  · -- `opLe` lifts blockwise through `⊗ (1/g)•I_g`.
    intro x
    have hmix_eq : ((M.mixCQ μ h_int).stateMap x).toOp
        = ((M.mixCQ_En μ h_int).stateMap x).toOp ⊗ ((1 / (g : ℂ)) • (1 : Op g)) := by
      rw [RawKeyMeasurement.mixCQ, CQState.tensorMaxMixed_stateMap_toOp]
    rw [CQState.tensorMaxMixed_stateMap_toOp, hmix_eq]
    exact opLe_tensor_psd (ρ_good.stateMap x).isHermitian
      (posSemidefOp_implies_mathlib ((M.mixCQ_En μ h_int).stateMap x).toPosSemidefOp)
      hCpsd hCpsd.isHermitian (hle x) (fun _ => le_rfl)
  · -- Trace gap preserved by the max-mixed extension.
    have hmix : (∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ μ h_int).stateMap x).trace)
        = ∑ x : Fin M.toProtocol.rawKeyDim, ((M.mixCQ_En μ h_int).stateMap x).trace := by
      rw [RawKeyMeasurement.mixCQ]
      exact Finset.sum_congr rfl (fun x _ => htr (M.mixCQ_En μ h_int) x)
    exact (congrArg₂ (fun a b : ℝ => a - b) hmix
      (Finset.sum_congr rfl (fun x _ => htr ρ_good x))).le.trans hgap
  · -- B17 register-extension penalty at the same radius `ε̄`, chained with the good floor.
    rw [RawKeyMeasurement.mixRef]
    have hB17 :
        smoothMinEntropyReal εbar ρ_good M.sigmaE - 2 * Real.log (g : ℝ) / Real.log 2
          ≤ smoothMinEntropyReal εbar (ρ_good.tensorMaxMixed g) (M.sigmaE.tensorMaxMixed g) :=
      smoothMinEntropyReal_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius
        (ρ_good.tensorMaxMixed g) ρ_good M.sigmaE
        (CQState.tensorMaxMixed_partialTraceB g ρ_good) εbar hεbar_nonneg
    have hlogb : Real.logb 2 (g : ℝ) = Real.log (g : ℝ) / Real.log 2 := rfl
    have hassoc : 2 * Real.log (g : ℝ) / Real.log 2 = 2 * (Real.log (g : ℝ) / Real.log 2) := by
      ring
    rw [hlogb]
    rw [hassoc] at hB17
    exact (sub_le_sub_right hfloor _).trans hB17

end RawKeyMeasurement

/-! ## The linear protocol-level postselection theorem (Nahar et al. App. B, B14 accept-split) -/

/-! ## The acceptance-criterion closure: the linear conclusion at Nahar et al.'s own hypotheses -/

/-- Extended IID entropy and the linear accept split bound reference secrecy by
`εPA + 2 * εbar + 2 * εAT`, without a retained-mass or radius upper bound.
The realization map need only preserve the support of the protocol difference. -/
theorem postselection_linear_referenceBound_of_iidSecurityProof
    (M : RawKeyMeasurement dA dB n) (μ : DensityMeasure (dA * dB))
    (εAT εPA εbar : ℝ) (l' : ℕ) (h_int : M.Integrable μ)
    (hproof : HasIIDSecurityProof M.toProtocol εAT εPA εbar)
    (hl' : (l' : ℝ) ≤
      (M.toProtocol.l : ℝ) - 2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n))
    (hι : hproof.ι = DensityOp (dA * dB))
    (hcond : hproof.condDim = M.condDim)
    (hraw : HEq hproof.rawKeyCQ M.rawKeyCQ)
    (href : HEq hproof.ref M.refCommon)
    (goodSet Pset : Set (DensityOp (dA * dB)))
    (hS : HEq hproof.S (goodSet ∩ Pset))
    (hClosed : IsClosed goodSet)
    (hP_closed : IsClosed Pset) (hP_ae : ∀ᵐ σ ∂μ.measure, σ ∈ Pset)
    (hcont : ∀ x : Fin M.toProtocol.rawKeyDim,
      Continuous (fun σ : DensityOp (dA * dB) => ((M.rawKeyCQ σ).stateMap x).toOp))
    (h_badBranch_traceNorm :
      ∑ x : Fin M.toProtocol.rawKeyDim,
          ((Matrix.of fun i j : Fin M.condDim =>
              ∫ σ in goodSetᶜ, ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure :
              Op M.condDim).trace).re ≤ εAT)
    {S Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (H : QuantumHashFamily S (Fin M.toProtocol.rawKeyDim) Z)
    (hH : H.isUniversal) (hcardZ : Fintype.card Z = 2 ^ l')
    (V : Matrix (Fin (M.mixCondDim * Fintype.card (S × Z)))
                (Fin (M.toProtocol.keyDim * M.toProtocol.annDim * (dA * dB) ^ n)) ℂ)
    (hV : Vᴴ * V * M.toProtocol.referenceDifference l' μ =
      M.toProtocol.referenceDifference l' μ)
    (hPA_realization :
      haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
      haveI : NeZero (M.mixCondDim * Fintype.card (S × Z)) :=
        ⟨Nat.mul_ne_zero M.instNeZeroMixCondDim.out Fintype.card_ne_zero⟩
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
        ⟨Nat.mul_ne_zero M.toProtocol.keyDim_neZero.ne M.toProtocol.annDim_neZero.ne⟩
      haveI : NeZero ((dA * dB) ^ n) :=
        ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
      (seedKeyExtractorOutputState H (M.mixCQ μ h_int)).toJointDensity.toOp -
          (seedUniformOutputState (M.mixCQ μ h_int).quantumMarginal).toJointDensity.toOp =
        V *
            (mapTensorId (k := (dA * dB) ^ n) (M.toProtocol.roundDifferenceMap l')
              (deFinettiMixturePurification dA dB n μ).toOp) * Vᴴ) :
    referenceSecrecy M.toProtocol l' μ ≤ εPA + 2 * εbar + 2 * εAT := by
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (M.mixCondDim * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero M.instNeZeroMixCondDim.out Fintype.card_ne_zero⟩
  have := M.toProtocol.keyDim_neZero
  have := M.toProtocol.annDim_neZero
  have : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
    ⟨Nat.mul_ne_zero M.toProtocol.keyDim_neZero.ne M.toProtocol.annDim_neZero.ne⟩
  have : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  rw [M.referenceSecrecy_eq_seedKeyExtractor_traceDistanceGen μ M.mixCondDim
    M.instNeZeroMixCondDim (M.mixCQ μ h_int) l' H V hV hPA_realization]
  have hεbar_nonneg := hproof.eq11.2.1
  obtain ⟨ι, Sσhat, S', pAcc, condTraceDist, condDim, condDim_neZero, rawKeyCQ, ref,
    eq10, eq11⟩ := hproof
  subst hι
  subst hcond
  rw [heq_iff_eq] at hraw href hS
  subst hraw
  subst href
  subst hS
  let K := ⨅ σ : (goodSet ∩ Pset : Set (DensityOp (dA * dB))),
    smoothMinEntropy εbar (M.rawKeyCQ σ.1) M.sigmaE
  have hpa : hashingError M.toProtocol.l K ≤ εPA := by
    apply hashingError_iInf_le _ _ eq11.1
    intro σ
    exact le_of_add_le_add_right (eq11.2.2 σ σ.2).2
  have hf : ∀ σ ∈ goodSet, σ ∈ Pset →
      K ≤ smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE := by
    intro σ hσg hσp
    exact iInf_le (fun σ' : (goodSet ∩ Pset : Set (DensityOp (dA * dB))) =>
      smoothMinEntropy εbar (M.rawKeyCQ σ'.1) M.sigmaE) ⟨σ, hσg, hσp⟩
  obtain ⟨ρ_good, hle, hgap, hfloor⟩ := M.registerExtendedMixtureFloor_linear_le_add
    μ h_int hcont goodSet Pset hClosed hP_closed hP_ae K εbar εAT
    hεbar_nonneg h_badBranch_traceNorm hf
  let ρ_bad := cqStateSubOfOpLe (M.mixCQ μ h_int) ρ_good hle
  have hsplit : ∀ x, ((M.mixCQ μ h_int).stateMap x).toOp =
      (ρ_good.stateMap x).toOp + (ρ_bad.stateMap x).toOp := by
    intro x
    rw [cqStateSubOfOpLe_stateMap_toOp]
    abel
  obtain ⟨hExtSplit, hIdealSplit⟩ := seedKeyExtractor_seedUniform_toJointDensity_add_of_split
    H (M.mixCQ μ h_int) ρ_good ρ_bad hsplit
  have hbad : ρ_bad.quantumMarginal.trace ≤ εAT := by
    rw [cqStateSubOfOpLe_quantumMarginal_trace]
    exact hgap
  have hExtPSD : (seedKeyExtractorOutputState H ρ_bad).toJointDensity.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib
      (seedKeyExtractorOutputState H ρ_bad).toJointDensity.toPosSemidefOp
  have hIdealPSD : (seedUniformOutputState (S := S) (Z := Z)
      ρ_bad.quantumMarginal).toJointDensity.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib
      (seedUniformOutputState (S := S) (Z := Z) ρ_bad.quantumMarginal).toJointDensity.toPosSemidefOp
  have hs : (1 / 2) * traceNorm (seedKeyExtractorOutputState H ρ_bad).toJointDensity.toOp +
      (1 / 2) * traceNorm
        (seedUniformOutputState (S := S) (Z := Z) ρ_bad.quantumMarginal).toJointDensity.toOp ≤
      εAT := by
    rw [Quantum.Channels.traceNorm_posSemidef_eq_trace _ hExtPSD,
      Quantum.Channels.traceNorm_posSemidef_eq_trace _ hIdealPSD,
      seedKeyExtractorOutputState_joint_trace_eq_quantumMarginal_trace,
      seedUniformOutputState_joint_trace_eq_quantumMarginal_trace]
    linarith only [hbad]
  have hAS := InfoTheory.CKRPostselection.traceDistanceGen_le_acceptSplit
    (seedKeyExtractorOutputState H (M.mixCQ μ h_int)).toJointDensity.toOp
    (seedKeyExtractorOutputState H ρ_good).toJointDensity.toOp
    (seedKeyExtractorOutputState H ρ_bad).toJointDensity.toOp
    (seedUniformOutputState (S := S) (Z := Z) (M.mixCQ μ h_int).quantumMarginal).toJointDensity.toOp
    (seedUniformOutputState (S := S) (Z := Z) ρ_good.quantumMarginal).toJointDensity.toOp
    (seedUniformOutputState (S := S) (Z := Z) ρ_bad.quantumMarginal).toJointDensity.toOp
    εAT hExtSplit hIdealSplit hs
  have hLHL := quantum_seedKey_LHL_smooth_hashingError H hH ρ_good M.mixRef
    M.mixRef_posDef εbar hεbar_nonneg l' hcardZ
  have hp : 0 ≤ 2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ) := by
    apply mul_nonneg (by norm_num)
    exact Real.logb_nonneg (by norm_num)
      (by exact_mod_cast deFinettiPrefactor_pos (dA ^ 2 * dB ^ 2) n)
  have herr := hashingError_le_of_le_add M.toProtocol.l l'
    (2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ)) K
    (smoothMinEntropy εbar ρ_good M.mixRef) hp hfloor hl'
  linarith only [hAS, hLHL, herr, hpa]

end InfoTheory.Postselection
