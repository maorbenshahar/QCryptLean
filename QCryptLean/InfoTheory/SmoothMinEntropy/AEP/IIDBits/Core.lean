import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBits.Budget

/-!
# Bit-valued IID spectral entropy floors

The spectral witness supplies an exponential feasible coefficient at the signed block entropy
floor. Inserting that witness gives the extended smooth entropy rate, with all bit conversions
performed in real arithmetic.
-/

open Quantum.Operators
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The bit-normalized setup threshold is the block-length-scaled bit floor. -/
theorem iidAEPBitBlockEntropyFloor_eq_witnessEntropyThreshold
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε =
      W.entropyThreshold := by
  have hcut :
      iidAEPBitSpectralCutCondition ρ hρ_norm σ n_copies ε W :=
    iidAEPBitSpectralSetup_spectralCutCondition hW
  exact hcut.1.symm

/-- Reference domination derived from the bit-normalized spectral setup. -/
theorem iidAEPReferenceDomination_of_bitSpectralSetup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W)
    (hweight_pos :
      0 < ∑ xs : Fin n_copies → X, (W.smoothedState.stateMap xs).trace) :
    iidAEPReferenceDomination σ n_copies W := by
  exact
    iidAEP_reference_domination_from_spectral_cut
      σ n_copies W
      (iidAEPBitSpectralSetup_blockDomination hW)
      hweight_pos

/-- Extract the explicit nonnegative-branch smoothing budget from a
bit-normalized spectral setup. -/
theorem iidAEPNonnegativeRtSmoothingBudget_of_bitSpectralSetupWithRtBudget
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPBitSpectralSetupWithRtBudget
      ρ hρ_norm σ n_copies ε W)
    (hnonnegative : iidAEPNonnegativeThresholdCrossing W) :
    iidAEPNonnegativeRtSmoothingBudget ρ σ n_copies ε W := by
  have hdata : IIDAEPNonnegativeRtBudgetData ρ σ n_copies ε W :=
    iidAEPBitSpectralSetupWithRtBudget_budgetData hW hnonnegative
  refine ⟨hdata.crossing, ?_, ?_⟩
  · simpa [iidAEPRtScalarAdmissibility] using hdata.scalar_admissible
  · simpa [iidAEPRtExponentToSmoothingBudget, iidAEPRtErrorBound]
      using hdata.exponent_to_smoothing

/-- `r_t` trace estimate for the nonnegative crossing branch of the
bit-normalized setup. -/
theorem iidAEPTraceDefect_le_rtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPBitSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε W)
    (hnonnegative : iidAEPNonnegativeThresholdCrossing W) :
    iidAEPTraceDefect ρ n_copies W ≤
      iidAEPRtErrorBound ρ σ n_copies ε W :=
  iidAEPBitSpectralSetupWithRtTraceBridge_traceBridge hW hnonnegative

/-- **Renner's trace-distance purified-distance route for the weight-cap state
(main.tex:4671–4706).**

The weight-cap state `ρ̄` is not a substate of `ρ^{⊗n}`, so the opLe trace-gap
purified-distance bound does not apply. Renner bounds the purified distance by
the trace distance via Fuchs–van de Graaf / Jensen:
`‖ρ^{⊗n} − ρ̄‖₁ ≤ 2√(1 − tr ρ̄)`, with `1 − tr ρ̄ = iidAEPTraceDefect`,
giving `d(ρ^{⊗n}, ρ̄) ≤ √(2 · iidAEPTraceDefect)`.

`hpin : iidAEPIsWeightCapSmoothedState ρ n_copies W` is load-bearing: it
pins the smoothed state to exactly `ρ̄`. Without it the free `smoothedState`
field admits e.g. a pure state orthogonal to `ρ^{⊗n}` with `traceDefect = 0`
yet positive purified distance, falsifying the bound.

`hreference : iidAEPReferenceSpectralDecomposition σ n_copies W` is equally
load-bearing: it pins each `B_z = W.cumulativeProjector z` (a bare field with no
projector property of its own) to an idempotent self-adjoint cumulative spectral
projector of `σ^{⊗ n_copies}`. Without idempotency, taking `B_z = swap` sends
`B_z·|0⟩⟨0|·B_z = |1⟩⟨1|`, yielding a sub-density with `traceDefect = δ`
(RHS `√(2δ) → 0`) but purified distance `1`, falsifying the bound for `δ < 1/2`. -/
theorem iidAEP_weightCap_purifiedDistance_le_sqrt_two_mul_traceDefect
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hpin : iidAEPIsWeightCapSmoothedState ρ n_copies W) :
    CQState.purifiedDistance (iidAEPTensorState ρ n_copies) W.smoothedState
      ≤ Real.sqrt (2 * iidAEPTraceDefect ρ n_copies W) := by
  have hcard : NeZero (Fintype.card (Fin n_copies → X)) :=
    ⟨Fintype.card_ne_zero⟩
  have hjoint : NeZero (n ^ n_copies * Fintype.card (Fin n_copies → X)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hdefect : iidAEPTraceDefect ρ n_copies W
      = (iidAEPTensorState ρ n_copies).toJointDensity.trace
        - W.smoothedState.toJointDensity.trace := by
    unfold iidAEPTraceDefect
    rw [CQState.toJointDensity_trace_eq_sum (iidAEPTensorState ρ n_copies),
        CQState.toJointDensity_trace_eq_sum W.smoothedState]
  rw [hdefect]
  unfold CQState.purifiedDistance
  exact SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_of_fidelityGen_ge
    _ _
    (iidAEP_weightCap_toJointDensity_trace_le ρ σ n_copies W hreference hpin)
    (iidAEP_weightCap_one_sub_traceGap_le_fidelityGen ρ σ n_copies W
      hreference hpin)

/-- Purified-distance smoothing control for a bit-normalized spectral witness. -/
theorem iidAEP_weightCap_purifiedDistance_le_of_rtControlsTrace
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε)
    (W : IIDAEPSpectralWitness X n n_copies)
    (_hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W)
    (hpd_route :
      CQState.purifiedDistance (iidAEPTensorState ρ n_copies) W.smoothedState
        ≤ Real.sqrt (2 * iidAEPTraceDefect ρ n_copies W))
    (hrt : iidAEPRtControlsTrace ρ σ n_copies ε W) :
    CQState.purifiedDistance
      (iidAEPTensorState ρ n_copies) W.smoothedState ≤ ε := by
  have hε_nonneg : 0 ≤ ε := le_of_lt _hε
  have htrace_gap :
      iidAEPTraceDefect ρ n_copies W ≤
        iidAEPSmoothingTraceBudget ε :=
    le_trans hrt.1 hrt.2
  refine le_trans hpd_route ?_
  rw [← iidAEP_sqrt_two_mul_smoothingTraceBudget hε_nonneg]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left htrace_gap (by norm_num)

/-- The bit-normalized spectral threshold bounds extended conditional entropy at any weight. -/
theorem iidAEPBitBlockEntropyFloor_le_conditionalMinEntropy
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W) :
    ENNReal.ofReal (iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε) ≤
      conditionalMinEntropy W.smoothedState (iidAEPTensorReference σ n_copies) := by
  rw [iidAEPBitBlockEntropyFloor_eq_witnessEntropyThreshold ρ hρ_norm σ n_copies ε W hW]
  exact iidAEP_entropy_from_reference_domination σ n_copies W
    (iidAEP_spectral_cut_feasible_domination σ n_copies W
      (iidAEPBitSpectralSetup_blockDomination hW))

/-- Under reference feasibility, the bit entropy contribution is at most the log classical rank. -/
theorem iidAEPBitEntropyContribution_le_logb_classicalRank
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ)) :
    iidAEPBitEntropyContribution ρ hρ_norm σ ≤ Real.logb 2 (ρ.classicalRank : ℝ) := by
  have hsupp := InfoTheory.RelativeEntropy.eigenvalue_support_of_ker_sub
    (ρ.quantumMarginalDensityOp hρ_norm) σ (by
      intro v hv
      change (∑ x, (ρ.stateMap x).toOp).mulVec v = 0
      rw [Matrix.sum_mulVec]
      obtain ⟨t, _, ht⟩ := hfeas
      exact Finset.sum_eq_zero fun x _ =>
        opLe_mulVec_eq_zero_of_psd
          (posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp) (ht x)
          (by
            change (Complex.ofReal t • σ.toOp).mulVec v = 0
            simp only [Matrix.smul_mulVec, hv, smul_zero]))
  have hD := InfoTheory.RelativeEntropy.klein_inequality_support
    (ρ.quantumMarginalDensityOp hρ_norm) σ hsupp
  have hH := ρ.cqConditional_vonNeumann_le_log_classicalRank hρ_norm
  unfold iidAEPBitEntropyContribution Real.logb
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    (by linarith)

/-- Outside the large-block regime, the correction makes the feasible bit floor nonpositive. -/
theorem iidAEPBitEntropyFloor_nonpos_of_not_largeBlock
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hregime : ¬ iidAEPLargeBlockRegime n_copies ε) :
    iidAEPBitEntropyFloor ρ hρ_norm σ n_copies ε ≤ 0 := by
  have hH := iidAEPBitEntropyContribution_le_logb_classicalRank ρ hρ_norm σ hfeas
  have hrank : (1 : ℝ) ≤ (ρ.classicalRank : ℝ) := by
    exact_mod_cast ρ.classicalRank_filter_pos hρ_norm
  have htr := tracedSquareTimesInvFactor_nonneg ρ σ
  have hlog : Real.logb 2 (ρ.classicalRank : ℝ) ≤
      Real.logb 2 ((ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hlog_nonneg : 0 ≤
      Real.logb 2 ((ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hnoise : (1 : ℝ) / 2 < noiseFactor n_copies ε := by
    unfold iidAEPLargeBlockRegime at hregime
    have hlog2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    linarith [not_le.mp hregime]
  unfold iidAEPBitEntropyFloor δ_iidAEP_general
  nlinarith

/-- Renner's bit-normalized AEP floor bounds the extended rate for every positive radius. -/
theorem iidAEPBitEntropyFloor_le_smoothRate_aep
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies]
    (ε : ℝ) (hε : 0 < ε)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ)) :
    ENNReal.ofReal (iidAEPBitEntropyFloor ρ hρ_norm σ n_copies ε) ≤
      iidAEPSmoothRate ρ σ n_copies ε := by
  by_cases hε_lt_one : ε < 1
  swap
  · rw [iidAEPSmoothRate,
      smoothMinEntropy_eq_top_of_weight_le_eps_sq hε.le _ _ (by
        rw [CQState.tensorPower_sum_trace ρ hρ_norm]
        nlinarith), ENNReal.top_div_of_ne_top (by simp)]
    exact le_top
  by_cases hregime : iidAEPLargeBlockRegime n_copies ε
  swap
  · rw [ENNReal.ofReal_eq_zero.mpr
      (iidAEPBitEntropyFloor_nonpos_of_not_largeBlock ρ hρ_norm σ n_copies ε hfeas hregime)]
    exact bot_le
  obtain ⟨W, hW_rt⟩ := exists_iidAEPBitSpectralSetupWithRtTraceBridge
    ρ hρ_norm σ n_copies ε hε hε_lt_one hfeas hregime
  have hW := iidAEPBitSpectralSetupWithRtTraceBridge_setup hW_rt
  have hcrossing := (iidAEPBitSpectralSetup_spectralCutCondition hW).2
  have hbudget := iidAEPNonnegativeRtSmoothingBudget_of_bitSpectralSetupWithRtBudget
    ρ hρ_norm σ n_copies ε hε hε_lt_one W
    (iidAEPBitSpectralSetupWithRtTraceBridge_budgetSetup hW_rt) hcrossing
  have htrace := iidAEPTraceDefect_le_rtErrorBound
    ρ hρ_norm σ n_copies ε hε hε_lt_one W hW_rt hcrossing
  have hrt := iidAEP_rt_trace_control ρ hρ_norm σ n_copies ε W hbudget htrace
  have hpd := iidAEP_weightCap_purifiedDistance_le_sqrt_two_mul_traceDefect
    ρ σ n_copies W (iidAEPBitSpectralSetup_referenceSpectralDecomposition hW)
    (iidAEPBitSpectralSetup_isWeightCapSmoothedState hW)
  exact iidAEPSmoothRate_ge_of_blockFloor_le ρ σ n_copies ε _ W.smoothedState
    (iidAEP_weightCap_purifiedDistance_le_of_rtControlsTrace
      ρ hρ_norm σ n_copies ε hε W hW hpd hrt)
    (iidAEPBitBlockEntropyFloor_le_conditionalMinEntropy ρ hρ_norm σ n_copies ε W hW)


/-- The bit-normalized spectral setup and positive witness weight give the signed conditional
entropy floor `iidAEPBitBlockEntropyFloor`. -/
theorem iidAEPBitBlockEntropyFloor_le_conditionalMinEntropyReal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W)
    (hweight_pos :
      0 < ∑ xs : Fin n_copies → X, (W.smoothedState.stateMap xs).trace) :
    iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε ≤
      conditionalMinEntropyReal W.smoothedState
        (iidAEPTensorReference σ n_copies) := by
  have hthreshold :=
    iidAEPBitBlockEntropyFloor_eq_witnessEntropyThreshold
      ρ hρ_norm σ n_copies ε W hW
  have hdom :=
    iidAEPReferenceDomination_of_bitSpectralSetup
      ρ hρ_norm σ n_copies ε W hW hweight_pos
  have hentropy :=
    iidAEP_entropy_from_reference_dominationReal
      σ n_copies W hdom
  rwa [hthreshold]

/-- A nearby spectral witness with the signed bit-normalized block floor gives the corresponding
signed smooth entropy rate. -/
theorem iidAEPBitEntropyFloor_le_smoothRate_of_smoothApproxReal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 ≤ ε)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε
      (iidAEPTensorState ρ n_copies)
      (iidAEPTensorReference σ n_copies))))
    (h_smooth :
      CQState.purifiedDistance
        (iidAEPTensorState ρ n_copies) W.smoothedState ≤ ε)
    (h_entropy :
      iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε ≤
        conditionalMinEntropyReal W.smoothedState
          (iidAEPTensorReference σ n_copies)) :
    iidAEPBitEntropyFloor ρ hρ_norm σ n_copies ε ≤
      iidAEPSmoothRateReal ρ σ n_copies ε := by
  have h_candidate_le_smooth :
      conditionalMinEntropyReal W.smoothedState
          (iidAEPTensorReference σ n_copies) ≤
        smoothMinEntropyReal ε (iidAEPTensorState ρ n_copies)
          (iidAEPTensorReference σ n_copies) :=
    smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove ε
      (iidAEPTensorState ρ n_copies)
      (iidAEPTensorReference σ n_copies)
      (conditionalMinEntropyReal W.smoothedState
        (iidAEPTensorReference σ n_copies))
      W.smoothedState hbdd h_smooth le_rfl
  have hN_pos : (0 : ℝ) < (n_copies : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n_copies))
  have h_inv_nonneg : 0 ≤ (1 / (n_copies : ℝ)) := by positivity
  have h_floor_scaled :
      iidAEPBitEntropyFloor ρ hρ_norm σ n_copies ε ≤
        (1 / (n_copies : ℝ)) *
          conditionalMinEntropyReal W.smoothedState
            (iidAEPTensorReference σ n_copies) := by
    have hmul := mul_le_mul_of_nonneg_left h_entropy h_inv_nonneg
    have hcancel :
        (1 / (n_copies : ℝ)) *
            iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε =
          iidAEPBitEntropyFloor ρ hρ_norm σ n_copies ε := by
      unfold iidAEPBitBlockEntropyFloor
      field_simp [ne_of_gt hN_pos]
    rwa [hcancel] at hmul
  have h_smooth_scaled :
      (1 / (n_copies : ℝ)) *
          conditionalMinEntropyReal W.smoothedState
            (iidAEPTensorReference σ n_copies) ≤
        iidAEPSmoothRateReal ρ σ n_copies ε := by
    have hmul := mul_le_mul_of_nonneg_left h_candidate_le_smooth h_inv_nonneg
    simpa [iidAEPSmoothRateReal, iidAEPTensorState,
      iidAEPTensorReference] using hmul
  exact le_trans h_floor_scaled h_smooth_scaled

/-- In the large-block regime, the signed smooth entropy rate is at least
`iidAEPBitEntropyFloor` against any feasible reference. -/
theorem iidAEPBitEntropyFloor_le_smoothRate_aepReal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hregime : iidAEPLargeBlockRegime n_copies ε) :
    iidAEPBitEntropyFloor ρ hρ_norm σ n_copies ε ≤
      iidAEPSmoothRateReal ρ σ n_copies ε := by
  obtain ⟨W, hW_rt⟩ :=
    exists_iidAEPBitSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one hfeas hregime
  have hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W :=
    iidAEPBitSpectralSetupWithRtTraceBridge_setup hW_rt
  have htensor_norm :=
    iidAEP_tensor_state_normalized ρ hρ_norm n_copies
  have hbdd :=
    smoothMinEntropyReal_bddAbove ε _hε_lt_one
      (iidAEPTensorState ρ n_copies)
      (iidAEP_tensor_state_normalized ρ hρ_norm n_copies)
      (iidAEPTensorReference σ n_copies)
  have hcrossing : iidAEPNonnegativeThresholdCrossing W :=
    (iidAEPBitSpectralSetup_spectralCutCondition hW).2
  have hrt_budget :
      iidAEPRtBudget ρ σ n_copies ε W :=
    iidAEPNonnegativeRtSmoothingBudget_of_bitSpectralSetupWithRtBudget
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one W
      (iidAEPBitSpectralSetupWithRtTraceBridge_budgetSetup hW_rt)
      hcrossing
  have hrt_estimate :=
    iidAEPTraceDefect_le_rtErrorBound
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one W hW_rt hcrossing
  have hrt :=
    iidAEP_rt_trace_control
      ρ hρ_norm σ n_copies ε W hrt_budget hrt_estimate
  have hweight_pos :=
    iidAEP_smoothed_weight_pos_of_trace_defect_lt_total ρ n_copies W htensor_norm
      (iidAEP_trace_defect_lt_total_of_rt_trace_control
        ρ σ n_copies ε _hε _hε_lt_one W hrt)
  have hpd_route :=
    iidAEP_weightCap_purifiedDistance_le_sqrt_two_mul_traceDefect
      ρ σ n_copies W
      (iidAEPBitSpectralSetup_referenceSpectralDecomposition hW)
      (iidAEPBitSpectralSetup_isWeightCapSmoothedState hW)
  have h_smooth :=
    iidAEP_weightCap_purifiedDistance_le_of_rtControlsTrace
      ρ hρ_norm σ n_copies ε _hε W hW hpd_route hrt
  have h_entropy :=
    iidAEPBitBlockEntropyFloor_le_conditionalMinEntropyReal
      ρ hρ_norm σ n_copies ε W hW hweight_pos
  exact
    iidAEPBitEntropyFloor_le_smoothRate_of_smoothApproxReal
      ρ hρ_norm σ n_copies ε (le_of_lt _hε) W hbdd h_smooth h_entropy

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
