import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.SpectralSetup

/-!
# Assembling IID entropy bounds

Reference domination yields a conditional entropy floor for the spectral witness. Purified-
distance control inserts the witness into canonical smooth entropy. Real relative-entropy algebra
and bit conversions are completed before the floor is cast to `ENNReal`.
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.VonNeumannEntropy
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open InfoTheory.SmoothMinEntropy.IIDAEPCumulative

/-- Spectral-cut block domination accessor: each retained projector-sandwich
block is dominated by `2 ^ (-entropyThreshold)` times the tensor-power
reference.

This theorem exposes the explicit relative-truncation obligation carried by
the spectral setup; the bare projector identity and reference spectral cut do
not imply it by themselves. -/
theorem iidAEP_spectral_cut_block_domination
    {X : Type*} [Fintype X]
    {n : ℕ} [NeZero n]
    (σ : DensityOp n)
    (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hblock : iidAEPSpectralCutBlockDomination σ n_copies W) :
    ∀ xs : Fin n_copies → X,
      opLe (W.smoothedState.stateMap xs).toOp
        (Complex.ofReal (iidAEPSpectralCutDominationScale W) •
          (iidAEPTensorReference σ n_copies).toOp) := by
  exact hblock

/-- Package the explicit spectral-cut block domination as a feasible scalar for
the conditional min-entropy SDP. -/
theorem iidAEP_spectral_cut_feasible_domination
    {X : Type*} [Fintype X]
    {n : ℕ} [NeZero n]
    (σ : DensityOp n)
    (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hblock : iidAEPSpectralCutBlockDomination σ n_copies W) :
    isFeasible W.smoothedState (iidAEPTensorReference σ n_copies)
      (iidAEPSpectralCutDominationScale W) := by
  refine ⟨le_of_lt ?_, ?_⟩
  · unfold iidAEPSpectralCutDominationScale
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  · exact iidAEP_spectral_cut_block_domination
      σ n_copies W hblock

lemma iidAEPSmoothingTraceBudget_lt_one {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    iidAEPSmoothingTraceBudget ε < 1 := by
  unfold iidAEPSmoothingTraceBudget
  have hε_sq_lt_one : ε ^ 2 < 1 := by
    nlinarith [sq_nonneg ε, hε_nonneg, hε_lt_one]
  nlinarith

/-- The `r_t` trace-control budget keeps the spectral truncation from losing
all tensor-power mass in the positive branch `0 < ε < 1`. -/
theorem iidAEP_trace_defect_lt_total_of_rt_trace_control
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ)
    (ε : ℝ) (_hε : 0 < ε)
    (hε_lt_one : ε < 1)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hrt : iidAEPRtControlsTrace ρ σ n_copies ε W) :
    iidAEPTraceDefect ρ n_copies W < 1 := by
  exact lt_of_le_of_lt (le_trans hrt.1 hrt.2)
    (iidAEPSmoothingTraceBudget_lt_one (le_of_lt _hε) hε_lt_one)

/-- If the retained trace defect is strictly smaller than the normalized total
mass, then the smoothed spectral witness has strictly positive CQ weight. -/
theorem iidAEP_smoothed_weight_pos_of_trace_defect_lt_total
    {X : Type*} [Fintype X]
    {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (htensor_norm :
      ∑ xs : Fin n_copies → X,
        ((iidAEPTensorState ρ n_copies).stateMap xs).trace = 1)
    (htrace_lt_total : iidAEPTraceDefect ρ n_copies W < 1) :
    0 < ∑ xs : Fin n_copies → X, (W.smoothedState.stateMap xs).trace := by
  unfold iidAEPTraceDefect at htrace_lt_total
  rw [htensor_norm] at htrace_lt_total
  linarith

/-- A positive retained CQ mass plus one feasible scalar makes the
min-feasible-lambda optimum strictly positive. This is the elementary
order-theoretic reduction used by the spectral-cut reference-domination
assembly. -/
theorem iidAEP_minFeasibleLambda_pos_of_weight_pos_and_isFeasible
    {Y : Type*} [Fintype Y] [Nonempty Y] {m : ℕ}
    (ρ : CQState Y m) (σ : SubDensityOp m) {t : ℝ}
    (hweight_pos : 0 < ∑ y : Y, (ρ.stateMap y).trace)
    (hfeasible : isFeasible ρ σ t) :
    0 < minFeasibleLambda ρ σ := by
  exact minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos
    ρ σ hweight_pos ⟨t, hfeasible⟩

/-- Reference domination derived from explicit spectral-cut block domination
plus separately established positive retained mass. The feasibility input is
the relative truncation obligation, not a consequence of the bare projector
identity or reference spectral cut; upstream callers extract it from the setup. -/
theorem iidAEP_reference_domination_from_spectral_cut
    {X : Type*} [Fintype X]
    {n : ℕ} [NeZero n]
    (σ : DensityOp n)
    (n_copies : ℕ)
    [Nonempty (Fin n_copies → X)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hblock : iidAEPSpectralCutBlockDomination σ n_copies W)
    (hweight_pos :
      0 < ∑ xs : Fin n_copies → X, (W.smoothedState.stateMap xs).trace) :
    iidAEPReferenceDomination σ n_copies W := by
  have hfeasible :
      isFeasible W.smoothedState (iidAEPTensorReference σ n_copies)
        (iidAEPSpectralCutDominationScale W) :=
    iidAEP_spectral_cut_feasible_domination
      σ n_copies W hblock
  exact
    ⟨iidAEP_minFeasibleLambda_pos_of_weight_pos_and_isFeasible
        W.smoothedState (iidAEPTensorReference σ n_copies)
        hweight_pos hfeasible,
      hfeasible⟩

/-- Nonnegative-branch scalar budget extracted from explicit
Chernoff/MGF exponent-to-smoothing data attached to the spectral setup. -/
theorem iidAEP_nonnegative_rt_smoothing_budget_obligation
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPSpectralSetupWithRtBudget
      ρ hρ_norm σ n_copies ε W)
    (hnonnegative : iidAEPNonnegativeThresholdCrossing W) :
    iidAEPNonnegativeRtSmoothingBudget ρ σ n_copies ε W := by
  have hdata : IIDAEPNonnegativeRtBudgetData ρ σ n_copies ε W :=
    iidAEPSpectralSetupWithRtBudget_budgetData hW hnonnegative
  refine ⟨hdata.crossing, ?_, ?_⟩
  · simpa [iidAEPRtScalarAdmissibility] using hdata.scalar_admissible
  · simpa [iidAEPRtExponentToSmoothingBudget, iidAEPRtErrorBound]
      using hdata.exponent_to_smoothing

/-- `r_t` estimate for the nonnegative crossing branch: the
probabilistic trace-defect bridge reduces the CQ trace defect to the spectral
tail mass, and the Chernoff/MGF tail bound controls that mass by the explicit
`iidAEPRtErrorBound`. -/
theorem iidAEP_rt_trace_estimate
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε W)
    (hnonnegative : iidAEPNonnegativeThresholdCrossing W) :
    iidAEPTraceDefect ρ n_copies W ≤
      iidAEPRtErrorBound ρ σ n_copies ε W := by
  have hbridge : IIDAEPRtTraceDefectBridgeData ρ σ n_copies ε W :=
    iidAEPSpectralSetupWithRtTraceBridge_traceBridge hW hnonnegative
  exact le_trans hbridge.trace_defect_to_tail hbridge.tail_to_rt_error

/-- On the nonnegative crossing branch, the explicit scalar budget makes the
Chernoff/MGF error fit inside the smoothing trace budget. -/
theorem iidAEP_rt_error_le_smoothing_budget
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hbudget :
      iidAEPNonnegativeRtSmoothingBudget ρ σ n_copies ε W) :
    iidAEPRtErrorBound ρ σ n_copies ε W ≤
      iidAEPSmoothingTraceBudget ε := by
  exact iidAEPNonnegativeRtSmoothingBudget_error_le hbudget

/-- Package the `r_t` scalar parameters from a nonnegative crossing setup with
the separately proved smoothing-budget inequality. -/
theorem iidAEP_rt_budget_from_nonnegative_spectral_setup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPNonnegativeSpectralSetup
      ρ hρ_norm σ n_copies ε W) :
    iidAEPRtBudget ρ σ n_copies ε W := by
  exact iidAEPNonnegativeSpectralSetup_rtSmoothingBudget hW

/-- Combine the Chernoff/MGF trace estimate with an explicitly derived
smoothing budget. -/
theorem iidAEP_rt_trace_control
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (_hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hbudget : iidAEPRtBudget ρ σ n_copies ε W)
    (htrace :
      iidAEPTraceDefect ρ n_copies W ≤
        iidAEPRtErrorBound ρ σ n_copies ε W) :
    iidAEPRtControlsTrace ρ σ n_copies ε W := by
  exact
    ⟨htrace,
      iidAEP_rt_error_le_smoothing_budget
        ρ σ n_copies ε W hbudget⟩

/-- Trace-distance / purified-distance smoothing control: projector sandwich
plus the `r_t` trace-defect estimate places the spectral witness in the
`ε`-ball of the tensor-power CQ state. -/
theorem iidAEP_smoothing_control
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W)
    (hrt : iidAEPRtControlsTrace ρ σ n_copies ε W) :
    CQState.purifiedDistance
      (iidAEPTensorState ρ n_copies) W.smoothedState ≤ ε := by
  have hε_nonneg : 0 ≤ ε := le_of_lt _hε
  have hdominated :
      iidAEPSmoothedStateDominated ρ n_copies W :=
    iidAEPSpectralSetup_smoothedStateDominated hW
  have htrace_gap :
      iidAEPTraceDefect ρ n_copies W ≤
        iidAEPSmoothingTraceBudget ε :=
    le_trans hrt.1 hrt.2
  have hpd :=
    CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      (iidAEPTensorState ρ n_copies) W.smoothedState
      (iidAEPSmoothingTraceBudget_nonneg hε_nonneg)
      hdominated htrace_gap
  rwa [iidAEP_sqrt_two_mul_smoothingTraceBudget hε_nonneg] at hpd

/-- Derive reference domination from the spectral setup by extracting its
explicit relative block-domination field, together with separately established
positive retained mass. -/
theorem iidAEP_reference_domination
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W)
    (hweight_pos :
      0 < ∑ xs : Fin n_copies → X, (W.smoothedState.stateMap xs).trace) :
    iidAEPReferenceDomination σ n_copies W := by
  exact
    iidAEP_reference_domination_from_spectral_cut
      σ n_copies W
      (iidAEPSpectralSetup_blockDomination hW)
      hweight_pos

/-- The setup threshold is the block-length-scaled entropy floor. -/
theorem iidAEP_entropy_threshold_identification
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPBlockEntropyFloor ρ hρ_norm σ n_copies ε =
      W.entropyThreshold := by
  have hcut :
      iidAEPSpectralCutCondition ρ hρ_norm σ n_copies ε W :=
    iidAEPSpectralSetup_spectralCutCondition hW
  exact hcut.1.symm

/-- Tensor-power normalization for the CQ tensor state used by
`iidAEP`. This is the normalization input needed by the standard
boundedness theorem for smooth-min-entropy balls below radius one. -/
theorem iidAEP_tensor_state_normalized
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)] :
    ∑ xs : Fin n_copies → X,
      ((iidAEPTensorState ρ n_copies).stateMap xs).trace = 1 := by
  unfold iidAEPTensorState
  exact InfoTheory.SmoothMinEntropy.CQState.tensorPower_sum_trace ρ hρ_norm n_copies

/-- A feasible spectral threshold bounds extended conditional entropy, including zero witnesses. -/
theorem iidAEP_entropy_from_reference_domination
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hdom : isFeasible W.smoothedState (iidAEPTensorReference σ n_copies)
      (iidAEPSpectralCutDominationScale W)) :
    ENNReal.ofReal W.entropyThreshold ≤
      conditionalMinEntropy W.smoothedState (iidAEPTensorReference σ n_copies) := by
  exact ofReal_le_conditionalMinEntropy_of_isFeasible
    W.smoothedState (iidAEPTensorReference σ n_copies) W.entropyThreshold hdom

/-- The spectral setup certifies the completed block floor without a retained-weight guard. -/
theorem iidAEP_entropy_relative_entropy_algebra
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W) :
    ENNReal.ofReal (iidAEPBlockEntropyFloor ρ hρ_norm σ n_copies ε) ≤
      conditionalMinEntropy W.smoothedState (iidAEPTensorReference σ n_copies) := by
  rw [iidAEP_entropy_threshold_identification ρ hρ_norm σ n_copies ε W hW]
  exact iidAEP_entropy_from_reference_domination σ n_copies W
    (iidAEP_spectral_cut_feasible_domination σ n_copies W
      (iidAEPSpectralSetup_blockDomination hW))

/-- At zero radius the extended block floor gives the corresponding per-copy rate. -/
theorem iidAEP_zero_smoothing_assembly
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies]
    (h_unsmoothed : ENNReal.ofReal (iidAEPBlockEntropyFloor ρ hρ_norm σ n_copies 0) ≤
      conditionalMinEntropy (iidAEPTensorState ρ n_copies)
        (iidAEPTensorReference σ n_copies)) :
    ENNReal.ofReal (iidAEPEntropyFloor ρ hρ_norm σ n_copies 0) ≤
      iidAEPSmoothRate ρ σ n_copies 0 := by
  apply (ofReal_le_iidAEPSmoothRate_iff ρ σ n_copies 0 _).mpr
  rw [smoothMinEntropy_zero_eq]
  exact h_unsmoothed


/-- Reference domination at the spectral threshold gives the signed floor `W.entropyThreshold`
on the smoothed state. -/
theorem iidAEP_entropy_from_reference_dominationReal
    {X : Type*} [Fintype X]
    {n : ℕ} [NeZero n]
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hdom : iidAEPReferenceDomination σ n_copies W) :
    W.entropyThreshold ≤
      conditionalMinEntropyReal W.smoothedState
        (iidAEPTensorReference σ n_copies) := by
  exact
    conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k
      W.smoothedState (iidAEPTensorReference σ n_copies)
      W.entropyThreshold hdom.1
      (by
        simpa [iidAEPSpectralCutDominationScale] using
          (minFeasibleLambda_le_of_isFeasible
            W.smoothedState (iidAEPTensorReference σ n_copies) hdom.2))

/-- The spectral setup and positive witness weight give the signed conditional entropy floor
`iidAEPBlockEntropyFloor`. -/
theorem iidAEP_entropy_relative_entropy_algebraReal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W)
    (hweight_pos :
      0 < ∑ xs : Fin n_copies → X, (W.smoothedState.stateMap xs).trace) :
    iidAEPBlockEntropyFloor ρ hρ_norm σ n_copies ε ≤
      conditionalMinEntropyReal W.smoothedState
        (iidAEPTensorReference σ n_copies) := by
  have hthreshold :=
    iidAEP_entropy_threshold_identification
      ρ hρ_norm σ n_copies ε W hW
  have hdom :=
    iidAEP_reference_domination
      ρ hρ_norm σ n_copies ε W hW hweight_pos
  have hentropy :=
    iidAEP_entropy_from_reference_dominationReal
      σ n_copies W hdom
  rwa [hthreshold]

/-- A spectral witness in a bounded smoothing ball converts its signed block floor into the
corresponding signed entropy rate. -/
theorem iidAEP_smooth_assemblyReal
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
      iidAEPBlockEntropyFloor ρ hρ_norm σ n_copies ε ≤
        conditionalMinEntropyReal W.smoothedState
          (iidAEPTensorReference σ n_copies)) :
    iidAEPEntropyFloor ρ hρ_norm σ n_copies ε ≤
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
      iidAEPEntropyFloor ρ hρ_norm σ n_copies ε ≤
        (1 / (n_copies : ℝ)) *
          conditionalMinEntropyReal W.smoothedState
            (iidAEPTensorReference σ n_copies) := by
    have hmul := mul_le_mul_of_nonneg_left h_entropy h_inv_nonneg
    have hcancel :
        (1 / (n_copies : ℝ)) *
            iidAEPBlockEntropyFloor ρ hρ_norm σ n_copies ε =
          iidAEPEntropyFloor ρ hρ_norm σ n_copies ε := by
      unfold iidAEPBlockEntropyFloor
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

/-- An unsmoothed signed block floor gives the corresponding signed entropy rate at radius zero. -/
theorem iidAEP_zero_smoothing_assemblyReal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (h_unsmoothed :
      iidAEPBlockEntropyFloor ρ hρ_norm σ n_copies 0 ≤
        conditionalMinEntropyReal (iidAEPTensorState ρ n_copies)
          (iidAEPTensorReference σ n_copies)) :
    iidAEPEntropyFloor ρ hρ_norm σ n_copies 0 ≤
      iidAEPSmoothRateReal ρ σ n_copies 0 := by
  have hzero :
      smoothMinEntropyReal 0 (iidAEPTensorState ρ n_copies)
          (iidAEPTensorReference σ n_copies) =
        conditionalMinEntropyReal (iidAEPTensorState ρ n_copies)
          (iidAEPTensorReference σ n_copies) :=
    smoothMinEntropyReal_zero_eq
      (iidAEPTensorState ρ n_copies)
      (iidAEPTensorReference σ n_copies)
  have hN_pos : (0 : ℝ) < (n_copies : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n_copies))
  have h_inv_nonneg : 0 ≤ (1 / (n_copies : ℝ)) := by positivity
  have h_floor_scaled :
      iidAEPEntropyFloor ρ hρ_norm σ n_copies 0 ≤
        (1 / (n_copies : ℝ)) *
          conditionalMinEntropyReal (iidAEPTensorState ρ n_copies)
            (iidAEPTensorReference σ n_copies) := by
    have hmul := mul_le_mul_of_nonneg_left h_unsmoothed h_inv_nonneg
    have hcancel :
        (1 / (n_copies : ℝ)) *
            iidAEPBlockEntropyFloor ρ hρ_norm σ n_copies 0 =
          iidAEPEntropyFloor ρ hρ_norm σ n_copies 0 := by
      unfold iidAEPBlockEntropyFloor
      field_simp [ne_of_gt hN_pos]
    rwa [hcancel] at hmul
  have h_floor_scaled_smooth :
      iidAEPEntropyFloor ρ hρ_norm σ n_copies 0 ≤
        (1 / (n_copies : ℝ)) *
          smoothMinEntropyReal 0 (iidAEPTensorState ρ n_copies)
            (iidAEPTensorReference σ n_copies) := by
    rw [hzero]
    exact h_floor_scaled
  simpa [iidAEPSmoothRateReal, iidAEPTensorState,
    iidAEPTensorReference] using h_floor_scaled_smooth

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
