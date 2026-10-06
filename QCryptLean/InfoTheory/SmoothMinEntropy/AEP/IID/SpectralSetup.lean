import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.Foundations

/-! # `IIDAEP`, part 2 of 3: block domination, `r_t` setup, and witness existence

This file is one component of the Renner `thm:Hmincondrep` development, whose full module
docstring lives in the re-export hub `IID.lean`. This
part carries the relative block-domination and reference-domination conditions,
the `r_t` parameters and smoothing budget, the spectral-setup definitions and
their support lemmas, and the witness-existence theorems feeding the assembly in
part 3. -/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.VonNeumannEntropy
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open InfoTheory.SmoothMinEntropy.IIDAEPCumulative

/-- Explicit relative block domination required from the spectral-projector
setup. This is the operator-order content that relates each truncated CQ block
to the tensor-power reference at the feasible scalar. It is not a consequence
of the bare reference spectral cut alone. -/
def iidAEPSpectralCutBlockDomination
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  ∀ xs : Fin n_copies → X,
    opLe (W.smoothedState.stateMap xs).toOp
      (Complex.ofReal (iidAEPSpectralCutDominationScale W) •
        (iidAEPTensorReference σ n_copies).toOp)

/-- Reference domination packaged after the explicit relative block domination
obligation has supplied feasibility. The feasible scalar is the exponential
threshold entering the conditional min-entropy definition, and the
positive-lambda condition keeps the real-valued min-entropy bridge away from
its boundary convention. -/
def iidAEPReferenceDomination
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  0 < minFeasibleLambda W.smoothedState (iidAEPTensorReference σ n_copies) ∧
    isFeasible W.smoothedState (iidAEPTensorReference σ n_copies)
      (iidAEPSpectralCutDominationScale W)

/-- Scalar tilt conditions for the `r_t` estimate.

Renner's Chernoff tilt is **non-positive** (`t ≤ 0`, main.tex:4965), the
admissibility condition under which the tilted moment generating function
`E[μ^{t·…}]` converges. The witness uses Renner's clamped optimal tilt
`W.rtTilt = iidAEPOptimalTilt ρ σ n_copies ε
  = −min(δ·log 2/(log μ)², log 2/log μ)`, which minimizes the entropy-cancelled
exponent over `t ≤ 0` in the in-range regime and otherwise sits at the
`lem:rtbound` boundary `|t·log μ| = log 2`. The base `μ > 1`. -/
def iidAEPRtParameters
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) {n_copies : ℕ} (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  1 < iidAEPSpectralRadius ρ σ ∧
    W.rtTilt = iidAEPOptimalTilt ρ σ n_copies ε

/-- Nonnegative-branch scalar budget for the Chernoff/MGF step. It records the
active crossing branch, the admissible tilt range, and the explicit budget
inequality tying Renner's proven discarded-mass tail bound to the requested
smoothing radius. -/
def iidAEPNonnegativeRtSmoothingBudget
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPNonnegativeThresholdCrossing W ∧
    iidAEPRtParameters ρ σ ε W ∧
    iidAEPRtErrorBound ρ σ n_copies ε W ≤
      iidAEPSmoothingTraceBudget ε

/-- Tilt parameters together with the requested smoothing-budget inequality,
available only through the nonnegative-branch scalar budget predicate. -/
def iidAEPRtBudget
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPNonnegativeRtSmoothingBudget ρ σ n_copies ε W

/-- The Renner `r_t` estimate controls the trace defect strongly enough for
the requested smoothing radius. -/
def iidAEPRtControlsTrace
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPTraceDefect ρ n_copies W ≤
      iidAEPRtErrorBound ρ σ n_copies ε W ∧
    iidAEPRtErrorBound ρ σ n_copies ε W ≤
      iidAEPSmoothingTraceBudget ε

/-- Scalar admissibility data for the `r_t` estimate. This names the
tilt/radius side conditions separately from the smoothing-budget comparison. -/
def iidAEPRtScalarAdmissibility
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPRtParameters ρ σ ε W

/-- The Chernoff/MGF exponent-to-`ε` comparison for the nonnegative branch. -/
def iidAEPRtExponentToSmoothingBudget
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPRtErrorBound ρ σ n_copies ε W ≤
    iidAEPSmoothingTraceBudget ε

/-- Matrix trace tail mass produced by the retained spectral projector. This
is the probabilistic quantity bridged to `iidAEPTraceDefect` before the
Chernoff/MGF bound is applied. -/
noncomputable def iidAEPSpectralTraceTailMass
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  ∑ xs : Fin n_copies → X,
    ((((iidAEPTensorState ρ n_copies).stateMap xs).toOp -
      W.truncationProjector *
        ((iidAEPTensorState ρ n_copies).stateMap xs).toOp *
        W.truncationProjector).trace).re

/-- Explicit nonnegative-branch budget data: the active crossing branch,
scalar admissibility, and exponent-to-smoothing comparison are separate
fields. -/
structure IIDAEPNonnegativeRtBudgetData
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop where
  crossing : iidAEPNonnegativeThresholdCrossing W
  scalar_admissible : iidAEPRtScalarAdmissibility ρ σ n_copies ε W
  exponent_to_smoothing :
    iidAEPRtExponentToSmoothingBudget ρ σ n_copies ε W

/-- Explicit trace-defect bridge data for the nonnegative branch. The first
field connects the CQ trace defect to the spectral tail mass, and the second
field applies the Chernoff/MGF tail estimate. -/
structure IIDAEPRtTraceDefectBridgeData
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop where
  trace_defect_to_tail :
    iidAEPTraceDefect ρ n_copies W ≤
      iidAEPSpectralTraceTailMass ρ n_copies W
  tail_to_rt_error :
    iidAEPSpectralTraceTailMass ρ n_copies W ≤
      iidAEPRtErrorBound ρ σ n_copies ε W

/-- The spectral setup ties the explicit witness data to the projector
sandwich, tensor-reference spectral decomposition, spectral cut, and scalar
tilt range. The relative block-domination condition is stored explicitly:
it is a setup/construction obligation, not a consequence of the bare reference
spectral cut. Reference domination and the nonnegative-branch scalar budget are
separate theorem leaves derived from this data. -/
def iidAEPSpectralSetup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPProjectorSandwich ρ n_copies W ∧
    iidAEPSmoothedStateDominated ρ n_copies W ∧
    iidAEPReferenceSpectralDecomposition σ n_copies W ∧
    iidAEPSpectralCutCondition ρ hρ_norm σ n_copies ε W ∧
    iidAEPSpectralCutBlockDomination σ n_copies W ∧
    iidAEPRtParameters ρ σ ε W

/-- The part of a spectral setup where the retained cut is a nonnegative
threshold crossing. This is the only branch that feeds the Chernoff/MGF
`r_t` budget. -/
def iidAEPNonnegativeSpectralSetup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W ∧
    iidAEPNonnegativeRtSmoothingBudget ρ σ n_copies ε W

/-- Always-smooth-branch smoothing-budget data attached to a constructed
spectral witness. The implication exposes the `r_t` budget exactly when the
retained crossing predicate holds. -/
def iidAEPNonnegativeRtBudgetAvailable
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPNonnegativeThresholdCrossing W →
    IIDAEPNonnegativeRtBudgetData ρ σ n_copies ε W

/-- Nonnegative-branch trace-defect bridge data attached to a constructed
spectral witness. -/
def iidAEPRtTraceDefectBridgeAvailable
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPNonnegativeThresholdCrossing W →
    IIDAEPRtTraceDefectBridgeData ρ σ n_copies ε W

/-- Spectral setup enriched with the nonnegative-branch exponent-to-smoothing
budget data. -/
def iidAEPSpectralSetupWithRtBudget
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W ∧
    iidAEPNonnegativeRtBudgetAvailable ρ σ n_copies ε W

/-- Spectral setup enriched with both nonnegative-branch budget data and the
probabilistic trace-defect bridge. -/
def iidAEPSpectralSetupWithRtTraceBridge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPSpectralSetupWithRtBudget ρ hρ_norm σ n_copies ε W ∧
    iidAEPRtTraceDefectBridgeAvailable ρ σ n_copies ε W

/-- Core data constructed with the spectral witness: projector sandwich and
blockwise domination by the original tensor-power CQ state. -/
def iidAEPWitnessProjectorSubstate
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPProjectorSandwich ρ n_copies W ∧
    iidAEPSmoothedStateDominated ρ n_copies W

lemma iidAEPSpectralConstructionCore_withReferenceEigenvalues
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    {ρ : CQState X n} {σ : DensityOp n} {n_copies : ℕ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPWitnessProjectorSubstate ρ n_copies W) :
    iidAEPWitnessProjectorSubstate ρ n_copies
      (iidAEPWitnessWithReferenceEigenvalues σ W) := by
  simpa [iidAEPWitnessWithReferenceEigenvalues,
    iidAEPWitnessProjectorSubstate, iidAEPProjectorSandwich,
    iidAEPSmoothedStateDominated] using hW

/-- Construction stage after nonnegative reference eigenvalue labels have
been tied to the constructed witness. -/
def iidAEPWitnessNonnegReferenceEigenvalues
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPWitnessProjectorSubstate ρ n_copies W ∧
    ∀ z : Fin (n ^ n_copies), 0 ≤ W.referenceEigenvalue z

/-- The canonical reference-spectrum updater preserves the already
constructed projector sandwich and blockwise domination core. -/
lemma iidAEPSpectralConstructionCore_withReferenceSpectrum
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    {ρ : CQState X n} {σ : DensityOp n} {n_copies : ℕ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPWitnessProjectorSubstate ρ n_copies W) :
    iidAEPWitnessProjectorSubstate ρ n_copies
      (iidAEPWitnessWithReferenceSpectrum σ W) := by
  simpa [iidAEPWitnessWithReferenceSpectrum,
    iidAEPWitnessProjectorSubstate, iidAEPProjectorSandwich,
    iidAEPSmoothedStateDominated] using hW

/-- The sorted-spectrum updater preserves the projector sandwich and blockwise
domination core. -/
lemma iidAEPSpectralConstructionCore_withSortedSpectrum
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    {ρ : CQState X n} {σ : DensityOp n} {n_copies : ℕ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPWitnessProjectorSubstate ρ n_copies W) :
    iidAEPWitnessProjectorSubstate ρ n_copies
      (iidAEPWitnessWithSortedSpectrum σ W) := by
  simpa [iidAEPWitnessWithSortedSpectrum, iidAEPWitnessProjectorSubstate,
    iidAEPProjectorSandwich, iidAEPSmoothedStateDominated] using hW

lemma iidAEPSpectralConstructionEigenvalues_withReferenceSpectrum
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    {ρ : CQState X n} {σ : DensityOp n} {n_copies : ℕ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPWitnessNonnegReferenceEigenvalues ρ n_copies W) :
    iidAEPWitnessNonnegReferenceEigenvalues ρ n_copies
      (iidAEPWitnessWithReferenceSpectrum σ W) := by
  refine
    ⟨iidAEPSpectralConstructionCore_withReferenceSpectrum hW.1, ?_⟩
  intro z
  exact iidAEPReferenceEigenvalueLabels_nonneg σ n_copies z

/-- Orthogonal nonzero rank-one increments from the tensor-reference
Hermitian eigenbasis resolve the identity. This is the matrix spectral-theory
leaf used by the reference-increment construction stage. -/
theorem iidAEPWitnessWithReferenceSpectrum_increments
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ} [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) :
    iidAEPReferenceSpectralIncrements
      (iidAEPWitnessWithReferenceSpectrum σ W) := by
  simpa [iidAEPReferenceSpectralIncrements,
    iidAEPWitnessWithReferenceSpectrum, iidAEPReferenceSpectrumData]
    using iidAEPReferenceSpectralIncrementProjector_increments
      σ n_copies

/-- The tensor-power reference acts diagonally on its canonical rank-one
spectral increments, and is reconstructed from the eigenvalue-weighted
increments. This is the action/diagonalization leaf used by the reference
spectral-action construction stage. -/
theorem iidAEPWitnessWithReferenceSpectrum_action
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (σ : DensityOp n) {n_copies : ℕ} [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) :
    iidAEPReferenceSpectralAction σ n_copies
      (iidAEPWitnessWithReferenceSpectrum σ W) := by
  simpa [iidAEPReferenceSpectralAction,
    iidAEPWitnessWithReferenceSpectrum, iidAEPReferenceSpectrumData,
    iidAEPReferenceEigenvalueLabels,
    iidAEPReferenceSpectralIncrementProjector]
    using isHermitian_eigenvectorBasis_rankOneProjectors_action
      (iidAEPTensorReference σ n_copies).toPosSemidefOp.toHermitianOp.isHermitian

/-- Construction stage after the nonzero orthogonal spectral increments have
been constructed for the witness. -/
def iidAEPWitnessOrthogonalIncrements
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPWitnessNonnegReferenceEigenvalues ρ n_copies W ∧
    iidAEPReferenceSpectralIncrements W

/-- Construction stage after the tensor-power reference action has been tied
to the constructed spectral increments. -/
def iidAEPWitnessReferenceSpectralAction
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPWitnessOrthogonalIncrements ρ n_copies W ∧
    iidAEPReferenceSpectralAction σ n_copies W

/-- Construction stage after the full tensor-reference spectral decomposition
has been established for the constructed witness. -/
def iidAEPWitnessReferenceSpectralDecomposition
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPWitnessProjectorSubstate ρ n_copies W ∧
    iidAEPReferenceSpectralDecomposition σ n_copies W

/-- Construction stage after the entropy threshold and spectral cut branch
have been selected for the constructed witness. -/
def iidAEPWitnessSpectralCut
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPWitnessReferenceSpectralDecomposition ρ σ n_copies W ∧
    iidAEPSpectralCutCondition ρ hρ_norm σ n_copies ε W

/-- Construction stage after relative block domination has been proved for
the constructed spectral cut. -/
def iidAEPWitnessBlockDomination
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPWitnessSpectralCut ρ hρ_norm σ n_copies ε W ∧
    iidAEPSpectralCutBlockDomination σ n_copies W

/-- Final construction stage before packaging as `iidAEPSpectralSetup`:
the block stage together with the scalar `r_t` parameters. -/
def iidAEPWitnessWithRtParameters
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPWitnessBlockDomination ρ hρ_norm σ n_copies ε W ∧
    iidAEPRtParameters ρ σ ε W

/-- Explicit core-stage witness with identity truncation and the original
tensor-power CQ state. This declaration proves only
`iidAEPWitnessProjectorSubstate`; the reference spectrum, cut, relative
domination, and `r_t` properties remain the separate construction leaves below. -/
noncomputable def iidAEPIdentityWitness
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)] :
    IIDAEPSpectralWitness X n n_copies where
  projectorData :=
    { truncationProjector := 1
      smoothedState := iidAEPTensorState ρ n_copies }
  referenceSpectrum :=
    { referenceEigenvalue := fun _ => 0
      spectralProjector := fun _ => 1 }
  cumulativeResolution :=
    { betaCoefficient := fun _ => 0
      cumulativeProjector := fun _ => 1 }
  spectralCut :=
    { cutIndex := 0
      entropyThreshold := 0 }
  rtData := { tilt := 0 }

lemma iidAEPIdentityCoreWitness_projectorSandwich
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)] :
    iidAEPProjectorSandwich ρ n_copies
      (iidAEPIdentityWitness ρ n_copies) := by
  refine ⟨?_, ?_, ?_⟩
  · change (1 : Op (n ^ n_copies)) * 1 = 1
    rw [Matrix.one_mul]
  · change (1 : Op (n ^ n_copies))† = 1
    exact Matrix.conjTranspose_one
  · intro xs
    change ((iidAEPTensorState ρ n_copies).stateMap xs).toOp =
      (1 : Op (n ^ n_copies)) *
        ((iidAEPTensorState ρ n_copies).stateMap xs).toOp * 1
    rw [Matrix.one_mul, Matrix.mul_one]

lemma iidAEPIdentityCoreWitness_smoothedStateDominated
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)] :
    iidAEPSmoothedStateDominated ρ n_copies
      (iidAEPIdentityWitness ρ n_copies) := by
  intro xs v
  exact le_rfl

lemma iidAEPSpectralSetup_projectorSandwich
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPProjectorSandwich ρ n_copies W := by
  rcases hW with ⟨hprojector, _⟩
  exact hprojector

lemma iidAEPSpectralSetup_smoothedStateDominated
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPSmoothedStateDominated ρ n_copies W := by
  rcases hW with ⟨_, hdominated, _⟩
  exact hdominated

lemma iidAEPSpectralSetup_referenceSpectralDecomposition
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPReferenceSpectralDecomposition σ n_copies W := by
  rcases hW with ⟨_, _, hspectral, _⟩
  exact hspectral

lemma iidAEPSpectralSetup_spectralCutCondition
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPSpectralCutCondition ρ hρ_norm σ n_copies ε W := by
  rcases hW with ⟨_, _, _, hcut, _, _⟩
  exact hcut

lemma iidAEPSpectralSetup_blockDomination
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPSpectralCutBlockDomination σ n_copies W := by
  rcases hW with ⟨_, _, _, _, hblock, _⟩
  exact hblock

lemma iidAEPSpectralSetup_rtParameters
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPRtParameters ρ σ ε W := by
  rcases hW with ⟨_, _, _, _, _, hparams⟩
  exact hparams

lemma iidAEPNonnegativeSpectralSetup_setup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPNonnegativeSpectralSetup
      ρ hρ_norm σ n_copies ε W) :
    iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W := by
  exact hW.1

lemma iidAEPNonnegativeRtSmoothingBudget_crossing
    {X : Type*} [Fintype X] {n : ℕ}
    {ρ : CQState X n} {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hbudget :
      iidAEPNonnegativeRtSmoothingBudget ρ σ n_copies ε W) :
    iidAEPNonnegativeThresholdCrossing W := by
  exact hbudget.1

lemma iidAEPNonnegativeRtSmoothingBudget_rtParameters
    {X : Type*} [Fintype X] {n : ℕ}
    {ρ : CQState X n} {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hbudget :
      iidAEPNonnegativeRtSmoothingBudget ρ σ n_copies ε W) :
    iidAEPRtParameters ρ σ ε W := by
  exact hbudget.2.1

lemma iidAEPNonnegativeRtSmoothingBudget_error_le
    {X : Type*} [Fintype X] {n : ℕ}
    {ρ : CQState X n} {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hbudget :
      iidAEPNonnegativeRtSmoothingBudget ρ σ n_copies ε W) :
    iidAEPRtErrorBound ρ σ n_copies ε W ≤
      iidAEPSmoothingTraceBudget ε :=
  hbudget.2.2

lemma iidAEPNonnegativeSpectralSetup_crossing
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPNonnegativeSpectralSetup
      ρ hρ_norm σ n_copies ε W) :
    iidAEPNonnegativeThresholdCrossing W := by
  exact iidAEPNonnegativeRtSmoothingBudget_crossing hW.2

lemma iidAEPNonnegativeSpectralSetup_rtSmoothingBudget
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPNonnegativeSpectralSetup
      ρ hρ_norm σ n_copies ε W) :
    iidAEPNonnegativeRtSmoothingBudget ρ σ n_copies ε W := by
  exact hW.2

lemma iidAEPSpectralSetupWithRtBudget_setup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetupWithRtBudget
      ρ hρ_norm σ n_copies ε W) :
    iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W := by
  exact hW.1

lemma iidAEPSpectralSetupWithRtBudget_budgetData
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetupWithRtBudget
      ρ hρ_norm σ n_copies ε W)
    (hnonnegative : iidAEPNonnegativeThresholdCrossing W) :
    IIDAEPNonnegativeRtBudgetData ρ σ n_copies ε W := by
  exact hW.2 hnonnegative

lemma iidAEPSpectralSetupWithRtTraceBridge_budgetSetup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε W) :
    iidAEPSpectralSetupWithRtBudget ρ hρ_norm σ n_copies ε W := by
  exact hW.1

lemma iidAEPSpectralSetupWithRtTraceBridge_setup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε W) :
    iidAEPSpectralSetup ρ hρ_norm σ n_copies ε W := by
  exact iidAEPSpectralSetupWithRtBudget_setup hW.1

lemma iidAEPSpectralSetupWithRtTraceBridge_budgetData
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε W)
    (hnonnegative : iidAEPNonnegativeThresholdCrossing W) :
    IIDAEPNonnegativeRtBudgetData ρ σ n_copies ε W := by
  exact iidAEPSpectralSetupWithRtBudget_budgetData hW.1 hnonnegative

lemma iidAEPSpectralSetupWithRtTraceBridge_traceBridge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε W)
    (hnonnegative : iidAEPNonnegativeThresholdCrossing W) :
    IIDAEPRtTraceDefectBridgeData ρ σ n_copies ε W := by
  exact hW.2 hnonnegative

lemma iidAEPRtBudget_error_le
    {X : Type*} [Fintype X] {n : ℕ}
    {ρ : CQState X n} {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hbudget : iidAEPRtBudget ρ σ n_copies ε W) :
    iidAEPRtErrorBound ρ σ n_copies ε W ≤
      iidAEPSmoothingTraceBudget ε := by
  exact iidAEPNonnegativeRtSmoothingBudget_error_le hbudget

/-- Construction leaf for the raw spectral-projector witness: it supplies the
projector sandwich and the blockwise substate relation. The spectral
resolution, cut branch, relative domination, and `r_t` parameters are
constructed by richer existential packages below and assembled together. -/
theorem exists_iidAEPWitnessProjectorSubstate
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (_hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (_σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPWitnessProjectorSubstate ρ n_copies W := by
  exact
    ⟨iidAEPIdentityWitness ρ n_copies,
      iidAEPIdentityCoreWitness_projectorSandwich ρ n_copies,
      iidAEPIdentityCoreWitness_smoothedStateDominated ρ n_copies⟩

/-- Nonnegativity of the explicit reference eigenvalue labels used by the
spectral-resolution witness, returned as a richer construction package rather
than asserted for an arbitrary witness. -/
theorem exists_iidAEPWitnessNonnegReferenceEigenvalues
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (_hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε)
    (_hε_lt_one : ε < 1)
    (hcore :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessProjectorSubstate ρ n_copies W) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPWitnessNonnegReferenceEigenvalues ρ n_copies W := by
  rcases hcore with ⟨W, hWcore⟩
  refine ⟨iidAEPWitnessWithReferenceEigenvalues σ W, ?_, ?_⟩
  · exact iidAEPSpectralConstructionCore_withReferenceEigenvalues hWcore
  · exact
      (iidAEPWitnessWithReferenceEigenvalues_referenceEigenvalueSetup
        σ W).2

/-- Orthogonal nonzero spectral increments resolving the tensor-power
reference support. This is the leaf that rules out assigning meaningful
weights to zero projectors. It consumes the constructed eigenvalue package and
returns a richer constructed witness package. -/
theorem exists_iidAEPWitnessOrthogonalIncrements
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (_hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε)
    (_hε_lt_one : ε < 1)
    (heigenvalues :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessNonnegReferenceEigenvalues ρ n_copies W) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPWitnessOrthogonalIncrements ρ n_copies W := by
  rcases heigenvalues with ⟨W, hW⟩
  refine ⟨iidAEPWitnessWithReferenceSpectrum σ W, ?_, ?_⟩
  · exact iidAEPSpectralConstructionEigenvalues_withReferenceSpectrum hW
  · exact iidAEPWitnessWithReferenceSpectrum_increments σ W

/-- The tensor-power reference is diagonal on the explicit spectral increments,
and the weighted increment sum reconstructs the reference operator. -/
theorem exists_iidAEPWitnessReferenceSpectralAction
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (_hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε)
    (_hε_lt_one : ε < 1)
    (hincrements :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessOrthogonalIncrements ρ n_copies W) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPWitnessReferenceSpectralAction ρ σ n_copies W := by
  rcases hincrements with ⟨W, hW⟩
  refine ⟨iidAEPWitnessWithReferenceSpectrum σ W, ⟨?_, ?_⟩, ?_⟩
  · exact iidAEPSpectralConstructionEigenvalues_withReferenceSpectrum hW.1
  · exact iidAEPWitnessWithReferenceSpectrum_increments σ W
  · exact iidAEPWitnessWithReferenceSpectrum_action σ W

/-- Renner cumulative projectors and `β_z` coefficients, tied back to the
orthogonal spectral increments. The result is the full reference spectral
decomposition package for a constructed witness. Unlike its siblings in this
construction chain, it does not need `ρ` to be normalized. -/
theorem exists_iidAEPWitnessReferenceSpectralDecomposition
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε)
    (_hε_lt_one : ε < 1)
    (haction :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessReferenceSpectralAction ρ σ n_copies W) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPWitnessReferenceSpectralDecomposition ρ σ n_copies W := by
  rcases haction with ⟨W, hW⟩
  refine ⟨iidAEPWitnessWithSortedSpectrum σ W, ?_, ?_, ?_, ?_, ?_⟩
  · exact iidAEPSpectralConstructionCore_withSortedSpectrum hW.1.1.1
  · exact iidAEPWitnessWithSortedSpectrum_eigenvalue_nonneg σ W
  · exact iidAEPWitnessWithSortedSpectrum_increments σ W
  · exact iidAEPWitnessWithSortedSpectrum_action σ W
  · exact iidAEPWitnessWithSortedSpectrum_cumulative σ W

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
