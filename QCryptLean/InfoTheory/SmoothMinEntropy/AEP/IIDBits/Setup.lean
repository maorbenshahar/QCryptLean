import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBlockDomination
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBitsBlockDomination
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCap
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCapFidelity
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDDiscardedMass
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDChernoffTail
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQConditionalEntropyMaxBound

/-!
# Bit-normalized Renner `thm:Hmincondrep` — spectral setup and weight-cap witness construction

Bit-normalized analogues of the natural-log spectral setup from `IID.lean`,
with the cut condition parameterized by the base-two entropy threshold and the
smoothed state given by Renner's weight-cap state `ρ̄` (main.tex:4636–4642). This
file collects the setup `Prop`s, their field accessors, the construction
predicates, and the existence theorems that construct the weight-cap spectral
witness.

## Main definitions
- `iidAEPBitSpectralCutCondition`, `iidAEPBitSpectralSetup`,
  `iidAEPBitSpectralSetupWithRtBudget`, `iidAEPBitSpectralSetupWithRtTraceBridge`:
  bit-normalized setup predicates.
- `iidAEPBitWeightCapCutWitness` / `…Block` / `…WithRt`: construction predicates.
- `iidAEPWitnessWithRtTilt`: overwrite the scalar `r_t` tilt of a witness.

## Main statements
- `exists_iidAEPBitWeightCapCutWitness`,
  `exists_iidAEPBitWeightCapCutWitnessWithBlockDomination`,
  `exists_iidAEPBitWeightCapCutWitnessWithRtTilt`,
  `exists_iidAEPBitSpectralSetup`:
  construct the weight-cap spectral witness.
-/

open Quantum.Operators
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Spectral cut condition with the entropy threshold measured in bits: pins the witness
threshold W.entropyThreshold to the base-two block-entropy floor
`iidAEPBitBlockEntropyFloor` and requires the nonnegative threshold-crossing condition
`iidAEPNonnegativeThresholdCrossing`. The downstream separation scale is
`2 ^ (-W.entropyThreshold)`. (Renner, main.tex:4600–4604.) -/
def iidAEPBitSpectralCutCondition
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  W.entropyThreshold =
      iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε ∧
    iidAEPNonnegativeThresholdCrossing W

/-- Bit-normalized spectral setup for the positive-smoothing Renner branch with the weight-cap
smoothed state `ρ̄` (main.tex:4636–4642). Bundles: the reference spectral decomposition, the
bit cut condition, the operator block domination `ρ̄_xs ≼ 2^(-T)·(id⊗σ)^⊗n`, the weight-cap
pin identifying each smoothed block with `weightCapBlockOp`, and the `r_t` parameters.

The pin is load-bearing: block domination alone is only an upper bound (satisfied by
`smoothedState = 0`), so the pin is what forces `iidAEPTraceDefect` to equal Renner's
discarded mass, making the downstream discarded-mass and purified-distance bounds genuine.
The single-projector substate domination is not included: `ρ̄` is not a substate of `ρ^{⊗n}`
(it redistributes spectral mass across the cumulative projectors `B_z`). -/
def iidAEPBitSpectralSetup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPReferenceSpectralDecomposition σ n_copies W ∧
    iidAEPBitSpectralCutCondition ρ hρ_norm σ n_copies ε W ∧
    iidAEPSpectralCutBlockDomination σ n_copies W ∧
    iidAEPIsWeightCapSmoothedState ρ n_copies W ∧
    iidAEPRtParameters ρ σ ε W

/-- Nonnegative-branch budget data attached to a bit-normalized spectral
setup. -/
def iidAEPBitSpectralSetupWithRtBudget
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W ∧
    iidAEPNonnegativeRtBudgetAvailable ρ σ n_copies ε W

/-- Renner's weight-cap discarded-mass bridge: for the weight-cap smoothed state `ρ̄`, the CQ
trace defect `iidAEPTraceDefect = Σ_xs [tr(ρ^{⊗}_xs) − tr(ρ̄_xs)]` equals Renner's
discarded mass `Σ_{(x,z): p_x > λ q_z} p_x |⟨z|x⟩|²` (main.tex:4665–4747); this predicate
asserts it is bounded by the Chernoff/MGF `r_t` error term, conditional on the nonnegative
threshold crossing. -/
def iidAEPBitWeightCapTraceDefectBridgeAvailable
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPNonnegativeThresholdCrossing W →
    iidAEPTraceDefect ρ n_copies W ≤
      iidAEPRtErrorBound ρ σ n_copies ε W

/-- Bit-normalized spectral setup enriched with the weight-cap discarded-mass
bridge used by the nonnegative branch. -/
def iidAEPBitSpectralSetupWithRtTraceBridge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPBitSpectralSetupWithRtBudget ρ hρ_norm σ n_copies ε W ∧
    iidAEPBitWeightCapTraceDefectBridgeAvailable ρ σ n_copies ε W

lemma iidAEPBitSpectralSetup_referenceSpectralDecomposition
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPReferenceSpectralDecomposition σ n_copies W := by
  exact hW.1

lemma iidAEPBitSpectralSetup_spectralCutCondition
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPBitSpectralCutCondition ρ hρ_norm σ n_copies ε W := by
  exact hW.2.1

lemma iidAEPBitSpectralSetup_blockDomination
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPSpectralCutBlockDomination σ n_copies W := by
  exact hW.2.2.1

lemma iidAEPBitSpectralSetup_rtParameters
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPRtParameters ρ σ ε W := by
  exact hW.2.2.2.2

lemma iidAEPBitSpectralSetup_isWeightCapSmoothedState
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W) :
    iidAEPIsWeightCapSmoothedState ρ n_copies W := by
  exact hW.2.2.2.1

lemma iidAEPBitSpectralSetupWithRtBudget_setup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetupWithRtBudget
      ρ hρ_norm σ n_copies ε W) :
    iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W := by
  exact hW.1

lemma iidAEPBitSpectralSetupWithRtBudget_budgetData
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetupWithRtBudget
      ρ hρ_norm σ n_copies ε W)
    (hnonnegative : iidAEPNonnegativeThresholdCrossing W) :
    IIDAEPNonnegativeRtBudgetData ρ σ n_copies ε W := by
  exact hW.2 hnonnegative

lemma iidAEPBitSpectralSetupWithRtTraceBridge_budgetSetup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε W) :
    iidAEPBitSpectralSetupWithRtBudget ρ hρ_norm σ n_copies ε W := by
  exact hW.1

lemma iidAEPBitSpectralSetupWithRtTraceBridge_setup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε W) :
    iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W := by
  exact iidAEPBitSpectralSetupWithRtBudget_setup hW.1

lemma iidAEPBitSpectralSetupWithRtTraceBridge_traceBridge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW : iidAEPBitSpectralSetupWithRtTraceBridge
      ρ hρ_norm σ n_copies ε W)
    (hnonnegative : iidAEPNonnegativeThresholdCrossing W) :
    iidAEPTraceDefect ρ n_copies W ≤
      iidAEPRtErrorBound ρ σ n_copies ε W := by
  exact hW.2 hnonnegative

/-- Conjunction characterizing a bit-normalized weight-cap cut witness: the reference spectral
decomposition, the bit cut condition, the operator block domination, and the weight-cap pin
identifying each smoothed block with `weightCapBlockOp`. The pin is load-bearing — without it
the free `smoothedState` field would admit adversarial values and the downstream
discarded-mass and purified-distance bounds would not hold. -/
def iidAEPBitWeightCapCutWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPReferenceSpectralDecomposition σ n_copies W ∧
    iidAEPBitSpectralCutCondition ρ hρ_norm σ n_copies ε W ∧
    iidAEPSpectralCutBlockDomination σ n_copies W ∧
    iidAEPIsWeightCapSmoothedState ρ n_copies W

lemma iidAEPBitSpectralConstructionCut_blockDomination
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    {ρ : CQState X n} {hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hW :
      iidAEPBitWeightCapCutWitness
        ρ hρ_norm σ n_copies ε W) :
    iidAEPSpectralCutBlockDomination σ n_copies W := by
  exact hW.2.2.1

/-- `iidAEPBitWeightCapCutWitness` re-conjoined with the (already-implied)
operator block domination `iidAEPSpectralCutBlockDomination`, as an explicit
standalone hypothesis for downstream lemmas that consume the domination directly. -/
def iidAEPBitWeightCapCutWitnessWithBlockDomination
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPBitWeightCapCutWitness ρ hρ_norm σ n_copies ε W ∧
    iidAEPSpectralCutBlockDomination σ n_copies W

/-- `iidAEPBitWeightCapCutWitnessWithBlockDomination` conjoined with Renner's
`r_t` estimate parameters `iidAEPRtParameters`. -/
def iidAEPBitWeightCapCutWitnessWithRtTilt
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  iidAEPBitWeightCapCutWitnessWithBlockDomination ρ hρ_norm σ n_copies ε W ∧
    iidAEPRtParameters ρ σ ε W

/-- Existence of Renner's weight-cap cut witness (main.tex:4575–4665). From a reference-stage
spectral witness, `iidAEPRennerCutWitness` at the bit block floor `T` yields a witness
satisfying: the reference spectral decomposition is preserved; the threshold equals the bit
block floor with retained cumulative crossing projector `B_{z*}` at scale `2^(-T)`; and the
weight-cap smoothed state `ρ̄ = Σ_{x,z} p_{x,z} B_z|x⟩⟨x|B_z` is operator dominated,
`ρ̄_xs ≼ 2^(-T)·(id⊗σ)^⊗n`.

The block domination is the weight cap `p_{x,z} ≤ λ β_z` (main.tex:4644–4665): the per-(x,z)
weight redistribution is what makes operator domination hold below the crossing threshold,
where a single projector sandwich cannot, since its cross terms `Π ρ Π⊥` do not vanish for
non-commuting `ρ, σ`. -/
theorem exists_iidAEPBitWeightCapCutWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε)
    (_hε_lt_one : ε < 1)
    (hreference :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessReferenceSpectralDecomposition ρ σ n_copies W) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPBitWeightCapCutWitness
        ρ hρ_norm σ n_copies ε W := by
  obtain ⟨W, _hcore, href⟩ := hreference
  set T := iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε
  refine ⟨iidAEPRennerCutWitness ρ n_copies σ W href T,
    iidAEPRennerCutWitness_reference ρ n_copies σ W href T, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- `entropyThreshold = T = bitBlockFloor`.
    show (iidAEPRennerCutWitness ρ n_copies σ W href T).entropyThreshold
        = iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε
    rw [iidAEPRennerCutWitness_entropyThreshold]
  · exact iidAEPRennerCutWitness_crossing ρ n_copies σ W href T
  · exact iidAEPRennerCutWitness_blockDomination ρ n_copies σ W href T
  · -- The smoothed state is the weight-cap state by construction.
    exact iidAEPRennerCutWitness_isWeightCapSmoothedState ρ n_copies σ W href T

theorem exists_iidAEPBitWeightCapCutWitnessWithBlockDomination
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε)
    (_hε_lt_one : ε < 1)
    (hcut :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPBitWeightCapCutWitness
          ρ hρ_norm σ n_copies ε W) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPBitWeightCapCutWitnessWithBlockDomination
        ρ hρ_norm σ n_copies ε W := by
  obtain ⟨W, hW⟩ := hcut
  exact
    ⟨W, hW,
      iidAEPBitSpectralConstructionCut_blockDomination hW⟩

/-- Overwrite only the scalar `r_t` tilt of a spectral witness, leaving every other field
unchanged. -/
def iidAEPWitnessWithRtTilt
    {X : Type*} [Fintype X] {n n_copies : ℕ}
    (W : IIDAEPSpectralWitness X n n_copies) (t : ℝ) :
    IIDAEPSpectralWitness X n n_copies :=
  { W with rtData := { tilt := t } }

/-- Pin Renner's optimal non-positive tilt `τ* = −δ·log 2/(log μ)²` on a weight-cap cut
witness, yielding a witness that additionally satisfies the `r_t` parameter requirements. -/
theorem exists_iidAEPBitWeightCapCutWitnessWithRtTilt
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε)
    (_hε_lt_one : ε < 1)
    (hblock :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPBitWeightCapCutWitnessWithBlockDomination
          ρ hρ_norm σ n_copies ε W) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPBitWeightCapCutWitnessWithRtTilt
        ρ hρ_norm σ n_copies ε W := by
  obtain ⟨W, hWblock⟩ := hblock
  have hR1 : 1 < iidAEPSpectralRadius ρ σ :=
    iidAEPSpectralRadius_one_lt ρ σ
  -- Pin Renner's optimal non-positive tilt `τ* = −δ·log 2/(log μ)²`.
  have htilt :
      (iidAEPWitnessWithRtTilt W
          (iidAEPOptimalTilt ρ σ n_copies ε)).rtTilt
        = iidAEPOptimalTilt ρ σ n_copies ε := rfl
  refine
    ⟨iidAEPWitnessWithRtTilt W
        (iidAEPOptimalTilt ρ σ n_copies ε),
      hWblock, hR1, ?_⟩
  rw [htilt]

/-- Construct the full bit-normalized weight-cap spectral setup witness
`iidAEPBitSpectralSetup` for the base-two Renner statement, by threading the
reference-stage spectral decomposition through the weight-cap cut and `r_t`-tilt
construction. -/
theorem exists_iidAEPBitSpectralSetup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W := by
  have hcore :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessProjectorSubstate ρ n_copies W :=
    exists_iidAEPWitnessProjectorSubstate
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one
  have heigenvalues :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessNonnegReferenceEigenvalues ρ n_copies W :=
    exists_iidAEPWitnessNonnegReferenceEigenvalues
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one hcore
  have hincrements :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessOrthogonalIncrements ρ n_copies W :=
    exists_iidAEPWitnessOrthogonalIncrements
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one heigenvalues
  have haction :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessReferenceSpectralAction ρ σ n_copies W :=
    exists_iidAEPWitnessReferenceSpectralAction
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one hincrements
  have hreference :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPWitnessReferenceSpectralDecomposition ρ σ n_copies W :=
    exists_iidAEPWitnessReferenceSpectralDecomposition
      ρ σ n_copies ε _hε _hε_lt_one haction
  have hcut :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPBitWeightCapCutWitness
          ρ hρ_norm σ n_copies ε W :=
    exists_iidAEPBitWeightCapCutWitness
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one hreference
  have hblock :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPBitWeightCapCutWitnessWithBlockDomination
          ρ hρ_norm σ n_copies ε W :=
    exists_iidAEPBitWeightCapCutWitnessWithBlockDomination
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one hcut
  obtain ⟨W, hwith_rt⟩ :=
    exists_iidAEPBitWeightCapCutWitnessWithRtTilt
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one hblock
  rcases hwith_rt with ⟨hblock_stage, hparams⟩
  rcases hblock_stage with ⟨hcut_stage, hblock_domination⟩
  rcases hcut_stage with ⟨hspectral, hcut_condition, _, hpin⟩
  exact ⟨W, hspectral, hcut_condition, hblock_domination, hpin, hparams⟩

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
