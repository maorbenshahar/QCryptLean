import QCryptLean.QKD.BB84.Streaming
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Util.AssertNoSorry
import QCryptLean.QKD.BB84.Program

/-!
# Definition-driven test for the streaming measurement witness

The fixtures inspect the actual split maps, private Alice-then-Bob constructor order, preserved
tails, arbitrary complex input coordinates, and full-program graft shape.  The four principal
identity theorems and all fixtures are checked for sorry-freedom.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QCryptLeanTest.BB84.Streaming

open TypedLOCC
open TypedLOCC.TwoParty
open QKD.BB84
open QKD.BB84.Measurement
open QKD.BB84.Measurement.Streaming
open QKD.BB84.Engine

/-- A nondegenerate biased law: probability `1/3` selects `X`, while `2/3` selects `Z`. -/
noncomputable def biasedBasisLaw : PMF Basis :=
  PMF.map (fun b : Bool => if b then Basis.x else Basis.z)
    (ProbabilityTheory.bernoulliMeasure true false
      ⟨(1 : ℝ) / 3, by constructor <;> norm_num⟩).toPMF

/-- One-bit future tail containing `1`. -/
def tailOne : Fin 1 → Bit := fun _ => 1

/-- One-bit future tail containing `0`. -/
def tailZero : Fin 1 → Bit := fun _ => 0

/-- Two arriving/future bits with head `0` and future tail `1`. -/
def bitsZeroOne : Fin 2 → Bit := Fin.cons 0 tailOne

/-- Two arriving/future bits with head `1` and future tail `0`. -/
def bitsOneZero : Fin 2 → Bit := Fin.cons 1 tailZero

/-- A concrete two-round input row with nonconstant, unequal Alice/Bob streams. -/
def twoRoundRow : (weightedStreamSystem Unit 2).total :=
  (TwoParty.pairEquiv (streamRegister Unit 2) (streamRegister Unit 2)).symm
    (((), bitsZeroOne), ((), bitsOneZero))

/-- A distinct two-round input column, retaining independent global row/column coordinates. -/
def twoRoundColumn : (weightedStreamSystem Unit 2).total :=
  (TwoParty.pairEquiv (streamRegister Unit 2) (streamRegister Unit 2)).symm
    (((), bitsOneZero), ((), bitsZeroOne))

/-- The first online split reads the actual heads and preserves both nonconstant future tails. -/
theorem twoRound_input_split :
    streamRoundInputSplit Unit 1 twoRoundRow =
      ((TwoParty.pairEquiv Bit Bit).symm (0, 1),
        (((), ()), (tailOne, tailZero))) := by
  rfl

/-- The inverse split rebuilds the exact two physical streams from the active pair and spectator. -/
theorem twoRound_input_split_inverse :
    (streamRoundInputSplit Unit 1).symm
        ((TwoParty.pairEquiv Bit Bit).symm (0, 1),
          (((), ()), (tailOne, tailZero))) = twoRoundRow := by
  rfl

/-- A tail-changing implementation is rejected by the concrete split: Alice's retained future bit
is `1`, not `0`. -/
theorem twoRound_Alice_tail_not_changed :
    (streamRoundInputSplit Unit 1 twoRoundRow).2.2.1 ≠ tailZero := by
  intro h
  rw [twoRound_input_split] at h
  exact one_ne_zero (congrFun h 0)

/-- A concrete pair of stored local records for output-coordinate checks. -/
def aliceRecord : StoredRecord := ((), (Basis.z, 0))

/-- A distinct concrete Bob record for output-coordinate checks. -/
def bobRecord : StoredRecord := ((), (Basis.x, 1))

/-! Explicit inhabitants of the one-round output registers.  The generic instance search for these
nested product/function types wanders through unrelated algebraic instances on `Unit` and is slow
enough to exhaust the synthesis budget; the concrete witnesses below are found immediately. -/

/-- The one-round output accumulator is inhabited by the concrete Alice record. -/
instance : Nonempty (Unit × StoredRecord) := ⟨((), aliceRecord)⟩

/-- The one-round output register is inhabited by the concrete Alice record and future tail. -/
instance : Nonempty (streamRegister (Unit × StoredRecord) 1) :=
  ⟨(((), aliceRecord), tailOne)⟩

/-- Concrete physical one-round output with one future qubit per party. -/
def twoRoundOutput :
    (Boundary.leaf (weightedStreamSystem (Unit × StoredRecord) 1)).space :=
  (Boundary.leafSpaceEquiv (weightedStreamSystem (Unit × StoredRecord) 1)).symm
    ((TwoParty.pairEquiv (streamRegister (Unit × StoredRecord) 1)
      (streamRegister (Unit × StoredRecord) 1)).symm
      ((((), aliceRecord), tailOne), (((), bobRecord), tailZero)))

/-- The output split exposes the just-created Alice/Bob records and leaves both future tails
unchanged. -/
theorem twoRound_output_split :
    streamRoundOutputSplit Unit 1 twoRoundOutput =
      ((Boundary.leafSpaceEquiv outputSystem).symm
          ((TwoParty.pairEquiv StoredRecord StoredRecord).symm
            (aliceRecord, bobRecord)),
        (((), ()), (tailOne, tailZero))) := by
  rfl

/-- The inverse output split restores the exact physical next-round registers. -/
theorem twoRound_output_split_inverse :
    (streamRoundOutputSplit Unit 1).symm
      ((Boundary.leafSpaceEquiv outputSystem).symm
          ((TwoParty.pairEquiv StoredRecord StoredRecord).symm
            (aliceRecord, bobRecord)),
        (((), ()), (tailOne, tailZero))) = twoRoundOutput := by
  rfl

/-- An arbitrary complex matrix unit between unequal two-round global configurations.  It is not
assumed positive, self-adjoint, normalized, or diagonal. -/
def coherentTwoRoundInput : Op (weightedStreamSystem Unit 2).total :=
  Matrix.single twoRoundRow twoRoundColumn 1

/-- The chosen unequal row/column coherence is genuinely present in the arbitrary input. -/
theorem coherentTwoRoundInput_entry :
    coherentTwoRoundInput twoRoundRow twoRoundColumn = 1 := by
  simp [coherentTwoRoundInput]

/-- A typed reference extension with distinct physical and reference row/column coordinates.  This
is an arbitrary complex matrix, not a density-operator assumption. -/
def coherentReferenceInput :
    Op ((weightedStreamSystem Unit 2).total × Fin 2) :=
  Matrix.single (twoRoundRow, 0) (twoRoundColumn, 1) 1

/-- The unequal reference-row/reference-column entry is present before applying the stubbed
`mapTensorIdLinear` identity. -/
theorem coherentReferenceInput_entry :
    coherentReferenceInput (twoRoundRow, 0) (twoRoundColumn, 1) = 1 := by
  simp [coherentReferenceInput]

/-- The two reference coordinates in the coherence fixture are genuinely distinct. -/
theorem coherentReference_indices_ne :
    (twoRoundRow, (0 : Fin 2)) ≠ (twoRoundColumn, (1 : Fin 2)) := by
  intro h
  exact Fin.zero_ne_one (congrArg Prod.snd h)

/-- Zero rounds terminate immediately without a private or public node. -/
theorem schedule_zero_shape (pA pB : PMF Basis) :
    weightedMeasurementSchedule pA pB 0 = Program.done := by
  rfl

/-- One round is the actual Alice private action followed by Bob's private action. -/
theorem schedule_one_shape (pA pB : PMF Basis) :
    weightedMeasurementSchedule pA pB 1 =
      Program.priv (weightedStreamAliceAction pA Unit 0)
        (Program.priv (weightedStreamBobAction pA pB Unit 0)
          (cast (by
            simp only [weightedStreamBobAction_out]
            rfl) (weightedMeasurementScheduleAux pA pB (Unit × StoredRecord) 0))) := by
  rfl

/-- At two rounds, the same private Alice-then-Bob head pair precedes recursion on the untouched
second pair. -/
theorem schedule_two_shape (pA pB : PMF Basis) :
    weightedMeasurementSchedule pA pB 2 =
      Program.priv (weightedStreamAliceAction pA Unit 1)
        (Program.priv (weightedStreamBobAction pA pB Unit 1)
          (cast (by
            simp only [weightedStreamBobAction_out]
            rfl) (weightedMeasurementScheduleAux pA pB (Unit × StoredRecord) 1))) := by
  rfl

/-- The standalone round constructor has the same actual Alice-then-Bob private-node order for
unequal, maximally biased laws. -/
theorem unequalPure_round_shape :
    HEq (weightedStreamRoundProgram (PMF.pure Basis.z) (PMF.pure Basis.x) Unit 0)
      (Program.priv (weightedStreamAliceAction (PMF.pure Basis.z) Unit 0)
        (Program.priv (weightedStreamBobAction (PMF.pure Basis.z) (PMF.pure Basis.x) Unit 0)
          Program.done)) := by
  unfold weightedStreamRoundProgram
  exact cast_heq _ _

/-- A genuinely biased Alice law and a zero-support Bob law remain separate parameters of the two
private nodes. -/
theorem biased_zeroSupport_round_shape :
    HEq (weightedStreamRoundProgram biasedBasisLaw (PMF.pure Basis.z) Unit 0)
      (Program.priv (weightedStreamAliceAction biasedBasisLaw Unit 0)
        (Program.priv (weightedStreamBobAction biasedBasisLaw (PMF.pure Basis.z) Unit 0)
          Program.done)) := by
  unfold weightedStreamRoundProgram
  exact cast_heq _ _

/-- The complete physical constructor first uses the actual scheduled late-public program, then
grafts the explicit quota-dependent classical continuation. -/
theorem program_constructor
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    QKD.BB84.program pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q =
      (weightedLatePublicSelectionProgram pA pB N nK mZ mX).graft
        (QKD.BB84.completeContinuation N nK mZ mX ℓ ℓEV leakEC ec delta Q) := by
  rfl

/-- The scheduled late-public constructor itself places all private destructive rounds before its
first basis announcement. -/
theorem weightedLatePublicSelectionProgram_prefix
    (pA pB : PMF Basis) (N nK mZ mX : ℕ) :
    weightedLatePublicSelectionProgram pA pB N nK mZ mX =
      (weightedMeasurementSchedule pA pB N).graft
        (fun _ => latePublicSelectionProgram N nK mZ mX) := by
  rfl

/-- With no signal rounds, the complete physical program reduces directly to the explicit
late-public/classical continuation. -/
theorem program_zero
    (pA pB : PMF Basis) (nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    QKD.BB84.program pA pB 0 nK mZ mX ℓ ℓEV leakEC ec delta Q =
      QKD.BB84.classicalContinuation
        0 nK mZ mX ℓ ℓEV leakEC ec delta Q := by
  rfl

-- Principal identity checks.

end QCryptLeanTest.BB84.Streaming
