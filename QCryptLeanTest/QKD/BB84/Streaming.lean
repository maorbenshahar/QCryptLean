import QCryptLean.QKD.BB84.Streaming
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Util.AssertNoSorry
import QCryptLean.QKD.BB84.CompleteOutput

/-!
# Definition-driven test for the streaming measurement witness

The fixtures inspect the actual split maps, private Alice-then-Bob constructor order, preserved
tails, arbitrary complex input coordinates, and the private measurement phase.
-/

open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QCryptLeanTest.BB84.Streaming

open _root_.LOCC
open _root_.LOCC.TwoParty
open QKD.BB84
open QKD.BB84.Measurement
open QKD.BB84.Measurement.Streaming
open QKD.BB84.FiniteKey

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

/-- Zero rounds immediately run the supplied continuation. -/
theorem schedule_zero_shape (pA pB : PMF Basis)
    (k : Program (weightedStreamSystem Unit 0)) :
    measureRounds pA pB Unit 0 k = k := rfl

/-- One round is the actual Alice private action followed by Bob's private action. -/
theorem schedule_one_shape (pA pB : PMF Basis)
    (k : Program (weightedStreamSystem (finishAcc Unit 1) 0)) :
    measureRounds pA pB Unit 1 k =
      (measureAlice pA Unit 0).then ((measureBob pB Unit 0).then k) := rfl

/-- Two private head actions precede recursion on the untouched second pair. -/
theorem schedule_two_shape (pA pB : PMF Basis)
    (k : Program (weightedStreamSystem (finishAcc Unit 2) 0)) :
    measureRounds pA pB Unit 2 k =
      (measureAlice pA Unit 1).then
        ((measureBob pB Unit 1).then (measureRounds pA pB (Unit × StoredRecord) 1 k)) := rfl

/-- The standalone round uses Alice then Bob for unequal pure basis laws. -/
theorem unequalPure_round_shape :
    weightedStreamRoundProgram (PMF.pure Basis.z) (PMF.pure Basis.x) Unit 0 =
      (measureAlice (PMF.pure Basis.z) Unit 0).then
        ((measureBob (PMF.pure Basis.x) Unit 0).then (.done PUnit.unit)) := rfl

/-- Biased and zero-support laws remain separate parameters of the two private actions. -/
theorem biased_zeroSupport_round_shape :
    weightedStreamRoundProgram biasedBasisLaw (PMF.pure Basis.z) Unit 0 =
      (measureAlice biasedBasisLaw Unit 0).then
        ((measureBob (PMF.pure Basis.z) Unit 0).then (.done PUnit.unit)) := rfl

end QCryptLeanTest.BB84.Streaming
