import QCryptLean.QKD.BB84.Model.RealChannelEntrywise
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.QKD.BB84.Transcript
import QCryptLean.LOCC.Typed.Program.GraftDenotation
import Mathlib.Tactic.FinCases
import Mathlib.Util.AssertNoSorry

/-!
# Regression probes for typed BB84 local instruments

These fixtures evaluate typed readout and hash instruments on diagonal and off-diagonal
inputs directly from their definitions.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QKD.BB84.FinalStage.LocalLawProbes
open TypedLOCC

open TypedLOCC.TwoParty
/-! ## Readout coherence -/

def coarseReadout : Fin 3 → Fin 2 := fun x => if x = 2 then 1 else 0

def readoutOffDiagonal : Op (Fin 3) := Matrix.single 0 1 1

/-- The readout branch for outcome zero retains coherence within that fibre. -/
theorem directPinned_semanticZero_preserves_offDiagonal :
    (Instrument.nondemolitionReadout coarseReadout).operation
        0 readoutOffDiagonal =
      readoutOffDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Instrument.nondemolitionReadout_operation_apply, coarseReadout, readoutOffDiagonal]

/-- A different semantic fibre kills the same nonzero matrix unit. -/
theorem directPinned_wrong_fibre_zero :
    (Instrument.nondemolitionReadout coarseReadout).operation 1 readoutOffDiagonal = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Instrument.nondemolitionReadout_operation_apply, coarseReadout,
      readoutOffDiagonal]

/-! ## Hash channels -/

def constantHash : Fin 2 → Fin 1 := fun _ => 0
def hashDiagonal : Op (Fin 2) := Matrix.single 1 1 1
def hashOffDiagonal : Op (Fin 2) := Matrix.single 0 1 1
def onePopulation : Op (Fin 1) := Matrix.single 0 0 1

theorem directHash_diagonal :
    (Instrument.functionAndForget constantHash).channel hashDiagonal = onePopulation := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Instrument.channel, Instrument.functionAndForget_operation_apply,
    constantHash, hashDiagonal, onePopulation]

theorem directHash_offDiagonal :
    (Instrument.functionAndForget constantHash).channel hashOffDiagonal = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Instrument.channel, Instrument.functionAndForget_operation_apply,
    constantHash, hashOffDiagonal]

theorem hashOffDiagonal_ne_zero : hashOffDiagonal ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  simp [hashOffDiagonal] at h01

end QKD.BB84.FinalStage.LocalLawProbes
