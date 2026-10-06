import QCryptLean.LOCC.Typed.Program.Classical
import QCryptLean.LOCC.Typed.TwoParty
import Mathlib.Tactic.NormNum
import Mathlib.Util.AssertNoSorry

/-!
# Regression probes for classical private actions

These finite fixtures check the joint-register formula for a many-to-one deterministic local
function. Row and column spectator coordinates remain independent, including for a
non-Hermitian matrix unit.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QKD.BB84.FinalStage.LocalLawProbes
open TypedLOCC

open TypedLOCC.TwoParty

/-! ## A concrete local action with an unequal spectator pair -/

abbrev inputSystem : MultipartiteSystem Party := system (Fin 2) (Fin 3)
def constantZero : Fin 2 → Fin 2 := fun _ => 0

def constantAction : PrivateAction inputSystem :=
  PrivateAction.ofInstrument .alice
    (Instrument.functionAndForget constantZero)

/-- The unique spectator tuple is presented independently of the actor coordinate. -/
def spectatorCoordinate (b : Fin 3) : inputSystem.rest .alice := fun j =>
  match h : j.1 with
  | .alice => (j.2 h).elim
  | .bob => b

def inputAt (a : Fin 2) (s : inputSystem.rest .alice) : inputSystem.total :=
  (inputSystem.splitAt .alice).symm (a, s)

def outputAt (a : Fin 2) (s : inputSystem.rest .alice) : constantAction.out.total :=
  (inputSystem.splitAtSet .alice (Fin 2)).symm (a, s)

theorem spectatorCoordinate_zero_ne_one :
    spectatorCoordinate 0 ≠ spectatorCoordinate 1 := by
  intro h
  have hb := congrFun h (⟨.bob, by decide⟩ : {j : Party // j ≠ .alice})
  exact Fin.zero_ne_one (show (0 : Fin 3) = 1 from hb)

theorem inputAt_unequal_spectators :
    inputAt 0 (spectatorCoordinate 0) ≠ inputAt 0 (spectatorCoordinate 1) := by
  intro h
  have hp := congrArg (inputSystem.splitAt .alice) h
  have hs : spectatorCoordinate 0 = spectatorCoordinate 1 := by
    simpa [inputAt] using congrArg Prod.snd hp
  exact spectatorCoordinate_zero_ne_one hs

/-- Compute the concrete action through the local instrument and shared tensor-lifting formulas.

The result deliberately retains separate spectator row and column coordinates.  This is a
finite fixture, not the generic theorem being tested. -/
theorem constantAction_entry
    (rho : Op inputSystem.total) (a a' : Fin 2)
    (s s' : inputSystem.rest .alice) :
    (constantAction.liftedOperation () rho) (outputAt a s) (outputAt a' s') =
      if a = 0 ∧ a' = 0 then
        ∑ x : Fin 2, rho (inputAt x s) (inputAt x s')
      else 0 := by
  classical
  refine (Instrument.liftAt_operation_apply .alice (Instrument.functionAndForget constantZero)
    () rho (outputAt a s) (outputAt a' s')).trans ?_
  simp only [outputAt, Equiv.apply_symm_apply]
  change (Instrument.functionAndForget constantZero).operation ()
    (rho.submatrix (fun x => inputAt x s) (fun x => inputAt x s')) a a' = _
  refine (Instrument.functionAndForget_operation_apply constantZero _ a a').trans ?_
  simp only [constantZero, Matrix.submatrix_apply]
  by_cases h : a = 0 ∧ a' = 0 <;> simp [h]

/-- A non-Hermitian matrix unit with different spectator row and column coordinates. -/
def unequalSpectatorUnit : Op inputSystem.total :=
  Matrix.single
    (inputAt 0 (spectatorCoordinate 0))
    (inputAt 0 (spectatorCoordinate 1)) 1

theorem unequalSpectatorUnit_not_selfAdjoint :
    unequalSpectatorUnitᴴ ≠ unequalSpectatorUnit := by
  intro h
  have h01 := congrFun
    (congrFun h
      (inputAt 0 (spectatorCoordinate 0)))
      (inputAt 0 (spectatorCoordinate 1))
  simp [unequalSpectatorUnit, Matrix.conjTranspose_apply,
    inputAt_unequal_spectators, inputAt_unequal_spectators.symm] at h01

/-- The actual lifted operation preserves the selected unequal-spectator matrix entry. -/
theorem lifted_preserves_unequal_spectator_entry :
    (constantAction.liftedOperation () unequalSpectatorUnit)
        (outputAt 0 (spectatorCoordinate 0))
        (outputAt 0 (spectatorCoordinate 1)) = 1 := by
  have h01 : inputAt 0 (spectatorCoordinate 0) ≠ inputAt 1 (spectatorCoordinate 0) := by
    intro h
    exact (Fin.zero_ne_one : (0 : Fin 2) ≠ 1)
      (congrArg Prod.fst ((inputSystem.splitAt .alice).symm.injective h))
  rw [constantAction_entry]
  simp only [unequalSpectatorUnit, Fin.sum_univ_two, Matrix.single_apply]
  simp [h01]

/-- Unequal actor output keys force zero without imposing equality on the spectators. -/
theorem lifted_unequal_output_keys_zero
    (rho : Op inputSystem.total) (s s' : inputSystem.rest .alice) :
    (constantAction.liftedOperation () rho) (outputAt 0 s) (outputAt 1 s') = 0 := by
  rw [constantAction_entry]
  simp

/-- Two different local input populations contribute to the same many-to-one output value. -/
def twoPopulations : Op inputSystem.total :=
  2 • Matrix.single
      (inputAt 0 (spectatorCoordinate 2))
      (inputAt 0 (spectatorCoordinate 2)) 1 +
  3 • Matrix.single
      (inputAt 1 (spectatorCoordinate 2))
      (inputAt 1 (spectatorCoordinate 2)) 1

theorem lifted_manyToOne_sums_input_contributions :
    (constantAction.liftedOperation () twoPopulations)
        (outputAt 0 (spectatorCoordinate 2))
        (outputAt 0 (spectatorCoordinate 2)) = 5 := by
  have hne : inputAt 0 (spectatorCoordinate 2) ≠ inputAt 1 (spectatorCoordinate 2) := by
    intro h
    exact Fin.zero_ne_one (congrArg Prod.fst ((inputSystem.splitAt .alice).symm.injective h))
  rw [constantAction_entry]
  simp only [twoPopulations, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.single_apply]
  norm_num [hne, hne.symm]

end QKD.BB84.FinalStage.LocalLawProbes
