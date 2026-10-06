import QCryptLean.LOCC.Typed.LocalAction.ComputationalMeasurement
import QCryptLean.LOCC.Typed.TwoParty
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for the private computational measurement

These finite probes unfold `Instrument.computationalMeasurement` and the typed local-action lift of
`PrivateAction.computationalMeasurement` on a heterogeneous two-party multipartite system.  They do
not invoke the integrated laws of
`QCryptLean.LOCC.Typed.LocalAction.ComputationalMeasurement`.  The fixture keeps the
spectator row and column independent, including on a non-Hermitian matrix unit.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QCryptLeanTest.LOCC.LocalAction.ComputationalMeasurementProbes

open TypedLOCC
open TypedLOCC.TwoParty

/-! ## A heterogeneous private-measurement fixture -/

abbrev testSystem : MultipartiteSystem Party := system (Fin 2) (Fin 3)

def testPrivateAction : PrivateAction testSystem :=
  PrivateAction.computationalMeasurement testSystem .alice

def spectatorCoordinate (b : Fin 3) : testSystem.rest .alice := fun j =>
  match h : j.1 with
  | .alice => (j.2 h).elim
  | .bob => b

def inputAt (a : Fin 2) (s : testSystem.rest .alice) : testSystem.total :=
  (testSystem.splitAt .alice).symm (a, s)

def outputAt (a : Fin 2) (s : testSystem.rest .alice) : testPrivateAction.out.total :=
  (testSystem.splitAtSet .alice (Fin 2)).symm (a, s)

/-- Finite-instance lifting calculation for an arbitrary local instrument and operator. -/
theorem testLiftedOperation_eq_local
    {O : Type} [Fintype O]
    (L : Instrument (testSystem.reg .alice) (testSystem.reg .alice) O)
    (o : O) (rho : Op testSystem.total) (q q' : testPrivateAction.out.total) :
    ((PrivateAction.ofInstrument (R := testSystem) .alice L).liftedOperation o rho) q q' =
      (L.operation o
        (rho.submatrix
          (fun x => (testSystem.splitAt .alice).symm
            (x, ((testSystem.splitAtSet .alice (Fin 2)) q).2))
          (fun y => (testSystem.splitAt .alice).symm
            (y, ((testSystem.splitAtSet .alice (Fin 2)) q').2))))
        ((testSystem.splitAtSet .alice (Fin 2)) q).1
        ((testSystem.splitAtSet .alice (Fin 2)) q').1 := by
  let rhoqq : Op (testSystem.reg .alice) :=
    rho.submatrix
      (fun x => (testSystem.splitAt .alice).symm
        (x, ((testSystem.splitAtSet .alice (Fin 2)) q).2))
      (fun y => (testSystem.splitAt .alice).symm
        (y, ((testSystem.splitAtSet .alice (Fin 2)) q').2))
  have hsum (g : testSystem.total → ℂ) :
      (∑ x, g x) =
        ∑ p : testSystem.reg .alice × testSystem.rest .alice,
          g ((testSystem.splitAt .alice).symm p) := by
    exact (Equiv.sum_comp (testSystem.splitAt .alice).symm g).symm
  simp only [PrivateAction.liftedOperation, PrivateAction.liftedKraus,
    PrivateAction.ofInstrument, Instrument.operation, matrixConjLinear,
    LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.sum_apply, Matrix.mul_apply, localKrausLift_apply, ite_mul,
    zero_mul, Matrix.conjTranspose_apply, RCLike.star_def]
  simp_rw [hsum]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp [apply_ite]

/-- The private computational measurement has the expected branch formula on arbitrary operators,
while its two spectator coordinates remain unrelated. -/
theorem testPrivateAction_entry
    (o a a' : Fin 2) (s s' : testSystem.rest .alice)
    (rho : Op testSystem.total) :
    (testPrivateAction.liftedOperation o rho) (outputAt a s) (outputAt a' s') =
      if a = o ∧ a' = o then rho (inputAt a s) (inputAt a' s') else 0 := by
  change
    ((PrivateAction.ofInstrument (R := testSystem) .alice
      (Instrument.computationalMeasurement (Fin 2))).liftedOperation o rho)
        (outputAt a s) (outputAt a' s') = _
  rw [testLiftedOperation_eq_local]
  simp [Instrument.computationalMeasurement, outputAt, inputAt]

/-- Summing the private outcomes dephases only Alice's coordinate. -/
theorem testPrivateAction_channel_entry
    (a a' : Fin 2) (s s' : testSystem.rest .alice)
    (rho : Op testSystem.total) :
    ((∑ o : Fin 2, testPrivateAction.liftedOperation o) rho)
        (outputAt a s) (outputAt a' s') =
      if a = a' then rho (inputAt a s) (inputAt a' s') else 0 := by
  simp only [LinearMap.sum_apply, Matrix.sum_apply]
  simp_rw [testPrivateAction_entry]
  by_cases h : a = a'
  · subst a'
    simp
  · fin_cases a <;> fin_cases a' <;> simp_all

theorem spectatorCoordinate_zero_ne_one :
    spectatorCoordinate 0 ≠ spectatorCoordinate 1 := by
  intro h
  have hb := congrFun h (⟨.bob, by decide⟩ : {j : Party // j ≠ .alice})
  exact Fin.zero_ne_one (show (0 : Fin 3) = 1 from hb)

theorem inputAt_unequal_spectators :
    inputAt 0 (spectatorCoordinate 0) ≠ inputAt 0 (spectatorCoordinate 1) := by
  intro h
  have hp := congrArg (testSystem.splitAt .alice) h
  have hs : spectatorCoordinate 0 = spectatorCoordinate 1 := by
    simpa [inputAt] using congrArg Prod.snd hp
  exact spectatorCoordinate_zero_ne_one hs

def unequalSpectatorUnit : Op testSystem.total :=
  Matrix.single
    (inputAt 0 (spectatorCoordinate 0))
    (inputAt 0 (spectatorCoordinate 1)) 1

theorem unequalSpectatorUnit_not_selfAdjoint :
    unequalSpectatorUnitᴴ ≠ unequalSpectatorUnit := by
  intro h
  have h01 := congrFun
    (congrFun h (inputAt 0 (spectatorCoordinate 0)))
      (inputAt 0 (spectatorCoordinate 1))
  simp [unequalSpectatorUnit, Matrix.conjTranspose_apply,
    inputAt_unequal_spectators, inputAt_unequal_spectators.symm] at h01

theorem privateBranch_preserves_unequal_spectator_entry :
    (testPrivateAction.liftedOperation (0 : Fin 2) unequalSpectatorUnit)
        (outputAt 0 (spectatorCoordinate 0))
        (outputAt 0 (spectatorCoordinate 1)) = 1 := by
  rw [testPrivateAction_entry]
  simp [unequalSpectatorUnit, inputAt]

theorem privateBranch_wrong_local_value_zero
    (rho : Op testSystem.total) (s s' : testSystem.rest .alice) :
    (testPrivateAction.liftedOperation (0 : Fin 2) rho) (outputAt 1 s) (outputAt 0 s') = 0 := by
  rw [testPrivateAction_entry]
  simp

end QCryptLeanTest.LOCC.LocalAction.ComputationalMeasurementProbes
