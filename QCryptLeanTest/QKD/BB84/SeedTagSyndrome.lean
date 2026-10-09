import QCryptLean.QKD.BB84.SeedTagSyndrome
import QCryptLean.QKD.BB84.FinalStage
import Mathlib.Tactic.NormNum
import Mathlib.Util.AssertNoSorry

/-!
# Natural seed, tag and syndrome announcement probes

These checks cover public seed visibility, the local operation formula, spectator coherence,
and the empty-parameter action.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QCryptLeanTest.BB84.SeedTagSyndrome

open _root_.LOCC QKD.BB84 QKD.BB84.Measurement
open _root_.LOCC.TwoParty
open QKD.BB84.FiniteKey
open QKD.BB84

/-! ## Local lifting with independent spectator coordinates -/

/-- The finite-register instance stored by the raw multipartite system, exposed while the acting
party remains dependent in the generic lifting probe. -/
local instance rawSystemRegFintype (n : ℕ) (actor : Party) :
    Fintype ((FinalStage.rawSystem n).reg actor) :=
  (FinalStage.rawSystem n).finReg actor

/-- The decidable-equality instance stored by the raw multipartite system, exposed while the acting
party remains dependent in the generic lifting probe. -/
local instance rawSystemRegDecidableEq (n : ℕ) (actor : Party) :
    DecidableEq ((FinalStage.rawSystem n).reg actor) :=
  (FinalStage.rawSystem n).decReg actor

/-- A finite BB84 multipartite system instance of the definition-level announced-action lifting
calculation. -/
theorem announcedLiftedOperation_eq_local
    (n : ℕ) (actor : Party)
    {O Public : Type} [Fintype O] [Fintype Public] [DecidableEq Public]
    (L : Instrument ((FinalStage.rawSystem n).reg actor)
      ((FinalStage.rawSystem n).reg actor) O)
    (announce : O → Public) (o : O)
    (rho : Quantum.Operators.Op (FinalStage.rawSystem n).total)
    (q q' : ((AnnouncedAction.ofInstrument actor L announce).out (announce o)).total) :
    ((AnnouncedAction.ofInstrument actor L
          announce).liftedOperation o rho) q q' =
      (L.operation o
        (rho.submatrix
          (fun x => ((FinalStage.rawSystem n).splitAt actor).symm
            (x, (((FinalStage.rawSystem n).splitAtSet actor ((FinalStage.rawSystem n).reg actor))
              q).2))
          (fun y => ((FinalStage.rawSystem n).splitAt actor).symm
            (y, (((FinalStage.rawSystem n).splitAtSet actor ((FinalStage.rawSystem n).reg actor))
              q').2))))
        (((FinalStage.rawSystem n).splitAtSet actor ((FinalStage.rawSystem n).reg actor)) q).1
        (((FinalStage.rawSystem n).splitAtSet actor ((FinalStage.rawSystem n).reg actor)) q').1 :=
          by
  rw [AnnouncedAction.liftedOperation_ofInstrument_eq_liftAt_operation]
  exact Instrument.liftAt_operation_apply actor L o rho q q'

/-! ## Fused public cell and visible seed -/

def samplePeSel : Fin 1 → Bool := fun _ => false

def samplePASeedZero : KeyHashSeed 1 1 samplePeSel := fun _ _ => 0
def samplePASeedOne : KeyHashSeed 1 1 samplePeSel := fun _ _ => 1
def sampleEVSeed : KeyHashSeed 1 0 samplePeSel := fun j => Fin.elim0 j

def sampleSeedPairZero : KeyHashSeedPairEV 1 1 0 samplePeSel :=
  (samplePASeedZero, sampleEVSeed)

def sampleSeedPairOne : KeyHashSeedPairEV 1 1 0 samplePeSel :=
  (samplePASeedOne, sampleEVSeed)

theorem sampleSeedPairs_distinct : sampleSeedPairZero ≠ sampleSeedPairOne := by
  intro h
  have hbit := congrArg
    (fun st : KeyHashSeedPairEV 1 1 0 samplePeSel =>
      st.1 0 (⟨0, rfl⟩ : {i : Fin 1 // samplePeSel i = false})) h
  change (0 : Fin 2) = 1 at hbit
  exact (by decide : (0 : Fin 2) ≠ 1) hbit

/-- Distinct seeds remain distinct in the natural public tuple. -/
theorem distinct_seeds_have_distinct_public_cells :
    (sampleSeedPairZero, (0 : Bits 0), (0 : Bits 0)) ≠
      (sampleSeedPairOne, (0 : Bits 0), (0 : Bits 0)) := by
  exact fun h => sampleSeedPairs_distinct (congrArg Prod.fst h)

def sampleEC : ECScheme 1 samplePeSel 0 :=
  ⟨fun _ => 0, fun b _ => b⟩

/-- Alice announces every component of the natural tuple. -/
theorem fused_announcement_is_injective :
    Function.Injective (announceSeedTagSyndrome (B := Bits 1) 1 0 sampleEC).announce :=
  Function.injective_id

theorem fusedReadout_localOperation_entry
    (r : KeyHashSeedPairEV 1 1 0 samplePeSel) (v : (Bits 0 × Bits 0))
    (rho : Quantum.Operators.Op (Bits 1)) (a b : Bits 1) :
    (Instrument.uniformChoice fun r => Instrument.nondemolitionReadout
      (tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r)).operation (r, v) rho a b =
      if QKD.BB84.tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r a = v ∧
          QKD.BB84.tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r b = v then
        (Fintype.card (KeyHashSeedPairEV 1 1 0 samplePeSel) : ℂ)⁻¹ * rho a b
      else 0 := by
  rw [Instrument.uniformChoice_operation]
  simp [Instrument.nondemolitionReadout_operation_apply]

def nonHermitianLocal : Quantum.Operators.Op (Bits 1) :=
  Matrix.single 0 0 1 + Matrix.single 0 1 1

theorem nonHermitianLocal_not_selfAdjoint : nonHermitianLocalᴴ ≠ nonHermitianLocal := by
  intro h
  have h01 := congrFun (congrFun h (0 : Bits 1)) (1 : Bits 1)
  simp [nonHermitianLocal, Matrix.conjTranspose_apply,
    show (0 : Bits 1) ≠ 1 by decide, show (1 : Bits 1) ≠ 0 by decide] at h01

theorem fusedReadout_retains_offDiagonal_in_one_fibre
    (r : KeyHashSeedPairEV 1 1 0 samplePeSel) (v : (Bits 0 × Bits 0))
    (h0 : QKD.BB84.tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r 0 = v)
    (h1 : QKD.BB84.tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r 1 = v) :
    (Instrument.uniformChoice fun r => Instrument.nondemolitionReadout
      (tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r)).operation
        (r, v) nonHermitianLocal 0 1 =
      (Fintype.card (KeyHashSeedPairEV 1 1 0 samplePeSel) : ℂ)⁻¹ := by
  rw [fusedReadout_localOperation_entry]
  simp [h0, h1, nonHermitianLocal, show (0 : Bits 1) ≠ 1 by decide]

theorem fusedReadout_removes_crossFibre_entry
    (r : KeyHashSeedPairEV 1 1 0 samplePeSel) (v : (Bits 0 × Bits 0))
    (h1 : QKD.BB84.tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r 1 ≠ v) :
    (Instrument.uniformChoice fun r => Instrument.nondemolitionReadout
      (tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r)).operation
        (r, v) nonHermitianLocal 0 1 = 0 := by
  rw [fusedReadout_localOperation_entry]
  simp [h1]

theorem fusedBranch_reduces_to_local
    (r : KeyHashSeedPairEV 1 1 0 samplePeSel) (v : (Bits 0 × Bits 0))
    (rho : Quantum.Operators.Op (FinalStage.rawSystem 1).total)
    (q q' : ((announceSeedTagSyndrome (B := Bits 1) 1 0 sampleEC).out
      (r, v)).total) :
    ((announceSeedTagSyndrome (B := Bits 1) 1 0 sampleEC).liftedOperation (r, v) rho) q q' =
      ((Instrument.uniformChoice fun r => Instrument.nondemolitionReadout
      (tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r)).operation (r, v)
        (rho.submatrix
          (fun x => ((FinalStage.rawSystem 1).splitAt .alice).symm
            (x, (((FinalStage.rawSystem 1).splitAtSet .alice ((FinalStage.rawSystem 1).reg
              .alice)) q).2))
          (fun y => ((FinalStage.rawSystem 1).splitAt .alice).symm
            (y, (((FinalStage.rawSystem 1).splitAtSet .alice ((FinalStage.rawSystem 1).reg
              .alice)) q').2))))
        (((FinalStage.rawSystem 1).splitAtSet .alice ((FinalStage.rawSystem 1).reg .alice)) q).1
        (((FinalStage.rawSystem 1).splitAtSet .alice ((FinalStage.rawSystem 1).reg .alice)) q').1
          := by
  exact announcedLiftedOperation_eq_local 1 .alice
    (Instrument.uniformChoice fun r => Instrument.nondemolitionReadout
      (tagAndSyndrome 1 1 0 samplePeSel 0 sampleEC r))
    id (r, v) rho q q'

/-! ## Empty-parameter construction -/

def emptyPeSel : Fin 0 → Bool := Fin.elim0
def emptyEC : ECScheme 0 emptyPeSel 0 := ⟨fun _ => 0, fun b _ => b⟩

def emptyFusedReadout : Instrument (Bits 0) (Bits 0)
    (KeyHashSeedPairEV 0 0 0 emptyPeSel × (Bits 0 × Bits 0)) :=
  Instrument.uniformChoice fun r => Instrument.nondemolitionReadout
    (tagAndSyndrome 0 0 0 emptyPeSel 0 emptyEC r)

theorem empty_fused_seed_card :
    Fintype.card (KeyHashSeedPairEV 0 0 0 emptyPeSel) = 1 := by
  decide

end QCryptLeanTest.BB84.SeedTagSyndrome
