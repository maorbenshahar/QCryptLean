import QCryptLean.QKD.BB84.SeedTagSyndrome
import Mathlib.Tactic.NormNum
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for the fused seed, tag and syndrome announcement

These fixtures exercise the uniformly seeded readout `QKD.BB84.fusedReadoutInstrument`, the public
map `QKD.BB84.fusedPublicEquiv` and the local-action lift of `QKD.BB84.fusedAnnouncement`.  They
include arbitrary operators with independent spectator row and column coordinates, distinct
announced seeds, retention and removal of off-diagonal entries, and the empty-parameter
construction.  The raw-system instances and the generic announced-action lifting calculation are
shared with the symmetrization-prefix probes.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QCryptLeanTest.BB84.SeedTagSyndrome

open TypedLOCC QKD.BB84
open TypedLOCC.TwoParty
open QKD.BB84.Engine
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
    (rho : Op (FinalStage.rawSystem n).total)
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
  simpa only [AnnouncedAction.liftedOperation_ofInstrument_eq_liftAt_operation] using
    Instrument.liftAt_operation_apply actor L o rho q q'

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

def sampleSeedIndexZero : FusedSeedIndex 1 1 0 samplePeSel :=
  Fintype.equivFin _ sampleSeedPairZero

def sampleSeedIndexOne : FusedSeedIndex 1 1 0 samplePeSel :=
  Fintype.equivFin _ sampleSeedPairOne

theorem sampleSeedIndices_distinct : sampleSeedIndexZero ≠ sampleSeedIndexOne := by
  intro h
  apply sampleSeedPairs_distinct
  exact (Fintype.equivFin (KeyHashSeedPairEV 1 1 0 samplePeSel)).injective h

def sampleFusedValue : FusedValue 0 0 := 0

def samplePublicZero : FusedPublic 1 1 0 samplePeSel 0 :=
  fusedPublicEquiv 1 1 0 samplePeSel 0 (sampleSeedIndexZero, sampleFusedValue)

def samplePublicOne : FusedPublic 1 1 0 samplePeSel 0 :=
  fusedPublicEquiv 1 1 0 samplePeSel 0 (sampleSeedIndexOne, sampleFusedValue)

theorem distinct_seeds_have_distinct_public_cells : samplePublicZero ≠ samplePublicOne := by
  intro h
  apply sampleSeedIndices_distinct
  have hp :
      (sampleSeedIndexZero, sampleFusedValue) =
        (sampleSeedIndexOne, sampleFusedValue) := by
    apply (fusedPublicEquiv 1 1 0 samplePeSel 0).injective
    exact h
  exact congrArg Prod.fst hp

def sampleEC : ECScheme 1 samplePeSel 0 :=
  ⟨fun _ => 0, fun b _ => b⟩

theorem fused_announcement_is_injective :
    Function.Injective (fusedAnnouncement 1 1 0 samplePeSel 0 sampleEC).announce := by
  simpa [fusedAnnouncement] using
    (fusedPublicEquiv 1 1 0 samplePeSel 0).injective

theorem fused_semantic_to_raw_to_semantic
    (rv : FusedSeedIndex 1 1 0 samplePeSel × FusedValue 0 0) :
    (fusedPublicEquiv 1 1 0 samplePeSel 0).symm
      ((fusedAnnouncement 1 1 0 samplePeSel 0 sampleEC).announce rv) = rv := by
  unfold fusedAnnouncement
  change (fusedPublicEquiv 1 1 0 samplePeSel 0).symm
    (fusedPublicEquiv 1 1 0 samplePeSel 0 rv) = rv
  exact Equiv.symm_apply_apply _ _

theorem fused_raw_to_semantic_to_raw
    (o : FusedPublic 1 1 0 samplePeSel 0) :
    fusedPublicEquiv 1 1 0 samplePeSel 0
      ((fusedPublicEquiv 1 1 0 samplePeSel 0).symm o) = o := by
  exact Equiv.apply_symm_apply _ _

theorem fusedReadout_localOperation_entry
    (r : FusedSeedIndex 1 1 0 samplePeSel) (v : FusedValue 0 0)
    (rho : Op (Fin (2 ^ 1))) (a b : Fin (2 ^ 1)) :
    (fusedReadoutInstrument 1 1 0 samplePeSel 0 sampleEC).operation (r, v) rho a b =
      if QKD.BB84.Model.evTagSynOf 1 1 0 samplePeSel 0 sampleEC r a = v ∧
          QKD.BB84.Model.evTagSynOf 1 1 0 samplePeSel 0 sampleEC r b = v then
        (Fintype.card (FusedSeedIndex 1 1 0 samplePeSel) : ℂ)⁻¹ * rho a b
      else 0 := by
  unfold fusedReadoutInstrument
  rw [Instrument.uniformChoice_operation]
  simp [Instrument.nondemolitionReadout_operation_apply]

def nonHermitianLocal : Op (Fin (2 ^ 1)) :=
  Matrix.single 0 0 1 + Matrix.single 0 1 1

theorem nonHermitianLocal_not_selfAdjoint : nonHermitianLocalᴴ ≠ nonHermitianLocal := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin (2 ^ 1))) (1 : Fin (2 ^ 1))
  simp [nonHermitianLocal, Matrix.conjTranspose_apply] at h01

theorem fusedReadout_retains_offDiagonal_in_one_fibre
    (r : FusedSeedIndex 1 1 0 samplePeSel) (v : FusedValue 0 0)
    (h0 : QKD.BB84.Model.evTagSynOf 1 1 0 samplePeSel 0 sampleEC r 0 = v)
    (h1 : QKD.BB84.Model.evTagSynOf 1 1 0 samplePeSel 0 sampleEC r 1 = v) :
    (fusedReadoutInstrument 1 1 0 samplePeSel 0 sampleEC).operation
        (r, v) nonHermitianLocal 0 1 =
      (Fintype.card (FusedSeedIndex 1 1 0 samplePeSel) : ℂ)⁻¹ := by
  rw [fusedReadout_localOperation_entry]
  simp [h0, h1, nonHermitianLocal]

theorem fusedReadout_removes_crossFibre_entry
    (r : FusedSeedIndex 1 1 0 samplePeSel) (v : FusedValue 0 0)
    (h1 : QKD.BB84.Model.evTagSynOf 1 1 0 samplePeSel 0 sampleEC r 1 ≠ v) :
    (fusedReadoutInstrument 1 1 0 samplePeSel 0 sampleEC).operation
        (r, v) nonHermitianLocal 0 1 = 0 := by
  rw [fusedReadout_localOperation_entry]
  simp [h1]

theorem fusedBranch_reduces_to_local
    (r : FusedSeedIndex 1 1 0 samplePeSel) (v : FusedValue 0 0)
    (rho : Op (FinalStage.rawSystem 1).total)
    (q q' : ((fusedAnnouncement 1 1 0 samplePeSel 0 sampleEC).out
      ((fusedPublicEquiv 1 1 0 samplePeSel 0) (r, v))).total) :
    ((fusedAnnouncement 1 1 0 samplePeSel 0 sampleEC).liftedOperation (r, v) rho) q q' =
      ((fusedReadoutInstrument 1 1 0 samplePeSel 0 sampleEC).operation (r, v)
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
    (fusedReadoutInstrument 1 1 0 samplePeSel 0 sampleEC)
    (fusedPublicEquiv 1 1 0 samplePeSel 0) (r, v) rho q q'

/-! ## Empty-parameter construction -/

def emptyPeSel : Fin 0 → Bool := Fin.elim0
def emptyEC : ECScheme 0 emptyPeSel 0 := ⟨fun _ => 0, fun b _ => b⟩

def emptyFusedReadout : Instrument (Fin (2 ^ 0)) (Fin (2 ^ 0))
    (FusedSeedIndex 0 0 0 emptyPeSel × FusedValue 0 0) :=
  fusedReadoutInstrument 0 0 0 emptyPeSel 0 emptyEC

theorem empty_fused_seed_card :
    Fintype.card (FusedSeedIndex 0 0 0 emptyPeSel) = 1 := by
  decide

end QCryptLeanTest.BB84.SeedTagSyndrome
