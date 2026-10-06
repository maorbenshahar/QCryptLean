import QCryptLean.QKD.BB84.ParameterEstimation
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for the parameter-estimation disclosure

These finite probes unfold `QKD.BB84.peBitAnnouncement` and `QKD.BB84.peAnnouncementLoop` on a
two-bit raw register. They check the raw public coordinate of one announcement against its decoded
semantic bit and the literal Bob-then-Alice order of the first recursion step.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QCryptLeanTest.BB84.ParameterEstimation

open TypedLOCC QKD.BB84
open TypedLOCC.TwoParty
open QKD.BB84.PE
open QKD.BB84

/-! ## Raw public coordinates and semantic PE outcomes -/

def testIndex : Fin 2 := 0

theorem localRegisterBit_alice (x : Fin (2 ^ 2)) :
    localRegisterBit 2 testIndex .alice x = LOCC.registerBit 2 testIndex x := rfl

theorem localRegisterBit_bob (x : Fin (2 ^ 2)) :
    localRegisterBit 2 testIndex .bob x = LOCC.registerBit 2 testIndex x := rfl

theorem peBitAnnouncement_announce_eq_raw (actor : Party) (x : Fin 2) :
    (peBitAnnouncement 2 testIndex actor).announce x =
      (LOCC.outcomeDigit 2).symm x := rfl

theorem peBitAnnouncement_announce_decode (actor : Party) (x : Fin 2) :
    LOCC.outcomeDigit 2 ((peBitAnnouncement 2 testIndex actor).announce x) = x := by
  exact Equiv.apply_symm_apply _ _

theorem peBitAnnouncement_announce_outcomeDigit (o : Fin 2) :
    (peBitAnnouncement 2 testIndex .alice).announce
      (LOCC.outcomeDigit 2 o) = o := by
  exact Equiv.symm_apply_apply _ _

/-! ## Zero- and one-round recursion -/

def zeroContinuation (_ : Fin 0 → Fin 2) (_ : Fin 0 → Fin 2) :
    Program (FinalStage.rawSystem 2)
      (Boundary.uniform (FinalStage.rawSystem 2) .nil) :=
  Program.done

def oneContinuation (_ : Fin 1 → Fin 2) (_ : Fin 1 → Fin 2) :
    Program (FinalStage.rawSystem 2)
      (Boundary.uniform (FinalStage.rawSystem 2) .nil) :=
  Program.done

def oneIndex : Fin 1 → Fin 2 := fun _ => 0

theorem peAnnouncementLoop_zero :
    peAnnouncementLoop 2 0 Fin.elim0 zeroContinuation =
      zeroContinuation Fin.elim0 Fin.elim0 := rfl

/-- The successor is literally Bob's raw public cell followed by Alice's raw public cell;
the continuation receives decoded semantic strings in Alice-then-Bob order. -/
theorem peAnnouncementLoop_one_bob_then_alice :
    peAnnouncementLoop 2 1 oneIndex oneContinuation =
      (bobPEBitAnnouncement 2 (oneIndex 0)).then fun b =>
        cast (by
          simp only [bobPEBitAnnouncement, peBitAnnouncement,
            AnnouncedAction.out_ofInstrument, MultipartiteSystem.set_self]
          rfl)
          ((alicePEBitAnnouncement 2 (oneIndex 0)).then
            (B := fun _ => Boundary.uniform (FinalStage.rawSystem 2) .nil) fun a =>
            cast (by
              simp only [alicePEBitAnnouncement, peBitAnnouncement,
                AnnouncedAction.out_ofInstrument, MultipartiteSystem.set_self]
              rfl)
              (peAnnouncementLoop 2 0 (fun j => oneIndex j.succ)
                (fun as bs => oneContinuation
                  (Fin.cons (LOCC.outcomeDigit 2 a) as)
                  (Fin.cons (LOCC.outcomeDigit 2 b) bs)))) := rfl

end QCryptLeanTest.BB84.ParameterEstimation
