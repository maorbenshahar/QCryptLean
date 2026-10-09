import QCryptLean.QKD.BB84.ParameterEstimation

/-!
# Definition-level probes for the parameter-estimation disclosure

The probes check the announced test bits and the actual
Bob-then-Alice recursion with named continuations at natural systems.
-/

noncomputable section
namespace QCryptLeanTest.BB84.ParameterEstimation
open _root_.LOCC _root_.LOCC.TwoParty QKD.BB84 QKD.BB84.Measurement

/-- The first bit of a two-bit raw register. -/
def testIndex : Fin 2 := 0

/-- Bob announces the bit read by his instrument. -/
theorem peBitAnnouncement_announce_eq_raw (x : Fin 2) :
    (announceBobTest (A := Bits 2) testIndex).announce x = x := rfl

/-- The zero-round continuation terminates at the unchanged raw system. -/
def zeroContinuation (_ : Fin 0 → Fin 2 × Fin 2) : Program (system (Bits 2) (Bits 2)) :=
  .done PUnit.unit

/-- The one-round continuation terminates at the unchanged raw system. -/
def oneContinuation (_ : Fin 1 → Fin 2 × Fin 2) : Program (system (Bits 2) (Bits 2)) :=
  .done PUnit.unit

/-- The single test selects the first raw bit. -/
def oneIndex : Fin 1 → Fin 2 := fun _ => 0

/-- Zero test rounds run their named continuation immediately. -/
theorem peAnnouncementLoop_zero :
    announceTests 0 (n := 2) Fin.elim0 zeroContinuation = zeroContinuation Fin.elim0 := rfl

/-- A test round announces Bob's then Alice's cell and passes the bit pair onward. -/
theorem peAnnouncementLoop_one_bob_then_alice :
    announceTests 1 oneIndex oneContinuation =
      (announceBobTest (oneIndex 0)).then fun b =>
        (announceAliceTest (oneIndex 0)).then fun a =>
          announceTests 0 (Fin.tail oneIndex) fun rest =>
            oneContinuation (Fin.cons (a, b) rest) := rfl

end QCryptLeanTest.BB84.ParameterEstimation
