import QCryptLean.LOCC.Program
import QCryptLean.LOCC.TwoParty
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.Discard

/-!
# Ordinary recursive discussions

These programs use symbolic fuel, public history, early termination and value-dependent final
systems. The loop is an ordinary continuation-passing recursive function.
-/

noncomputable section
open Quantum.Operators (Op)

namespace LOCC.IterationExample
open TwoParty

/-- Public replies and whether the discussion has already stopped. -/
inductive History where
  | active (bits : List Bool)
  | stopped (bits : List Bool)

/-- Stopping discards Bob's register. -/
def historySystem : History → MultipartiteSystem Party
  | .active _ => system Unit Bool
  | .stopped _ => system Unit Unit

/-- Bob's announced predicate depends on the preceding public history. -/
def ask (bits : List Bool) :=
  AnnouncedAction.ofInstrument (R := system Unit Bool) .bob
    (Instrument.nondemolitionReadout (fun b : Bool => b != bits.contains true)) id

/-- Announce replies until fuel runs out or a negative reply stops the discussion. -/
def discussion {End : MultipartiteSystem Party → Type 1} (fuel : ℕ) (h : History)
    (k : ∀ h, Program (historySystem h) End) : Program (historySystem h) End :=
  match fuel, h with
  | 0, h => k h
  | _ + 1, .stopped bits => k (.stopped bits)
  | n + 1, .active bits =>
      (ask bits).then fun bit =>
        if bit then discussion n (.active (bits ++ [bit])) k
        else (PrivateAction.ofInstrument (R := system Unit Bool) .bob
          (Instrument.discardToUnit Bool)).then (k (.stopped (bits ++ [bit])))

example : (discussion 0 (.active [])
      (fun _ => Program.done (End := fun _ => PUnit) PUnit.unit)).boundary =
    .leaf (system Unit Bool) := rfl

example : (discussion 1 (.active [])
      (fun _ => Program.done (End := fun _ => PUnit) PUnit.unit)).boundary.system
    ⟨true, ()⟩ = system Unit Bool := rfl

example : (discussion 1 (.active [])
      (fun _ => Program.done (End := fun _ => PUnit) PUnit.unit)).boundary.system
    ⟨false, ()⟩ = system Unit Unit := rfl

/-- A stopped discussion passes its history directly to the continuation for any remaining fuel. -/
theorem stopped_discussion {End : MultipartiteSystem Party → Type 1}
    (fuel : ℕ) (bits : List Bool) (k : ∀ h, Program (historySystem h) End) :
    discussion fuel (.stopped bits) k = k (.stopped bits) := by
  cases fuel <;> rfl

example : (discussion 2 (.active [])
    (fun h => .done (End := fun _ => ULift History) ⟨h⟩)).terminal
      ⟨true, false, ()⟩ = ⟨History.stopped [true, false]⟩ := rfl

/-- Repeated announcements need only ordinary structural recursion. -/
def publicRepeat (I : Instrument Unit Unit Bool) (n : ℕ) : Program (system Unit Unit) :=
  match n with
  | 0 => .done PUnit.unit
  | n + 1 => (AnnouncedAction.ofInstrument (R := system Unit Unit) .alice I id).then
      fun _ => publicRepeat I n

example (I J : Instrument Unit Unit Bool) (n : ℕ) :
    (publicRepeat I n).boundary = (publicRepeat J n).boundary := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Boundary.announce Bool (fun _ => (publicRepeat I n).boundary) =
        Boundary.announce Bool (fun _ => (publicRepeat J n).boundary)
      rw [ih]

end LOCC.IterationExample
