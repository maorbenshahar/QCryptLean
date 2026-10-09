import QCryptLean.QKD.BB84.Program

/-!
# Protocol authoring regressions

These checks cover direct actions, natural named handoffs, heterogeneous branches, terminal
values, and the actual BB84 recursion at a symbolic round count.
-/

noncomputable section

open Quantum.Operators (Op)

namespace LOCC.AuthoringTest
open TwoParty

/-- A named private action replaces Alice's bit with a pair. -/
def duplicate := PrivateAction.ofInstrument (R := system Bool Bool) .alice
  (Instrument.functionAndForget (fun b : Bool => (b, b)))

/-- A named continuation uses the natural successor system. -/
def tail : Program (system (Bool × Bool) Bool) := .done PUnit.unit

/-- A separately defined action starts at the natural successor system. -/
def second := PrivateAction.ofInstrument (R := system (Bool × Bool) Bool) .bob
  (Instrument.functionAndForget (fun b : Bool => (b, b)))

/-- Inline sequencing infers every intermediate system. -/
def inline : Program (system Bool Bool) :=
  duplicate.then <|
    (PrivateAction.ofInstrument .bob
      (Instrument.functionAndForget (fun b : Bool => (b, b)))).then (.done PUnit.unit)

/-- A named continuation connects directly at a natural successor. -/
def named := duplicate.then tail

/-- A separately defined action can be reused directly in a chain. -/
def reused : Program (system Bool Bool) :=
  duplicate.then (second.then (.done PUnit.unit))

/-- A register-changing announcement connects directly to the named natural continuation. -/
def announcedNamed : Program (system Bool Bool) :=
  (AnnouncedAction.ofInstrument (R := system Bool Bool) .alice
    (Instrument.functionAndForget (fun b : Bool => (b, b))) id).then fun _ => tail

/-- The positive branch erases Alice's register. -/
def yes : Program (system Bool Bool) :=
  (PrivateAction.ofInstrument .alice (Instrument.discardToUnit Bool)).then (.done PUnit.unit)

/-- The negative branch keeps both registers. -/
def no : Program (system Bool Bool) := .done PUnit.unit

/-- An ordinary conditional chooses continuations with different output systems. -/
def branching : Program (system Bool Bool) :=
  (AnnouncedAction.ofInstrument (R := system Bool Bool) .alice
    (Instrument.nondemolitionReadout id) id).then fun bit =>
    if bit = true then yes else no

/-- Ordinary pattern matching also chooses different output systems. -/
def matching : Program (system Bool Bool) :=
  (AnnouncedAction.ofInstrument (R := system Bool Bool) .alice
    (Instrument.nondemolitionReadout id) id).then fun bit =>
    match bit with
    | true => yes
    | false => no

example : inline.boundary = .leaf (system (Bool × Bool) (Bool × Bool)) := rfl
example : reused = inline := rfl
example : named.boundary = .leaf (system (Bool × Bool) Bool) := rfl
example : yes.boundary = .leaf (system Unit Bool) := rfl
example : no.boundary = .leaf (system Bool Bool) := rfl
example : (if true then yes else no).boundary = .leaf (system Unit Bool) := rfl
example : (if false then yes else no).boundary = .leaf (system Bool Bool) := rfl

example : branching.boundary = .announce Bool (fun bit =>
    if bit then .leaf (system Unit Bool) else .leaf (system Bool Bool)) := by
  change Boundary.announce Bool _ = _
  congr 1
  funext bit
  cases bit <;> rfl

example : matching.boundary = .announce Bool (fun bit =>
    if bit then .leaf (system Unit Bool) else .leaf (system Bool Bool)) := by
  change Boundary.announce Bool _ = _
  congr 1
  funext bit
  cases bit <;> rfl

example (A B X : Type) [Nonempty A] [Fintype A] [DecidableEq A]
    [Nonempty B] [Fintype B] [DecidableEq B]
    [Nonempty X] [Fintype X] [DecidableEq X] :
    SystemPresentation.update (system A B) .alice X = system X B := rfl

example (A B X : Type) [Nonempty A] [Fintype A] [DecidableEq A]
    [Nonempty B] [Fintype B] [DecidableEq B]
    [Nonempty X] [Fintype X] [DecidableEq X] :
    SystemPresentation.update (system A B) .bob X = system A X := rfl

example {P : Type} [Fintype P] [DecidableEq P] (R : MultipartiteSystem P)
    (i : P) (X : Type) [Nonempty X] [Fintype X] [DecidableEq X] :
    SystemPresentation.update R i X = R.set i X := rfl

open QKD.BB84 QKD.BB84.Measurement

/-- The symbolic measurement recursion feeds natural completed records to named announcements. -/
def symbolicRounds (pA pB : PMF Basis) (N : ℕ) :
    Program (system (streamRegister Unit N) (streamRegister Unit N)) :=
  measureRounds pA pB Unit N <|
    (announceAliceBases N).then fun _ =>
      (announceBobBases N).then fun _ => .done PUnit.unit

example (pA pB : PMF Basis) : (symbolicRounds pA pB 0).boundary =
    .announce (Fin 0 → Basis) (fun _ => .announce (Fin 0 → Basis) (fun _ =>
      .leaf (system (CompletedLocalRecord 0) (CompletedLocalRecord 0)))) := rfl


end LOCC.AuthoringTest
