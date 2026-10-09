import QCryptLean.LOCC.Program.Uniform
import QCryptLeanTest.LOCC.Examples.HeterogeneousProgram
import Mathlib.Util.AssertNoSorry

/-!
# Complete exits of typed programs

Completeness supplies an exit for programs with inhabited input registers, including dependent
outputs
and empty party types. Raw boundaries may still have no exits, and declared public labels may be
unused.
-/

namespace QCryptLeanTest.LOCC.Program.NonemptyProbes

open _root_.LOCC

variable {P : Type} [Fintype P] [DecidableEq P] [SystemPresentation P]
variable {End : MultipartiteSystem P → Type 1}

example {R : MultipartiteSystem P} [Nonempty R.total] (p : Program R End) : Nonempty p.boundary.Exit
  :=
  p.nonempty_exit

/-- A syntactic boundary with no declared public values. -/
def emptyBoundary (P : Type) [Fintype P] [DecidableEq P] : Boundary P :=
  .announce Empty (fun y => nomatch y)

example : ¬ Nonempty (emptyBoundary P).Exit := by
  rintro ⟨e⟩
  exact e.1.elim

example : True := by
  fail_if_success
    let _ := inferInstanceAs (Nonempty (emptyBoundary P).Exit)
  trivial

example {R : MultipartiteSystem P} [Nonempty R.total] (p : Program R End) : p.boundary ≠
  emptyBoundary P := by
  intro h
  obtain ⟨e⟩ := p.nonempty_exit.map (Equiv.cast (congrArg Boundary.Exit h))
  exact e.1.elim

/-- The joint register of an empty party family is still inhabited. -/
def emptyPartySystem : MultipartiteSystem Empty where
  reg p := nomatch p
  finReg p := nomatch p
  decReg p := nomatch p

example : Nonempty (Boundary.leaf emptyPartySystem).Exit :=
  (Program.done PUnit.unit : Program emptyPartySystem).nonempty_exit

open _root_.LOCC.Examples.HeterogeneousProgram

example : Nonempty branchBoundary.Exit := branchProgram.nonempty_exit

example : Nonempty unusedLabelProgram.boundary.Exit := unusedLabelProgram.nonempty_exit

example (b : unusedLabelProgram.Branch) : b.exit.1 = false :=
  unusedLabelProgram_exit_false b

/-! Uniform programs supply transcripts, but raw transcript words may still be empty. -/

example {R S : MultipartiteSystem P} [Nonempty R.total] {T : TList} (p : Program R End)
    (h : p.boundary = Boundary.uniform S T) :
    Nonempty (Transcript T) := p.nonempty_transcript h

example : ¬ Nonempty (Transcript (.cons Empty .nil)) := by
  rintro ⟨t⟩
  exact t.1.elim

example : True := by
  fail_if_success
    let _ := inferInstanceAs (Nonempty (Transcript (.cons Empty .nil)))
  trivial

example {R S : MultipartiteSystem P} [Nonempty R.total] (p : Program R End) :
    p.boundary ≠ Boundary.uniform S (.cons Empty .nil) := by
  intro h
  exact (p.nonempty_transcript h).elim fun t => t.1.elim

end QCryptLeanTest.LOCC.Program.NonemptyProbes


namespace LOCC.EmptyInputProbe

/-- An empty local input supports a complete instrument with no outcomes. -/
def noOutcomeInstrument : Instrument Empty Empty Empty :=
  Instrument.ofFine Empty.elim (by ext i; exact i.elim)

/-- An empty-input protocol may have no public exit. -/
def noExitProgram : Program (TwoParty.system Empty Unit) :=
  (AnnouncedAction.ofInstrument .alice noOutcomeInstrument id).then (fun e => nomatch e)

example : ¬ Nonempty noExitProgram.boundary.Exit := by
  rintro ⟨e⟩
  change (Σ e : Empty, _) at e
  exact e.1.elim

end LOCC.EmptyInputProbe
