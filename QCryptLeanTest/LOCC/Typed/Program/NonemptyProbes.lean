import QCryptLean.LOCC.Typed.Program.Uniform
import QCryptLeanTest.LOCC.Typed.Examples.HeterogeneousProgram
import Mathlib.Util.AssertNoSorry

/-!
# Complete exits of typed programs

Completeness supplies an exit for actual programs, including dependent output multipartite systems
and empty party types. Raw boundaries may still have no exits, and declared public labels may be
unused.
-/

namespace QCryptLeanTest.LOCC.Program.NonemptyProbes

open TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

example {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) : Nonempty B.Exit :=
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

example (R : MultipartiteSystem P) : IsEmpty (Program R (emptyBoundary P)) :=
  ⟨fun p => p.nonempty_exit.elim fun e => e.1.elim⟩

/-- The joint register of an empty party family is still inhabited. -/
def emptyPartySystem : MultipartiteSystem Empty where
  reg p := nomatch p
  nonemptyReg p := nomatch p
  finReg p := nomatch p
  decReg p := nomatch p

example : Nonempty (Boundary.leaf emptyPartySystem).Exit :=
  (Program.done : Program emptyPartySystem (.leaf emptyPartySystem)).nonempty_exit

open Examples.HeterogeneousProgram

example : Nonempty branchBoundary.Exit := branchProgram.nonempty_exit

example : Nonempty unusedLabelAction.boundary.Exit := unusedLabelProgram.nonempty_exit

example (b : unusedLabelProgram.Branch) : b.exit.1 = false :=
  unusedLabelProgram_exit_false b

/-! Uniform programs supply transcripts, but raw transcript words may still be empty. -/

example {R S : MultipartiteSystem P} {T : TList} (p : Program R (Boundary.uniform S T)) :
    Nonempty (Transcript T) := p.nonempty_transcript

example : ¬ Nonempty (Transcript (.cons Empty .nil)) := by
  rintro ⟨t⟩
  exact t.1.elim

example : True := by
  fail_if_success
    let _ := inferInstanceAs (Nonempty (Transcript (.cons Empty .nil)))
  trivial

example {R S : MultipartiteSystem P} : IsEmpty (Program R (Boundary.uniform S (.cons Empty .nil)))
    :=
  ⟨fun p => p.nonempty_transcript.elim fun t => t.1.elim⟩

end QCryptLeanTest.LOCC.Program.NonemptyProbes
