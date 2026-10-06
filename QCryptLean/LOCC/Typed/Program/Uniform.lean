import QCryptLean.LOCC.Typed.Program.Denotation
import QCryptLean.LOCC.Typed.Boundary.Uniform

/-!
# Uniform-output coordinates for typed LOCC programs

A program whose boundary has one fixed terminal multipartite system and a transcript-shaped public
tree already denotes a channel into the boundary's dependent-sum output.  This module relabels that
output by the canonical product `S.total × Transcript T`.  It introduces no padding and does not
change the program's complete-path instrument.
-/

open scoped Matrix

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Program

/-- A complete uniform-output program supplies a transcript of its announcement word. -/
theorem nonempty_transcript {R S : MultipartiteSystem P} {T : TList}
    (p : Program R (Boundary.uniform S T)) : Nonempty (Transcript T) :=
  p.nonempty_exit.map (Boundary.uniformExitEquiv S T)

/-- View a program from the terminal multipartite system as a continuation from any exit of a
uniform boundary. Recursion on the transcript shape computes without inserting an equality transport
around the program. -/
def atUniformExit {S : MultipartiteSystem P} {B : Boundary P}
    (p : Program S B) (T : TList) (e : (Boundary.uniform S T).Exit) :
    Program ((Boundary.uniform S T).system e) B :=
  match T with
  | .nil => p
  | @TList.cons _ _ _ T => atUniformExit p T e.2

/-- Reindex the native denotation of a uniform-boundary program into final-register and transcript
coordinates.

This is only the coordinate presentation of the finite public measurement-history tree from
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2: every public history has the
same final multipartite system `S`, so `Boundary.uniformSpaceEquiv` identifies the native dependent
sum with `S.total × Transcript T`.
-/
noncomputable def uniformDenote {R S : MultipartiteSystem P} {T : TList}
    (p : Program R (Boundary.uniform S T)) :
    Op R.total →ₗ[ℂ] Op (S.total × Transcript T) :=
  (Matrix.reindexLinearEquiv ℂ ℂ
    (Boundary.uniformSpaceEquiv S T) (Boundary.uniformSpaceEquiv S T)).toLinearMap.comp p.denote

/-- Uniform-output reindexing preserves complete positivity and trace preservation in arbitrary
explicit finite coordinates.

The statement specializes `Program.coordinateDenote_isCPTP`; it adds no physical hypothesis and
only replaces the native dependent-sum output coordinates by `S.total × Transcript T`.
-/
theorem coordinateUniformDenote_isCPTP {R S : MultipartiteSystem P} {T : TList}
    (p : Program R (Boundary.uniform S T))
    {dR dOut : ℕ} [NeZero dR] [NeZero dOut]
    (eR : R.total ≃ Fin dR) (eOut : (S.total × Transcript T) ≃ Fin dOut) :
    Quantum.Channels.IsCPTP ⇑(coordinateLinear eR eOut p.uniformDenote) := by
  simpa only [uniformDenote, coordinateLinear, LinearMap.comp_assoc,
    Matrix.reindexLinearEquiv_trans] using
    p.coordinateDenote_isCPTP eR ((Boundary.uniformSpaceEquiv S T).trans eOut)

end Program
end TypedLOCC
