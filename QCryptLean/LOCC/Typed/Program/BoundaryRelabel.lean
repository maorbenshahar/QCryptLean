import QCryptLean.LOCC.Typed.Program.BoundaryRelabel.Basic
import QCryptLean.LOCC.Typed.Program.BoundaryRelabel.Uniform
import QCryptLean.LOCC.Typed.Program.BoundaryRelabel.Graft
import QCryptLean.LOCC.Typed.Program.BoundaryRelabel.Graded

/-!
# Relabelling typed boundaries and program channels

This is the stable import entry point for the protocol-independent transport laws of typed output
boundaries and of the channels of typed programs.  Everything below it is structural: it speaks only
about `Boundary.graft`, `Boundary.announce`, `Boundary.uniform`, `Program.graft`,
`Program.controlledContinuation` and register relabellings `reindexOp`.  No protocol, key layout,
security notion or norm estimate occurs anywhere in the family, and no module below imports BB84 or
any finite-key analysis.

All declarations live in the namespace TypedLOCC.BoundaryRelabel and are distributed over four
children, in this dependency order:

* Basic — the `reindexOp` calculus, multipartite system transports, the exit block
  `blockAt`/`exitBlock`, and denotations of programs transported along multipartite system or
  boundary equalities.
* Uniform — uniform boundaries: concatenation as grafting, the exit and multipartite system
  dictionaries, and the channel of a program viewed at a complete public exit.
* Graft — iterated grafting and its reassociation (`graftAssoc*`, `cc_comp_cc`,
  `denote_graft_graft_cast`), and the grafted output relabelling `graftSpaceRelabel` with its
  congruence `denote_graft_congr_relabel`.
* `BoundaryRelabel.Graded` — announced and private node congruences (`announceSpaceRelabel`,
  `denote_announced_congr_cont_relabel`, `denote_priv_congr_graded`), exit-graded relabellings
  `Graded` with their graft and announce congruences, and the cast-free double graft
  `graftAssocSpaceEquiv`/`denote_graft_graft`.

The two central notions are

* the *exit block* `blockAt` of a complete public exit, which is what an exit-controlled
  continuation consumes, and
* an *exit-graded* relabelling `Graded` of two boundary output spaces: a bijection of complete
  public exits together with, at each exit, a bijection of the selected joint registers.  These are
  exactly the relabellings that commute with exit-controlled continuations.
-/
