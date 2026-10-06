import QCryptLean.LOCC.Typed.Program.ExitWeight
import QCryptLean.QKD.Protocol
import QCryptLean.QKD.OutputLayout.Graft

/-!
# Acceptance and abort probabilities of typed QKD protocols

Every complete public exit of a QKD protocol is either accepting or aborting
(`BoundaryKeyLayout.Disposition`).  The **acceptance probability** of a protocol on an input state
is the probability that its real run ends at an accepting exit, and the **abort probability** is
the probability that it ends at an aborting one; they add up to the trace of the input
(`QKD.Protocol.acceptProbability_add_abortProbability`).

The abort probability on the honest noisy channel is what Portmann--Renner call the *robustness*
of the protocol: "For every `q`, the protocol has a probability of aborting, `δ`, which is called
the robustness" (arXiv:2102.00021, `qkd.tex:845`--`:850`,
`\label{sec:security.rob}`).  It is a statement about the real protocol alone.  It is not the
distance criterion `eq:robustness` between the noisy real system and a probabilistic ideal key
resource, and it says nothing about which key an accepting run holds.

The graft and transport laws below compute these probabilities for protocols assembled from
exit-dependent continuations, as the measure-first BB84 experiment is.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace BoundaryKeyLayout

variable {B : Boundary P} (L : BoundaryKeyLayout B)

/-- The diagonal mass of an output operator on the accepting complete exits. -/
def acceptWeight (M : Op B.space) : ℝ :=
  B.exitWeight (fun e => L.disposition e ≠ .abort) M

/-- The diagonal mass of an output operator on the aborting complete exits. -/
def abortWeight (M : Op B.space) : ℝ :=
  B.exitWeight (fun e => L.disposition e = .abort) M

/-- **Accepting and aborting exits partition the output trace.** -/
theorem acceptWeight_add_abortWeight (M : Op B.space) :
    L.acceptWeight M + L.abortWeight M = (Matrix.trace M).re := by
  rw [add_comm, acceptWeight, abortWeight]
  exact B.exitWeight_add_exitWeight_not _ M

/-- A positive semidefinite output has nonnegative acceptance weight. -/
theorem acceptWeight_nonneg {M : Op B.space} (hM : M.PosSemidef) : 0 ≤ L.acceptWeight M :=
  B.exitWeight_nonneg _ hM

/-- A positive semidefinite output has nonnegative abort weight. -/
theorem abortWeight_nonneg {M : Op B.space} (hM : M.PosSemidef) : 0 ≤ L.abortWeight M :=
  B.exitWeight_nonneg _ hM

/-- A layout that aborts at every exit has zero acceptance weight. -/
theorem acceptWeight_eq_zero_of_forall_abort (h : ∀ e, L.disposition e = .abort)
    (M : Op B.space) : L.acceptWeight M = 0 := by
  rw [acceptWeight, B.exitWeight_congr (E' := fun _ => False) (fun e => by simp [h e]) M,
    B.exitWeight_false M]

end BoundaryKeyLayout

end TypedLOCC

namespace QKD

open TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Protocol

variable (A : Protocol P)

/-- **The acceptance probability of a protocol on an input state**: the diagonal mass of its real
output on the accepting complete public exits. -/
def acceptProbability (ρ : Op A.start.total) : ℝ :=
  A.layout.toBoundaryKeyLayout.acceptWeight (A.real ρ)

/-- **The abort probability of a protocol on an input state**: the diagonal mass of its real output
on the aborting complete public exits.  On the honest noisy channel this is the robustness of
Portmann--Renner, arXiv:2102.00021, `qkd.tex:845`--`:850`. -/
def abortProbability (ρ : Op A.start.total) : ℝ :=
  A.layout.toBoundaryKeyLayout.abortWeight (A.real ρ)

/-- **Every run either accepts or aborts.**  The two probabilities add up to the trace of the input;
for a state they add up to one. -/
theorem acceptProbability_add_abortProbability (ρ : Op A.start.total) :
    A.acceptProbability ρ + A.abortProbability ρ = (Matrix.trace ρ).re := by
  rw [acceptProbability, abortProbability, BoundaryKeyLayout.acceptWeight_add_abortWeight, real,
    Program.trace_denote]

/-- On a unit-trace input the abort probability is one minus the acceptance probability. -/
theorem abortProbability_eq_one_sub (ρ : Op A.start.total) (hρ : Matrix.trace ρ = 1) :
    A.abortProbability ρ = 1 - A.acceptProbability ρ := by
  have h := A.acceptProbability_add_abortProbability ρ
  rw [hρ, Complex.one_re] at h
  linarith

/-- The acceptance probability of a positive semidefinite input is nonnegative. -/
theorem acceptProbability_nonneg {ρ : Op A.start.total} (hρ : ρ.PosSemidef) :
    0 ≤ A.acceptProbability ρ :=
  BoundaryKeyLayout.acceptWeight_nonneg _ (A.program.denote_posSemidef hρ)

/-- The abort probability of a positive semidefinite input is nonnegative. -/
theorem abortProbability_nonneg {ρ : Op A.start.total} (hρ : ρ.PosSemidef) :
    0 ≤ A.abortProbability ρ :=
  BoundaryKeyLayout.abortWeight_nonneg _ (A.program.denote_posSemidef hρ)

end Protocol

namespace OutputLayout

/-- **Acceptance through a graft.**  For a grafted program with the grafted layout of its
continuations, the acceptance weight is the sum over the base exits of each continuation's
acceptance weight on the block extracted at that exit. -/
theorem acceptWeight_graftFixedParties_denote {R : MultipartiteSystem P} {B : Boundary P} (p :
    Program R B)
    {C : B.Exit → Boundary P} (k : ∀ e : B.Exit, Program (B.system e) (C e))
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b) (ρ : Op R.total) :
    (graftFixedParties a b hab L hA hB).toBoundaryKeyLayout.acceptWeight ((p.graft k).denote ρ) =
      ∑ e, (L e).toBoundaryKeyLayout.acceptWeight
        ((k e).denote (BoundaryKeyLayout.leafBlock e (p.denote ρ))) := by
  rw [BoundaryKeyLayout.acceptWeight, Program.exitWeight_graft_denote]
  refine Finset.sum_congr rfl fun e _ => Boundary.exitWeight_congr _ (fun c => ?_) _
  rw [toBoundaryKeyLayout_disposition, graftFixedParties_disposition,
    toBoundaryKeyLayout_disposition]

/-- **Abort through a graft**, the companion of `acceptWeight_graftFixedParties_denote`. -/
theorem abortWeight_graftFixedParties_denote {R : MultipartiteSystem P} {B : Boundary P} (p :
    Program R B)
    {C : B.Exit → Boundary P} (k : ∀ e : B.Exit, Program (B.system e) (C e))
    (L : ∀ e, QKD.OutputLayout (C e)) (a b : P) (hab : a ≠ b)
    (hA : ∀ e, (L e).alice = a) (hB : ∀ e, (L e).bob = b) (ρ : Op R.total) :
    (graftFixedParties a b hab L hA hB).toBoundaryKeyLayout.abortWeight ((p.graft k).denote ρ) =
      ∑ e, (L e).toBoundaryKeyLayout.abortWeight
        ((k e).denote (BoundaryKeyLayout.leafBlock e (p.denote ρ))) := by
  rw [BoundaryKeyLayout.abortWeight, Program.exitWeight_graft_denote]
  refine Finset.sum_congr rfl fun e _ => Boundary.exitWeight_congr _ (fun c => ?_) _
  rw [toBoundaryKeyLayout_disposition, graftFixedParties_disposition,
    toBoundaryKeyLayout_disposition]

/-- Transporting a layout along a boundary equality and the output along the matching coordinate
cast leaves the acceptance weight unchanged. -/
theorem acceptWeight_transport {B B' : Boundary P} (h : B = B') (L : QKD.OutputLayout B)
    (M : Op B.space) :
    (transport h L).toBoundaryKeyLayout.acceptWeight
        (reindexOp (Equiv.cast (congrArg Boundary.space h)) M) =
      L.toBoundaryKeyLayout.acceptWeight M := by
  subst h
  rfl

/-- A layout transported along a boundary equality keeps a disposition shared by all its exits. -/
theorem transport_disposition_of_forall {B B' : Boundary P} (h : B = B') (L : QKD.OutputLayout B)
    {d : BoundaryKeyLayout.Disposition} (hL : ∀ f, L.disposition f = d) (e : B'.Exit) :
    (transport h L).disposition e = d := by
  subst h
  exact hL e

/-- **Acceptance of a transported program.**  Transporting a program along equalities of its input
multipartite system and output boundary, and its layout along the same boundary equality, leaves its
acceptance weight unchanged once the input is transported along the multipartite system equality. -/
theorem acceptWeight_transport_denote_cast {R R' : MultipartiteSystem P} {B B' : Boundary P} (hR : R
    = R')
    (hB : B' = B) (p : Program R' B') (L : QKD.OutputLayout B') (ρ : Op R.total) :
    (transport hB L).toBoundaryKeyLayout.acceptWeight
        ((cast (by subst hR hB; rfl) p : Program R B).denote ρ) =
      L.toBoundaryKeyLayout.acceptWeight
        (p.denote (reindexOp (Equiv.cast (congrArg MultipartiteSystem.total hR)) ρ)) := by
  subst hR hB
  rfl

/-- Transporting a layout along a boundary equality and the output along the matching coordinate
cast leaves the abort weight unchanged. -/
theorem abortWeight_transport {B B' : Boundary P} (h : B = B') (L : QKD.OutputLayout B)
    (M : Op B.space) :
    (transport h L).toBoundaryKeyLayout.abortWeight
        (reindexOp (Equiv.cast (congrArg Boundary.space h)) M) =
      L.toBoundaryKeyLayout.abortWeight M := by
  subst h
  rfl

/-- **Abort of a transported program**, the companion of `acceptWeight_transport_denote_cast`. -/
theorem abortWeight_transport_denote_cast {R R' : MultipartiteSystem P} {B B' : Boundary P} (hR : R
    = R')
    (hB : B' = B) (p : Program R' B') (L : QKD.OutputLayout B') (ρ : Op R.total) :
    (transport hB L).toBoundaryKeyLayout.abortWeight
        ((cast (by subst hR hB; rfl) p : Program R B).denote ρ) =
      L.toBoundaryKeyLayout.abortWeight
        (p.denote (reindexOp (Equiv.cast (congrArg MultipartiteSystem.total hR)) ρ)) := by
  subst hR hB
  rfl

end OutputLayout

end QKD
