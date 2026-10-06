import QCryptLean.LOCC.Typed.LocalAction

/-!
# Branch-dependent typed LOCC programs

This module is the primary recursive syntax for finite typed LOCC programs.  Public announcements
select both the next multipartite system and the continuation boundary; private outcomes are
contained inside a local action and never become continuation indices.
-/

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- A finite typed LOCC program from an input multipartite system to a branch-dependent output
boundary.

At an announced node, the action computes its successor system from its output register, and only
the public coarse outcome indexes the continuation. Consequently
the acting party, local dimensions, and remaining tree may all depend on the public measurement
history, as in the finite-round instrument trees of Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section II.  A private node performs a fixed-output local instrument and has one
continuation, so its physical outcome is not leaked into public control flow.
-/
inductive Program : MultipartiteSystem P → Boundary P → Type 1
  /-- Terminate at the current multipartite system. -/
  | done {R : MultipartiteSystem P} : Program R (.leaf R)
  /-- Perform an announced action and continue using only its public value. -/
  | announced {R : MultipartiteSystem P} {Y : Type} [Fintype Y] [DecidableEq Y]
      (A : AnnouncedAction R Y) {B : Y → Boundary P}
      (k : ∀ y, Program (A.out y) (B y)) : Program R (.announce Y B)
  /-- Perform a private action and continue without exposing its outcome. -/
  | priv {R : MultipartiteSystem P} {B : Boundary P} (A : PrivateAction R)
      (k : Program A.out B) : Program R B

namespace Program

/-- Substitute a continuation program at every complete public exit.

The result boundary is `Boundary.graft B C`.  The continuation starts at `B.system e`, so the type
enforces exact agreement between each completed branch and the program attached there.
-/
def graft {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
    {C : B.Exit → Boundary P} (k : ∀ e : B.Exit, Program (B.system e) (C e)) :
    Program R (B.graft C) :=
  match p, C, k with
  | @Program.done _ _ _ _, _, k => k ()
  | @Program.announced _ _ _ _ _ _ _ A _ next, C, k =>
      .announced A fun y =>
        graft (next y) (C := fun e => C ⟨y, e⟩) fun e => k ⟨y, e⟩
  | @Program.priv _ _ _ _ _ A next, _, k =>
      .priv A (graft next k)

/-- Transporting the input system commutes with grafting exit continuations. -/
@[simp] theorem graft_castInput {R S : MultipartiteSystem P} (h : R = S)
    {B : Boundary P} (p : Program R B) {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) :
    (cast (congrArg (fun R => Program R B) h) p).graft k =
      cast (congrArg (fun R => Program R (B.graft C)) h) (p.graft k) := by
  cases h
  rfl

/-- Grafting after termination runs the continuation at the unique exit. -/
@[simp] theorem graft_done {R : MultipartiteSystem P}
    {C : (Boundary.leaf R).Exit → Boundary P}
    (k : ∀ e : (Boundary.leaf R).Exit,
      Program ((Boundary.leaf R).system e) (C e)) :
    graft (.done : Program R (.leaf R)) k = k () := rfl

/-- Grafting an announced node distributes the exit continuation over its public branches. -/
@[simp] theorem graft_announced {R : MultipartiteSystem P} {Y : Type} [Fintype Y] [DecidableEq Y]
    (A : AnnouncedAction R Y)
    {B : Y → Boundary P} (next : ∀ y, Program (A.out y) (B y))
    {C : (Boundary.announce Y B).Exit → Boundary P}
    (k : ∀ e : (Boundary.announce Y B).Exit,
      Program ((Boundary.announce Y B).system e) (C e)) :
    graft (.announced A next) k =
      .announced A (fun y =>
        graft (next y) (C := fun e => C ⟨y, e⟩) fun e => k ⟨y, e⟩) := rfl

/-- Grafting a private node passes the same exit continuation through its sole branch. -/
@[simp] theorem graft_priv {R : MultipartiteSystem P} {B : Boundary P}
    (A : PrivateAction R) (next : Program A.out B)
    {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) :
    graft (.priv A next) k = .priv A (graft next k) := rfl

end Program

/-- Continue after an announced action, indexed only by the public value. -/
def AnnouncedAction.then {R : MultipartiteSystem P} {Y : Type} [Fintype Y] [DecidableEq Y]
    (A : AnnouncedAction R Y) {B : Y → Boundary P}
    (k : ∀ y, Program (A.out y) (B y)) : Program R (.announce Y B) :=
  .announced A k

/-- Run one announced action and terminate independently at every successor multipartite system. -/
def AnnouncedAction.run {R : MultipartiteSystem P} {Y : Type} [Fintype Y] [DecidableEq Y]
    (A : AnnouncedAction R Y) : Program R A.boundary :=
  A.then fun _ => .done

/-- Continue after a private action without exposing its physical outcome. -/
def PrivateAction.then {R : MultipartiteSystem P} (A : PrivateAction R) {B : Boundary P}
    (k : Program A.out B) : Program R B :=
  .priv A k

/-- Run one private action and terminate at its fixed successor multipartite system. -/
def PrivateAction.run {R : MultipartiteSystem P} (A : PrivateAction R) : Program R (.leaf A.out)
    :=
  A.then .done

end TypedLOCC
