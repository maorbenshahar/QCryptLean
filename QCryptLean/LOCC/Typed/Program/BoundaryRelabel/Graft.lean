import QCryptLean.LOCC.Typed.Program.BoundaryRelabel.Uniform

/-!
# Iterated grafting, its reassociation, and grafted output relabellings

Third layer of the BoundaryRelabel family.  Two independent themes:

* the `graftAssoc*` family, which reassociates an iterated graft `(B.graft C).graft D` into
  `B.graft (graftAssocBoundary B C D)`, together with the resulting channel identities
  `cc_comp_cc` and `denote_graft_graft_cast`;
* the *grafted output relabelling* `graftSpaceRelabel B C₁ C₂ theta`, which relabels only the
  attached continuation boundaries of one graft, its value dictionary, and the graft congruence
  `denote_graft_congr_relabel`.

Both are protocol-independent: they speak only about `Boundary.graft`, `Program.graft`,
`Program.controlledContinuation` and register relabellings `reindexOp`.
-/

open scoped Matrix BigOperators

noncomputable section

namespace TypedLOCC.BoundaryRelabel

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## Iterated grafting and its reassociation -/

/-- Continuation family of the reassociated graft. -/
def graftAssocCont {B : Boundary P} {C : B.Exit → Boundary P}
    {D : (B.graft C).Exit → Boundary P}
    (l : ∀ g : (B.graft C).Exit, Program ((B.graft C).system g) (D g))
    (e : B.Exit) (f : (C e).Exit) :
    Program ((C e).system f) (D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)) :=
  (Boundary.system_graftExitEquiv_symm B C ⟨e, f⟩) ▸ l ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)

/-- The reassociated continuation boundary. -/
def graftAssocBoundary (B : Boundary P) (C : B.Exit → Boundary P)
    (D : (B.graft C).Exit → Boundary P) (e : B.Exit) : Boundary P :=
  (C e).graft (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))

/-- The reassociated continuation family of programs. -/
def graftAssocProgram {B : Boundary P} {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e))
    {D : (B.graft C).Exit → Boundary P}
    (l : ∀ g : (B.graft C).Exit, Program ((B.graft C).system g) (D g))
    (e : B.Exit) : Program (B.system e) (graftAssocBoundary B C D e) :=
  (k e).graft (graftAssocCont l e)

/-- Reassociation bijection between the two iterated grafted output spaces. -/
def graftAssocSpace (B : Boundary P) (C : B.Exit → Boundary P)
    (D : (B.graft C).Exit → Boundary P) :
    (B.graft (graftAssocBoundary B C D)).space ≃ ((B.graft C).graft D).space :=
  (Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).trans
    (((Equiv.sigmaCongrRight fun e =>
        Boundary.graftSpaceEquiv (C e)
          (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))).trans
      ((Equiv.sigmaAssoc
          (fun (e : B.Exit) (f : (C e).Exit) =>
            (D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)).space)).symm.trans
        (Equiv.sigmaCongrLeft (β := fun g => (D g).space)
          (Boundary.graftExitEquiv B C).symm))).trans
      (Boundary.graftSpaceEquiv (B.graft C) D).symm)

/-- Action of the reassociation bijection on iterated graft coordinates. -/
theorem graftAssocSpace_apply (B : Boundary P) (C : B.Exit → Boundary P)
    (D : (B.graft C).Exit → Boundary P) (e : B.Exit)
    (z : (graftAssocBoundary B C D e).space) :
    graftAssocSpace B C D
        ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm ⟨e, z⟩) =
      (Boundary.graftSpaceEquiv (B.graft C) D).symm
        ⟨(Boundary.graftExitEquiv B C).symm
            ⟨e, (Boundary.graftSpaceEquiv (C e)
              (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)) z).1⟩,
          (Boundary.graftSpaceEquiv (C e)
            (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)) z).2⟩ := by
  simp only [graftAssocSpace, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- A grafted-boundary point written in graft coordinates. -/
theorem graft_point_eq {B : Boundary P} (C : B.Exit → Boundary P)
    (g : (B.graft C).Exit) (q : ((B.graft C).system g).total) :
    (⟨g, q⟩ : (B.graft C).space) =
      (Boundary.graftSpaceEquiv B C).symm
        ⟨(Boundary.graftExitEquiv B C g).1,
          ⟨(Boundary.graftExitEquiv B C g).2,
            Equiv.cast (congrArg (fun R : MultipartiteSystem P => R.total)
              (Boundary.system_graftExitEquiv B C g)) q⟩⟩ := by
  have h := (Boundary.graftSpaceEquiv B C).symm_apply_apply (⟨g, q⟩ : (B.graft C).space)
  rw [Boundary.graftSpaceEquiv_apply] at h
  exact h.symm

/-- Exit blocks of a controlled continuation are the child denotations of the base blocks. -/
theorem blockAt_cc {B : Boundary P} {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) (M : TypedLOCC.Op B.space)
    (g : (B.graft C).Exit) (q q' : ((B.graft C).system g).total) :
    blockAt (B.graft C) g (Program.controlledContinuation k M) q q' =
      (k (Boundary.graftExitEquiv B C g).1).denote
          (blockAt B (Boundary.graftExitEquiv B C g).1 M)
        ⟨(Boundary.graftExitEquiv B C g).2,
          Equiv.cast (congrArg (fun R : MultipartiteSystem P => R.total)
            (Boundary.system_graftExitEquiv B C g)) q⟩
        ⟨(Boundary.graftExitEquiv B C g).2,
          Equiv.cast (congrArg (fun R : MultipartiteSystem P => R.total)
            (Boundary.system_graftExitEquiv B C g)) q'⟩ := by
  change Program.controlledContinuation k M ⟨g, q⟩ ⟨g, q'⟩ = _
  rw [graft_point_eq C g q, graft_point_eq C g q', cc_sameExit]

/-- Action of the reassociation bijection on fully decomposed graft coordinates. -/
theorem graftAssocSpace_apply' (B : Boundary P) (C : B.Exit → Boundary P)
    (D : (B.graft C).Exit → Boundary P) (e : B.Exit) (f : (C e).Exit)
    (xx : (D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)).space) :
    graftAssocSpace B C D
        ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm
          ⟨e, (Boundary.graftSpaceEquiv (C e)
            (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))).symm ⟨f, xx⟩⟩) =
      (Boundary.graftSpaceEquiv (B.graft C) D).symm
        ⟨(Boundary.graftExitEquiv B C).symm ⟨e, f⟩, xx⟩ := by
  rw [graftAssocSpace_apply, Equiv.apply_symm_apply]

/-- Exit blocks of a controlled continuation at a decomposed graft exit. -/
theorem blockAt_cc' {B : Boundary P} {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) (M : TypedLOCC.Op B.space)
    (e : B.Exit) (f : (C e).Exit)
    (q q' : ((B.graft C).system ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)).total) :
    blockAt (B.graft C) ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)
        (Program.controlledContinuation k M) q q' =
      (k e).denote (blockAt B e M)
        ⟨f, Boundary.graftSystemCast B C e f q⟩ ⟨f, Boundary.graftSystemCast B C e f q'⟩ := by
  have key : ∀ w : ((B.graft C).system ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)).total,
      (Boundary.graftSpaceEquiv B C).symm ⟨e, ⟨f, Boundary.graftSystemCast B C e f w⟩⟩ =
        ⟨(Boundary.graftExitEquiv B C).symm ⟨e, f⟩, w⟩ := by
    intro w
    rw [Boundary.graftSpaceEquiv_symm_pair]
    exact congrArg (Sigma.mk ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))
      (Equiv.symm_apply_apply _ w)
  change Program.controlledContinuation k M
      ⟨(Boundary.graftExitEquiv B C).symm ⟨e, f⟩, q⟩
      ⟨(Boundary.graftExitEquiv B C).symm ⟨e, f⟩, q'⟩ = _
  rw [← key q, ← key q', cc_sameExit]

/-- Matrix form of `blockAt_cc'`. -/
theorem blockAt_cc'' {B : Boundary P} {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) (M : TypedLOCC.Op B.space)
    (e : B.Exit) (f : (C e).Exit) :
    blockAt (B.graft C) ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)
        (Program.controlledContinuation k M) =
      (blockAt (C e) f ((k e).denote (blockAt B e M))).submatrix
        (Boundary.graftSystemCast B C e f) (Boundary.graftSystemCast B C e f) := by
  ext q q'
  exact blockAt_cc' k M e f q q'

/-- **Associativity of iterated continuation grafting.** -/
theorem cc_comp_cc {B : Boundary P} {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e))
    {D : (B.graft C).Exit → Boundary P}
    (l : ∀ g : (B.graft C).Exit, Program ((B.graft C).system g) (D g))
    (M : TypedLOCC.Op B.space) :
    Program.controlledContinuation l (Program.controlledContinuation k M) =
      reindexOp (graftAssocSpace B C D)
        (Program.controlledContinuation (graftAssocProgram k l) M) := by
  classical
  ext x y
  obtain ⟨wx, rfl⟩ : ∃ w : Σ e : B.Exit, (graftAssocBoundary B C D e).space,
      graftAssocSpace B C D
        ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm w) = x :=
    ⟨Boundary.graftSpaceEquiv B _ ((graftAssocSpace B C D).symm x), by
      rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]⟩
  obtain ⟨wy, rfl⟩ : ∃ w : Σ e : B.Exit, (graftAssocBoundary B C D e).space,
      graftAssocSpace B C D
        ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm w) = y :=
    ⟨Boundary.graftSpaceEquiv B _ ((graftAssocSpace B C D).symm y), by
      rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]⟩
  obtain ⟨e, z⟩ := wx
  obtain ⟨e', z'⟩ := wy
  obtain ⟨v, rfl⟩ : ∃ v, (Boundary.graftSpaceEquiv (C e)
      (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))).symm v = z :=
    ⟨_, Equiv.symm_apply_apply _ _⟩
  obtain ⟨v', rfl⟩ : ∃ v, (Boundary.graftSpaceEquiv (C e')
      (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e', f⟩))).symm v = z' :=
    ⟨_, Equiv.symm_apply_apply _ _⟩
  obtain ⟨f, xx⟩ := v
  obtain ⟨f', yy⟩ := v'
  rw [show (reindexOp (graftAssocSpace B C D)
        (Program.controlledContinuation (graftAssocProgram k l) M))
      (graftAssocSpace B C D ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm
        ⟨e, (Boundary.graftSpaceEquiv (C e) _).symm ⟨f, xx⟩⟩))
      (graftAssocSpace B C D ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm
        ⟨e', (Boundary.graftSpaceEquiv (C e') _).symm ⟨f', yy⟩⟩)) =
      Program.controlledContinuation (graftAssocProgram k l) M
        ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm
          ⟨e, (Boundary.graftSpaceEquiv (C e) _).symm ⟨f, xx⟩⟩)
        ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm
          ⟨e', (Boundary.graftSpaceEquiv (C e') _).symm ⟨f', yy⟩⟩) from by
    simp [reindexOp]]
  rw [graftAssocSpace_apply', graftAssocSpace_apply']
  by_cases hee : e = e'
  · subst hee
    rw [cc_sameExit,
      show (graftAssocProgram k l e).denote (blockAt B e M) =
          Program.controlledContinuation (graftAssocCont l e)
            ((k e).denote (blockAt B e M)) from by
        rw [graftAssocProgram, Program.denote_graft]; rfl]
    by_cases hff : f = f'
    · subst hff
      rw [cc_sameExit, Program.controlledContinuation_sameExit,
        exitKraus_sandwich_eq_blockAt, blockAt_cc'']
      simp only [graftAssocCont]
      rw [denote_systemCast]
    · have hne : (Boundary.graftExitEquiv B C).symm ⟨e, f⟩ ≠
          (Boundary.graftExitEquiv B C).symm ⟨e, f'⟩ := by
        intro hcon
        exact hff (eq_of_heq (Sigma.mk.inj_iff.mp
          ((Boundary.graftExitEquiv B C).symm.injective hcon)).2)
      rw [Program.controlledContinuation_block_zero _ _ hne,
        Program.controlledContinuation_block_zero _ _ hff]
  · have hne : (Boundary.graftExitEquiv B C).symm ⟨e, f⟩ ≠
        (Boundary.graftExitEquiv B C).symm ⟨e', f'⟩ := by
      intro hcon
      exact hee (congrArg Sigma.fst ((Boundary.graftExitEquiv B C).symm.injective hcon))
    rw [Program.controlledContinuation_block_zero _ _ hne,
      Program.controlledContinuation_block_zero _ _ hee]

/-- Continuation family of the reassociated graft, transported along a boundary equality. -/
def graftAssocProgramCast {B : Boundary P} {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e))
    {Bz : Boundary P} (hY : B.graft C = Bz) {D : Bz.Exit → Boundary P}
    (l : ∀ g : Bz.Exit, Program (Bz.system g) (D g)) (e : B.Exit) :
    Program (B.system e)
      (graftAssocBoundary B C (fun g => D (Equiv.cast (congrArg Boundary.Exit hY) g)) e) := by
  subst hY
  exact graftAssocProgram k l e

/-- Continuation of the reassociated graft, transported along a boundary equality. -/
def graftAssocContCast {B : Boundary P} {C : B.Exit → Boundary P}
    {Bz : Boundary P} (hY : B.graft C = Bz) {D : Bz.Exit → Boundary P}
    (l : ∀ g : Bz.Exit, Program (Bz.system g) (D g)) (e : B.Exit) (f : (C e).Exit) :
    Program ((C e).system f) (D (Equiv.cast (congrArg Boundary.Exit hY)
      ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))) := by
  subst hY
  exact graftAssocCont l e f

/-- The transported reassociated continuation is the original one. -/
theorem graftAssocContCast_heq {B : Boundary P} {C : B.Exit → Boundary P}
    {Bz : Boundary P} (hY : B.graft C = Bz) {D : Bz.Exit → Boundary P}
    (l : ∀ g : Bz.Exit, Program (Bz.system g) (D g)) (e : B.Exit) (f : (C e).Exit) :
    graftAssocContCast hY l e f ≍
      l (Equiv.cast (congrArg Boundary.Exit hY)
        ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)) := by
  subst hY
  exact systemTransport_heq _ _

/-- Reassociation bijection, transported along a boundary equality. -/
def graftAssocSpaceCast (B : Boundary P) (C : B.Exit → Boundary P)
    {Bz : Boundary P} (hY : B.graft C = Bz) (D : Bz.Exit → Boundary P) :
    (B.graft (graftAssocBoundary B C
        (fun g => D (Equiv.cast (congrArg Boundary.Exit hY) g)))).space ≃ (Bz.graft D).space := by
  subst hY
  exact graftAssocSpace B C D

/-- Action of the transported reassociation bijection on fully decomposed graft coordinates. -/
theorem graftAssocSpaceCast_apply (B : Boundary P) (C : B.Exit → Boundary P)
    {Bz : Boundary P} (hY : B.graft C = Bz) (D : Bz.Exit → Boundary P)
    (e : B.Exit) (f : (C e).Exit)
    (xx : (D (Equiv.cast (congrArg Boundary.Exit hY)
      ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))).space) :
    graftAssocSpaceCast B C hY D
        ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C
            (fun g => D (Equiv.cast (congrArg Boundary.Exit hY) g)))).symm
          ⟨e, (Boundary.graftSpaceEquiv (C e)
            (fun f => D (Equiv.cast (congrArg Boundary.Exit hY)
              ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)))).symm ⟨f, xx⟩⟩) =
      (Boundary.graftSpaceEquiv Bz D).symm
        ⟨Equiv.cast (congrArg Boundary.Exit hY)
          ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩), xx⟩ := by
  subst hY
  exact graftAssocSpace_apply' B C D e f xx

/-- Reduction of the transported reassociated continuation family. -/
theorem graftAssocProgramCast_eq {B : Boundary P} {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e))
    {Bz : Boundary P} (hY : B.graft C = Bz) {D : Bz.Exit → Boundary P}
    (l : ∀ g : Bz.Exit, Program (Bz.system g) (D g)) (e : B.Exit) :
    graftAssocProgramCast k hY l e = (k e).graft (graftAssocContCast hY l e) := by
  subst hY
  rfl

/-- **Iterated grafting through a boundary identification.** -/
theorem denote_graft_graft_cast {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
    {C : B.Exit → Boundary P} (k : ∀ e : B.Exit, Program (B.system e) (C e))
    {Bz : Boundary P} (hY : B.graft C = Bz) (q : Program R Bz)
    (hq : ∀ rho : TypedLOCC.Op R.total, q.denote rho =
      reindexOp (Equiv.cast (congrArg Boundary.space hY)) ((p.graft k).denote rho))
    {D : Bz.Exit → Boundary P} (l : ∀ g : Bz.Exit, Program (Bz.system g) (D g))
    (rho : TypedLOCC.Op R.total) :
    (q.graft l).denote rho =
      reindexOp (graftAssocSpaceCast B C hY D)
        ((p.graft (graftAssocProgramCast k hY l)).denote rho) := by
  subst hY
  simp only [reindexOp_cast_rfl] at hq
  rw [Program.denote_graft]
  change Program.controlledContinuation l (q.denote rho) = _
  rw [hq rho, Program.denote_graft]
  change Program.controlledContinuation l
      (Program.controlledContinuation k (p.denote rho)) = _
  rw [cc_comp_cc, Program.denote_graft]
  rfl

/-- A fibrewise injective map of dependent sums is injective. -/
theorem sigma_fibre_map_inj {α : Type} {F G : α → Type}
    (ex : ∀ a, F a → G a) (hex : ∀ a, Function.Injective (ex a))
    (z z' : Σ a, F a)
    (h : (⟨z.1, ex z.1 z.2⟩ : Σ a, G a) = ⟨z'.1, ex z'.1 z'.2⟩) : z = z' := by
  obtain ⟨e₁, f₁⟩ := z
  obtain ⟨e₂, f₂⟩ := z'
  obtain ⟨he, hf⟩ := Sigma.mk.inj_iff.mp h
  subst he
  exact congrArg (Sigma.mk e₁) (hex e₁ (eq_of_heq hf))

/-- Reassociation bijection of the complete public exits of an iterated graft. -/
def graftAssocExitEquiv (B : Boundary P) (C : B.Exit → Boundary P)
    (D : (B.graft C).Exit → Boundary P) :
    (B.graft (graftAssocBoundary B C D)).Exit ≃ ((B.graft C).graft D).Exit :=
  (Boundary.graftExitEquiv B (graftAssocBoundary B C D)).trans
    (((Equiv.sigmaCongrRight fun e =>
        Boundary.graftExitEquiv (C e)
          (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))).trans
      ((Equiv.sigmaAssoc
          (fun (e : B.Exit) (f : (C e).Exit) =>
            (D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)).Exit)).symm.trans
        (Equiv.sigmaCongrLeft (β := fun g => (D g).Exit)
          (Boundary.graftExitEquiv B C).symm))).trans
      (Boundary.graftExitEquiv (B.graft C) D).symm)

/-- Action of the exit reassociation on decomposed iterated graft exits. -/
theorem graftAssocExitEquiv_apply (B : Boundary P) (C : B.Exit → Boundary P)
    (D : (B.graft C).Exit → Boundary P) (e : B.Exit)
    (y : (graftAssocBoundary B C D e).Exit) :
    graftAssocExitEquiv B C D
        ((Boundary.graftExitEquiv B (graftAssocBoundary B C D)).symm ⟨e, y⟩) =
      (Boundary.graftExitEquiv (B.graft C) D).symm
        ⟨(Boundary.graftExitEquiv B C).symm
            ⟨e, (Boundary.graftExitEquiv (C e)
              (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)) y).1⟩,
          (Boundary.graftExitEquiv (C e)
            (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩)) y).2⟩ := by
  simp only [graftAssocExitEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-! ## Exit-controlled continuations -/

/-- Two exit-controlled continuation families with the same per-exit denotation induce the same
channel. -/
theorem controlledContinuation_congr {B : Boundary P} {C : B.Exit → Boundary P}
    (k k' : ∀ e : B.Exit, Program (B.system e) (C e))
    (h : ∀ e, (k e).denote = (k' e).denote) :
    Program.controlledContinuation k = Program.controlledContinuation k' := by
  classical
  apply LinearMap.ext
  intro rho
  ext x y
  obtain ⟨⟨e, a⟩, rfl⟩ : ∃ z, (Boundary.graftSpaceEquiv B C).symm z = x :=
    ⟨Boundary.graftSpaceEquiv B C x, Equiv.symm_apply_apply _ _⟩
  obtain ⟨⟨f, c⟩, rfl⟩ : ∃ z, (Boundary.graftSpaceEquiv B C).symm z = y :=
    ⟨Boundary.graftSpaceEquiv B C y, Equiv.symm_apply_apply _ _⟩
  by_cases hef : e = f
  · subst hef
    rw [Program.controlledContinuation_sameExit, Program.controlledContinuation_sameExit, h e]
  · rw [Program.controlledContinuation_block_zero _ _ hef,
      Program.controlledContinuation_block_zero _ _ hef]

/-! ## Relabelling the attached continuations of one graft

`graftSpaceRelabel` keeps the base boundary and its complete public exits fixed and relabels only
the attached continuation output spaces.  It is the special case of an output relabelling which a
stagewise program comparison produces when only the attached stage is re-presented. -/

/-- Relabel the attached output spaces of a grafted boundary. -/
def graftSpaceRelabel (B : Boundary P) (C₁ C₂ : B.Exit → Boundary P)
    (theta : ∀ e, (C₁ e).space ≃ (C₂ e).space) :
    (B.graft C₁).space ≃ (B.graft C₂).space :=
  (Boundary.graftSpaceEquiv B C₁).trans
    ((Equiv.sigmaCongrRight theta).trans (Boundary.graftSpaceEquiv B C₂).symm)

/-- Forward value of the grafted output relabelling. -/
theorem graftSpaceRelabel_apply (B : Boundary P) (C₁ C₂ : B.Exit → Boundary P)
    (theta : ∀ e, (C₁ e).space ≃ (C₂ e).space) (x : (B.graft C₁).space) :
    graftSpaceRelabel B C₁ C₂ theta x =
      (Boundary.graftSpaceEquiv B C₂).symm
        ⟨(Boundary.graftExitEquiv B C₁ x.1).1,
          theta _ ⟨(Boundary.graftExitEquiv B C₁ x.1).2,
            Equiv.cast (congrArg (fun R : MultipartiteSystem P => R.total)
              (Boundary.system_graftExitEquiv B C₁ x.1)) x.2⟩⟩ := by
  change (Boundary.graftSpaceEquiv B C₂).symm
    (Equiv.sigmaCongrRight theta (Boundary.graftSpaceEquiv B C₁ x)) = _
  rw [Boundary.graftSpaceEquiv_apply]
  rfl

/-- A grafted relabelling only changes the attached payload: its value at a point named in
graft coordinates. -/
theorem graftSpaceRelabel_graftPoint (B : Boundary P) (C₁ C₂ : B.Exit → Boundary P)
    (theta : ∀ e, (C₁ e).space ≃ (C₂ e).space) (e : B.Exit) (z : (C₁ e).space) :
    graftSpaceRelabel B C₁ C₂ theta ((Boundary.graftSpaceEquiv B C₁).symm ⟨e, z⟩) =
      (Boundary.graftSpaceEquiv B C₂).symm ⟨e, theta e z⟩ := by
  simp only [graftSpaceRelabel, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.sigmaCongrRight_apply]

/-- Reindexing along the identity relabelling of a grafted boundary. -/
theorem graftSpaceRelabel_refl (B : Boundary P) (C : B.Exit → Boundary P) :
    graftSpaceRelabel B C C (fun _ => Equiv.refl _) = Equiv.refl _ := by
  refine Equiv.ext fun x => ?_
  exact (Boundary.graftSpaceEquiv B C).symm_apply_apply x

/-- Reassociation applied to a relabelled attached continuation. -/
theorem graftAssocSpaceCast_relabel_apply (B : Boundary P) (C : B.Exit → Boundary P)
    {Bz : Boundary P} (hY : B.graft C = Bz) (D : Bz.Exit → Boundary P)
    (e : B.Exit) (C₁ : (C e).Exit → Boundary P)
    (theta : ∀ f, (C₁ f).space ≃ (D (Equiv.cast (congrArg Boundary.Exit hY)
        ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))).space)
    (f : (C e).Exit) (y : (C₁ f).space) :
    graftAssocSpaceCast B C hY D
        ((Boundary.graftSpaceEquiv B (graftAssocBoundary B C
            (fun g => D (Equiv.cast (congrArg Boundary.Exit hY) g)))).symm
          ⟨e, graftSpaceRelabel (C e) C₁
              (fun f => D (Equiv.cast (congrArg Boundary.Exit hY)
                ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩))) theta
              ((Boundary.graftSpaceEquiv (C e) C₁).symm ⟨f, y⟩)⟩) =
      (Boundary.graftSpaceEquiv Bz D).symm
        ⟨Equiv.cast (congrArg Boundary.Exit hY)
          ((Boundary.graftExitEquiv B C).symm ⟨e, f⟩), theta f y⟩ := by
  rw [graftSpaceRelabel_graftPoint, graftAssocSpaceCast_apply]

/-- **Transport an output relabelling of grafted continuations through the graft.**  The base
program is arbitrary; only the attached continuations are compared, and the equality holds for
every complex input operator. -/
theorem denote_graft_congr_relabel {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
    {C₁ C₂ : B.Exit → Boundary P}
    (k₁ : ∀ e, Program (B.system e) (C₁ e)) (k₂ : ∀ e, Program (B.system e) (C₂ e))
    (theta : ∀ e, (C₁ e).space ≃ (C₂ e).space)
    (h : ∀ e sigma, (k₂ e).denote sigma = reindexOp (theta e) ((k₁ e).denote sigma))
    (rho : TypedLOCC.Op R.total) :
    (p.graft k₂).denote rho =
      reindexOp (graftSpaceRelabel B C₁ C₂ theta) ((p.graft k₁).denote rho) := by
  classical
  rw [Program.denote_graft, Program.denote_graft]
  ext x y
  obtain ⟨⟨e, a⟩, hx⟩ : ∃ z, (Boundary.graftSpaceEquiv B C₂).symm z = x :=
    ⟨Boundary.graftSpaceEquiv B C₂ x, Equiv.symm_apply_apply _ _⟩
  obtain ⟨⟨f, c⟩, hy⟩ : ∃ z, (Boundary.graftSpaceEquiv B C₂).symm z = y :=
    ⟨Boundary.graftSpaceEquiv B C₂ y, Equiv.symm_apply_apply _ _⟩
  subst hx
  subst hy
  have hsymm (z : (B.graft C₂).space) :
      (graftSpaceRelabel B C₁ C₂ theta).symm z =
        (Boundary.graftSpaceEquiv B C₁).symm
          ⟨(Boundary.graftSpaceEquiv B C₂ z).1,
            (theta _).symm (Boundary.graftSpaceEquiv B C₂ z).2⟩ := rfl
  simp only [LinearMap.comp_apply, reindexOp, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.submatrix_apply]
  rw [hsymm, hsymm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  dsimp only
  by_cases hef : e = f
  · subst hef
    rw [Program.controlledContinuation_sameExit, Program.controlledContinuation_sameExit,
      h e]
    rfl
  · rw [Program.controlledContinuation_block_zero _ _ hef,
      Program.controlledContinuation_block_zero _ _ hef]

/-- Grafted continuations with equal denotations give equal grafted denotations. -/
theorem denote_graft_congr_cont {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
    {C : B.Exit → Boundary P} (k₁ k₂ : ∀ e : B.Exit, Program (B.system e) (C e))
    (h : ∀ e sigma, (k₂ e).denote sigma = (k₁ e).denote sigma)
    (rho : TypedLOCC.Op R.total) :
    (p.graft k₂).denote rho = (p.graft k₁).denote rho := by
  have hstep := denote_graft_congr_relabel p k₁ k₂ (fun _ => Equiv.refl _)
    (fun e sigma => by
      rw [h e sigma]
      ext a b
      simp [reindexOp]) rho
  rw [hstep, graftSpaceRelabel_refl]
  ext a b
  simp [reindexOp]

end TypedLOCC.BoundaryRelabel
