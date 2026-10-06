import QCryptLean.LOCC.Typed.Program.BoundaryRelabel.Basic

/-!
# Uniform boundaries and their exits

Second layer of the BoundaryRelabel family.  A *uniform* boundary `Boundary.uniform S T` announces
the word `T` and then terminates at the fixed multipartite system `S`. This file records how such
boundaries interact with grafting and with the recursive exit/multipartite system dictionaries
`Boundary.uniformExitEquiv` and `Boundary.uniformSystemEquiv`:

* `uniform_append_eq_graft` — concatenating announcement words is grafting;
* `uniformExitEquiv_graft_append`, `uniformExitEquiv_cast` — complete exits in graft coordinates and
  along an equality of announcement words;
* `uniformSystemEquiv_eq_cast` — the recursive multipartite system transport is the cast along
  `Boundary.uniform_system`;
* `atUniformExit_denote`, `denote_uniformSystemCast` — the channel of a program viewed at a complete
  public exit, for the recursive transport `Program.atUniformExit` and for the cast form;
* `atUniformExit_graft` — the recursive transport commutes with grafting.

Everything is protocol-independent: no key layout, security notion or norm estimate occurs.
-/

open scoped Matrix BigOperators

noncomputable section

namespace TypedLOCC.BoundaryRelabel

variable {P : Type} [Fintype P] [DecidableEq P]

/-- A uniform boundary over a concatenated word is the graft of the two uniform pieces. -/
theorem uniform_append_eq_graft (S₀ S : MultipartiteSystem P) (U : TList) :
    ∀ T : TList, Boundary.uniform S (TList.append T U) =
      (Boundary.uniform S₀ T).graft (fun _ => Boundary.uniform S U) := by
  intro T
  induction T with
  | nil => rfl
  | @cons Yc instY decY T ih =>
      change Boundary.announce Yc (fun _ => Boundary.uniform S (TList.append T U)) =
        Boundary.announce Yc
          (fun _ => (Boundary.uniform S₀ T).graft (fun _ => Boundary.uniform S U))
      rw [ih]

/-- Casting an announced-boundary exit along a pointwise boundary equality. -/
theorem cast_announce_exit {Pub : Type} [Fintype Pub] [DecidableEq Pub]
    (B₁ B₂ : Pub → Boundary P) (h : ∀ y, B₁ y = B₂ y)
    (hann : Boundary.announce Pub B₁ = Boundary.announce Pub B₂)
    (y : Pub) (x : (B₁ y).Exit) :
    Equiv.cast (congrArg Boundary.Exit hann) ⟨y, x⟩ =
      ⟨y, Equiv.cast (congrArg Boundary.Exit (h y)) x⟩ := by
  have hfun : B₁ = B₂ := funext h
  subst hfun
  rfl

/-- Complete exits of the appended uniform boundary in graft coordinates. -/
theorem uniformExitEquiv_graft_append (S₀ S : MultipartiteSystem P) (U : TList) :
    ∀ (T : TList)
      (x : ((Boundary.uniform S₀ T).graft (fun _ => Boundary.uniform S U)).Exit),
      Boundary.uniformExitEquiv S (TList.append T U)
          (Equiv.cast (congrArg Boundary.Exit
            (uniform_append_eq_graft S₀ S U T).symm) x) =
        (Transcript.appendEquiv T U).symm
          (Boundary.uniformExitEquiv S₀ T
              (Boundary.graftExitEquiv (Boundary.uniform S₀ T)
                (fun _ => Boundary.uniform S U) x).1,
            Boundary.uniformExitEquiv S U
              (Boundary.graftExitEquiv (Boundary.uniform S₀ T)
                (fun _ => Boundary.uniform S U) x).2) := by
  intro T
  induction T with
  | nil => intro x; rfl
  | @cons Yc instY decY T ih =>
      intro x
      obtain ⟨y, x'⟩ := x
      have hcast := cast_announce_exit
        (fun _ : Yc => (Boundary.uniform S₀ T).graft (fun _ => Boundary.uniform S U))
        (fun _ : Yc => Boundary.uniform S (TList.append T U))
        (fun _ => (uniform_append_eq_graft S₀ S U T).symm)
        (congrArg (fun F : Yc → Boundary P => Boundary.announce Yc F)
          (funext fun _ => (uniform_append_eq_graft S₀ S U T).symm))
        y x'
      have h1 : Boundary.uniformExitEquiv S (TList.append (TList.cons Yc T) U)
            (Equiv.cast (congrArg Boundary.Exit
              (uniform_append_eq_graft S₀ S U (TList.cons Yc T)).symm) ⟨y, x'⟩) =
          Boundary.uniformExitEquiv S (TList.append (TList.cons Yc T) U)
            ⟨y, Equiv.cast (congrArg Boundary.Exit
              (uniform_append_eq_graft S₀ S U T).symm) x'⟩ :=
        congrArg (⇑(Boundary.uniformExitEquiv S (TList.append (TList.cons Yc T) U))) hcast
      refine h1.trans ?_
      change (y, Boundary.uniformExitEquiv S (TList.append T U)
          (Equiv.cast (congrArg Boundary.Exit
            (uniform_append_eq_graft S₀ S U T).symm) x')) = _
      rw [ih x']
      rfl

/-- Uniform exits transported along an equality of announcement words. -/
theorem uniformExitEquiv_cast (S : MultipartiteSystem P) {W W' : TList} (hW : W = W')
    (g : (Boundary.uniform S W).Exit) :
    Equiv.cast (congrArg Transcript hW) (Boundary.uniformExitEquiv S W g) =
      Boundary.uniformExitEquiv S W'
        (Equiv.cast (congrArg Boundary.Exit
          (congrArg (fun V : TList => Boundary.uniform S V) hW)) g) := by
  subst hW
  rfl

/-- The recursive uniform-system equivalence is the cast along `Boundary.uniform_system`. -/
theorem uniformSystemEquiv_eq_cast (S : MultipartiteSystem P) :
    ∀ (T : TList) (e : (Boundary.uniform S T).Exit),
      Boundary.uniformSystemEquiv S T e =
        Equiv.cast (congrArg (fun R : MultipartiteSystem P => R.total) (Boundary.uniform_system S T
          e)) := by
  intro T
  induction T with
  | nil => intro e; rfl
  | @cons Yc instY decY T ih => intro e; exact ih e.2

/-- The denotation of a program viewed at a uniform-boundary exit is the original denotation at
the recursively transported input. -/
theorem atUniformExit_denote {S : MultipartiteSystem P} {B : Boundary P}
    (p : Program S B) : ∀ (T : TList) (e : (Boundary.uniform S T).Exit)
      (sigma : TypedLOCC.Op ((Boundary.uniform S T).system e).total),
      (Program.atUniformExit p T e).denote sigma =
        p.denote (reindexOp (Boundary.uniformSystemEquiv S T e) sigma) := by
  intro T
  induction T with
  | nil =>
      intro e sigma
      have hre : reindexOp (Boundary.uniformSystemEquiv S .nil e) sigma = sigma := by
        ext a b
        rfl
      rw [hre]
      rfl
  | @cons Y _ _ T ih =>
      intro e sigma
      exact ih e.2 sigma

/-- Entrywise form of `atUniformExit_denote`. -/
theorem atUniformExit_denote_apply {S : MultipartiteSystem P} {B : Boundary P} (p : Program S B)
    (T : TList) (e : (Boundary.uniform S T).Exit)
    (rho : TypedLOCC.Op ((Boundary.uniform S T).system e).total) (a b : B.space) :
    (Program.atUniformExit p T e).denote rho a b =
      p.denote (Matrix.reindex (Boundary.uniformSystemEquiv S T e)
        (Boundary.uniformSystemEquiv S T e) rho) a b := by
  rw [atUniformExit_denote]
  rfl

/-- The recursive uniform-exit transport commutes with grafting: viewing a grafted program at a
complete public exit is grafting the viewed base program. -/
theorem atUniformExit_graft {S : MultipartiteSystem P} {B : Boundary P} {C : B.Exit → Boundary P}
    (p : Program S B) (k : ∀ f : B.Exit, Program (B.system f) (C f)) :
    ∀ (T : TList) (e : (Boundary.uniform S T).Exit),
      Program.atUniformExit (p.graft k) T e = (Program.atUniformExit p T e).graft k := by
  intro T
  induction T with
  | nil => intro e; rfl
  | @cons XX _ _ T ih => intro e; exact ih e.2

/-- The denotation of a program transported to a uniform-boundary exit multipartite system is the
original denotation at the transported input.  The transport is the recursive
`Boundary.uniformSystemEquiv`, not an opaque cast. -/
theorem denote_uniformSystemCast
    (R : MultipartiteSystem P) (T : TList) (D : Boundary P)
    (p : Program R D) (e : (Boundary.uniform R T).Exit)
    (sigma : TypedLOCC.Op ((Boundary.uniform R T).system e).total)
    (a b : D.space) :
    (show Program ((Boundary.uniform R T).system e) D from
        by simpa only [Boundary.uniform_system] using p).denote sigma a b =
      p.denote (Matrix.reindex (Boundary.uniformSystemEquiv R T e)
        (Boundary.uniformSystemEquiv R T e) sigma) a b := by
  induction T with
  | nil => rfl
  | @cons Pub _ _ T ih => exact ih e.2 sigma

end TypedLOCC.BoundaryRelabel
