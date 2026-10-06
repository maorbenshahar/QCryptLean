import QCryptLean.LOCC.Typed.Boundary.DirectSum

/-!
# Direct-sum coordinates for grafted boundaries

Grafting replaces each complete public exit of a boundary by an exit-dependent continuation
boundary.  This module gives the canonical reassociation from the native grafted boundary space
to the dependent sum of continuation spaces, together with the corresponding orthogonal
inclusions.

The construction is the coordinate form of exit-dependent classical control in the finite-round
LOCC instrument trees of Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583,
Section II.
-/

open scoped Matrix BigOperators

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Boundary

/-- The output space of a graft is canonically the dependent sum of the spaces attached to the
base boundary's complete exits.

The forward direction is from the native `Boundary.graft` coordinate space to
`Σ e : B.Exit, (C e).space`.  This orientation is used to pull the standard sigma-fibre
inclusions back to native graft coordinates.
-/
def graftSpaceEquiv (B : Boundary P) (C : B.Exit → Boundary P) :
    (B.graft C).space ≃ Σ e : B.Exit, (C e).space :=
  match B with
  | @Boundary.leaf _ _ _ _ =>
      { toFun := fun x => ⟨(), x⟩
        invFun := fun x => x.2
        left_inv := fun _ => rfl
        right_inv := fun x => by
          rcases x with ⟨⟨⟩, x⟩
          rfl }
  | @Boundary.announce _ _ _ Y _ _ next =>
      (publicSpaceEquiv (fun y => (next y).graft fun e => C ⟨y, e⟩)).trans
        ((Equiv.sigmaCongrRight fun y =>
          graftSpaceEquiv (next y) fun e => C ⟨y, e⟩).trans
          (Equiv.sigmaAssoc fun y e => (C ⟨y, e⟩).space).symm)

/-- At a terminal boundary, the graft-space equivalence adds the unique base exit. -/
@[simp] theorem graftSpaceEquiv_leaf_apply (R : MultipartiteSystem P)
    (C : (Boundary.leaf R).Exit → Boundary P) (x : (C ()).space) :
    graftSpaceEquiv (.leaf R) C x = ⟨(), x⟩ :=
  rfl

/-- At an announced boundary, the graft-space equivalence exposes the outer public outcome and
then recursively exposes the continuation exit. -/
@[simp] theorem graftSpaceEquiv_announce_apply {Y : Type} [Fintype Y] [DecidableEq Y]
    (next : Y → Boundary P) (C : (Boundary.announce Y next).Exit → Boundary P)
    (x : (Boundary.announce Y (fun y => (next y).graft fun e => C ⟨y, e⟩)).space) :
    graftSpaceEquiv (.announce Y next) C x =
      ⟨⟨x.1.1, ((next x.1.1).graftSpaceEquiv (fun e => C ⟨x.1.1, e⟩)
        ⟨x.1.2, x.2⟩).1⟩,
        ((next x.1.1).graftSpaceEquiv (fun e => C ⟨x.1.1, e⟩)
          ⟨x.1.2, x.2⟩).2⟩ :=
  rfl

/-- The graft-space equivalence exposes both the decomposed graft exit and the leaf payload
transported along the canonical equality of its selected multipartite systems. -/
@[simp] theorem graftSpaceEquiv_apply (B : Boundary P) (C : B.Exit → Boundary P)
    (x : (B.graft C).space) :
    graftSpaceEquiv B C x =
      ⟨(graftExitEquiv B C x.1).1,
        ⟨(graftExitEquiv B C x.1).2,
          Equiv.cast (congrArg (fun R : MultipartiteSystem P => R.total)
            (system_graftExitEquiv B C x.1)) x.2⟩⟩ := by
  induction B with
  | leaf R => rfl
  | @announce Y _ _ next ih =>
      rcases x with ⟨⟨y, e⟩, q⟩
      rw [graftSpaceEquiv_announce_apply]
      have h := ih y (fun f => C ⟨y, f⟩) ⟨e, q⟩
      rw [h]
      rfl

/-- The base public exit exposed by `graftSpaceEquiv` is exactly the base component exposed by
`graftExitEquiv`.  Thus the forward reindex orientation agrees at the type and matrix layers. -/
@[simp] theorem graftSpaceEquiv_fst (B : Boundary P) (C : B.Exit → Boundary P)
    (x : (B.graft C).space) :
    (graftSpaceEquiv B C x).1 = (graftExitEquiv B C x.1).1 := by
  induction B with
  | leaf R => rfl
  | @announce Y _ _ next ih =>
      rcases x with ⟨⟨y, e⟩, a⟩
      change
        (⟨y, (graftSpaceEquiv (next y) (fun e => C ⟨y, e⟩) ⟨e, a⟩).1⟩ :
          (Boundary.announce Y next).Exit) =
        (⟨y, (graftExitEquiv (next y) (fun e => C ⟨y, e⟩) e).1⟩ :
          (Boundary.announce Y next).Exit)
      exact congrArg (Sigma.mk y)
        (ih y (fun e => C ⟨y, e⟩) ⟨e, a⟩)

/-- When every continuation boundary has a unique public exit, two graft-space coordinates over
the same base exit select the same native graft exit. -/
theorem graftSpaceEquiv_symm_fst_eq_of_subsingleton (B : Boundary P)
    (C : B.Exit → Boundary P) [∀ e, Subsingleton (C e).Exit]
    (e : B.Exit) (a b : (C e).space) :
    ((graftSpaceEquiv B C).symm ⟨e, a⟩).1 =
      ((graftSpaceEquiv B C).symm ⟨e, b⟩).1 := by
  apply (graftExitEquiv B C).injective
  have hbase :
      (graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, a⟩).1).1 =
        (graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, b⟩).1).1 := by
    calc
      (graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, a⟩).1).1 =
          (graftSpaceEquiv B C ((graftSpaceEquiv B C).symm ⟨e, a⟩)).1 :=
        (graftSpaceEquiv_fst B C _).symm
      _ = e := congrArg Sigma.fst ((graftSpaceEquiv B C).apply_symm_apply ⟨e, a⟩)
      _ = (graftSpaceEquiv B C ((graftSpaceEquiv B C).symm ⟨e, b⟩)).1 :=
        (congrArg Sigma.fst ((graftSpaceEquiv B C).apply_symm_apply ⟨e, b⟩)).symm
      _ = (graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, b⟩).1).1 :=
        graftSpaceEquiv_fst B C _
  apply Sigma.ext hbase
  let u := graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, a⟩).1
  let v := graftExitEquiv B C ((graftSpaceEquiv B C).symm ⟨e, b⟩).1
  let htype : (C u.1).Exit = (C v.1).Exit := congrArg (fun f => (C f).Exit) hbase
  exact (cast_heq htype u.2).symm.trans
    (heq_of_eq (Subsingleton.elim (cast htype u.2) v.2))

/-- The complete exit of a point named in graft coordinates is the graft exit of its base exit and
continuation exit. -/
theorem graftSpaceEquiv_symm_fst (B : Boundary P) (C : B.Exit → Boundary P) (e : B.Exit)
    (r : (C e).space) :
    ((graftSpaceEquiv B C).symm ⟨e, r⟩).1 = (graftExitEquiv B C).symm ⟨e, r.1⟩ := by
  induction B with
  | leaf S =>
      cases e
      rfl
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases e with ⟨y, e⟩
      exact congrArg (Sigma.mk y) (ih y (fun f => C ⟨y, f⟩) e r)

/-- The payload of a point named in graft coordinates is the attached payload. -/
theorem graftSpaceEquiv_symm_snd_heq (B : Boundary P) (C : B.Exit → Boundary P) (e : B.Exit)
    (r : (C e).space) :
    ((graftSpaceEquiv B C).symm ⟨e, r⟩).2 ≍ r.2 := by
  induction B with
  | leaf S =>
      cases e
      exact HEq.rfl
  | @announce Outcome instOutcome decOutcome next ih =>
      rcases e with ⟨y, e⟩
      exact ih y (fun f => C ⟨y, f⟩) e r

/-- The multipartite system transport attached to a decomposed graft exit. -/
abbrev graftSystemCast (B : Boundary P) (C : B.Exit → Boundary P) (e : B.Exit) (f : (C e).Exit) :
    ((B.graft C).system ((graftExitEquiv B C).symm ⟨e, f⟩)).total ≃ ((C e).system f).total :=
  Equiv.cast (congrArg (fun R : MultipartiteSystem P => R.total) (system_graftExitEquiv_symm B C ⟨e,
    f⟩))

/-- Fully decomposed inverse of the graft-space equivalence. -/
theorem graftSpaceEquiv_symm_pair (B : Boundary P) (C : B.Exit → Boundary P) (e : B.Exit)
    (f : (C e).Exit) (q : ((C e).system f).total) :
    (graftSpaceEquiv B C).symm ⟨e, ⟨f, q⟩⟩ =
      ⟨(graftExitEquiv B C).symm ⟨e, f⟩, (graftSystemCast B C e f).symm q⟩ := by
  refine Sigma.ext (graftSpaceEquiv_symm_fst B C e ⟨f, q⟩) ?_
  refine (graftSpaceEquiv_symm_snd_heq B C e ⟨f, q⟩).trans ?_
  exact (cast_heq _ q).symm

/-- Include the entire continuation space attached to one base exit into the native output space
of the grafted boundary. -/
def graftInclKraus (B : Boundary P) (C : B.Exit → Boundary P) (e : B.Exit) :
    Matrix (B.graft C).space (C e).space ℂ :=
  (sigmaInclKraus (fun f => (C f).space) e).submatrix (graftSpaceEquiv B C) id

/-- Coordinate formula for a graft-continuation inclusion. -/
@[simp] theorem graftInclKraus_apply (B : Boundary P) (C : B.Exit → Boundary P)
    (e : B.Exit) (p : (B.graft C).space) (q : (C e).space) :
    graftInclKraus B C e p q =
      if graftSpaceEquiv B C p = ⟨e, q⟩ then 1 else 0 :=
  rfl

/-- Every row outside the selected base-exit continuation block is zero. -/
theorem graftInclKraus_apply_eq_zero_of_fst_ne (B : Boundary P)
    (C : B.Exit → Boundary P) {e : B.Exit} {p : (B.graft C).space}
    (h : (graftSpaceEquiv B C p).1 ≠ e) (q : (C e).space) :
    graftInclKraus B C e p q = 0 := by
  apply sigmaInclKraus_apply_eq_zero_of_fst_ne (fun f => (C f).space) h q

/-- At a terminal base boundary, the sole graft-continuation inclusion is the identity matrix on
the attached continuation space. -/
@[simp] theorem graftInclKraus_leaf (R : MultipartiteSystem P)
    (C : (Boundary.leaf R).Exit → Boundary P) :
    graftInclKraus (.leaf R) C () =
      (1 : Matrix (C ()).space (C ()).space ℂ) := by
  ext p q
  simp only [graftInclKraus, Matrix.submatrix_apply, sigmaInclKraus_apply,
    graftSpaceEquiv_leaf_apply, Matrix.one_apply, id_eq]
  apply if_congr
  · constructor
    · intro h
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    · intro h
      subst q
      rfl
  · rfl
  · rfl

/-- At an announced base boundary, a graft-continuation inclusion factors through the selected
outer public block and the corresponding child graft inclusion. -/
theorem graftInclKraus_announce {Y : Type} [Fintype Y] [DecidableEq Y]
    (next : Y → Boundary P)
    (C : (Boundary.announce Y next).Exit → Boundary P)
    (y : Y) (e : (next y).Exit) :
    graftInclKraus (.announce Y next) C ⟨y, e⟩ =
      publicInclKraus (fun z => (next z).graft fun f => C ⟨z, f⟩) y *
        graftInclKraus (next y) (fun f => C ⟨y, f⟩) e := by
  ext p q
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single
    ((graftSpaceEquiv (next y) (fun f => C ⟨y, f⟩)).symm ⟨e, q⟩)]
  · simp only [graftInclKraus_apply, publicInclKraus_apply, Equiv.apply_symm_apply,
      if_pos, mul_one]
    change (if
        ((Equiv.sigmaCongrRight fun z =>
          graftSpaceEquiv (next z) fun f => C ⟨z, f⟩).trans
            (Equiv.sigmaAssoc fun z f => (C ⟨z, f⟩).space).symm)
          (publicSpaceEquiv (fun z => (next z).graft fun f => C ⟨z, f⟩) p) =
            ⟨⟨y, e⟩, q⟩ then 1 else 0) =
      (if publicSpaceEquiv (fun z => (next z).graft fun f => C ⟨z, f⟩) p =
          ⟨y, (graftSpaceEquiv (next y) (fun f => C ⟨y, f⟩)).symm ⟨e, q⟩⟩
        then 1 else 0)
    apply if_congr
    · exact Equiv.apply_eq_iff_eq_symm_apply
        ((Equiv.sigmaCongrRight fun z =>
          graftSpaceEquiv (next z) fun f => C ⟨z, f⟩).trans
            (Equiv.sigmaAssoc fun z f => (C ⟨z, f⟩).space).symm)
    · rfl
    · rfl
  · intro r _ hr
    rw [graftInclKraus_apply, if_neg]
    · simp
    · intro h
      apply hr
      have h' := congrArg
        (graftSpaceEquiv (next y) (fun f => C ⟨y, f⟩)).symm h
      simpa only [Equiv.symm_apply_apply] using h'
  · simp

/-- A graft-continuation inclusion is an isometry. -/
@[simp] theorem graftInclKraus_conjTranspose_mul_self (B : Boundary P)
    (C : B.Exit → Boundary P) (e : B.Exit) :
    (graftInclKraus B C e)ᴴ * graftInclKraus B C e = 1 := by
  rw [graftInclKraus, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, sigmaInclKraus_conjTranspose_mul_self]
  rfl

/-- Continuation spaces attached to distinct base exits are orthogonal, even when their coordinate
types differ. -/
theorem graftInclKraus_conjTranspose_mul_of_ne (B : Boundary P)
    (C : B.Exit → Boundary P) {e f : B.Exit} (h : e ≠ f) :
    (graftInclKraus B C e)ᴴ * graftInclKraus B C f = 0 := by
  rw [graftInclKraus, graftInclKraus, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, sigmaInclKraus_conjTranspose_mul_of_ne _ h]
  rfl

/-- The continuation-space inclusions resolve the identity on the native grafted boundary space. -/
@[simp] theorem sum_graftInclKraus_mul_conjTranspose (B : Boundary P)
    (C : B.Exit → Boundary P) :
    ∑ e : B.Exit, graftInclKraus B C e * (graftInclKraus B C e)ᴴ = 1 := by
  have hmul (e : B.Exit) :
      graftInclKraus B C e * (graftInclKraus B C e)ᴴ =
        (sigmaInclKraus (fun f => (C f).space) e *
          (sigmaInclKraus (fun f => (C f).space) e)ᴴ).submatrix
            (graftSpaceEquiv B C) (graftSpaceEquiv B C) := by
    ext p q
    simp [graftInclKraus, Matrix.mul_apply, Matrix.conjTranspose_apply]
  ext p q
  simp_rw [hmul]
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]
  change (∑ e : B.Exit,
      (sigmaInclKraus (fun f => (C f).space) e *
        (sigmaInclKraus (fun f => (C f).space) e)ᴴ)
          (graftSpaceEquiv B C p) (graftSpaceEquiv B C q)) = _
  rw [← Matrix.sum_apply, sum_sigmaInclKraus_mul_conjTranspose]
  by_cases hpq : p = q
  · subst q
    simp
  · have heq : graftSpaceEquiv B C p ≠ graftSpaceEquiv B C q :=
      fun h => hpq ((graftSpaceEquiv B C).injective h)
    rw [Matrix.one_apply, if_neg heq, Matrix.one_apply, if_neg hpq]

end Boundary
end TypedLOCC
