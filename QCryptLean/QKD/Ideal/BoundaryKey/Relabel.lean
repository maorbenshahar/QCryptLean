import QCryptLean.QKD.Ideal.BoundaryKey.Hom
import QCryptLean.LOCC.Typed.Program.BoundaryRelabel

/-!
# Transport of the boundary-derived ideal key resource along an output relabelling

The boundary-derived ideal of `TypedLOCC.BoundaryKeyLayout` pinches between distinct complete public
exits and, inside one exit, replaces both ordered key registers by one uniform shared key while
retaining the private residual coordinate.  This module records two protocol-independent sufficient
conditions for a relabelling of complete output spaces to intertwine two such resources exactly.

* `RegisterKeyed`: the two key coordinates are the named laboratories' own registers and the
  retained coordinate is trivial.  For two register-keyed layouts, any *exit-renaming register
  relabelling* `CanonRel` — complete public exits renamed injectively, corresponding exits carrying
  the same multipartite system, every joint register transported unchanged — intertwines the
  resources (`ideal_reindexOp_of_canonRel`).
* `ideal_transport_of_keys`: alternatively, a map of complete output spaces which carries complete
  public exits injectively and relabels Alice's and Bob's key coordinates by *one* common bijection
  of the key alphabet intertwines the resources, provided the residual coordinate is a subsingleton
  on the target side.

Nothing here is a security statement: the resource is the finite shared-key replacement of the
real/ideal QKD interface of Christandl--Koenig--Renner, arXiv:0809.3019, Theorem 1 and Lemma 1. No
protocol, selector, entropy or finite-key estimate occurs.
-/

open scoped Matrix BigOperators

open Matrix

noncomputable section

namespace TypedLOCC

open BoundaryRelabel

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## Register-keyed boundary layouts -/

/-- A boundary key layout whose two key coordinates are the named laboratories' own registers and
whose retained coordinate is trivial. -/
structure RegisterKeyed {B : Boundary P} (L : BoundaryKeyLayout B) (a b : P) : Prop where
  /-- The retained coordinate carries no information. -/
  residual : ∀ e : B.Exit, Subsingleton (L.Residual e)
  /-- Alice's key coordinate is her own register. -/
  aliceKey : ∀ (e : B.Exit) (q : (B.system e).total), (L.coordinates e q).1 ≍ q a
  /-- Bob's key coordinate is his own register. -/
  bobKey : ∀ (e : B.Exit) (q : (B.system e).total), (L.coordinates e q).2.1 ≍ q b

namespace RegisterKeyed

variable {B : Boundary P} {L : BoundaryKeyLayout B} {a b : P}

/-- The key alphabet at a complete exit is Alice's own register there. -/
theorem key_eq (h : RegisterKeyed L a b) (e : B.Exit) :
    (L.disposition e).Key = (B.system e).reg a := by
  letI : Nonempty (B.system e).total := inferInstance
  obtain ⟨q⟩ := (inferInstance : Nonempty (B.system e).total)
  exact type_eq_of_heq (h.aliceKey e q)

/-- The key alphabet at a complete exit is Bob's own register there.  The mirror of `key_eq`; on an
accepting exit it says the two parties hold registers of the *same* key alphabet, and on an
aborting exit that both hold the trivial one. -/
theorem key_eq_bob (h : RegisterKeyed L a b) (e : B.Exit) :
    (L.disposition e).Key = (B.system e).reg b := by
  obtain ⟨q⟩ := (inferInstance : Nonempty (B.system e).total)
  exact type_eq_of_heq (h.bobKey e q)

/-- The key alphabet and Alice's register have the same cardinality. -/
theorem card_key (h : RegisterKeyed L a b) (e : B.Exit) :
    Fintype.card ((L.disposition e).Key) = Fintype.card ((B.system e).reg a) :=
  Fintype.card_congr (Equiv.cast (h.key_eq e))

/-- Alice's and Bob's key coordinates agree exactly when their registers do. -/
theorem alice_eq_bob_iff (h : RegisterKeyed L a b) (e : B.Exit) (q : (B.system e).total) :
    (L.coordinates e q).1 = (L.coordinates e q).2.1 ↔ q a ≍ q b := by
  constructor
  · intro hq
    exact ((h.aliceKey e q).symm.trans (hq ▸ (h.bobKey e q))).symm.symm
  · intro hq
    exact eq_of_heq ((h.aliceKey e q).trans (hq.trans (h.bobKey e q).symm))

/-- Alice's key coordinates at two points agree exactly when her registers do. -/
theorem alice_eq_alice_iff (h : RegisterKeyed L a b) (e : B.Exit) (q q' : (B.system e).total) :
    (L.coordinates e q).1 = (L.coordinates e q').1 ↔ q a ≍ q' a := by
  constructor
  · intro hq
    exact ((h.aliceKey e q).symm.trans (hq ▸ (h.aliceKey e q'))).symm.symm
  · intro hq
    exact eq_of_heq ((h.aliceKey e q).trans (hq.trans (h.aliceKey e q').symm))

/-- Enumerating one exit fibre by its two key coordinates. -/
noncomputable def fibreEquiv (h : RegisterKeyed L a b) (e : B.Exit) :
    (L.disposition e).Key × (L.disposition e).Key ≃ (B.system e).total :=
  letI : Subsingleton (L.Residual e) := h.residual e
  letI : Unique (L.Residual e) := uniqueOfSubsingleton (Classical.arbitrary _)
  (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodUnique (L.disposition e).Key (L.Residual e)).symm).trans
    (L.coordinates e).symm

theorem fibreEquiv_apply (h : RegisterKeyed L a b) (e : B.Exit)
    (k l : (L.disposition e).Key) (u : L.Residual e) :
    h.fibreEquiv e (k, l) = (L.coordinates e).symm (k, l, u) := by
  letI : Subsingleton (L.Residual e) := h.residual e
  change (L.coordinates e).symm (k, l, _) = _
  exact congrArg (L.coordinates e).symm
    (congrArg (fun r => (k, l, r)) (Subsingleton.elim _ _))

/-- **Register-level entry formula for the boundary-derived ideal, on the agreeing diagonal.** -/
theorem ideal_apply_diag (h : RegisterKeyed L a b) (rho : TypedLOCC.Op B.space)
    (e : B.Exit) (q q' : (B.system e).total)
    (hq : q a ≍ q b) (hq' : q' a ≍ q' b) (hqq : q a ≍ q' a) :
    L.ideal rho ⟨e, q⟩ ⟨e, q'⟩ =
      (((Fintype.card ((B.system e).reg a) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∑ p : (B.system e).total, rho ⟨e, p⟩ ⟨e, p⟩ := by
  letI : Subsingleton (L.Residual e) := h.residual e
  rcases hc : L.coordinates e q with ⟨A, Bk, u⟩
  rcases hc' : L.coordinates e q' with ⟨A', Bk', u'⟩
  have hqe : q = (L.coordinates e).symm (A, Bk, u) := by rw [← hc]; simp
  have hqe' : q' = (L.coordinates e).symm (A', Bk', u') := by rw [← hc']; simp
  have hAB : A = Bk := by
    have := (h.alice_eq_bob_iff e q).mpr hq
    rw [hc] at this
    exact this
  have hAB' : A' = Bk' := by
    have := (h.alice_eq_bob_iff e q').mpr hq'
    rw [hc'] at this
    exact this
  have hAA : A = A' := by
    have := (h.alice_eq_alice_iff e q q').mpr hqq
    rw [hc, hc'] at this
    exact this
  rw [hqe, hqe', L.ideal_coordinate_entry, if_pos ⟨hAB, hAB', hAA⟩, h.card_key e]
  refine congrArg (fun z : ℂ => (((Fintype.card ((B.system e).reg a) : ℝ)⁻¹ : ℝ) : ℂ) * z) ?_
  have hprod := Fintype.sum_prod_type
    (f := fun z : (L.disposition e).Key × (L.disposition e).Key =>
      rho (⟨e, (L.coordinates e).symm (z.1, z.2, u)⟩ : B.space)
        (⟨e, (L.coordinates e).symm (z.1, z.2, u')⟩ : B.space))
  rw [← hprod]
  refine Fintype.sum_equiv (h.fibreEquiv e) _ _ ?_
  intro z
  obtain ⟨k, l⟩ := z
  have huu : (L.coordinates e).symm (k, l, u') = (L.coordinates e).symm (k, l, u) :=
    congrArg (L.coordinates e).symm
      (congrArg (fun r => (k, l, r)) (Subsingleton.elim u' u))
  simp only []
  rw [huu, h.fibreEquiv_apply e k l u]

/-- The boundary-derived ideal vanishes off the agreeing diagonal. -/
theorem ideal_apply_zero (h : RegisterKeyed L a b) (rho : TypedLOCC.Op B.space)
    (x y : B.space)
    (hne : ¬ (x.1 = y.1 ∧ (x.2 a ≍ x.2 b) ∧ (y.2 a ≍ y.2 b) ∧ (x.2 a ≍ y.2 a))) :
    L.ideal rho x y = 0 := by
  classical
  obtain ⟨e, q⟩ := x
  obtain ⟨f, q'⟩ := y
  by_cases hef : e = f
  · subst hef
    letI : Subsingleton (L.Residual e) := h.residual e
    rcases hc : L.coordinates e q with ⟨A, Bk, u⟩
    rcases hc' : L.coordinates e q' with ⟨A', Bk', u'⟩
    have hqe : q = (L.coordinates e).symm (A, Bk, u) := by rw [← hc]; simp
    have hqe' : q' = (L.coordinates e).symm (A', Bk', u') := by rw [← hc']; simp
    rw [hqe, hqe', L.ideal_coordinate_entry, if_neg]
    rintro ⟨hAB, hAB', hAA⟩
    refine hne ⟨rfl, ?_, ?_, ?_⟩
    · refine (h.alice_eq_bob_iff e q).mp ?_
      rw [hc]
      exact hAB
    · refine (h.alice_eq_bob_iff e q').mp ?_
      rw [hc']
      exact hAB'
    · refine (h.alice_eq_alice_iff e q q').mp ?_
      rw [hc, hc']
      exact hAA
  · exact L.ideal_crossExit_zero rho hef q q'

end RegisterKeyed

/-! ## Exit-renaming register relabellings -/

/-- An **exit-renaming register relabelling** of boundary output spaces: complete public exits are
renamed injectively, corresponding exits carry the same multipartite system, and every joint
register coordinate is transported unchanged. -/
structure CanonRel {B₁ B₂ : Boundary P} (Θ : B₁.space ≃ B₂.space) where
  /-- The induced renaming of complete public exits. -/
  exits : B₁.Exit → B₂.Exit
  /-- Distinct complete public exits stay distinct. -/
  exits_inj : Function.Injective exits
  /-- Renamed complete exits carry the same multipartite system. -/
  systems : ∀ g : B₁.Exit, B₂.system (exits g) = B₁.system g
  /-- The relabelling renames the complete public exit. -/
  fst : ∀ x : B₁.space, (Θ x).1 = exits x.1
  /-- The relabelling leaves the joint register coordinate unchanged. -/
  snd : ∀ x : B₁.space, (Θ x).2 ≍ x.2

namespace CanonRel

variable {B₁ B₂ B₃ : Boundary P}

/-- Explicit value of an exit-renaming register relabelling. -/
theorem sigma_eq {Θ : B₁.space ≃ B₂.space} (hΘ : CanonRel Θ) (g : B₁.Exit)
    (p : (B₁.system g).total) :
    Θ ⟨g, p⟩ = ⟨hΘ.exits g, (systemTotalCast (hΘ.systems g)).symm p⟩ := by
  refine Sigma.ext (hΘ.fst ⟨g, p⟩) ?_
  exact (hΘ.snd ⟨g, p⟩).trans (systemTotalCast_symm_heq (hΘ.systems g) p).symm

/-- Composition of exit-renaming register relabellings. -/
def trans {Θ₁ : B₁.space ≃ B₂.space} {Θ₂ : B₂.space ≃ B₃.space}
    (h₁ : CanonRel Θ₁) (h₂ : CanonRel Θ₂) : CanonRel (Θ₁.trans Θ₂) where
  exits g := h₂.exits (h₁.exits g)
  exits_inj := h₂.exits_inj.comp h₁.exits_inj
  systems g := (h₂.systems (h₁.exits g)).trans (h₁.systems g)
  fst x := by
    change (Θ₂ (Θ₁ x)).1 = _
    rw [h₂.fst (Θ₁ x), h₁.fst x]
  snd x := by
    change (Θ₂ (Θ₁ x)).2 ≍ _
    exact (h₂.snd (Θ₁ x)).trans (h₁.snd x)

/-- The exit renaming of an exit-renaming register relabelling is onto. -/
theorem exits_surjective {Θ : B₁.space ≃ B₂.space} (hΘ : CanonRel Θ) :
    Function.Surjective hΘ.exits := by
  intro g'
  obtain ⟨p⟩ := (inferInstance : Nonempty (B₂.system g').total)
  refine ⟨(Θ.symm ⟨g', p⟩).1, ?_⟩
  have h := hΘ.fst (Θ.symm ⟨g', p⟩)
  rw [Θ.apply_symm_apply] at h
  exact h.symm

/-- The exit renaming as a bijection of complete public exits. -/
noncomputable def exitEquiv {Θ : B₁.space ≃ B₂.space} (hΘ : CanonRel Θ) :
    B₁.Exit ≃ B₂.Exit :=
  Equiv.ofBijective hΘ.exits ⟨hΘ.exits_inj, hΘ.exits_surjective⟩

/-- The inverse of an exit-renaming register relabelling is one. -/
noncomputable def symm {Θ : B₁.space ≃ B₂.space} (hΘ : CanonRel Θ) : CanonRel Θ.symm where
  exits := hΘ.exitEquiv.symm
  exits_inj := hΘ.exitEquiv.symm.injective
  systems g' := by
    have hE : hΘ.exits (hΘ.exitEquiv.symm g') = g' := hΘ.exitEquiv.apply_symm_apply g'
    have h := hΘ.systems (hΘ.exitEquiv.symm g')
    rw [hE] at h
    exact h.symm
  fst y := by
    have h := hΘ.fst (Θ.symm y)
    rw [Θ.apply_symm_apply] at h
    exact (hΘ.exitEquiv.symm_apply_eq.mpr h).symm
  snd y := by
    have h := hΘ.snd (Θ.symm y)
    rw [Θ.apply_symm_apply] at h
    exact h.symm

end CanonRel

/-- **The boundary-derived ideal key resource is intertwined by an exit-renaming register
relabelling of two register-keyed layouts.**  Every complete public exit, both ordered keys and
the entire retained coordinate are preserved; no state, positivity, classicality or reachability
hypothesis is used. -/
theorem ideal_reindexOp_of_canonRel {B₁ B₂ : Boundary P}
    {L₁ : BoundaryKeyLayout B₁} {L₂ : BoundaryKeyLayout B₂} {a b : P}
    (h₁ : RegisterKeyed L₁ a b) (h₂ : RegisterKeyed L₂ a b)
    {Θ : B₁.space ≃ B₂.space} (hΘ : CanonRel Θ) (M : TypedLOCC.Op B₁.space) :
    L₂.ideal (reindexOp Θ M) = reindexOp Θ (L₁.ideal M) := by
  classical
  ext x' y'
  obtain ⟨x, rfl⟩ : ∃ x, Θ x = x' := ⟨Θ.symm x', Θ.apply_symm_apply x'⟩
  obtain ⟨y, rfl⟩ : ∃ y, Θ y = y' := ⟨Θ.symm y', Θ.apply_symm_apply y'⟩
  have hrhs : reindexOp Θ (L₁.ideal M) (Θ x) (Θ y) = L₁.ideal M x y := by
    simp [reindexOp]
  rw [hrhs]
  obtain ⟨g, q⟩ := x
  obtain ⟨f, q'⟩ := y
  have hpull : ∀ (e : B₁.Exit) (p : (B₂.system (hΘ.exits e)).total),
      Θ.symm ⟨hΘ.exits e, p⟩ = ⟨e, systemTotalCast (hΘ.systems e) p⟩ := by
    intro e p
    refine Θ.injective ?_
    rw [Θ.apply_symm_apply, hΘ.sigma_eq e (systemTotalCast (hΘ.systems e) p),
      Equiv.symm_apply_apply]
  by_cases hgf : g = f
  · subst hgf
    by_cases hd : (q a ≍ q b) ∧ (q' a ≍ q' b) ∧ (q a ≍ q' a)
    · obtain ⟨hq, hq', hqq⟩ := hd
      have hcq : (systemTotalCast (hΘ.systems g)).symm q ≍ q :=
        systemTotalCast_symm_heq (hΘ.systems g) q
      have hcq' : (systemTotalCast (hΘ.systems g)).symm q' ≍ q' :=
        systemTotalCast_symm_heq (hΘ.systems g) q'
      have hSystem := (hΘ.systems g).symm
      rw [hΘ.sigma_eq g q, hΘ.sigma_eq g q',
        h₂.ideal_apply_diag (reindexOp Θ M) (hΘ.exits g)
          ((systemTotalCast (hΘ.systems g)).symm q) ((systemTotalCast (hΘ.systems g)).symm q')
          ((heq_apply_of_system_eq hSystem hcq.symm a).symm.trans
            (hq.trans (heq_apply_of_system_eq hSystem hcq.symm b)))
          ((heq_apply_of_system_eq hSystem hcq'.symm a).symm.trans
            (hq'.trans (heq_apply_of_system_eq hSystem hcq'.symm b)))
          ((heq_apply_of_system_eq hSystem hcq.symm a).symm.trans
            (hqq.trans (heq_apply_of_system_eq hSystem hcq'.symm a))),
        h₁.ideal_apply_diag M g q q' hq hq' hqq]
      have hcard : Fintype.card ((B₂.system (hΘ.exits g)).reg a) =
          Fintype.card ((B₁.system g).reg a) := by
        rw [hΘ.systems g]
      rw [hcard]
      refine congrArg (fun z : ℂ => (((Fintype.card ((B₁.system g).reg a) : ℝ)⁻¹ : ℝ) : ℂ) * z) ?_
      refine Eq.trans ?_ (Equiv.sum_comp (systemTotalCast (hΘ.systems g))
        (fun p => M (⟨g, p⟩ : B₁.space) (⟨g, p⟩ : B₁.space)))
      refine Finset.sum_congr rfl ?_
      intro p _
      simp only [reindexOp, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply]
      rw [hpull g p]
    · have hL : L₂.ideal (reindexOp Θ M) (Θ ⟨g, q⟩) (Θ ⟨g, q'⟩) = 0 := by
        refine h₂.ideal_apply_zero (reindexOp Θ M) _ _ ?_
        rintro ⟨-, hA, hB, hC⟩
        refine hd ⟨?_, ?_, ?_⟩
        · have hcq : (Θ ⟨g, q⟩).2 ≍ q := hΘ.snd ⟨g, q⟩
          have hSystem : B₂.system (Θ ⟨g, q⟩).1 = B₁.system g := by
            rw [hΘ.fst ⟨g, q⟩]; exact hΘ.systems g
          exact (heq_apply_of_system_eq hSystem hcq a).symm.trans
            (hA.trans (heq_apply_of_system_eq hSystem hcq b))
        · have hcq : (Θ ⟨g, q'⟩).2 ≍ q' := hΘ.snd ⟨g, q'⟩
          have hSystem : B₂.system (Θ ⟨g, q'⟩).1 = B₁.system g := by
            rw [hΘ.fst ⟨g, q'⟩]; exact hΘ.systems g
          exact (heq_apply_of_system_eq hSystem hcq a).symm.trans
            (hB.trans (heq_apply_of_system_eq hSystem hcq b))
        · have hcq : (Θ ⟨g, q⟩).2 ≍ q := hΘ.snd ⟨g, q⟩
          have hcq' : (Θ ⟨g, q'⟩).2 ≍ q' := hΘ.snd ⟨g, q'⟩
          have hSystem : B₂.system (Θ ⟨g, q⟩).1 = B₁.system g := by
            rw [hΘ.fst ⟨g, q⟩]; exact hΘ.systems g
          have hSystem' : B₂.system (Θ ⟨g, q'⟩).1 = B₁.system g := by
            rw [hΘ.fst ⟨g, q'⟩]; exact hΘ.systems g
          exact (heq_apply_of_system_eq hSystem hcq a).symm.trans
            (hC.trans (heq_apply_of_system_eq hSystem' hcq' a))
      rw [hL]
      refine (h₁.ideal_apply_zero M _ _ ?_).symm
      rintro ⟨-, hA, hB, hC⟩
      exact hd ⟨hA, hB, hC⟩
  · have hne : (Θ (⟨g, q⟩ : B₁.space)).1 ≠ (Θ (⟨f, q'⟩ : B₁.space)).1 := by
      rw [hΘ.fst ⟨g, q⟩, hΘ.fst ⟨f, q'⟩]
      exact fun h => hgf (hΘ.exits_inj h)
    rw [L₂.ideal_crossExit_zero (reindexOp Θ M) hne _ _,
      L₁.ideal_crossExit_zero M hgf q q']

/-! ### Exit-renaming register relabellings of the structural building blocks -/

/-- Transport along an equality of output boundaries is an exit-renaming register relabelling. -/
def canonRel_cast {B₁ B₂ : Boundary P} (h : B₁ = B₂) :
    CanonRel (Equiv.cast (congrArg Boundary.space h)) where
  exits := Equiv.cast (congrArg Boundary.Exit h)
  exits_inj := (Equiv.cast (congrArg Boundary.Exit h)).injective
  systems g := by subst h; rfl
  fst x := by subst h; rfl
  snd x := by subst h; rfl

/-- Reassociating an iterated graft is an exit-renaming register relabelling. -/
def canonRel_graftAssocSpace (B : Boundary P) (C : B.Exit → Boundary P)
    (D : (B.graft C).Exit → Boundary P) :
    CanonRel (graftAssocSpace B C D) where
  exits := graftAssocExitEquiv B C D
  exits_inj := (graftAssocExitEquiv B C D).injective
  systems g := by
    rw [← (Boundary.graftExitEquiv B (graftAssocBoundary B C D)).symm_apply_apply g]
    rw [graftAssocExitEquiv_apply, Boundary.system_graftExitEquiv_symm,
      Boundary.system_graftExitEquiv_symm]
    exact (Boundary.system_graftExitEquiv (C _)
      (fun f => D ((Boundary.graftExitEquiv B C).symm ⟨_, f⟩)) _).symm
  fst x := by
    obtain ⟨w, rfl⟩ :
        ∃ w, (Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm w = x :=
      ⟨Boundary.graftSpaceEquiv B (graftAssocBoundary B C D) x, Equiv.symm_apply_apply _ _⟩
    obtain ⟨e, z⟩ := w
    rw [graftAssocSpace_apply, Boundary.graftSpaceEquiv_symm_fst,
      Boundary.graftSpaceEquiv_symm_fst, graftAssocExitEquiv_apply,
      Boundary.graftSpaceEquiv_apply]
  snd x := by
    obtain ⟨w, rfl⟩ :
        ∃ w, (Boundary.graftSpaceEquiv B (graftAssocBoundary B C D)).symm w = x :=
      ⟨Boundary.graftSpaceEquiv B (graftAssocBoundary B C D) x, Equiv.symm_apply_apply _ _⟩
    obtain ⟨e, z⟩ := w
    rw [graftAssocSpace_apply]
    refine (Boundary.graftSpaceEquiv_symm_snd_heq (B.graft C) D _ _).trans ?_
    refine HEq.trans ?_
      (Boundary.graftSpaceEquiv_symm_snd_heq B (graftAssocBoundary B C D) e z).symm
    rw [Boundary.graftSpaceEquiv_apply]
    exact cast_heq _ _

/-- Reassociating an iterated graft through a boundary identification is an exit-renaming
register relabelling. -/
def canonRel_graftAssocSpaceCast (B : Boundary P) (C : B.Exit → Boundary P)
    {Bz : Boundary P} (hY : B.graft C = Bz) (D : Bz.Exit → Boundary P) :
    CanonRel (graftAssocSpaceCast B C hY D) := by
  subst hY
  exact canonRel_graftAssocSpace B C D

/-- Grafting an exit-indexed family of exit-renaming register relabellings gives one. -/
def canonRel_graftSpaceRelabel (B : Boundary P) (C₁ C₂ : B.Exit → Boundary P)
    (theta : ∀ e, (C₁ e).space ≃ (C₂ e).space)
    (htheta : ∀ e, CanonRel (theta e)) :
    CanonRel (graftSpaceRelabel B C₁ C₂ theta) where
  exits g := (Boundary.graftExitEquiv B C₂).symm
    ⟨(Boundary.graftExitEquiv B C₁ g).1,
      (htheta _).exits (Boundary.graftExitEquiv B C₁ g).2⟩
  exits_inj := by
    intro g g' hgg
    refine (Boundary.graftExitEquiv B C₁).injective ?_
    exact sigma_fibre_map_inj (fun e => (htheta e).exits)
      (fun e => (htheta e).exits_inj)
      (Boundary.graftExitEquiv B C₁ g) (Boundary.graftExitEquiv B C₁ g')
      ((Boundary.graftExitEquiv B C₂).symm.injective hgg)
  systems g := by
    refine ((Boundary.system_graftExitEquiv_symm B C₂
      ⟨(Boundary.graftExitEquiv B C₁ g).1,
        (htheta _).exits (Boundary.graftExitEquiv B C₁ g).2⟩).trans ?_)
    exact ((htheta (Boundary.graftExitEquiv B C₁ g).1).systems
      (Boundary.graftExitEquiv B C₁ g).2).trans
      (Boundary.system_graftExitEquiv B C₁ g).symm
  fst x := by
    rw [graftSpaceRelabel_apply, Boundary.graftSpaceEquiv_symm_fst]
    refine congrArg (Boundary.graftExitEquiv B C₂).symm (congrArg (Sigma.mk _) ?_)
    exact (htheta (Boundary.graftExitEquiv B C₁ x.1).1).fst _
  snd x := by
    rw [graftSpaceRelabel_apply]
    refine (Boundary.graftSpaceEquiv_symm_snd_heq B C₂ _ _).trans ?_
    refine ((htheta (Boundary.graftExitEquiv B C₁ x.1).1).snd _).trans ?_
    exact cast_heq _ _

/-! ## The key-graded resource transport -/

/-- **The boundary-native ideal key resource is transported by a key-graded output map.**

`V` sends the complete output space of `B₂` into that of `B₁`, carrying complete public exits by
the injective map `F` (`hfst`) and the two ordered key coordinates by one common bijection `kappa`
(`hk1`, `hk2`).  The residual coordinate of the target layout is a subsingleton (`hres₁`), so `V`
is a morphism of boundary key layouts and `BoundaryKeyLayout.Hom.ideal_apply` applies; that is the
general form, with an arbitrary map of residual coordinates.

Then the `B₁`-resource read through `V` is the `B₂`-resource of the pulled-back operator.  Every
complete public exit and both ordered keys are retained; no state, positivity or reachability
hypothesis is used. -/
theorem ideal_transport_of_keys {B₁ B₂ : Boundary P}
    (L₁ : BoundaryKeyLayout B₁) (L₂ : BoundaryKeyLayout B₂)
    (V : B₂.space → B₁.space) (F : B₂.Exit → B₁.Exit) (hF : Function.Injective F)
    (kappa : ∀ e : B₂.Exit, (L₂.disposition e).Key ≃ (L₁.disposition (F e)).Key)
    (hres₁ : ∀ (f : B₁.Exit) (u v : L₁.Residual f), u = v)
    (hfst : ∀ x : B₂.space, (V x).1 = F x.1)
    (hk1 : ∀ x : B₂.space,
      (L₁.coordinates (V x).1 (V x).2).1 ≍ kappa x.1 (L₂.coordinates x.1 x.2).1)
    (hk2 : ∀ x : B₂.space,
      (L₁.coordinates (V x).1 (V x).2).2.1 ≍ kappa x.1 (L₂.coordinates x.1 x.2).2.1)
    (rho : TypedLOCC.Op B₁.space) (x y : B₂.space) :
    L₁.ideal rho (V x) (V y) = L₂.ideal (rho.submatrix V V) x y := by
  refine BoundaryKeyLayout.Hom.ideal_apply
    { toFun := V
      exit := F
      exit_injective := hF
      key := kappa
      residual := fun f _ => (L₁.nonemptyResidual (F f)).some
      apply_coordinates_symm' := ?_ } rho x y
  rintro e ⟨a, b, u⟩
  have h1 := hfst (⟨e, (L₂.coordinates e).symm (a, b, u)⟩ : B₂.space)
  have h2 := hk1 (⟨e, (L₂.coordinates e).symm (a, b, u)⟩ : B₂.space)
  have h3 := hk2 (⟨e, (L₂.coordinates e).symm (a, b, u)⟩ : B₂.space)
  simp only [Equiv.apply_symm_apply] at h2 h3
  refine Sigma.ext h1 ?_
  generalize V (⟨e, (L₂.coordinates e).symm (a, b, u)⟩ : B₂.space) = vx at h1 h2 h3 ⊢
  obtain ⟨e', q⟩ := vx
  obtain rfl : e' = F e := h1
  refine heq_of_eq ((L₁.coordinates (F e)).injective ?_)
  rw [Equiv.apply_symm_apply]
  exact Prod.ext (eq_of_heq h2) (Prod.ext (eq_of_heq h3) (hres₁ _ _ _))

/-- Operator form of `ideal_transport_of_keys` along an output relabelling. -/
theorem ideal_reindexOp_of_keys {B₁ B₂ : Boundary P}
    (L₁ : BoundaryKeyLayout B₁) (L₂ : BoundaryKeyLayout B₂)
    (V : B₂.space ≃ B₁.space) (F : B₂.Exit → B₁.Exit) (hF : Function.Injective F)
    (kappa : ∀ e : B₂.Exit, (L₂.disposition e).Key ≃ (L₁.disposition (F e)).Key)
    (hres₁ : ∀ (f : B₁.Exit) (u v : L₁.Residual f), u = v)
    (hfst : ∀ x : B₂.space, (V x).1 = F x.1)
    (hk1 : ∀ x : B₂.space,
      (L₁.coordinates (V x).1 (V x).2).1 ≍ kappa x.1 (L₂.coordinates x.1 x.2).1)
    (hk2 : ∀ x : B₂.space,
      (L₁.coordinates (V x).1 (V x).2).2.1 ≍ kappa x.1 (L₂.coordinates x.1 x.2).2.1)
    (rho : TypedLOCC.Op B₁.space) :
    L₂.ideal (reindexOp V.symm rho) = reindexOp V.symm (L₁.ideal rho) := by
  ext x y
  change L₂.ideal ((rho.submatrix V V)) x y = (L₁.ideal rho) (V x) (V y)
  exact (ideal_transport_of_keys L₁ L₂ (V : B₂.space → B₁.space) F hF kappa
    hres₁ hfst hk1 hk2 rho x y).symm

end TypedLOCC
