import QCryptLean.LOCC.Typed.Program.BoundaryRelabel.Graft

/-!
# Announced and private nodes, and exit-graded relabellings

Fourth layer of the BoundaryRelabel family.

The first section transports an output relabelling of the continuations through one announced or
one private node.  `announceSpaceRelabel B₁ B₂ theta` is the announced-boundary relabelling built
from an arbitrary per-branch bijection `theta`; `reindexOp_announceSpaceRelabel_conj` says it
intertwines the two public-block inclusions, and `denote_announced_congr_cont_relabel` and
`denote_priv_congr_graded` are the resulting node congruences.  `denote_announced_congr_cont` and
`denote_priv_congr_channel` are the corresponding statements when the two continuations already
have the same output boundary.

The second section introduces the *exit-graded* relabelling `Graded B₁ B₂`: a bijection of
complete public exits together with, at each exit, a bijection of the selected joint registers.
These are exactly the relabellings that commute with exit-controlled continuations, so they give
the graft congruences `denote_graft_congr_graded` and `denote_graft_congr_graftRelabel`.  An
exit-respecting bijection of output spaces is exit graded (`Graded.ofExitMap`), and so is a
relabelling induced by an equality of boundaries (`castGraded`).

The last section reassociates a double graft with a *constant* middle boundary
(`graftAssocSpaceEquiv`, `denote_graft_graft`); this is the cast-free companion of the
`graftAssoc*` family of the Graft module.

Everything is protocol-independent: no protocol, key layout, security notion or norm estimate
occurs.
-/

open scoped Matrix BigOperators

noncomputable section

namespace TypedLOCC.BoundaryRelabel

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## Announced and private nodes -/

/-- Diagonal public block of an announced-boundary inclusion. -/
private theorem conj_publicIncl_same {Y : Type} [Fintype Y] [DecidableEq Y]
    (C : Y → Boundary P) (y : Y) (M : TypedLOCC.Op (C y).space)
    (ep eq' : (C y).Exit)
    (ap : ((C y).system ep).total) (aq : ((C y).system eq').total) :
    matrixConjLinear (Boundary.publicInclKraus C y) M
        ⟨⟨y, ep⟩, ap⟩ ⟨⟨y, eq'⟩, aq⟩ = M ⟨ep, ap⟩ ⟨eq', aq⟩ := by
  classical
  simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Boundary.publicInclKraus_apply,
    Boundary.publicSpaceEquiv_apply, Sigma.mk.injEq, heq_eq_eq, true_and]
  rw [Finset.sum_eq_single (⟨eq', aq⟩ : (C y).space)]
  · rw [Finset.sum_eq_single (⟨ep, ap⟩ : (C y).space)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Off-diagonal public blocks of an announced-boundary inclusion vanish. -/
private theorem conj_publicIncl_ne {Y : Type} [Fintype Y] [DecidableEq Y]
    (C : Y → Boundary P) (y : Y) (M : TypedLOCC.Op (C y).space)
    (p q : (Boundary.announce Y C).space)
    (h : p.1.1 ≠ y ∨ q.1.1 ≠ y) :
    matrixConjLinear (Boundary.publicInclKraus C y) M p q = 0 := by
  classical
  simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rcases h with h | h
  · apply Finset.sum_eq_zero
    intro i _
    have hz : (∑ j, Boundary.publicInclKraus C y p j * M j i) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [Boundary.publicInclKraus_apply_eq_zero_of_fst_ne C h j]
      simp
    rw [hz]
    simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [Boundary.publicInclKraus_apply_eq_zero_of_fst_ne C h i]
    simp

/-- Relabel the continuation output spaces of an announced boundary. -/
def announceSpaceRelabel {Pub : Type} [Fintype Pub] [DecidableEq Pub]
    (B₁ B₂ : Pub → Boundary P) (theta : ∀ y, (B₁ y).space ≃ (B₂ y).space) :
    (Boundary.announce Pub B₁).space ≃ (Boundary.announce Pub B₂).space :=
  (Boundary.publicSpaceEquiv B₁).trans
    ((Equiv.sigmaCongrRight theta).trans (Boundary.publicSpaceEquiv B₂).symm)

/-- The induced announced-boundary relabelling intertwines the two public-block inclusions. -/
theorem reindexOp_announceSpaceRelabel_conj {Pub : Type} [Fintype Pub] [DecidableEq Pub]
    (B₁ B₂ : Pub → Boundary P) (theta : ∀ y, (B₁ y).space ≃ (B₂ y).space)
    (y : Pub) (M : TypedLOCC.Op (B₁ y).space) :
    reindexOp (announceSpaceRelabel B₁ B₂ theta)
        (matrixConjLinear (Boundary.publicInclKraus B₁ y) M) =
      matrixConjLinear (Boundary.publicInclKraus B₂ y) (reindexOp (theta y) M) := by
  classical
  ext p q
  have hsymm (x : (Boundary.announce Pub B₂).space) :
      (announceSpaceRelabel B₁ B₂ theta).symm x =
        (⟨⟨x.1.1, ((theta x.1.1).symm ⟨x.1.2, x.2⟩).1⟩,
          ((theta x.1.1).symm ⟨x.1.2, x.2⟩).2⟩ :
            (Boundary.announce Pub B₁).space) := rfl
  change matrixConjLinear (Boundary.publicInclKraus B₁ y) M
      ((announceSpaceRelabel B₁ B₂ theta).symm p)
      ((announceSpaceRelabel B₁ B₂ theta).symm q) = _
  obtain ⟨⟨yp, ep⟩, ap⟩ := p
  obtain ⟨⟨yq, eq'⟩, aq⟩ := q
  by_cases hp : yp = y
  · subst hp
    by_cases hq : yq = yp
    · subst hq
      rw [hsymm, hsymm]
      dsimp only
      rw [conj_publicIncl_same, conj_publicIncl_same]
      simp [reindexOp]
    · rw [conj_publicIncl_ne B₁ yp _ _ _ (Or.inr (by
        rw [hsymm]; exact hq)),
        conj_publicIncl_ne B₂ yp _ _ _ (Or.inr hq)]
  · rw [conj_publicIncl_ne B₁ y _ _ _ (Or.inl (by
      rw [hsymm]; exact hp)),
      conj_publicIncl_ne B₂ y _ _ _ (Or.inl hp)]

/-- Transport an output relabelling of the continuations through one announced node. -/
theorem denote_announced_congr_cont_relabel
    {R : MultipartiteSystem P} {Pub : Type} [Fintype Pub] [DecidableEq Pub]
    {B₁ B₂ : Pub → Boundary P}
    (A : AnnouncedAction R Pub)
    (k₁ : ∀ y, Program (A.out y) (B₁ y)) (k₂ : ∀ y, Program (A.out y) (B₂ y))
    (theta : ∀ y, (B₁ y).space ≃ (B₂ y).space)
    (h : ∀ y sigma, (k₂ y).denote sigma = reindexOp (theta y) ((k₁ y).denote sigma))
    (rho : TypedLOCC.Op R.total) :
    (A.then k₂).denote rho =
      reindexOp (announceSpaceRelabel B₁ B₂ theta) ((A.then k₁).denote rho) := by
  change (Program.announced A k₂).denote rho =
    reindexOp _ ((Program.announced A k₁).denote rho)
  rw [Program.denote_announced_eq_sum_liftedOperation,
    Program.denote_announced_eq_sum_liftedOperation]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [h (A.announce o) (A.liftedOperation o rho),
    reindexOp_announceSpaceRelabel_conj]

/-- **Private-node congruence along an output relabelling.**  The private action is unchanged. -/
theorem denote_priv_congr_graded {R : MultipartiteSystem P} {B₁ B₂ : Boundary P}
    (A : PrivateAction R) (k₁ : Program A.out B₁) (k₂ : Program A.out B₂)
    (Theta : B₁.space ≃ B₂.space)
    (h : ∀ sigma, k₂.denote sigma = reindexOp Theta (k₁.denote sigma))
    (rho : TypedLOCC.Op R.total) :
    (A.then k₂).denote rho = reindexOp Theta ((A.then k₁).denote rho) := by
  change (Program.priv A k₂).denote rho = reindexOp Theta ((Program.priv A k₁).denote rho)
  rw [Program.denote_priv_eq_sum_liftedOperation,
    Program.denote_priv_eq_sum_liftedOperation]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  exact Finset.sum_congr rfl fun o _ => h (A.liftedOperation o rho)

/-- Replacing the continuations of one announced node by channel-equal continuations does not
change the node's denotation. -/
theorem denote_announced_congr_cont
    {R : MultipartiteSystem P} {Pub : Type} [Fintype Pub] [DecidableEq Pub]
    {B : Pub → Boundary P}
    (A : AnnouncedAction R Pub)
    (k k' : ∀ y, Program (A.out y) (B y))
    (h : ∀ y sigma, (k y).denote sigma = (k' y).denote sigma)
    (rho : TypedLOCC.Op R.total) :
    (A.then k).denote rho = (A.then k').denote rho := by
  change (Program.announced A k).denote rho = (Program.announced A k').denote rho
  rw [Program.denote_announced_eq_sum_liftedOperation,
    Program.denote_announced_eq_sum_liftedOperation]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  exact congrArg _ (h (A.announce o) (A.liftedOperation o rho))

/-- Two private nodes with heterogeneously equal total lifted channels and continuation functions
have the same denotation. No state, positivity or classicality premise is used. -/
theorem denote_priv_congr_channel {R : MultipartiteSystem P} {B : Boundary P}
    (A A' : PrivateAction R) (k : Program A.out B) (k' : Program A'.out B)
    (hchannel : ∀ rho : TypedLOCC.Op R.total,
      HEq ((∑ o, A.liftedOperation o) rho) ((∑ o, A'.liftedOperation o) rho))
    (hcont : HEq (⇑k.denote) (⇑k'.denote))
    (rho : TypedLOCC.Op R.total) :
    (A.then k).denote rho = (A'.then k').denote rho := by
  have hA : (A.then k).denote rho = k.denote ((∑ o, A.liftedOperation o) rho) := by
    change (Program.priv A k).denote rho = _
    rw [Program.denote_priv_eq_sum_liftedOperation]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  have hA' : (A'.then k').denote rho = k'.denote ((∑ o, A'.liftedOperation o) rho) := by
    change (Program.priv A' k').denote rho = _
    rw [Program.denote_priv_eq_sum_liftedOperation]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  rw [hA, hA']
  exact congr_heq hcont (hchannel rho)

/-- An announced-node relabelling built from casts is the corresponding cast. -/
theorem announceSpaceRelabel_cast {Pub : Type} [Fintype Pub] [DecidableEq Pub]
    (B₁ B₂ : Pub → Boundary P) (h : ∀ y, B₁ y = B₂ y)
    (hann : Boundary.announce Pub B₁ = Boundary.announce Pub B₂) :
    announceSpaceRelabel B₁ B₂ (fun y => Equiv.cast (congrArg Boundary.space (h y))) =
      Equiv.cast (congrArg Boundary.space hann) := by
  have hfun : B₁ = B₂ := funext h
  subst hfun
  refine Equiv.ext fun x => ?_
  change (Boundary.publicSpaceEquiv B₁).symm (Boundary.publicSpaceEquiv B₁ x) = x
  exact (Boundary.publicSpaceEquiv B₁).symm_apply_apply x

/-! ## Exit-graded relabellings -/

section Graded

variable {B₁ B₂ B₃ : Boundary P}

/-- An *exit-graded* relabelling of boundary output spaces: a bijection of complete public exits
together with a register bijection at each exit. -/
structure Graded (B₁ B₂ : Boundary P) where
  /-- The induced bijection of complete public exits. -/
  exits : B₁.Exit ≃ B₂.Exit
  /-- At each complete public exit, the induced bijection of selected joint registers. -/
  systems : ∀ e : B₁.Exit, ((B₁.system e).total ≃ (B₂.system (exits e)).total)

namespace Graded

/-- The output-space equivalence determined by an exit-graded relabelling. -/
def space (G : Graded B₁ B₂) : B₁.space ≃ B₂.space :=
  Equiv.sigmaCongr G.exits G.systems

@[simp] theorem space_apply (G : Graded B₁ B₂) (e : B₁.Exit) (q : (B₁.system e).total) :
    G.space ⟨e, q⟩ = ⟨G.exits e, G.systems e q⟩ := by
  simp [space, Equiv.sigmaCongr]

theorem space_symm_space (G : Graded B₁ B₂) (e : B₁.Exit) (q : (B₁.system e).total) :
    G.space.symm ⟨G.exits e, G.systems e q⟩ = ⟨e, q⟩ := by
  rw [← space_apply]
  exact G.space.symm_apply_apply _

/-- Every point of the target boundary space has an exit-graded preimage description. -/
theorem exists_point (G : Graded B₁ B₂) (x : B₂.space) :
    ∃ (e : B₁.Exit) (q : (B₁.system e).total), x = ⟨G.exits e, G.systems e q⟩ := by
  refine ⟨(G.space.symm x).1, (G.space.symm x).2, ?_⟩
  rw [← space_apply]
  exact (G.space.apply_symm_apply x).symm

/-- The identity relabelling. -/
def refl (B : Boundary P) : Graded B B where
  exits := Equiv.refl _
  systems _ := Equiv.refl _

@[simp] theorem refl_space (B : Boundary P) : (Graded.refl B).space = Equiv.refl B.space := by
  apply Equiv.ext
  intro x
  rcases x with ⟨e, q⟩
  simp [space_apply, Graded.refl]

/-- Compose two exit-graded relabellings. -/
def trans (G : Graded B₁ B₂) (H : Graded B₂ B₃) : Graded B₁ B₃ where
  exits := G.exits.trans H.exits
  systems e := (G.systems e).trans (H.systems (G.exits e))

@[simp] theorem trans_space (G : Graded B₁ B₂) (H : Graded B₂ B₃) :
    (G.trans H).space = G.space.trans H.space := by
  apply Equiv.ext
  intro x
  rcases x with ⟨e, q⟩
  simp [space_apply, trans]

end Graded

/-- An exit-graded relabelling of the branches of an announced boundary induces one of the
announced boundaries. -/
def announceGraded {Y : Type} [Fintype Y] [DecidableEq Y]
    {C₁ C₂ : Y → Boundary P} (G : ∀ y, Graded (C₁ y) (C₂ y)) :
    Graded (Boundary.announce Y C₁) (Boundary.announce Y C₂) where
  exits := Equiv.sigmaCongrRight fun y => (G y).exits
  systems e := (G e.1).systems e.2

@[simp] theorem announceGraded_space_apply {Y : Type} [Fintype Y] [DecidableEq Y]
    {C₁ C₂ : Y → Boundary P} (G : ∀ y, Graded (C₁ y) (C₂ y))
    (x : (Boundary.announce Y C₁).space) :
    (announceGraded G).space x =
      ⟨⟨x.1.1, (G x.1.1).exits x.1.2⟩, (G x.1.1).systems x.1.2 x.2⟩ := by
  rcases x with ⟨⟨y, e⟩, q⟩
  rw [Graded.space_apply]
  rfl

/-- The general announced-node relabelling built from exit-graded branch data is the induced
exit-graded relabelling of the announced boundaries. -/
theorem announceSpaceRelabel_eq_announceGraded {Pub : Type} [Fintype Pub] [DecidableEq Pub]
    {C₁ C₂ : Pub → Boundary P} (G : ∀ y, Graded (C₁ y) (C₂ y)) :
    announceSpaceRelabel C₁ C₂ (fun y => (G y).space) = (announceGraded G).space := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨y, e⟩, q⟩ := x
  rw [Graded.space_apply]
  rfl

/-! ### Recovering the graded data from an exit-respecting equivalence -/

/-- The fibre of a dependent sum over one index. -/
def sigmaFibre {ι : Type} {beta : ι → Type} (i : ι) :
    beta i ≃ {x : Σ j : ι, beta j // x.1 = i} where
  toFun q := ⟨⟨i, q⟩, rfl⟩
  invFun x := cast (congrArg beta x.2) x.1.2
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨j, q⟩, hj⟩
    subst hj
    rfl

/-- An equivalence of dependent sums which respects the index restricts to every fibre. -/
def sigmaFibreEquiv {ι ι' : Type} {beta : ι → Type} {beta' : ι' → Type}
    (Theta : (Σ j : ι, beta j) ≃ (Σ j : ι', beta' j)) (ThetaE : ι ≃ ι')
    (h : ∀ x, (Theta x).1 = ThetaE x.1) (i : ι) :
    beta i ≃ beta' (ThetaE i) :=
  (sigmaFibre i).trans
    ((Equiv.subtypeEquiv Theta (fun x => by
      rw [h x]
      exact ⟨fun hh => by rw [hh], fun hh => ThetaE.injective hh⟩)).trans
      (sigmaFibre (ThetaE i)).symm)

theorem sigmaFibreEquiv_apply {ι ι' : Type} {beta : ι → Type} {beta' : ι' → Type}
    (Theta : (Σ j : ι, beta j) ≃ (Σ j : ι', beta' j)) (ThetaE : ι ≃ ι')
    (h : ∀ x, (Theta x).1 = ThetaE x.1) (i : ι) (q : beta i) :
    Theta ⟨i, q⟩ = ⟨ThetaE i, sigmaFibreEquiv Theta ThetaE h i q⟩ := by
  have hfst : (Theta ⟨i, q⟩).1 = ThetaE i := h ⟨i, q⟩
  refine Sigma.ext hfst ?_
  simp only [sigmaFibreEquiv, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    sigmaFibre, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  exact (cast_heq _ _).symm

namespace Graded

/-- An exit-respecting equivalence of boundary output spaces is exit graded. -/
def ofExitMap (Theta : B₁.space ≃ B₂.space) (ThetaE : B₁.Exit ≃ B₂.Exit)
    (h : ∀ x : B₁.space, (Theta x).1 = ThetaE x.1) : Graded B₁ B₂ where
  exits := ThetaE
  systems := sigmaFibreEquiv Theta ThetaE h

@[simp] theorem ofExitMap_space (Theta : B₁.space ≃ B₂.space) (ThetaE : B₁.Exit ≃ B₂.Exit)
    (h : ∀ x : B₁.space, (Theta x).1 = ThetaE x.1) :
    (ofExitMap Theta ThetaE h).space = Theta := by
  apply Equiv.ext
  intro x
  rcases x with ⟨e, q⟩
  rw [space_apply]
  exact (sigmaFibreEquiv_apply Theta ThetaE h e q).symm

@[simp] theorem ofExitMap_exits (Theta : B₁.space ≃ B₂.space) (ThetaE : B₁.Exit ≃ B₂.Exit)
    (h : ∀ x : B₁.space, (Theta x).1 = ThetaE x.1) :
    (ofExitMap Theta ThetaE h).exits = ThetaE := rfl

end Graded

/-! ### Relabellings induced by a boundary equality -/

/-- The exit-graded relabelling induced by an equality of boundaries. -/
def castGraded {B₁ B₂ : Boundary P} (hB : B₁ = B₂) : Graded B₁ B₂ := by
  subst hB
  exact { exits := Equiv.refl _, systems := fun _ => Equiv.refl _ }

theorem castGraded_space {B₁ B₂ : Boundary P} (hB : B₁ = B₂) :
    (castGraded hB).space = Equiv.cast (congrArg Boundary.space hB) := by
  subst hB
  apply Equiv.ext
  intro x
  obtain ⟨e, q⟩ := x
  rw [Graded.space_apply]
  rfl

theorem castGraded_exits {B₁ B₂ : Boundary P} (hB : B₁ = B₂) :
    (castGraded hB).exits = Equiv.cast (congrArg Boundary.Exit hB) := by
  subst hB
  rfl

theorem castGraded_systems_refl {B : Boundary P} (e : B.Exit) :
    (castGraded (rfl : B = B)).systems e = Equiv.refl _ := rfl

/-! ### Exit blocks and grafts along an exit-graded relabelling -/

/-- An exit-graded relabelling transports exit blocks. -/
theorem exitBlock_reindexOp (G : Graded B₁ B₂) (rho : TypedLOCC.Op B₁.space)
    (e : B₁.Exit) :
    exitBlock B₂ (G.exits e) (reindexOp G.space rho) =
      reindexOp (G.systems e) (exitBlock B₁ e rho) := by
  ext u v
  obtain ⟨u', rfl⟩ : ∃ u', G.systems e u' = u := ⟨(G.systems e).symm u, by simp⟩
  obtain ⟨v', rfl⟩ : ∃ v', G.systems e v' = v := ⟨(G.systems e).symm v, by simp⟩
  rw [exitBlock_apply, reindexOp_apply, reindexOp_apply, exitBlock_apply,
    ← Graded.space_apply, ← Graded.space_apply, G.space.symm_apply_apply,
    G.space.symm_apply_apply]
  simp only [Equiv.symm_apply_apply]

/-- The relabelling of grafted output spaces induced by a base relabelling and an exit-indexed
family of continuation relabellings. -/
def graftRelabel {C₁ : B₁.Exit → Boundary P} {C₂ : B₂.Exit → Boundary P}
    (G : Graded B₁ B₂) (Hf : ∀ e : B₁.Exit, (C₁ e).space ≃ (C₂ (G.exits e)).space) :
    (B₁.graft C₁).space ≃ (B₂.graft C₂).space :=
  (Boundary.graftSpaceEquiv B₁ C₁).trans
    ((Equiv.sigmaCongr G.exits Hf).trans
      (Boundary.graftSpaceEquiv B₂ C₂).symm)

theorem graftRelabel_apply {C₁ : B₁.Exit → Boundary P} {C₂ : B₂.Exit → Boundary P}
    (G : Graded B₁ B₂) (Hf : ∀ e : B₁.Exit, (C₁ e).space ≃ (C₂ (G.exits e)).space)
    (e : B₁.Exit) (z : (C₁ e).space) :
    graftRelabel G Hf ((Boundary.graftSpaceEquiv B₁ C₁).symm ⟨e, z⟩) =
      (Boundary.graftSpaceEquiv B₂ C₂).symm ⟨G.exits e, Hf e z⟩ := by
  simp [graftRelabel, Equiv.sigmaCongr]

/-- **Graft congruence along an exit-graded relabelling, with an explicitly supplied output
relabelling of the graft.**

If two programs have the same channel up to an exit-graded output relabelling `G`, their attached
continuations agree up to per-exit relabellings `Hf`, and `Xi` is *any* output relabelling of the
two grafts which acts by `G` on the base exit and by `Hf` on the attached fibre, then the two
grafted programs have the same channel up to `Xi`.  Every public exit and every register
coordinate is retained. -/
theorem denote_graft_congr_graded {R : MultipartiteSystem P}
    (p₁ : Program R B₁) (p₂ : Program R B₂) (G : Graded B₁ B₂)
    (hp : ∀ rho, p₂.denote rho = reindexOp G.space (p₁.denote rho))
    {C₁ : B₁.Exit → Boundary P} {C₂ : B₂.Exit → Boundary P}
    (k₁ : ∀ e : B₁.Exit, Program (B₁.system e) (C₁ e))
    (k₂ : ∀ f : B₂.Exit, Program (B₂.system f) (C₂ f))
    (Hf : ∀ e : B₁.Exit, (C₁ e).space ≃ (C₂ (G.exits e)).space)
    (Xi : (B₁.graft C₁).space ≃ (B₂.graft C₂).space)
    (hXi : ∀ (e : B₁.Exit) (z : (C₁ e).space),
      Xi ((Boundary.graftSpaceEquiv B₁ C₁).symm ⟨e, z⟩) =
        (Boundary.graftSpaceEquiv B₂ C₂).symm ⟨G.exits e, Hf e z⟩)
    (hk : ∀ (e : B₁.Exit) (sigma : TypedLOCC.Op (B₁.system e).total),
      (k₂ (G.exits e)).denote (reindexOp (G.systems e) sigma) =
        reindexOp (Hf e) ((k₁ e).denote sigma))
    (rho : TypedLOCC.Op R.total) :
    (p₂.graft k₂).denote rho = reindexOp Xi ((p₁.graft k₁).denote rho) := by
  classical
  rw [Program.denote_graft, Program.denote_graft]
  ext x y
  obtain ⟨f, a, rfl⟩ : ∃ (f : B₂.Exit) (a : (C₂ f).space),
      x = (Boundary.graftSpaceEquiv B₂ C₂).symm ⟨f, a⟩ :=
    ⟨(Boundary.graftSpaceEquiv B₂ C₂ x).1, (Boundary.graftSpaceEquiv B₂ C₂ x).2,
      by rw [Sigma.eta, Equiv.symm_apply_apply]⟩
  obtain ⟨f', a', rfl⟩ : ∃ (f' : B₂.Exit) (a' : (C₂ f').space),
      y = (Boundary.graftSpaceEquiv B₂ C₂).symm ⟨f', a'⟩ :=
    ⟨(Boundary.graftSpaceEquiv B₂ C₂ y).1, (Boundary.graftSpaceEquiv B₂ C₂ y).2,
      by rw [Sigma.eta, Equiv.symm_apply_apply]⟩
  obtain ⟨e, rfl⟩ : ∃ e, G.exits e = f := ⟨G.exits.symm f, by simp⟩
  obtain ⟨e', rfl⟩ : ∃ e', G.exits e' = f' := ⟨G.exits.symm f', by simp⟩
  obtain ⟨z, rfl⟩ : ∃ z, Hf e z = a := ⟨(Hf e).symm a, by simp⟩
  obtain ⟨z', rfl⟩ : ∃ z', Hf e' z' = a' := ⟨(Hf e').symm a', by simp⟩
  have hx : Xi.symm
      ((Boundary.graftSpaceEquiv B₂ C₂).symm ⟨G.exits e, Hf e z⟩) =
        (Boundary.graftSpaceEquiv B₁ C₁).symm ⟨e, z⟩ := by
    rw [← hXi e z, Xi.symm_apply_apply]
  have hy : Xi.symm
      ((Boundary.graftSpaceEquiv B₂ C₂).symm ⟨G.exits e', Hf e' z'⟩) =
        (Boundary.graftSpaceEquiv B₁ C₁).symm ⟨e', z'⟩ := by
    rw [← hXi e' z', Xi.symm_apply_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, reindexOp_apply, hx, hy]
  by_cases hee : e = e'
  · subst hee
    rw [Program.controlledContinuation_sameExit, Program.controlledContinuation_sameExit]
    change (k₂ (G.exits e)).denote (exitBlock B₂ (G.exits e) (p₂.denote rho))
        (Hf e z) (Hf e z') =
      (k₁ e).denote (exitBlock B₁ e (p₁.denote rho)) z z'
    rw [hp rho, exitBlock_reindexOp G (p₁.denote rho) e, hk e, reindexOp_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · rw [Program.controlledContinuation_block_zero _ _ (fun h => hee (G.exits.injective h)),
      Program.controlledContinuation_block_zero _ _ hee]

/-- **Graft congruence along an exit-graded relabelling.**  If two programs have the same channel
up to an exit-graded output relabelling, and their attached continuations agree up to the
transported relabellings, then the two grafted programs have the same channel up to the induced
graft relabelling.  Every public exit and every register coordinate is retained. -/
theorem denote_graft_congr_graftRelabel {R : MultipartiteSystem P}
    (p₁ : Program R B₁) (p₂ : Program R B₂) (G : Graded B₁ B₂)
    (hp : ∀ rho, p₂.denote rho = reindexOp G.space (p₁.denote rho))
    {C₁ : B₁.Exit → Boundary P} {C₂ : B₂.Exit → Boundary P}
    (k₁ : ∀ e : B₁.Exit, Program (B₁.system e) (C₁ e))
    (k₂ : ∀ f : B₂.Exit, Program (B₂.system f) (C₂ f))
    (H : ∀ e : B₁.Exit, Graded (C₁ e) (C₂ (G.exits e)))
    (hk : ∀ (e : B₁.Exit) (sigma : TypedLOCC.Op (B₁.system e).total),
      (k₂ (G.exits e)).denote (reindexOp (G.systems e) sigma) =
        reindexOp (H e).space ((k₁ e).denote sigma))
    (rho : TypedLOCC.Op R.total) :
    (p₂.graft k₂).denote rho =
      reindexOp (graftRelabel G (fun e => (H e).space)) ((p₁.graft k₁).denote rho) :=
  denote_graft_congr_graded p₁ p₂ G hp k₁ k₂ (fun e => (H e).space)
    (graftRelabel G (fun e => (H e).space))
    (graftRelabel_apply G (fun e => (H e).space)) hk rho

/-! ### Announced nodes along an exit-graded relabelling -/

/-- The induced announced relabelling intertwines the two public-block inclusions. -/
theorem reindexOp_announceGraded_conj {Y : Type} [Fintype Y] [DecidableEq Y]
    {C₁ C₂ : Y → Boundary P} (G : ∀ y, Graded (C₁ y) (C₂ y))
    (y : Y) (M : TypedLOCC.Op (C₁ y).space) :
    reindexOp (announceGraded G).space
        (matrixConjLinear (Boundary.publicInclKraus C₁ y) M) =
      matrixConjLinear (Boundary.publicInclKraus C₂ y) (reindexOp (G y).space M) := by
  rw [← announceSpaceRelabel_eq_announceGraded G]
  exact reindexOp_announceSpaceRelabel_conj C₁ C₂ (fun y => (G y).space) y M

/-- **Announced-node congruence along an exit-graded relabelling.**  Only the continuations are
compared; the announced action and every public value are unchanged. -/
theorem denote_announced_congr_cont_graded {R : MultipartiteSystem P} {Y : Type} [Fintype Y]
    [DecidableEq Y]
    {C₁ C₂ : Y → Boundary P}
    (A : AnnouncedAction R Y)
    (k₁ : ∀ y, Program (A.out y) (C₁ y)) (k₂ : ∀ y, Program (A.out y) (C₂ y))
    (G : ∀ y, Graded (C₁ y) (C₂ y))
    (h : ∀ y sigma, (k₂ y).denote sigma = reindexOp (G y).space ((k₁ y).denote sigma))
    (rho : TypedLOCC.Op R.total) :
    (A.then k₂).denote rho = reindexOp (announceGraded G).space ((A.then k₁).denote rho) := by
  rw [← announceSpaceRelabel_eq_announceGraded G]
  exact denote_announced_congr_cont_relabel A k₁ k₂ (fun y => (G y).space) h rho

end Graded

/-! ## Double grafts with a constant middle boundary

When the first graft attaches the *same* boundary `C` at every complete public exit, the
reassociation of the double graft is cast-free: it is built from `announceSpaceRelabel` by
recursion on the base boundary. -/

/-- Transport an exit-controlled continuation of a **constant** attached boundary to the complete
public exits of the graft itself.  The recursion is cast-free. -/
def atGraftExit {C : Boundary P} {Dfam : C.Exit → Boundary P}
    (c : ∀ f : C.Exit, Program (C.system f) (Dfam f)) (B : Boundary P) :
    ∀ g : (B.graft (fun _ => C)).Exit,
      Program ((B.graft (fun _ => C)).system g)
        (Dfam (Boundary.graftExitEquiv B (fun _ => C) g).2) :=
  match B with
  | @Boundary.leaf _ _ _ _ => fun g => c g
  | @Boundary.announce _ _ _ _ _ _ nxt => fun g => atGraftExit c (nxt g.1) g.2

/-- Reassociating a double graft with a constant middle boundary is an explicit output
relabelling. -/
def graftAssocSpaceEquiv (C : Boundary P) (Dfam : C.Exit → Boundary P) (B : Boundary P) :
    ((B.graft (fun _ => C)).graft
        (fun g => Dfam (Boundary.graftExitEquiv B (fun _ => C) g).2)).space ≃
      (B.graft (fun _ => C.graft Dfam)).space :=
  match B with
  | @Boundary.leaf _ _ _ _ => Equiv.refl _
  | @Boundary.announce _ _ _ _ _ _ nxt =>
      announceSpaceRelabel _ _ fun y => graftAssocSpaceEquiv C Dfam (nxt y)

/-- **Grafting twice is grafting the reassociated continuation.**

Both continuations are arbitrary; the base program is arbitrary; the identity is pointwise in the
input operator and retains every public cell of both grafts. -/
theorem denote_graft_graft {C : Boundary P} {Dfam : C.Exit → Boundary P}
    (c : ∀ f : C.Exit, Program (C.system f) (Dfam f)) :
    ∀ {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
      (k : ∀ e : B.Exit, Program (B.system e) C)
      (rho : TypedLOCC.Op R.total),
      (p.graft (fun e => (k e).graft c)).denote rho =
        reindexOp (graftAssocSpaceEquiv C Dfam B)
          (((p.graft k).graft (atGraftExit c B)).denote rho) := by
  intro R B p
  induction p with
  | done =>
      intro k rho
      rfl
  | @announced R XX _ _ A Bf next ih =>
      intro k rho
      exact denote_announced_congr_cont_relabel A _ _
        (fun y => graftAssocSpaceEquiv C Dfam (Bf y))
        (fun y sigma => ih y (fun e => k ⟨y, e⟩) sigma) rho
  | @priv R Bf A next ih =>
      intro k rho
      exact denote_priv_congr_graded A _ _
        (graftAssocSpaceEquiv C Dfam Bf)
        (fun sigma => ih k sigma) rho

end TypedLOCC.BoundaryRelabel
