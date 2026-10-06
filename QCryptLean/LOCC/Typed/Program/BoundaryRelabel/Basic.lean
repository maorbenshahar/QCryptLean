import QCryptLean.LOCC.Typed.Program.GraftDenotation
import QCryptLean.LOCC.Typed.Program.Uniform
import QCryptLean.LOCC.Typed.Instrument.Classical

/-!
# Elementary boundary relabellings: registers, multipartite systems, exit blocks

This is the first layer of the BoundaryRelabel family.  It collects the elementary,
protocol-independent transport laws:

* the `reindexOp` calculus (identity, composition, both cancellation directions, and reading an
  intertwining relation in either direction);
* transports of a joint laboratory register along an equality of multipartite systems;
* the *exit block* `blockAt` of a complete public exit — what an exit-controlled continuation
  consumes — and its Kraus-sandwich presentation `exitBlock`;
* denotations of programs transported along equalities of the input multipartite system or the
  output boundary.

No protocol, key layout, security notion or norm estimate occurs anywhere in this file.
-/

open scoped Matrix BigOperators

noncomputable section

namespace TypedLOCC.BoundaryRelabel

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## Elementary register relabellings -/

theorem reindexOp_apply {HH HH' : Type} [Fintype HH] [DecidableEq HH]
    [Fintype HH'] [DecidableEq HH'] (e : HH ≃ HH') (M : TypedLOCC.Op HH) (a b : HH') :
    reindexOp e M a b = M (e.symm a) (e.symm b) := rfl

@[simp] theorem reindexOp_refl {HH : Type} [Fintype HH] [DecidableEq HH]
    (M : TypedLOCC.Op HH) : reindexOp (Equiv.refl HH) M = M := by
  ext a b
  rfl

/-- Composing two output reindexings. -/
theorem reindexOp_trans {HH HH' HH'' : Type} [Fintype HH] [DecidableEq HH]
    [Fintype HH'] [DecidableEq HH'] [Fintype HH''] [DecidableEq HH'']
    (e : HH ≃ HH') (f : HH' ≃ HH'') (M : TypedLOCC.Op HH) :
    reindexOp f (reindexOp e M) = reindexOp (e.trans f) M := rfl

/-- Reindexing along the identity bijection of a boundary space. -/
@[simp] theorem reindexOp_cast_rfl {Bx : Boundary P} (M : TypedLOCC.Op Bx.space) :
    reindexOp (Equiv.cast (congrArg Boundary.space (rfl : Bx = Bx))) M = M := by
  ext i j
  simp [reindexOp]

/-- Reindexing along the inverse of a bijection undoes reindexing along the bijection. -/
theorem reindexOp_symm_reindexOp {HH HH' : Type} [Fintype HH] [DecidableEq HH]
    [Fintype HH'] [DecidableEq HH'] (e : HH ≃ HH') (M : TypedLOCC.Op HH) :
    reindexOp e.symm (reindexOp e M) = M := by
  ext i j
  change M (e.symm (e i)) (e.symm (e j)) = M i j
  simp only [Equiv.symm_apply_apply]

/-- Reindexing along a bijection undoes reindexing along its inverse. -/
theorem reindexOp_reindexOp_symm {HH HH' : Type} [Fintype HH] [DecidableEq HH]
    [Fintype HH'] [DecidableEq HH'] (e : HH ≃ HH') (M : TypedLOCC.Op HH') :
    reindexOp e (reindexOp e.symm M) = M := by
  ext i j
  change M (e (e.symm i)) (e (e.symm j)) = M i j
  simp only [Equiv.apply_symm_apply]

/-- An intertwining relation for a register relabelling can be read in either direction. -/
theorem map_reindexOp_symm_of_reindexOp {HH HH' : Type} [Fintype HH] [DecidableEq HH]
    [Fintype HH'] [DecidableEq HH'] (e : HH ≃ HH')
    (F : TypedLOCC.Op HH → TypedLOCC.Op HH) (G : TypedLOCC.Op HH' → TypedLOCC.Op HH')
    (h : ∀ M, G (reindexOp e M) = reindexOp e (F M)) (rho : TypedLOCC.Op HH') :
    F (reindexOp e.symm rho) = reindexOp e.symm (G rho) := by
  have h1 := h (reindexOp e.symm rho)
  rw [reindexOp_reindexOp_symm] at h1
  rw [h1, reindexOp_symm_reindexOp]

/-! ## Multipartite system transports -/

/-- Two multipartite systems with the same register assignment are equal: the remaining fields are
`Fintype`, `DecidableEq` and `Nonempty` witnesses, all of which are subsingletons. -/
theorem system_eq_of_reg_eq {R S : MultipartiteSystem P} (h : R.reg = S.reg) : R = S := by
  cases R
  cases S
  cases h
  congr <;> (funext p; exact Subsingleton.elim _ _)

/-- Transport of a joint register along an equality of multipartite systems. -/
abbrev systemTotalCast {R R' : MultipartiteSystem P} (h : R = R') : R.total ≃ R'.total :=
  Equiv.cast (congrArg (fun S : MultipartiteSystem P => S.total) h)

theorem systemTotalCast_symm_heq {R R' : MultipartiteSystem P} (h : R = R') (q : R'.total) :
    (systemTotalCast h).symm q ≍ q := by
  subst h
  rfl

theorem systemTotalCast_heq {R R' : MultipartiteSystem P} (h : R = R') (q : R.total) :
    systemTotalCast h q ≍ q := by
  subst h
  rfl

theorem systemTotalCast_symm_symm {R₁ R₂ R₃ : MultipartiteSystem P} (h₁ : R₂ = R₁) (h₂ : R₃ = R₂)
    (q : R₁.total) :
    (systemTotalCast h₂).symm ((systemTotalCast h₁).symm q) = (systemTotalCast (h₂.trans h₁)).symm q
      := by
  subst h₁
  subst h₂
  rfl

/-- Registers of heterogeneously equal joint coordinates over equal multipartite systems. -/
theorem heq_apply_of_system_eq {R R' : MultipartiteSystem P} (h : R = R') {q : R.total} {q' :
    R'.total}
    (hq : q ≍ q') (p : P) : q p ≍ q' p := by
  subst h
  rw [eq_of_heq hq]

/-- The multipartite system of a leaf boundary named through a boundary equality. -/
theorem system_eq_of_boundary_eq_leaf {B : Boundary P} {R : MultipartiteSystem P} (h : B =
    Boundary.leaf R)
    (f : B.Exit) : B.system f = R := by
  subst h
  rfl

/-- A transported leaf-space equivalence is the leaf projection. -/
theorem leaf_cast_space_snd_heq {B : Boundary P} {R : MultipartiteSystem P} (hB : B = Boundary.leaf
    R)
    (hT : ((Boundary.leaf R).space ≃ R.total) = (B.space ≃ R.total)) (a : B.space) :
    (cast hT (Boundary.leafSpaceEquiv R)) a ≍ a.2 := by
  subst hB
  exact HEq.rfl

/-- Two one-element coordinate types carry heterogeneously equal elements. -/
theorem heq_of_unit_types {XX YY : Type} (hX : XX = Unit) (hY : YY = Unit) (x : XX) (y : YY) :
    x ≍ y := by
  subst hX
  subst hY
  exact heq_of_eq (Subsingleton.elim x y)

/-! ## Exit blocks -/

/-- The operator block of a complete public exit. -/
def blockAt (B : Boundary P) (e : B.Exit) (M : TypedLOCC.Op B.space) :
    TypedLOCC.Op (B.system e).total :=
  Matrix.of fun q q' => M ⟨e, q⟩ ⟨e, q'⟩

/-- The exit-Kraus sandwich used by `controlledContinuation_sameExit` is exit-block extraction. -/
theorem exitKraus_sandwich_eq_blockAt (B : Boundary P) (e : B.Exit)
    (M : TypedLOCC.Op B.space) :
    (Boundary.exitKraus B e).conjTranspose * M * Boundary.exitKraus B e = blockAt B e M := by
  ext q q'
  simp [Matrix.mul_apply, Boundary.exitKraus_apply, blockAt, Matrix.conjTranspose_apply,
    Finset.sum_ite_eq']

/-- The operator block of one complete public exit, written as a Kraus sandwich. -/
def exitBlock (B : Boundary P) (e : B.Exit) (rho : TypedLOCC.Op B.space) :
    TypedLOCC.Op ((B.system e).total) :=
  (Boundary.exitKraus B e)ᴴ * rho * Boundary.exitKraus B e

@[simp] theorem exitBlock_apply (B : Boundary P) (e : B.Exit)
    (rho : TypedLOCC.Op B.space) (a b : (B.system e).total) :
    exitBlock B e rho a b = rho ⟨e, a⟩ ⟨e, b⟩ := by
  simp [exitBlock, Matrix.mul_apply, Boundary.exitKraus, sigmaInclKraus]

/-- The two presentations of the exit block agree. -/
theorem exitBlock_eq_blockAt (B : Boundary P) (e : B.Exit) (M : TypedLOCC.Op B.space) :
    exitBlock B e M = blockAt B e M :=
  exitKraus_sandwich_eq_blockAt B e M

/-- Entrywise form of `Program.controlledContinuation_sameExit`. -/
theorem cc_sameExit {B : Boundary P} {C : B.Exit → Boundary P}
    (k : ∀ e : B.Exit, Program (B.system e) (C e)) (M : TypedLOCC.Op B.space)
    (e : B.Exit) (a b : (C e).space) :
    Program.controlledContinuation k M
        ((Boundary.graftSpaceEquiv B C).symm ⟨e, a⟩)
        ((Boundary.graftSpaceEquiv B C).symm ⟨e, b⟩) =
      (k e).denote (blockAt B e M) a b := by
  rw [Program.controlledContinuation_sameExit, exitKraus_sandwich_eq_blockAt]

/-! ## Programs transported along multipartite system and boundary equalities -/

/-- Transport a program along an equality of its input multipartite system. -/
theorem denote_systemCast {R R' : MultipartiteSystem P} (h : R = R') {Bd : Boundary P} (p : Program
    R Bd)
    (N : TypedLOCC.Op R'.total) (u u' : Bd.space) :
    (h ▸ p : Program R' Bd).denote N u u' =
      p.denote (N.submatrix (Equiv.cast (congrArg (fun S : MultipartiteSystem P => S.total) h))
        (Equiv.cast (congrArg (fun S : MultipartiteSystem P => S.total) h))) u u' := by
  subst h
  simp

/-- Transporting a program along an equality of its input multipartite system does not change it. -/
theorem systemTransport_heq {R R' : MultipartiteSystem P} (h : R = R') {Bd : Boundary P} (p :
    Program R Bd) :
    (h ▸ p : Program R' Bd) ≍ p := by
  subst h
  rfl

/-- Denotations of heterogeneously equal programs agree after transporting the input. -/
theorem denote_of_heq {R₁ R₂ : MultipartiteSystem P} {D : Boundary P} (p : Program R₁ D) (q :
    Program R₂ D)
    (h : R₁ = R₂) (hpq : p ≍ q) (sigma : TypedLOCC.Op R₁.total) (a b : D.space) :
    p.denote sigma a b =
      q.denote (sigma.submatrix
        (Equiv.cast (congrArg (fun S : MultipartiteSystem P => S.total) h)).symm
        (Equiv.cast (congrArg (fun S : MultipartiteSystem P => S.total) h)).symm) a b := by
  subst h
  rw [eq_of_heq hpq]
  congr 1

/-- A program transported to a uniform-boundary exit is the original program. -/
theorem atUniformExit_heq {S : MultipartiteSystem P} {B : Boundary P} (p : Program S B) :
    ∀ (T : TList) (e : (Boundary.uniform S T).Exit),
      Program.atUniformExit p T e ≍ p := by
  intro T
  induction T with
  | nil => intro e; exact HEq.rfl
  | @cons Yc instY decY T ih => intro e; exact ih e.2

/-- Programs into a subsingleton output boundary all have the same channel. -/
theorem denote_eq_singleton_cast {R : MultipartiteSystem P}
    {D₁ D₂ : Boundary P} (hD : D₁ = D₂) (hsub : ∀ x y : D₂.space, x = y)
    (p : Program R D₁) (q : Program R D₂) (sigma : TypedLOCC.Op R.total) :
    p.denote sigma =
      reindexOp (Equiv.cast (congrArg Boundary.space hD.symm)) (q.denote sigma) := by
  subst hD
  rw [reindexOp_cast_rfl]
  ext z z'
  have hzz : z = z' := hsub z z'
  subst hzz
  have hp := Instrument.channel_trace_eq p.toInstrument sigma
  have hq := Instrument.channel_trace_eq q.toInstrument sigma
  have hpq := hp.trans hq.symm
  change (∑ x, p.denote sigma x x) = ∑ x, q.denote sigma x x at hpq
  have hsum (M : TypedLOCC.Op D₁.space) : (∑ x, M x x) = M z z := by
    refine Fintype.sum_eq_single z ?_
    intro b hne
    exact (hne (hsub b z)).elim
  rw [hsum, hsum] at hpq
  exact hpq

/-- Denotations of heterogeneously equal programs over equal boundaries. -/
theorem denote_eq_of_heq_boundary {R : MultipartiteSystem P}
    {D₁ D₂ : Boundary P} (hD : D₁ = D₂) (p : Program R D₁) (q : Program R D₂)
    (hpq : p ≍ q) (sigma : TypedLOCC.Op R.total) :
    p.denote sigma =
      reindexOp (Equiv.cast (congrArg Boundary.space hD.symm)) (q.denote sigma) := by
  subst hD
  rw [reindexOp_cast_rfl, eq_of_heq hpq]

/-- A program whose complete output boundary carries a single coordinate returns exactly the input
trace.  This is trace preservation of the program channel, not a positivity or state
assumption. -/
theorem denote_of_subsingleton_space {R : MultipartiteSystem P} {B : Boundary P}
    (hsub : Subsingleton B.space) (p : Program R B)
    (sigma : TypedLOCC.Op R.total) (x y : B.space) :
    p.denote sigma x y = Matrix.trace sigma := by
  classical
  have hxy : x = y := hsub.allEq x y
  subst hxy
  have hcard : Fintype.card B.space = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨x, fun z => hsub.allEq z x⟩
  let eOut : B.space ≃ Fin 1 := Fintype.equivFinOfCardEq hcard
  let eIn : R.total ≃ Fin (Fintype.card R.total) := Fintype.equivFin R.total
  have : NeZero (Fintype.card R.total) := ⟨Fintype.card_ne_zero⟩
  have : NeZero 1 := ⟨one_ne_zero⟩
  have hcptp := p.coordinateDenote_isCPTP eIn eOut
  have htp := hcptp.2.2 (Matrix.reindex eIn eIn sigma)
  have hcoord : coordinateLinear eIn eOut p.denote (Matrix.reindex eIn eIn sigma) =
      Matrix.reindex eOut eOut (p.denote sigma) := by
    ext i j
    simp [coordinateLinear, Matrix.reindex_apply]
  rw [hcoord] at htp
  have hleft : Matrix.trace (Matrix.reindex eOut eOut (p.denote sigma)) =
      p.denote sigma x x := by
    rw [Matrix.trace]
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · have h0 : eOut.symm 0 = x := hsub.allEq _ _
      simp only [Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply, h0]
    · intro i _ hi
      exact absurd (Fin.eq_zero i) hi
    · simp
  have hright : Matrix.trace (Matrix.reindex eIn eIn sigma) = Matrix.trace sigma := by
    rw [Matrix.trace, Matrix.trace]
    exact Fintype.sum_equiv eIn.symm _ _ (fun i => by
      simp [Matrix.reindex_apply])
  rw [hleft, hright] at htp
  exact htp

end TypedLOCC.BoundaryRelabel
