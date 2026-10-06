import QCryptLean.LOCC.Typed.Instrument.ClassicalPreservation
import QCryptLean.LOCC.Typed.Program.GraftDenotation
import QCryptLean.LOCC.Typed.TwoParty

/-!
# Recursive classical-storage certificate for two-party programs

The definitions below track Alice/Bob register diagonality through every raw action branch of an
existing `Program`.  This refines an endpoint-only output statement: the inductive certificate
checks each action before its continuation.  It is implementation infrastructure for the finite
LOCC tree of Chitambar et al., arXiv:1210.4583, Section 2, not a security theorem.
-/

noncomputable section

namespace TypedLOCC

namespace MultipartiteSystem

/-- An operator has no off-diagonal entry in either named honest-party register. -/
def HonestRegistersDiagonal
    (R : MultipartiteSystem TwoParty.Party) (rho : Op R.total) : Prop :=
  ∀ q q', q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob → rho q q' = 0

end MultipartiteSystem

namespace Boundary

/-- Within every fixed public exit, an output operator is diagonal in Alice's and Bob's
registers. -/
def HonestRegistersDiagonal
    (B : Boundary TwoParty.Party) (sigma : Op B.space) : Prop :=
  ∀ e (q q' : (B.system e).total),
    q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob → sigma ⟨e, q⟩ ⟨e, q'⟩ = 0

end Boundary

namespace PrivateAction

/-- Every private raw outcome preserves honest-register diagonality. -/
def PreservesHonestRegistersDiagonal {R : MultipartiteSystem TwoParty.Party}
    (A : PrivateAction R) : Prop :=
  ∀ o rho, R.HonestRegistersDiagonal rho →
    A.out.HonestRegistersDiagonal (A.liftedOperation o rho)

/-- A party-local instrument preserving its local diagonal also preserves the two-party predicate.

This is the `K ⊗ 1` lifting step in the finite local-instrument model of Chitambar et al.,
arXiv:1210.4583, Section 2.
-/
theorem ofInstrument_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} (i : TwoParty.Party)
    {HH : Type} [Nonempty HH] [Fintype HH] [DecidableEq HH]
    {Y : Type} [Fintype Y] (I : Instrument (R.reg i) HH Y)
    (hI : I.PreservesDiagonalBranches) :
    (PrivateAction.ofInstrument i I).PreservesHonestRegistersDiagonal := by
  intro o rho hrho q q' hqq'
  change ((I.liftAt R i).operation o rho) q q' = 0
  rw [Instrument.liftAt_operation_apply (R := R) i I o rho q q']
  let sigma : Op (R.reg i) :=
    rho.submatrix
      (fun x => (R.splitAt i).symm
        (x, ((R.splitAtSet i HH) q).2))
      (fun y => (R.splitAt i).symm
        (y, ((R.splitAtSet i HH) q').2))
  have hsigma : ∀ a a', a ≠ a' → sigma a a' = 0 := by
    intro a a' haa'
    apply hrho
    have htotal :
        (R.splitAt i).symm
            (a, ((R.splitAtSet i HH) q).2) ≠
          (R.splitAt i).symm
            (a', ((R.splitAtSet i HH) q').2) := by
      intro h
      apply haa'
      have := congrArg (fun z => ((R.splitAt i) z).1) h
      simpa using this
    by_cases ha :
        ((R.splitAt i).symm
            (a, ((R.splitAtSet i HH) q).2)) .alice =
          ((R.splitAt i).symm
            (a', ((R.splitAtSet i HH) q').2)) .alice
    · exact Or.inr (by
        intro hb
        apply htotal
        funext j
        cases j with
        | alice => exact ha
        | bob => exact hb)
    · exact Or.inl ha
  by_cases hlocal :
      ((R.splitAtSet i HH) q).1 ≠ ((R.splitAtSet i HH) q').1
  · exact hI o sigma hsigma _ _ hlocal
  · have hlocalEq :
        ((R.splitAtSet i HH) q).1 = ((R.splitAtSet i HH) q').1 :=
      not_ne_iff.mp hlocal
    have hqne : q ≠ q' := by
      intro h
      subst h
      exact hqq'.elim (fun h => h rfl) (fun h => h rfl)
    have hrest :
        ((R.splitAtSet i HH) q).2 ≠ ((R.splitAtSet i HH) q').2 := by
      intro h
      apply hqne
      apply (R.splitAtSet i HH).injective
      exact Prod.ext hlocalEq h
    have hsigmaZero : sigma = 0 := by
      ext a a'
      apply hrho
      have htotal :
          (R.splitAt i).symm
              (a, ((R.splitAtSet i HH) q).2) ≠
            (R.splitAt i).symm
              (a', ((R.splitAtSet i HH) q').2) := by
        intro h
        apply hrest
        have := congrArg (fun z => ((R.splitAt i) z).2) h
        simpa using this
      by_cases ha :
          ((R.splitAt i).symm
              (a, ((R.splitAtSet i HH) q).2)) .alice =
            ((R.splitAt i).symm
              (a', ((R.splitAtSet i HH) q').2)) .alice
      · exact Or.inr (by
          intro hb
          apply htotal
          funext j
          cases j with
          | alice => exact ha
          | bob => exact hb)
      · exact Or.inl ha
    change (I.operation o sigma) _ _ = 0
    rw [hsigmaZero]
    simp

end PrivateAction

namespace AnnouncedAction

/-- Every raw outcome of an announced action preserves the diagonal predicate at its announced
multipartite system. -/
def PreservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} {Y : Type} [Fintype Y] [DecidableEq Y]
    (A : AnnouncedAction R Y) : Prop :=
  ∀ o rho, R.HonestRegistersDiagonal rho →
    (A.out (A.announce o)).HonestRegistersDiagonal (A.liftedOperation o rho)

/-- An announced party-local instrument preserving its local diagonal preserves the two-party
predicate on every raw branch.

This is the announced `K ⊗ 1` lifting step in the finite LOCC model of Chitambar et al.,
arXiv:1210.4583, Section 2.
-/
theorem ofInstrument_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} (i : TwoParty.Party)
    {HH : Type} [Nonempty HH] [Fintype HH] [DecidableEq HH]
    {O : Type} [Fintype O] {Y : Type} [Fintype Y] [DecidableEq Y]
    (I : Instrument (R.reg i) HH O) (announce : O → Y)
    (hI : I.PreservesDiagonalBranches) :
    (AnnouncedAction.ofInstrument i I announce).PreservesHonestRegistersDiagonal := by
  intro o rho hrho
  exact PrivateAction.ofInstrument_preservesHonestRegistersDiagonal i I hI o rho hrho

end AnnouncedAction

namespace Program

/-- Recursive certificate that every raw action branch preserves honest classical storage before
its continuation. -/
inductive IsHonestClassical :
    {R : MultipartiteSystem TwoParty.Party} → {B : Boundary TwoParty.Party} → Program R B → Prop
      where
  /-- Termination is an honest-classical program. -/
  | done {R : MultipartiteSystem TwoParty.Party} :
      IsHonestClassical (Program.done : Program R (.leaf R))
  /-- An announced node is certified by its raw-action preservation law and every continuation. -/
  | announced {R : MultipartiteSystem TwoParty.Party} {Y : Type} [Fintype Y] [DecidableEq Y]
      {B : Y → Boundary TwoParty.Party}
      (A : AnnouncedAction R Y) (k : ∀ y, Program (A.out y) (B y))
      (hA : A.PreservesHonestRegistersDiagonal)
      (hk : ∀ y, IsHonestClassical (k y)) :
      IsHonestClassical (Program.announced A k)
  /-- A private node is certified by its raw-action preservation law and its continuation. -/
  | priv {R : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party}
      (A : PrivateAction R) (k : Program A.out B)
      (hA : A.PreservesHonestRegistersDiagonal) (hk : IsHonestClassical k) :
      IsHonestClassical (Program.priv A k)

/-- A private program is honest-classical exactly when its action and continuation are certified. -/
@[simp] theorem isHonestClassical_priv_iff
    {R : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party}
    (A : PrivateAction R) (k : Program A.out B) :
    (Program.priv A k).IsHonestClassical ↔
      A.PreservesHonestRegistersDiagonal ∧ k.IsHonestClassical := by
  constructor
  · intro h
    cases h with
    | priv _ _ hA hk => exact ⟨hA, hk⟩
  · rintro ⟨hA, hk⟩
    exact .priv A k hA hk

/-- Grafting recursively certified continuations onto a certified program preserves the
all-step certificate.  This is the syntactic substitution law for the existing LOCC tree.
-/
theorem IsHonestClassical.graft
    {R : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party} {p : Program R B}
    (hp : p.IsHonestClassical) {C : B.Exit → Boundary TwoParty.Party}
    {k : ∀ e, Program (B.system e) (C e)} (hk : ∀ e, (k e).IsHonestClassical) :
    (p.graft k).IsHonestClassical := by
  induction hp with
  | done => simpa using hk ()
  | announced A next hA hnext ih =>
      rw [Program.graft_announced]
      exact .announced _ _ hA (fun y => ih y (fun e => hk ⟨y, e⟩))
  | priv A next hA hnext ih =>
      rw [Program.graft_priv]
      exact .priv _ _ hA (ih hk)

/-- A recursively certified program maps an honest-register diagonal input to an output diagonal
within every fixed public exit.  Cross-exit blocks are handled separately by
`Program.denote_isExitBlockDiagonal`.
-/
theorem IsHonestClassical.denote
    {R : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party} {p : Program R B}
    (hp : p.IsHonestClassical) (rho : Op R.total)
    (hrho : R.HonestRegistersDiagonal rho) :
    B.HonestRegistersDiagonal (p.denote rho) := by
  induction hp with
  | done =>
      intro e q q' hqq'
      rcases e with ⟨⟩
      simpa [Program.denote_done, Matrix.reindexLinearEquiv_apply,
        Matrix.reindex_apply, Boundary.leafSpaceEquiv] using hrho q q' hqq'
  | announced A next hA hnext ih =>
      intro e q q' hqq'
      rcases e with ⟨y, e⟩
      rw [Program.denote_announced_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro o _
      by_cases ho : A.announce o = y
      · subst y
        simpa [matrixConjLinear, Matrix.mul_apply,
          Boundary.publicInclKraus_apply] using
          ih (A.announce o) (A.liftedOperation o rho) (hA o rho hrho) e q q' hqq'
      · simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk,
          Matrix.mul_apply, Boundary.publicInclKraus_apply,
          Boundary.publicSpaceEquiv_apply, Sigma.mk.injEq, ite_mul, one_mul,
          zero_mul, Matrix.conjTranspose_apply, RCLike.star_def,
          MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero]
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg]
        intro h
        exact ho (congrArg Sigma.fst h).symm
  | priv A next hA hnext ih =>
      intro e q q' hqq'
      rw [Program.denote_priv_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro o _
      exact ih (A.liftedOperation o rho) (hA o rho hrho) e q q' hqq'

end Program

end TypedLOCC
