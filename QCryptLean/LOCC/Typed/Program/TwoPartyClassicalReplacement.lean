import QCryptLean.LOCC.Typed.Instrument.ClassicalTransition
import QCryptLean.LOCC.Typed.Program.TwoPartyClassicalStorage

/-!
# Explicit classical realizations of two-party programs

The replacement below keeps the existing `Program` syntax and replaces each local action by
basis-to-basis Kraus matrices implementing its stochastic action on CQ inputs.  It retains raw
outcomes, announcements, actors, dependent successor multipartite systems, continuations, and the
complete public boundary.  The local-instrument interpretation is that of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2; the CQ domain is the finite
matrix form of Renner's `classform` condition in quant-ph/0512258v2.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace TypedLOCC

namespace AnnouncedAction

variable {P Public : Type} [Fintype P] [DecidableEq P]
  [Fintype Public] [DecidableEq Public]

/-- The party-local CP operation at one raw outcome of a possibly dependent-output announced
action. -/
def localOperation {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome) :
    Op (R.reg A.actor) →ₗ[ℂ] Op (A.Output (A.announce o)) :=
  ∑ r, matrixConjLinear (A.kraus o r)

/-- Canonical local transition weight for one raw outcome of an announced action. -/
def localClassicalWeight {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome)
    (a : R.reg A.actor) (b : A.Output (A.announce o)) : ℝ :=
  ((A.localOperation o (Matrix.single a a 1)) b b).re

/-- A raw announced-action transition weight is the sum of squared moduli over its hidden Kraus
fibre. -/
theorem localClassicalWeight_eq_sum_normSq {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome)
    (a : R.reg A.actor) (b : A.Output (A.announce o)) :
    A.localClassicalWeight o a b = ∑ r, Complex.normSq (A.kraus o r b a) := by
  simp only [localClassicalWeight, localOperation, LinearMap.sum_apply,
    Matrix.sum_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hterm :
      (matrixConjLinear (A.kraus o r) (Matrix.single a a 1)) b b =
        A.kraus o r b a * star (A.kraus o r b a) := by
    simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_eq_single a]
    · simp [Matrix.single_apply]
    · intro x _ hxa
      simp [hxa.symm]
    · simp
  rw [hterm]
  simp [Complex.normSq_apply]

/-- Raw announced-action transition weights are nonnegative. -/
theorem localClassicalWeight_nonneg {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome)
    (a : R.reg A.actor) (b : A.Output (A.announce o)) :
    0 ≤ A.localClassicalWeight o a b := by
  rw [A.localClassicalWeight_eq_sum_normSq]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Raw announced-action transition weights are normalized jointly across raw outcomes and their
dependent local output bases. -/
theorem sum_localClassicalWeight {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (a : R.reg A.actor) :
    ∑ o, ∑ b, A.localClassicalWeight o a b = 1 := by
  simp_rw [A.localClassicalWeight_eq_sum_normSq]
  calc
    (∑ o, ∑ b, ∑ r, Complex.normSq (A.kraus o r b a)) =
        ∑ o, ∑ r, ∑ b, Complex.normSq (A.kraus o r b a) := by
      apply Finset.sum_congr rfl
      intro o _
      exact Finset.sum_comm
    _ = 1 := by
      have h := congrArg (fun M => M a a) A.complete
      simp only [Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.one_apply, ite_eq_left] at h
      have hre := congrArg Complex.re h
      simp only [Complex.re_sum, Complex.one_re] at hre
      simpa [Complex.normSq_apply] using hre

/-- One basis-to-basis Kraus matrix of an announced action's canonical replacement. -/
def classicalReplacementKraus {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome)
    (ab : R.reg A.actor × A.Output (A.announce o)) :
    Matrix (A.Output (A.announce o)) (R.reg A.actor) ℂ :=
  Matrix.single ab.2 ab.1
    ((Real.sqrt (A.localClassicalWeight o ab.1 ab.2) : ℝ) : ℂ)

/-- The announced replacement Kraus family is complete across all raw outcomes. -/
theorem classicalReplacementKraus_complete {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) :
    ∑ o, ∑ ab : R.reg A.actor × A.Output (A.announce o),
      (A.classicalReplacementKraus o ab)ᴴ * A.classicalReplacementKraus o ab = 1 := by
  simp only [classicalReplacementKraus]
  simp only [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
  simp_rw [Fintype.sum_prod_type]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [RCLike.star_def, Complex.conj_ofReal, one_apply_eq]
    simp_rw [← Complex.ofReal_mul,
      Real.mul_self_sqrt (A.localClassicalWeight_nonneg _ _ _)]
    convert congrArg (fun x : ℝ => (x : ℂ))
      (A.sum_localClassicalWeight i) using 1
    · simp [Matrix.sum_apply, Matrix.single_apply]
  · simp only [Matrix.sum_apply, Matrix.one_apply, hij, ite_false]
    apply Finset.sum_eq_zero
    intro o _
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rw [Matrix.single_apply_of_ne]
    intro h
    exact hij (h.1.symm.trans h.2)

/-- Replace each raw local operation by its canonical basis-to-basis realization while preserving
the actor, raw outcomes, announcement map, and dependent successor multipartite systems
definitionally. -/
def classicalReplacement {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) : AnnouncedAction R Public where
  actor := A.actor
  Output := A.Output
  Outcome := A.Outcome
  announce := A.announce
  krausIndex o := R.reg A.actor × A.Output (A.announce o)
  kraus := A.classicalReplacementKraus
  complete := A.classicalReplacementKraus_complete

@[simp] theorem classicalReplacement_actor {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) : A.classicalReplacement.actor = A.actor := rfl

@[simp] theorem classicalReplacement_announce {R : MultipartiteSystem P}
    (A : AnnouncedAction R Public) (o : A.Outcome) :
    A.classicalReplacement.announce o = A.announce o := rfl

end AnnouncedAction

namespace PrivateAction

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Replace a private local instrument by its canonical basis-to-basis realization, preserving the
actor, private raw-outcome type, and input/output multipartite systems. -/
def classicalReplacement {R : MultipartiteSystem P} (A : PrivateAction R) :
    PrivateAction R :=
  PrivateAction.ofInstrument A.actor A.instrument.classicalReplacement

@[simp] theorem classicalReplacement_actor {R : MultipartiteSystem P} (A : PrivateAction R) :
    A.classicalReplacement.actor = A.actor := rfl

end PrivateAction

namespace AnnouncedAction

/-- Entrywise action of one announced raw branch after adjoining spectator identities. -/
theorem liftedOperation_apply
    {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P} {Public : Type} [Fintype Public] [DecidableEq Public]
    (A : AnnouncedAction R Public)
    (o : A.Outcome) (rho : Op R.total)
    (q q' : (A.out (A.announce o)).total) :
    (A.liftedOperation o rho) q q' =
      (A.localOperation o
        (rho.submatrix
          (fun x =>
            (R.splitAt A.actor).symm
              (x, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2))
          (fun y =>
            (R.splitAt A.actor).symm
              (y, ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2))))
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q).1
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q').1 := by
  have hsum (f : R.total → ℂ) :
      (∑ x, f x) =
        ∑ p : R.reg A.actor × R.rest A.actor,
          f ((R.splitAt A.actor).symm p) := by
    exact (Equiv.sum_comp (R.splitAt A.actor).symm f).symm
  simp only [AnnouncedAction.liftedOperation, AnnouncedAction.liftedKraus,
    localOperation, matrixConjLinear, LinearMap.coe_sum, LinearMap.coe_mk,
    AddHom.coe_mk, Finset.sum_apply, Matrix.sum_apply, Matrix.mul_apply,
    localKrausLift_apply, ite_mul, zero_mul, Matrix.conjTranspose_apply,
    RCLike.star_def]
  simp_rw [hsum]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp only [apply_ite, map_zero, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Matrix.submatrix_apply]

/-- Every raw local operation of the announced replacement preserves diagonal matrices. -/
theorem classicalReplacement_localOperation_preservesDiagonal
    {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P} {Public : Type} [Fintype Public] [DecidableEq Public]
    (A : AnnouncedAction R Public) :
    ∀ o rho,
      (∀ a a', a ≠ a' → rho a a' = 0) →
      ∀ b b', b ≠ b' →
        (A.classicalReplacement.localOperation o rho) b b' = 0 := by
  intro o rho _ b b' hne
  change A.Outcome at o
  change Op (R.reg A.actor) at rho
  change A.Output (A.announce o) at b b'
  change ((∑ ab : R.reg A.actor × A.Output (A.announce o),
    matrixConjLinear (A.classicalReplacementKraus o ab)) rho) b b' = 0
  simp only [matrixConjLinear,
    classicalReplacementKraus, Matrix.conjTranspose_single, RCLike.star_def,
    Complex.conj_ofReal, Matrix.single_mul_mul_single, LinearMap.coe_sum,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro ab _
  rw [Matrix.single_apply_of_ne]
  intro h
  exact hne (h.1.symm.trans h.2)

/-- A diagonal-preserving announced raw operation is its stochastic transition on diagonals. -/
theorem localOperation_diagonal_apply
    {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P} {Public : Type} [Fintype Public] [DecidableEq Public]
    (A : AnnouncedAction R Public)
    (o : A.Outcome)
    (hlocal : ∀ rho,
      (∀ a a', a ≠ a' → rho a a' = 0) →
      ∀ b b', b ≠ b' → (A.localOperation o rho) b b' = 0)
    (d : R.reg A.actor → ℂ)
    (b b' : A.Output (A.announce o)) :
    A.localOperation o (Matrix.diagonal d) b b' =
      if b = b' then
        ∑ a, (A.localClassicalWeight o a b : ℂ) * d a
      else 0 := by
  by_cases hbb' : b = b'
  · subst b'
    rw [← Matrix.sum_single_eq_diagonal d]
    simp only [map_sum, Matrix.sum_apply, ite_true]
    apply Finset.sum_congr rfl
    intro a _
    have hsingle :
        Matrix.single a a (d a) =
          d a • Matrix.single a a (1 : ℂ) := by
      ext i j
      simp [Matrix.single_apply]
    rw [hsingle, map_smul, Matrix.smul_apply]
    have hdiag :
        A.localOperation o (Matrix.single a a 1) b b =
          (A.localClassicalWeight o a b : ℂ) := by
      rw [A.localClassicalWeight_eq_sum_normSq]
      simp only [localOperation, LinearMap.sum_apply, Matrix.sum_apply,
        Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro r _
      have hterm :
          (matrixConjLinear (A.kraus o r) (Matrix.single a a 1)) b b =
            A.kraus o r b a * star (A.kraus o r b a) := by
        simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk,
          Matrix.mul_apply, Matrix.conjTranspose_apply]
        rw [Finset.sum_eq_single a]
        · simp [Matrix.single_apply]
        · intro x _ hxa
          simp [hxa.symm]
        · simp
      rw [hterm]
      change _ = ((Complex.normSq _ : ℝ) : ℂ)
      rw [Complex.normSq_eq_conj_mul_self]
      simp [mul_comm]
    rw [hdiag]
    simp [smul_eq_mul, mul_comm]
  · rw [ite_eq_right hbb']
    exact hlocal (Matrix.diagonal d)
      (fun a a' haa' => Matrix.diagonal_apply_ne _ haa') b b' hbb'

/-- The replacement and original raw local operations agree on diagonal inputs whenever the
original raw operation preserves diagonality. -/
theorem classicalReplacement_localOperation_diagonal
    {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P} {Public : Type} [Fintype Public] [DecidableEq Public]
    (A : AnnouncedAction R Public)
    (o : A.Outcome)
    (hlocal : ∀ rho,
      (∀ a a', a ≠ a' → rho a a' = 0) →
      ∀ b b', b ≠ b' → (A.localOperation o rho) b b' = 0)
    (d : R.reg A.actor → ℂ) :
    A.classicalReplacement.localOperation o (Matrix.diagonal d) =
      A.localOperation o (Matrix.diagonal d) := by
  have hweight (a : R.reg A.actor)
      (b : A.Output (A.announce o)) :
      A.classicalReplacement.localClassicalWeight o a b =
        A.localClassicalWeight o a b := by
    refine (localClassicalWeight_eq_sum_normSq A.classicalReplacement o a b).trans ?_
    change (∑ ab : R.reg A.actor × A.Output (A.announce o),
      Complex.normSq (A.classicalReplacementKraus o ab b a)) = _
    simp only [classicalReplacementKraus,
      Matrix.single_apply]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simpa [Complex.normSq_apply] using
          Real.mul_self_sqrt (A.localClassicalWeight_nonneg o a b)
      · intro b' _ hb'
        simp [hb']
      · simp
    · intro a' _ ha'
      simp [ha']
    · simp
  ext b b'
  rw [A.classicalReplacement.localOperation_diagonal_apply o
      (A.classicalReplacement_localOperation_preservesDiagonal o) d b b',
    A.localOperation_diagonal_apply o hlocal d b b']
  apply if_congr Iff.rfl
  · exact Finset.sum_congr rfl (fun a _ => congrArg (fun t : ℝ => (t : ℂ) * d a)
      (hweight a b))
  · rfl

/-- Honest-register preservation recovers the acting party's diagonal-preservation law once a
spectator basis point is fixed. -/
theorem PreservesHonestRegistersDiagonal.localOperation_preservesDiagonal_at
    {R : MultipartiteSystem TwoParty.Party} {Public : Type}
    [Fintype Public] [DecidableEq Public]
    (A : AnnouncedAction R Public)
    (hA : A.PreservesHonestRegistersDiagonal)
    (s : R.rest A.actor) (o : A.Outcome) :
    ∀ sigma,
      (∀ a a', a ≠ a' → sigma a a' = 0) →
      ∀ b b', b ≠ b' → (A.localOperation o sigma) b b' = 0 := by
  intro sigma hsigma b b' hbb'
  let rho : Op R.total := fun q q' =>
    if ((R.splitAt A.actor) q).2 = s ∧
        ((R.splitAt A.actor) q').2 = s then
      sigma ((R.splitAt A.actor q).1) ((R.splitAt A.actor q').1)
    else 0
  have hrho : R.HonestRegistersDiagonal rho := by
    intro q q' hqq'
    by_cases hs :
        ((R.splitAt A.actor) q).2 = s ∧
          ((R.splitAt A.actor) q').2 = s
    · rw [show rho q q' =
          sigma ((R.splitAt A.actor q).1) ((R.splitAt A.actor q').1) by
        simp [rho, hs]]
      apply hsigma
      intro hlocal
      have hrest : ((R.splitAt A.actor) q).2 =
          ((R.splitAt A.actor) q').2 := hs.1.trans hs.2.symm
      have hq : q = q' :=
        (R.splitAt A.actor).injective (Prod.ext hlocal hrest)
      subst q'
      exact hqq'.elim (fun h => h rfl) (fun h => h rfl)
    · simp [rho, hs]
  let q := (R.splitAtSet A.actor (A.Output (A.announce o))).symm (b, s)
  let q' := (R.splitAtSet A.actor (A.Output (A.announce o))).symm (b', s)
  have hqne : q ≠ q' := by
    intro h
    apply hbb'
    have := congrArg (fun z =>
      ((R.splitAtSet A.actor (A.Output (A.announce o))) z).1) h
    simpa [q, q'] using this
  have hdiff : q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob := by
    by_cases ha : q .alice = q' .alice
    · exact Or.inr (by
        intro hb
        apply hqne
        funext i
        cases i with
        | alice => exact ha
        | bob => exact hb)
    · exact Or.inl ha
  have hzero := hA o rho hrho q q' hdiff
  rw [AnnouncedAction.liftedOperation_apply] at hzero
  have hslice :
      rho.submatrix
          (fun x => (R.splitAt A.actor).symm
            (x, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2))
          (fun y => (R.splitAt A.actor).symm
            (y, ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2)) = sigma := by
    ext a a'
    have hq : ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2 = s :=
      congrArg Prod.snd ((R.splitAtSet A.actor (A.Output (A.announce o))).apply_symm_apply
        (b, s))
    have hq' : ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2 = s :=
      congrArg Prod.snd ((R.splitAtSet A.actor (A.Output (A.announce o))).apply_symm_apply
        (b', s))
    rw [hq, hq']
    change (if (R.splitAt A.actor ((R.splitAt A.actor).symm (a, s))).2 = s ∧
      (R.splitAt A.actor ((R.splitAt A.actor).symm (a', s))).2 = s then
        sigma (R.splitAt A.actor ((R.splitAt A.actor).symm (a, s))).1
          (R.splitAt A.actor ((R.splitAt A.actor).symm (a', s))).1 else 0) = sigma a a'
    simp only [Equiv.apply_symm_apply, and_self, ite_true]
  rw [hslice] at hzero
  simpa [q, q'] using hzero

/-- The canonical replacement of any announced action preserves honest-register diagonality on
every raw branch. -/
theorem classicalReplacement_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} {Public : Type}
    [Fintype Public] [DecidableEq Public]
    (A : AnnouncedAction R Public) :
    A.classicalReplacement.PreservesHonestRegistersDiagonal := by
  intro o rho hrho q q' hqq'
  rw [AnnouncedAction.liftedOperation_apply]
  let sigma : Op (R.reg A.actor) :=
    rho.submatrix
      (fun x => (R.splitAt A.actor).symm
        (x, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2))
      (fun y => (R.splitAt A.actor).symm
        (y, ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2))
  have hsigma : ∀ a a', a ≠ a' → sigma a a' = 0 := by
    intro a a' haa'
    apply hrho
    have htotal :
        (R.splitAt A.actor).symm
            (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2) ≠
          (R.splitAt A.actor).symm
            (a', ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2) := by
      intro h
      apply haa'
      have := congrArg (fun z => ((R.splitAt A.actor) z).1) h
      simpa using this
    by_cases ha :
        ((R.splitAt A.actor).symm
            (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2)) .alice =
          ((R.splitAt A.actor).symm
            (a', ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2)) .alice
    · exact Or.inr (by
        intro hb
        apply htotal
        funext j
        cases j with
        | alice => exact ha
        | bob => exact hb)
    · exact Or.inl ha
  by_cases hlocal :
      ((R.splitAtSet A.actor (A.Output (A.announce o))) q).1 ≠
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q').1
  · exact A.classicalReplacement_localOperation_preservesDiagonal
      o sigma hsigma _ _ hlocal
  · have hlocalEq :
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q).1 =
          ((R.splitAtSet A.actor (A.Output (A.announce o))) q').1 :=
      not_ne_iff.mp hlocal
    have hqne : q ≠ q' := by
      intro h
      subst h
      exact hqq'.elim (fun h => h rfl) (fun h => h rfl)
    have hrest :
        ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2 ≠
          ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2 := by
      intro h
      apply hqne
      apply (R.splitAtSet A.actor (A.Output (A.announce o))).injective
      exact Prod.ext hlocalEq h
    have hsigmaZero : sigma = 0 := by
      ext a a'
      apply hrho
      have htotal :
          (R.splitAt A.actor).symm
              (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2) ≠
            (R.splitAt A.actor).symm
              (a', ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2) := by
        intro h
        apply hrest
        have := congrArg (fun z => ((R.splitAt A.actor) z).2) h
        simpa using this
      by_cases ha :
          ((R.splitAt A.actor).symm
              (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) q).2)) .alice =
            ((R.splitAt A.actor).symm
              (a', ((R.splitAtSet A.actor (A.Output (A.announce o))) q').2)) .alice
      · exact Or.inr (by
          intro hb
          apply htotal
          funext j
          cases j with
          | alice => exact ha
          | bob => exact hb)
      · exact Or.inl ha
    change (A.classicalReplacement.localOperation o sigma) _ _ = 0
    rw [hsigmaZero]
    exact congrFun (congrFun (map_zero (A.classicalReplacement.localOperation o)) _) _

/-- On CQ inputs, a diagonality-preserving raw announced branch and its manifest classical
replacement have the same lifted operation, including arbitrary reference blocks. -/
theorem PreservesHonestRegistersDiagonal.classicalReplacement_liftedOperation_tensorId
    {R : MultipartiteSystem TwoParty.Party} {Public : Type}
    [Fintype Public] [DecidableEq Public]
    (A : AnnouncedAction R Public)
    (hA : A.PreservesHonestRegistersDiagonal)
    {E : Type} [Fintype E] [DecidableEq E]
    (rho : Op (R.total × E))
    (hrho : IsClassicalOnFirst (Alpha := R.total) (Ref := E) rho)
    (o : A.Outcome) :
    tensorIdLinear E (A.classicalReplacement.liftedOperation o) rho =
      tensorIdLinear E (A.liftedOperation o) rho := by
  rcases isEmpty_or_nonempty (R.rest A.actor) with hEmpty | hNonempty
  · let := hEmpty
    ext p q
    exact isEmptyElim
      (((R.splitAtSet A.actor (A.Output (A.announce o))) p.1).2)
  · rcases hNonempty with ⟨s⟩
    ext p q
    rcases p with ⟨qOut, e⟩
    rcases q with ⟨qOut', e'⟩
    change (A.out (A.announce o)).total at qOut qOut'
    refine (tensorIdLinear_apply (A.classicalReplacement.liftedOperation o)
      rho (qOut, e) (qOut', e')).trans ?_
    refine Eq.trans ?_ (tensorIdLinear_apply (A.liftedOperation o)
      rho (qOut, e) (qOut', e')).symm
    refine (AnnouncedAction.liftedOperation_apply A.classicalReplacement o
      (rho.submatrix (fun a => (a, e)) (fun a => (a, e'))) qOut qOut').trans ?_
    refine Eq.trans ?_ (AnnouncedAction.liftedOperation_apply A o
      (rho.submatrix (fun a => (a, e)) (fun a => (a, e'))) qOut qOut').symm
    let sigma : Op (R.reg A.actor) :=
      (rho.submatrix (fun a => (a, e)) (fun a => (a, e'))).submatrix
        (fun x => (R.splitAt A.actor).symm
          (x, ((R.splitAtSet A.actor (A.Output (A.announce o))) qOut).2))
        (fun y => (R.splitAt A.actor).symm
          (y, ((R.splitAtSet A.actor (A.Output (A.announce o))) qOut').2))
    have hsigma :
        sigma = Matrix.diagonal (fun a =>
          rho
            ((R.splitAt A.actor).symm
              (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) qOut).2), e)
            ((R.splitAt A.actor).symm
              (a, ((R.splitAtSet A.actor (A.Output (A.announce o))) qOut').2), e')) := by
      ext a a'
      by_cases haa' : a = a'
      · subst a'
        simp [sigma]
      · rw [Matrix.diagonal_apply_ne _ haa']
        exact hrho _ _ e e' (by
          intro h
          apply haa'
          have := congrArg (fun z => ((R.splitAt A.actor) z).1) h
          simpa using this)
    change
      (A.classicalReplacement.localOperation o sigma)
          ((R.splitAtSet A.actor (A.Output (A.announce o)) qOut).1)
          ((R.splitAtSet A.actor (A.Output (A.announce o)) qOut').1) =
        (A.localOperation o sigma)
          ((R.splitAtSet A.actor (A.Output (A.announce o)) qOut).1)
          ((R.splitAtSet A.actor (A.Output (A.announce o)) qOut').1)
    rw [hsigma]
    exact congrFun (congrFun (A.classicalReplacement_localOperation_diagonal o
      (hA.localOperation_preservesDiagonal_at A s o) _) _) _

end AnnouncedAction

namespace PrivateAction

/-- The canonical replacement of any private action preserves honest-register diagonality on
every raw branch. -/
theorem classicalReplacement_preservesHonestRegistersDiagonal
    {R : MultipartiteSystem TwoParty.Party} (A : PrivateAction R) :
    A.classicalReplacement.PreservesHonestRegistersDiagonal := by
  simpa [PrivateAction.classicalReplacement] using
    PrivateAction.ofInstrument_preservesHonestRegistersDiagonal
      A.actor A.instrument.classicalReplacement
      A.instrument.classicalReplacement_preservesDiagonalBranches

/-- On CQ inputs, a diagonality-preserving private raw branch and its manifest classical
replacement have the same lifted operation, including arbitrary reference blocks. -/
theorem PreservesHonestRegistersDiagonal.classicalReplacement_liftedOperation_tensorId
    {R : MultipartiteSystem TwoParty.Party} (A : PrivateAction R)
    (hA : A.PreservesHonestRegistersDiagonal)
    {E : Type} [Fintype E] [DecidableEq E]
    (rho : Op (R.total × E))
    (hrho : IsClassicalOnFirst (Alpha := R.total) (Ref := E) rho)
    (o : A.Outcome) :
    tensorIdLinear E (A.classicalReplacement.liftedOperation o) rho =
      tensorIdLinear E (A.liftedOperation o) rho := by
  have hAunit : A.asUnitAnnouncement.PreservesHonestRegistersDiagonal := by
    exact hA
  have h := hAunit.classicalReplacement_liftedOperation_tensorId
    A.asUnitAnnouncement rho hrho o
  exact h

end PrivateAction

namespace Program

/-- Replace every action by its canonical basis-to-basis local realization while recursing over
the existing program syntax.  The result has exactly the original program's indexed boundary. -/
def classicalReplacement
    {R : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party} (p : Program R B) :
      Program R B :=
  match p with
  | .done => .done
  | @Program.announced _ _ _ _ Public _ _ A _ k =>
      .announced
        (AnnouncedAction.classicalReplacement (Public := Public) A)
        (fun y => (k y).classicalReplacement)
  | .priv A k =>
      .priv A.classicalReplacement k.classicalReplacement

/-- The canonical replacement of every program has an action-by-action honest-classical
certificate. -/
theorem classicalReplacement_isHonestClassical
    {R : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party} (p : Program R B) :
    p.classicalReplacement.IsHonestClassical := by
  induction p with
  | done => exact .done
  | announced A k ih =>
      exact .announced _ _ A.classicalReplacement_preservesHonestRegistersDiagonal ih
  | priv A k ih =>
      exact .priv _ _ A.classicalReplacement_preservesHonestRegistersDiagonal ih

/-- A two-party honest-register diagonal operator becomes a CQ operator after adjoining the
unique reference coordinate. -/
private theorem honestRegistersDiagonal_isClassicalOnFirst_unit
    {R : MultipartiteSystem TwoParty.Party} (rho : Op R.total)
    (hrho : R.HonestRegistersDiagonal rho) :
    IsClassicalOnFirst (Alpha := R.total) (Ref := Unit)
      (fun p q => rho p.1 q.1) := by
  intro q q' _ _ hqq'
  apply hrho
  by_cases ha : q .alice = q' .alice
  · exact Or.inr (by
      intro hb
      apply hqq'
      funext i
      cases i with
      | alice => exact ha
      | bob => exact hb)
  · exact Or.inl ha

/-- Reference-free core of program replacement: induction follows raw outcomes before they are
coarse-grained, using the corresponding announced/private tensor-identity bridge at each node. -/
private theorem IsHonestClassical.classicalReplacement_denote_eq
    {R : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party} {p : Program R B}
    (hp : p.IsHonestClassical) (rho : Op R.total)
    (hrho : R.HonestRegistersDiagonal rho) :
    p.classicalReplacement.denote rho = p.denote rho := by
  induction hp with
  | done =>
      rfl
  | announced A k hA hk ih =>
      change
        (Program.announced A.classicalReplacement
          (fun y => (k y).classicalReplacement)).denote rho =
        (Program.announced A k).denote rho
      refine (LinearMap.congr_fun (Program.denote_announced_eq_sum_liftedOperation
        A.classicalReplacement (fun y => (k y).classicalReplacement)) rho).trans ?_
      refine Eq.trans ?_ (LinearMap.congr_fun
        (Program.denote_announced_eq_sum_liftedOperation A k) rho).symm
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      apply Finset.sum_congr rfl
      intro o _
      let rhoRef : Op (_ × Unit) := fun p q => rho p.1 q.1
      have hactionTensor :=
        hA.classicalReplacement_liftedOperation_tensorId A rhoRef
          (honestRegistersDiagonal_isClassicalOnFirst_unit rho hrho) o
      have haction :
          A.classicalReplacement.liftedOperation o rho =
            A.liftedOperation o rho := by
        ext q q'
        have hentry := congrArg (fun M => M (q, ()) (q', ())) hactionTensor
        simp only [tensorIdLinear_apply] at hentry
        exact hentry
      rw [haction]
      exact congrArg _ (ih (A.announce o) (A.liftedOperation o rho) (hA o rho hrho))
  | priv A k hA hk ih =>
      change
        (Program.priv A.classicalReplacement k.classicalReplacement).denote rho =
        (Program.priv A k).denote rho
      refine (LinearMap.congr_fun (Program.denote_priv_eq_sum_liftedOperation
        A.classicalReplacement k.classicalReplacement) rho).trans ?_
      refine Eq.trans ?_ (LinearMap.congr_fun
        (Program.denote_priv_eq_sum_liftedOperation A k) rho).symm
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      apply Finset.sum_congr rfl
      intro o _
      let rhoRef : Op (_ × Unit) := fun p q => rho p.1 q.1
      have hactionTensor :=
        hA.classicalReplacement_liftedOperation_tensorId A rhoRef
          (honestRegistersDiagonal_isClassicalOnFirst_unit rho hrho) o
      have haction :
          A.classicalReplacement.liftedOperation o rho =
            A.liftedOperation o rho := by
        ext q q'
        have hentry := congrArg (fun M => M (q, ()) (q', ())) hactionTensor
        simp only [tensorIdLinear_apply] at hentry
        exact hentry
      rw [haction]
      exact ih (A.liftedOperation o rho) (hA o rho hrho)

/-- The explicit local classical replacement has the same complete public boundary and the same
CQ denotation as the authored program.  Raw outcomes and announcements are retained at every
node. -/
theorem IsHonestClassical.classicalReplacement_denote_tensorId_eq
    {R : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party} {p : Program R B}
    (hp : p.IsHonestClassical)
    {E : Type} [Fintype E] [DecidableEq E]
    (rho : Op (R.total × E))
    (hrho : IsClassicalOnFirst (Alpha := R.total) (Ref := E) rho) :
    tensorIdLinear E p.classicalReplacement.denote rho =
      tensorIdLinear E p.denote rho := by
  ext x x'
  rcases x with ⟨q, e⟩
  rcases x' with ⟨q', e'⟩
  rw [tensorIdLinear_apply, tensorIdLinear_apply]
  let sigma : Op R.total :=
    rho.submatrix (fun a => (a, e)) (fun a => (a, e'))
  have hsigma : R.HonestRegistersDiagonal sigma := by
    intro a a' hdiff
    exact hrho a a' e e' (by
      intro h
      subst a'
      exact hdiff.elim (fun ha => ha rfl) (fun hb => hb rfl))
  have hdenote := hp.classicalReplacement_denote_eq sigma hsigma
  exact congrArg (fun M => M q q') hdenote

/-- A recursively certified two-party program preserves full CQ structure, including its
complete public exit and both honest registers, against arbitrary independent reference
row/column indices. -/
theorem IsHonestClassical.denote_tensorId
    {R : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party} {p : Program R B}
    (hp : p.IsHonestClassical)
    {E : Type} [Fintype E] [DecidableEq E]
    (rho : Op (R.total × E))
    (hrho : IsClassicalOnFirst (Alpha := R.total) (Ref := E) rho) :
    IsClassicalOnFirst (Alpha := B.space) (Ref := E)
      (tensorIdLinear E p.denote rho) := by
  intro x x' e e' hxx
  rcases x with ⟨y, q⟩
  rcases x' with ⟨y', q'⟩
  rw [tensorIdLinear_apply]
  have hblock : R.HonestRegistersDiagonal
      (Matrix.of fun i j => rho (i, e) (j, e')) := by
    intro qIn qIn' hdiff
    exact hrho qIn qIn' e e' (by
      intro h
      subst qIn'
      exact hdiff.elim (fun ha => ha rfl) (fun hb => hb rfl))
  by_cases hyy' : y = y'
  · subst y'
    have hdiff : q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob := by
      by_cases hAlice : q .alice = q' .alice
      · right
        intro hBob
        apply hxx
        congr
        funext i
        cases i with
        | alice => exact hAlice
        | bob => exact hBob
      · exact Or.inl hAlice
    exact hp.denote (Matrix.of fun i j => rho (i, e) (j, e')) hblock y q q' hdiff
  · exact p.denote_isExitBlockDiagonal
      (Matrix.of fun i j => rho (i, e) (j, e')) y y' q q' hyy'

/-- Entering and then removing the unique public coordinate of a leaf boundary is the identity
channel. -/
private theorem denote_done_comp_reindexOp (R : MultipartiteSystem TwoParty.Party) :
    (Program.done : Program R (.leaf R)).denote.comp
        (reindexOp (Boundary.leafSpaceEquiv R)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro rho
  ext x y
  rcases x with ⟨⟨⟩, x⟩
  rcases y with ⟨⟨⟩, y⟩
  simp [Program.denote_done, LinearMap.comp_apply, reindexOp,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, Boundary.leafSpaceEquiv]

/-- A continuation controlled by a leaf's unique exit is its sole continuation after removing
the leaf's trivial public coordinate. -/
private theorem controlledContinuation_leaf_eq_denote_comp_reindexOp
    (R : MultipartiteSystem TwoParty.Party)
    {C : (Boundary.leaf R).Exit → Boundary TwoParty.Party}
    (k : ∀ e : (Boundary.leaf R).Exit,
      Program ((Boundary.leaf R).system e) (C e)) :
    controlledContinuation k =
      (k ()).denote.comp (reindexOp (Boundary.leafSpaceEquiv R)) := by
  let L : Op (Boundary.leaf R).space →ₗ[ℂ] Op (C ()).space := controlledContinuation k
  let J : Op R.total →ₗ[ℂ] Op (Boundary.leaf R).space :=
    (Program.done : Program R (.leaf R)).denote
  let E := reindexOp (Boundary.leafSpaceEquiv R)
  have hid : J.comp E = LinearMap.id := denote_done_comp_reindexOp R
  have hL : (L.comp J).comp E = (k ()).denote.comp E :=
    congrArg (fun C : Op R.total →ₗ[ℂ] Op (C ()).space => C.comp E)
      (controlledContinuation_comp_denote_done R k)
  exact (congrArg L.comp hid.symm).trans hL

/-- A program that creates a CQ leaf output followed by an honest-classical continuation has a CQ
grafted output.  The leaf's unique public coordinate is transported to the continuation's input
multipartite system before applying `IsHonestClassical.denote_tensorId`. -/
theorem IsHonestClassical.graft_leaf_denote_tensorId
    {R S : MultipartiteSystem TwoParty.Party} {B : Boundary TwoParty.Party}
    (p : Program R (.leaf S)) (k : Program S B)
    (hk : k.IsHonestClassical)
    {E : Type} [Fintype E] [DecidableEq E]
    (rho : Op (R.total × E))
    (hp : IsClassicalOnFirst
      (Alpha := (Boundary.leaf S).space) (Ref := E)
      (tensorIdLinear E p.denote rho)) :
    IsClassicalOnFirst (Alpha := B.space) (Ref := E)
      (tensorIdLinear E (p.graft (fun _ => k)).denote rho) := by
  have hden : (p.graft (fun _ => k)).denote =
      k.denote.comp ((reindexOp (Boundary.leafSpaceEquiv S)).comp p.denote) := by
    exact (Program.denote_graft p (fun _ => k)).trans
      (congrArg (fun L : Op (Boundary.leaf S).space →ₗ[ℂ] Op B.space => L.comp p.denote)
        (controlledContinuation_leaf_eq_denote_comp_reindexOp S (fun _ => k)))
  rw [hden]
  exact hk.denote_tensorId
    (tensorIdLinear E (reindexOp (Boundary.leafSpaceEquiv S))
      (tensorIdLinear E p.denote rho))
    (hp.reindexOp (Boundary.leafSpaceEquiv S))

end Program
end TypedLOCC
