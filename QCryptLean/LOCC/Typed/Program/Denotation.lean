import QCryptLean.LOCC.Typed.Program
import QCryptLean.LOCC.Typed.Boundary.DirectSum
import QCryptLean.LOCC.Typed.ChannelCoordinates
import QCryptLean.LOCC.Typed.Instrument.MatrixConj

/-!
# Complete-path denotation of branch-dependent typed LOCC programs

This module flattens every finite `Program` into one certified instrument.  A hidden branch records
raw outcomes, Kraus multiplicities, and the remaining hidden branch, while `Branch.exit` records
only the public exit.  Its path Kraus matrix is injected into the corresponding exit block of the
heterogeneous output space.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

namespace Boundary

/-- Erase the unique outer public coordinate of a singleton announcement boundary.

This equivalence removes exactly one `Unit`-valued announcement cell.  It does not identify the
two boundary syntax trees: the announced boundary still records a public node, while `B` does not.
-/
def unitAnnouncementSpaceEquiv (B : Boundary P) :
    (Boundary.announce Unit (fun _ => B)).space ≃ B.space :=
  (publicSpaceEquiv (fun _ : Unit => B)).trans
    (Equiv.uniqueSigma (fun _ : Unit => B.space))

/-- Forward coordinate formula for erasing a singleton public announcement. -/
@[simp] theorem unitAnnouncementSpaceEquiv_apply (B : Boundary P)
    (x : (Boundary.announce Unit (fun _ => B)).space) :
    unitAnnouncementSpaceEquiv B x = ⟨x.1.2, x.2⟩ :=
  rfl

/-- Inverse coordinate formula for inserting a singleton public announcement. -/
@[simp] theorem unitAnnouncementSpaceEquiv_symm_apply (B : Boundary P) (x : B.space) :
    (unitAnnouncementSpaceEquiv B).symm x = ⟨⟨(), x.1⟩, x.2⟩ :=
  rfl

/-- Reindexing away the unique public block cancels its Kraus inclusion. -/
@[simp] theorem reindexOp_comp_matrixConjLinear_publicInclKraus_unit (B : Boundary P) :
    (reindexOp (unitAnnouncementSpaceEquiv B)).comp
        (matrixConjLinear (publicInclKraus (fun _ : Unit => B) ())) =
      LinearMap.id := by
  apply LinearMap.ext
  intro rho
  ext p q
  simp only [reindexOp, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.submatrix_apply, unitAnnouncementSpaceEquiv_symm_apply,
    matrixConjLinear, Matrix.mul_apply, Matrix.conjTranspose_apply,
    publicInclKraus_apply, publicSpaceEquiv_apply, LinearMap.id_apply]
  simp

/-- Operators on a boundary are block diagonal when distinct complete exits have no cross terms. -/
def IsExitBlockDiagonal (B : Boundary P) (ρ : Op B.space) : Prop :=
  ∀ (e f : B.Exit) (a : (B.system e).total) (b : (B.system f).total),
    e ≠ f → ρ ⟨e, a⟩ ⟨f, b⟩ = 0

end Boundary

namespace Program

/-- The finite hidden complete paths through a program.

Only raw outcomes and Kraus multiplicities occur here.  Public continuation control still sees
only `A.announce o`, and a private continuation remains independent of `o` and `r`.
-/
def Branch {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) : Type :=
  match p with
  | @Program.done _ _ _ _ => Unit
  | @Program.announced _ _ _ _ _ _ _ A _ k =>
      Σ o : A.Outcome, Σ _r : A.krausIndex o, Branch (k (A.announce o))
  | @Program.priv _ _ _ _ _ A k =>
      Σ o : A.Outcome, Σ _r : A.instrument.krausIndex o, Branch k

/-- Complete hidden paths form a finite type. -/
instance instFintypeBranch {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) : Fintype
    p.Branch :=
  match p with
  | @Program.done _ _ _ _ => inferInstanceAs (Fintype Unit)
  | @Program.announced _ _ _ _ _ _ _ A _ k =>
      @Sigma.instFintype A.Outcome
        (fun o => Σ _r : A.krausIndex o, Branch (k (A.announce o)))
        (fun o => @Sigma.instFintype (A.krausIndex o)
          (fun _r => Branch (k (A.announce o)))
          (fun _r => instFintypeBranch (k (A.announce o))) (A.finKrausIndex o))
        inferInstance
  | @Program.priv _ _ _ _ _ A k =>
      @Sigma.instFintype A.Outcome
        (fun o => Σ _r : A.instrument.krausIndex o, Branch k)
        (fun o => @Sigma.instFintype (A.instrument.krausIndex o)
          (fun _r => Branch k) (fun _r => instFintypeBranch k)
          (A.instrument.finKrausIndex o)) inferInstance

namespace Branch

/-- The complete public exit reached by a hidden branch. -/
def exit {R : MultipartiteSystem P} {B : Boundary P} {p : Program R B} : p.Branch → B.Exit :=
  match p with
  | @Program.done _ _ _ _ => fun _ => ()
  | @Program.announced _ _ _ _ _ _ _ A _ k => fun b =>
      ⟨A.announce b.1, exit (p := k (A.announce b.1)) b.2.2⟩
  | @Program.priv _ _ _ _ _ _ k => fun b => exit (p := k) b.2.2

/-- The product of joint-register Kraus matrices along a hidden branch.

Later actions multiply on the left because these matrices act on column vectors from the right.
-/
noncomputable def pathKraus {R : MultipartiteSystem P} {B : Boundary P} {p : Program R B} (b :
    p.Branch) :
    Matrix (B.system b.exit).total R.total ℂ :=
  match p, b with
  | @Program.done _ _ _ R, () => (1 : Matrix R.total R.total ℂ)
  | @Program.announced _ _ _ _ _ _ _ A _ k, b =>
      pathKraus (p := k (A.announce b.1)) b.2.2 * A.liftedKraus b.1 b.2.1
  | @Program.priv _ _ _ _ _ A k, b =>
      pathKraus (p := k) b.2.2 * A.liftedKraus b.1 b.2.1

end Branch

/-- Compose a fixed earlier matrix with a complete dependent family of later matrices. -/
private theorem sum_path_comp {In Mid H : Type}
    [Fintype Mid] [DecidableEq Mid] [Fintype H]
    (Final : H → Type) [∀ h, Fintype (Final h)]
    (A : Matrix Mid In ℂ) (L : ∀ h, Matrix (Final h) Mid ℂ)
    (hL : ∑ h, (L h)ᴴ * L h = 1) :
    ∑ h, (L h * A)ᴴ * (L h * A) = Aᴴ * A := by
  calc
    _ = ∑ h, Aᴴ * ((L h)ᴴ * L h) * A := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (∑ h, Aᴴ * ((L h)ᴴ * L h)) * A := by
      rw [Matrix.sum_mul]
    _ = Aᴴ * (∑ h, (L h)ᴴ * L h) * A := by
      rw [Matrix.mul_sum]
    _ = Aᴴ * A := by rw [hL, Matrix.mul_one]

/-- Completeness of path Kraus matrices at a terminal program. -/
private theorem pathKraus_complete_done {R : MultipartiteSystem P} :
    ∑ b : (Program.done : Program R (.leaf R)).Branch,
      (b.pathKraus)ᴴ * b.pathKraus = 1 := by
  simp only [Branch, Branch.pathKraus, Fintype.sum_unique]
  change (1 : Op R.total)ᴴ * (1 : Op R.total) = (1 : Op R.total)
  simp

/-- Completeness of path Kraus matrices is preserved by an announced node. -/
private theorem pathKraus_complete_announced {R : MultipartiteSystem P} {Y : Type}
    [Fintype Y] [DecidableEq Y] (A : AnnouncedAction R Y)
    {B : Y → Boundary P} (k : ∀ y, Program (A.out y) (B y))
    (ih : ∀ y, ∑ b : (k y).Branch, (b.pathKraus)ᴴ * b.pathKraus = 1) :
    ∑ b : (Program.announced A k).Branch, (b.pathKraus)ᴴ * b.pathKraus = 1 := by
  simp only [Branch]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  change ∑ o, ∑ r, ∑ b : (k (A.announce o)).Branch,
    (b.pathKraus * A.liftedKraus o r)ᴴ * (b.pathKraus * A.liftedKraus o r) = 1
  have hcomp (o : A.Outcome) (r : A.krausIndex o) :=
    sum_path_comp
      (Final := fun b : (k (A.announce o)).Branch =>
        ((B (A.announce o)).system b.exit).total)
      (A.liftedKraus o r) (fun b => b.pathKraus) (ih (A.announce o))
  simp_rw [hcomp]
  exact A.liftedKraus_complete

/-- Completeness of path Kraus matrices is preserved by a private node. -/
private theorem pathKraus_complete_priv {R : MultipartiteSystem P} {B : Boundary P}
    (A : PrivateAction R) (k : Program A.out B)
    (ih : ∑ b : k.Branch, (b.pathKraus)ᴴ * b.pathKraus = 1) :
    ∑ b : (Program.priv A k).Branch, (b.pathKraus)ᴴ * b.pathKraus = 1 := by
  simp only [Branch]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  change ∑ o, ∑ r, ∑ b : k.Branch,
    (b.pathKraus * A.liftedKraus o r)ᴴ * (b.pathKraus * A.liftedKraus o r) = 1
  have hcomp (o : A.Outcome) (r : A.instrument.krausIndex o) :=
    sum_path_comp (Final := fun b : k.Branch => (B.system b.exit).total)
      (A.liftedKraus o r) (fun b => b.pathKraus) ih
  simp_rw [hcomp]
  exact A.liftedKraus_complete

/-- The path Kraus matrices of a complete program are complete on its input register. -/
theorem pathKraus_complete {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) :
    ∑ b : p.Branch, (b.pathKraus)ᴴ * b.pathKraus = 1 :=
  match p with
  | .done => pathKraus_complete_done
  | @Program.announced _ _ _ _ Y finY decY A B k =>
      @pathKraus_complete_announced P _ _ _ Y finY decY A B k
        (fun y => pathKraus_complete (k y))
  | .priv A k => pathKraus_complete_priv A k (pathKraus_complete k)

/-- A complete program has a complete public exit.

Completeness on the inhabited input register supplies a hidden path, whose public exit lies
in the declared boundary. This does not assert that every declared exit is reachable. -/
theorem nonempty_exit {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) : Nonempty
    B.Exit := by
  classical
  have hsum : (∑ b : p.Branch, (b.pathKraus)ᴴ * b.pathKraus) ≠ 0 := by
    rw [p.pathKraus_complete]
    exact one_ne_zero
  obtain ⟨b, _⟩ := Finset.nonempty_of_sum_ne_zero hsum
  exact ⟨b.exit⟩

/-- A hidden branch's Kraus matrix with its final row embedded into the common boundary space. -/
noncomputable def kraus {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) (b : p.Branch)
    :
    Matrix B.space R.total ℂ :=
  Boundary.exitKraus B b.exit * b.pathKraus

/-- The common-output Kraus matrix of an announced node factors as the selected public-block
inclusion, the continuation Kraus matrix, and the current local Kraus matrix.

This is the matrix form of public-outcome-controlled continuation for the finite-round LOCC
instrument trees of Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2. -/
@[simp] theorem kraus_announced {R : MultipartiteSystem P} {Y : Type}
    [Fintype Y] [DecidableEq Y] (A : AnnouncedAction R Y)
    {B : Y → Boundary P} (k : ∀ y, Program (A.out y) (B y))
    (o : A.Outcome) (r : A.krausIndex o) (b : (k (A.announce o)).Branch) :
    (Program.announced A k).kraus ⟨o, ⟨r, b⟩⟩ =
      Boundary.publicInclKraus B (A.announce o) *
        ((k (A.announce o)).kraus b * A.liftedKraus o r) := by
  simp only [kraus, Branch.exit, Branch.pathKraus, Boundary.exitKraus_announce]
  rw [Matrix.mul_assoc]
  exact Matrix.mul_assoc _ _ _

/-- The common-output Kraus matrix of a private node is the continuation Kraus matrix multiplied
by the current local Kraus matrix.

This is sequential composition at a non-announced node of the finite-round LOCC instrument tree
in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2. -/
@[simp] theorem kraus_priv {R : MultipartiteSystem P} {B : Boundary P}
    (A : PrivateAction R) (k : Program A.out B)
    (o : A.Outcome) (r : A.instrument.krausIndex o) (b : k.Branch) :
    (Program.priv A k).kraus ⟨o, ⟨r, b⟩⟩ =
      k.kraus b * A.liftedKraus o r := by
  simp only [kraus, Branch.exit, Branch.pathKraus, Matrix.mul_assoc]
  rfl

/-- The common-output Kraus family of a complete program is complete. -/
theorem kraus_complete {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) :
    ∑ b : p.Branch, (p.kraus b)ᴴ * p.kraus b = 1 := by
  calc
    _ = ∑ b : p.Branch, (b.pathKraus)ᴴ * b.pathKraus := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [kraus, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Boundary.exitKraus B b.exit)ᴴ
        (Boundary.exitKraus B b.exit) b.pathKraus,
        Boundary.exitKraus_conjTranspose_mul_self, Matrix.one_mul]
    _ = 1 := p.pathKraus_complete

/-- The complete-path instrument of a program.  Its unique observed outcome is `Unit`; the public
exit is represented exactly once, by the corresponding summand of `B.space`. -/
noncomputable def toInstrument {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) :
    Instrument R.total B.space Unit where
  krausIndex _ := p.Branch
  kraus _ := p.kraus
  complete := by simpa using p.kraus_complete

/-- The channel denoted by a branch-dependent typed LOCC program. -/
noncomputable def denote {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) :
    Op R.total →ₗ[ℂ] Op B.space :=
  p.toInstrument.channel

/-- The denotation is the sum of conjugations by all common-output path Kraus matrices. -/
theorem denote_eq_krausSum {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) :
    p.denote = ∑ b : p.Branch, matrixConjLinear (p.kraus b) := by
  simp only [denote, toInstrument, Instrument.channel, Instrument.operation, Fintype.sum_unique]
  rfl

/-- Termination places the input operator in the unique terminal output block, inserting the
trivial exit coordinate of the terminal boundary.

This is the completed-branch case of the finite-round LOCC instrument tree in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2. -/
@[simp] theorem denote_done {R : MultipartiteSystem P} :
    (Program.done : Program R (.leaf R)).denote =
      (Matrix.reindexLinearEquiv ℂ ℂ (Boundary.leafSpaceEquiv R).symm
        (Boundary.leafSpaceEquiv R).symm).toLinearMap := by
  have hkraus : (Program.done : Program R (.leaf R)).kraus () =
      Boundary.exitKraus (.leaf R) () := Matrix.mul_one _
  rw [denote_eq_krausSum]
  change (∑ b : Unit, matrixConjLinear ((Program.done : Program R (.leaf R)).kraus b)) = _
  rw [Fintype.sum_unique, hkraus]
  apply LinearMap.ext
  intro ρ
  ext p q
  rcases p with ⟨⟨⟩, p⟩
  rcases q with ⟨⟨⟩, q⟩
  change R.total at p q
  let E : Matrix (Σ _ : Unit, R.total) R.total ℂ := Boundary.exitKraus (.leaf R) ()
  have hE (x : Σ _ : Unit, R.total) (y : R.total) :
      E x y = if x = ⟨(), y⟩ then 1 else 0 := rfl
  change (E * ρ * Eᴴ) ⟨(), p⟩ ⟨(), q⟩ = ρ p q
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hE]

/-- Denotation of an announced node is the sum over its raw outcomes and hidden Kraus indices of
the current local operation, the selected continuation, and inclusion into the selected public
output block.

Only `A.announce o` selects the continuation.  This is the coarse-grained public control rule for
finite-round LOCC instrument trees in Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2. -/
theorem denote_announced {R : MultipartiteSystem P} {Y : Type} [Fintype Y] [DecidableEq Y]
    (A : AnnouncedAction R Y)
    {B : Y → Boundary P} (k : ∀ y, Program (A.out y) (B y)) :
    (Program.announced A k).denote =
      ∑ o : A.Outcome, ∑ r : A.krausIndex o,
        (matrixConjLinear (Boundary.publicInclKraus B (A.announce o))).comp
          ((k (A.announce o)).denote.comp (matrixConjLinear (A.liftedKraus o r))) := by
  rw [denote_eq_krausSum]
  simp only [Branch, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑ b : (k (A.announce o)).Branch,
        (matrixConjLinear (Boundary.publicInclKraus B (A.announce o))).comp
          ((matrixConjLinear ((k (A.announce o)).kraus b)).comp
            (matrixConjLinear (A.liftedKraus o r))) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [kraus_announced, matrixConjLinear_mul, matrixConjLinear_mul]
    _ = (matrixConjLinear (Boundary.publicInclKraus B (A.announce o))).comp
          ((∑ b : (k (A.announce o)).Branch,
              matrixConjLinear ((k (A.announce o)).kraus b)).comp
            (matrixConjLinear (A.liftedKraus o r))) := by
      apply LinearMap.ext
      intro ρ
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    _ = _ := by rw [← (k (A.announce o)).denote_eq_krausSum]

/-- Denotation of an announced node, compressed to the completely positive operation associated
with each raw outcome.  Public continuation depends only on `A.announce o`, as in the finite-round
LOCC instrument trees of Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2. -/
theorem denote_announced_eq_sum_liftedOperation {R : MultipartiteSystem P} {Y : Type}
    [Fintype Y] [DecidableEq Y] (A : AnnouncedAction R Y)
    {B : Y → Boundary P} (k : ∀ y, Program (A.out y) (B y)) :
    (Program.announced A k).denote =
      ∑ o : A.Outcome,
        (matrixConjLinear (Boundary.publicInclKraus B (A.announce o))).comp
          ((k (A.announce o)).denote.comp (A.liftedOperation o)) := by
  rw [denote_announced]
  apply Finset.sum_congr rfl
  intro o _
  apply LinearMap.ext
  intro rho
  simp only [AnnouncedAction.liftedOperation, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]

/-- Relabelling raw outcomes preserves the denotation when it preserves announcements, lifted
operations, and continuation denotations. The output systems are computed independently for the
two actions, so operation and continuation equality use heterogeneous equality. -/
theorem denote_announced_congr_outcomeEquiv
    {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P}
    {Public : Type} [Fintype Public] [DecidableEq Public]
    {B : Public → Boundary P}
    (oldAction newAction : AnnouncedAction R Public)
    (e : oldAction.Outcome ≃ newAction.Outcome)
    (hannounce : ∀ o, newAction.announce (e o) = oldAction.announce o)
    (hoperation : ∀ o (rho : Op R.total),
      HEq (oldAction.liftedOperation o rho)
        (newAction.liftedOperation (e o) rho))
    (oldCont : ∀ y, Program (oldAction.out y) (B y))
    (newCont : ∀ y, Program (newAction.out y) (B y))
    (hcont : ∀ y, HEq (⇑(newCont y).denote) (⇑(oldCont y).denote))
    (rho : Op R.total) :
    (newAction.then newCont).denote rho =
      (oldAction.then oldCont).denote rho := by
  unfold AnnouncedAction.then
  rw [Program.denote_announced_eq_sum_liftedOperation,
    Program.denote_announced_eq_sum_liftedOperation]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro o _
  have hterm (y z : Public) (hy : y = z)
      (sigma : Op (newAction.out y).total) (tau : Op (oldAction.out z).total)
      (h : HEq sigma tau) :
      matrixConjLinear (Boundary.publicInclKraus B y) ((newCont y).denote sigma) =
        matrixConjLinear (Boundary.publicInclKraus B z) ((oldCont z).denote tau) := by
    subst z
    rw [congr_heq (hcont y) h]
  exact hterm _ _ (hannounce o) _ _ (hoperation o rho).symm

/-- Denotation of a private node is the sum of the continuation after every raw outcome and hidden
Kraus index of the current local action; no outcome is available to select a continuation.

This is the non-announced node equation for finite-round LOCC instrument trees in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2. -/
theorem denote_priv {R : MultipartiteSystem P} {B : Boundary P}
    (A : PrivateAction R) (k : Program A.out B) :
    (Program.priv A k).denote =
      ∑ o : A.Outcome, ∑ r : A.instrument.krausIndex o,
        k.denote.comp (matrixConjLinear (A.liftedKraus o r)) := by
  rw [denote_eq_krausSum]
  simp only [Branch, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑ b : k.Branch,
        (matrixConjLinear (k.kraus b)).comp
          (matrixConjLinear (A.liftedKraus o r)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [kraus_priv, matrixConjLinear_mul]
    _ = (∑ b : k.Branch, matrixConjLinear (k.kraus b)).comp
          (matrixConjLinear (A.liftedKraus o r)) := by
      apply LinearMap.ext
      intro ρ
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    _ = _ := by rw [← k.denote_eq_krausSum]

/-- Denotation of a private node, compressed to the completely positive operation associated with
each raw outcome.  The same outcome-independent continuation is composed after every outcome
operation; the outer sum then coarse-grains away the local outcome. -/
theorem denote_priv_eq_sum_liftedOperation {R : MultipartiteSystem P} {B : Boundary P}
    (A : PrivateAction R) (k : Program A.out B) :
    (Program.priv A k).denote =
      ∑ o : A.Outcome, k.denote.comp (A.liftedOperation o) := by
  rw [denote_priv]
  apply Finset.sum_congr rfl
  intro o _
  apply LinearMap.ext
  intro rho
  simp only [PrivateAction.liftedOperation, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]

/-- A matrix entry of a branch Kraus operator vanishes outside that branch's exit block. -/
theorem kraus_apply_eq_zero_of_exit_ne {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
    (b : p.Branch) {e : B.Exit} (h : e ≠ b.exit) (a : (B.system e).total) (x : R.total) :
    p.kraus b ⟨e, a⟩ x = 0 := by
  simp only [kraus, Matrix.mul_apply, Boundary.exitKraus_apply]
  apply Finset.sum_eq_zero
  intro q _
  rw [if_neg]
  · simp
  · intro heq
    exact h (congrArg Sigma.fst heq)

/-- A program denotation has zero matrix entries between distinct complete public exits. -/
theorem denote_isExitBlockDiagonal {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
    (ρ : Op R.total) : Boundary.IsExitBlockDiagonal B (p.denote ρ) := by
  intro e f a c hef
  rw [p.denote_eq_krausSum]
  simp only [LinearMap.sum_apply, matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases he : e = b.exit
  · have hf : f ≠ b.exit := fun h => hef (he.trans h.symm)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [p.kraus_apply_eq_zero_of_exit_ne b hf c x, star_zero, mul_zero]
  · simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [show (∑ j, p.kraus b ⟨e, a⟩ j * ρ j x) = 0 by
      apply Finset.sum_eq_zero
      intro j _
      rw [p.kraus_apply_eq_zero_of_exit_ne b he a j, zero_mul], zero_mul]

/-- In particular, the denotation of a program with an announced output boundary has zero entries
between distinct outer public blocks. -/
theorem denote_public_block_zero {R : MultipartiteSystem P} {Y : Type} [Fintype Y] [DecidableEq Y]
    {next : Y → Boundary P} (p : Program R (.announce Y next)) (ρ : Op R.total)
    {y z : Y} (hyz : y ≠ z) (e : (next y).Exit) (f : (next z).Exit)
    (a : ((next y).system e).total) (b : ((next z).system f).total) :
    p.denote ρ ⟨⟨y, e⟩, a⟩ ⟨⟨z, f⟩, b⟩ = 0 := by
  apply p.denote_isExitBlockDiagonal ρ ⟨y, e⟩ ⟨z, f⟩ a b
  intro h
  exact hyz (congrArg (fun x => x.1) h)

/-- **An announced node read inside one public block.** Let the announcement relabel raw
outcomes by the equivalence `e`. In the block `A.announce o`, the denotation is the continuation
`k (A.announce o)` applied to the lifted operation of `o`; all other outcomes enter different
public blocks. The continuation boundary may depend on the announced value. -/
theorem denote_then_publicSpaceEquiv_symm_apply {R : MultipartiteSystem P} {Pub : Type}
    [Fintype Pub] [DecidableEq Pub] (A : AnnouncedAction R Pub) (e : A.Outcome ≃ Pub)
    (he : ∀ o, A.announce o = e o) (B : Pub → Boundary P)
    (k : ∀ y, Program (A.out y) (B y)) (ρ : Op R.total) (o : A.Outcome)
    (u v : (B (A.announce o)).space) :
    (A.then k).denote ρ ((Boundary.publicSpaceEquiv B).symm ⟨A.announce o, u⟩)
        ((Boundary.publicSpaceEquiv B).symm ⟨A.announce o, v⟩) =
      (k (A.announce o)).denote (A.liftedOperation o ρ) u v := by
  rw [AnnouncedAction.then, denote_announced_eq_sum_liftedOperation]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
  have hrow (w : (B (A.announce o)).space) :
      Boundary.publicInclKraus B (A.announce o)
          ((Boundary.publicSpaceEquiv B).symm ⟨A.announce o, w⟩) = Pi.single w 1 := by
    funext w'
    rw [Boundary.publicInclKraus_apply, Equiv.apply_symm_apply, Pi.single_apply]
    exact if_congr (by rw [Sigma.mk.inj_iff, heq_eq_eq]; exact (and_iff_right rfl).trans eq_comm)
      rfl rfl
  have hrow_ne {other : A.Outcome} (hne : other ≠ o) (w : (B (A.announce o)).space) :
      Boundary.publicInclKraus B (A.announce other)
          ((Boundary.publicSpaceEquiv B).symm ⟨A.announce o, w⟩) = 0 :=
    funext fun _ => Boundary.publicInclKraus_apply_eq_zero_of_fst_ne _ (by
      rw [Equiv.apply_symm_apply]
      exact fun h => hne (e.injective (by simpa only [he] using h)).symm) _
  rw [Fintype.sum_eq_single o]
  · rw [matrixConjLinear_apply_of_row_eq_single _ _ (hrow u) (hrow v), one_mul, star_one,
      mul_one]
  · intro other hne
    exact matrixConjLinear_apply_eq_zero_of_row_left _ _ (hrow_ne hne u) _

/-- The complete-path denotation is CPTP after any explicit finite coordinate choices. -/
theorem coordinateDenote_isCPTP {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
    {dR dB : ℕ} [NeZero dR] [NeZero dB]
    (eR : R.total ≃ Fin dR) (eB : B.space ≃ Fin dB) :
    Quantum.Channels.IsCPTP ⇑(coordinateLinear eR eB p.denote) := by
  exact p.toInstrument.coordinateChannel_isCPTP eR eB

end Program

namespace PrivateAction

/-- A private action and its `Unit`-announced presentation have the same denotation after erasing
the canonical singleton public output coordinate.

The raw outcomes, Kraus fibres, and continuation are identical.  This is the one-node
coarse-graining identity for the finite-round LOCC instrument trees of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2.  The equality is semantic,
not definitional: the announced program retains a `Unit` transcript cell.
-/
@[simp] theorem reindex_denote_asUnitAnnouncement_then
    {R : MultipartiteSystem P} {B : Boundary P} (V : PrivateAction R) (k : Program V.out B) :
    (reindexOp (Boundary.unitAnnouncementSpaceEquiv B)).comp
        ((V.asUnitAnnouncement.then (fun _ => k)).denote) =
      (V.then k).denote := by
  rw [AnnouncedAction.then, Program.denote_announced,
    PrivateAction.then, Program.denote_priv]
  apply LinearMap.ext
  intro rho
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro r _
  rw [← LinearMap.comp_apply,
    Boundary.reindexOp_comp_matrixConjLinear_publicInclKraus_unit,
    LinearMap.id_apply]
  rfl

/-- Running a private action agrees with running its singleton-announced presentation after the
canonical output reindexing.  The latter program still records the explicit `Unit` public node. -/
@[simp] theorem reindex_denote_asUnitAnnouncement_run {R : MultipartiteSystem P}
    (V : PrivateAction R) :
    (reindexOp (Boundary.unitAnnouncementSpaceEquiv (Boundary.leaf V.out))).comp
        V.asUnitAnnouncement.run.denote =
      V.run.denote := by
  exact
    V.reindex_denote_asUnitAnnouncement_then
      (Program.done : Program V.out (.leaf V.out))

end PrivateAction
end TypedLOCC
