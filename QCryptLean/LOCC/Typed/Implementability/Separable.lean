import QCryptLean.LOCC.Typed.Implementability.ProductKraus
import QCryptLean.LOCC.Typed.Program.Denotation

/-!
# Separable instruments denoted by branch-dependent programs

Every complete hidden path through a finite `Program` composes to one product Kraus matrix across
the parties.  Grouping those paths by their public exit gives a dependent separable Kraus
presentation: different exits may have genuinely different final multipartite systems.  The common
boundary space is used only to store the orthogonal exit blocks and is never treated as a party
product.

The construction formalizes the finite LOCC instrument trees of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2, together with the treewise
composition and coarse-graining described in Appendix A.
-/

open scoped Matrix BigOperators

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## Separable maps between fixed multipartite systems -/

/-- A fixed-output map has a separable Kraus presentation when it is a finite sum of
conjugations by party-product matrices.

This predicate records the product-Kraus representation and does not add a trace-preservation
condition.  It is the fixed-exit separable-map condition used in the definition of SEP in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2. -/
def IsSeparableOperation {R S : MultipartiteSystem P} (Φ : Op R.total →ₗ[ℂ] Op S.total) : Prop :=
  ∃ (index : Type) (_ : Fintype index)
      (K : index → ∀ i, Matrix (S.reg i) (R.reg i) ℂ),
    Φ = ∑ x, matrixConjLinear (famKraus (K x))

/-! ## Product matrices along complete paths -/

namespace Program

namespace Branch

/-- The party-local factors accumulated along one complete hidden path.

Later local actions multiply on the left, matching `Program.Branch.pathKraus`.  This explicit
family is the typed version of multiplying the local Kraus operators along a measurement history
in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Appendix A. -/
noncomputable def partyKraus {R : MultipartiteSystem P} {B : Boundary P} {p : Program R B}
    (b : p.Branch) (i : P) : Matrix ((B.system b.exit).reg i) (R.reg i) ℂ :=
  match p, b with
  | @Program.done _ _ _ R, () => (1 : Matrix (R.reg i) (R.reg i) ℂ)
  | @Program.announced _ _ _ R _ _ _ A B _k, b =>
      partyKraus b.2.2 i *
        R.localFam A.actor (A.Output (A.announce b.1))
          (A.kraus b.1 b.2.1) i
  | @Program.priv _ _ _ R B A _k, ⟨o, r, b⟩ =>
      partyKraus b i * R.localFam A.actor A.Output (A.instrument.kraus o r) i

/-- The joint path Kraus matrix is exactly the product of its explicitly accumulated party
factors.

This is the treewise product-Kraus conclusion for a complete finite LOCC history in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem pathKraus_eq_famKraus {R : MultipartiteSystem P} {B : Boundary P} {p : Program R B}
    (b : p.Branch) : b.pathKraus = famKraus (b.partyKraus) := by
  induction p with
  | done =>
      rcases b with ⟨⟩
      simp [Program.Branch.pathKraus, partyKraus]
  | @announced R Y _ _ A B k ih =>
      rcases b with ⟨o, r, b⟩
      simp only [Program.Branch.pathKraus, partyKraus]
      rw [ih (A.announce o) b, A.liftedKraus_eq_famKraus, famKraus_mul]
  | @priv R B A k ih =>
      rcases b with ⟨o, r, b⟩
      simp only [Program.Branch.pathKraus, partyKraus]
      rw [ih b, A.liftedKraus_eq_famKraus, famKraus_mul]

end Branch

/-- Hidden program branches whose public exit is exactly `e`. -/
def ExitBranch {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) (e : B.Exit) : Type :=
  {b : p.Branch // b.exit = e}

/-- Branches over a fixed exit form a finite type. -/
instance instFintypeExitBranch {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) (e :
    B.Exit) :
    Fintype (p.ExitBranch e) :=
  Fintype.subtype (Finset.univ.filter fun b => b.exit = e) (by simp)

/-- Grouping all hidden branches by their public exit neither loses nor duplicates a branch. -/
def exitBranchSigmaEquiv {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) :
    (Σ e : B.Exit, p.ExitBranch e) ≃ p.Branch where
  toFun x := x.2.1
  invFun b := ⟨b.exit, ⟨b, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨e, b, h⟩
    subst e
    rfl
  right_inv _ := rfl

namespace ExitBranch

/-- The accumulated party factors of a branch, transported from its recorded exit to the fixed
exit indexing its fibre. -/
noncomputable def partyKraus {R : MultipartiteSystem P} {B : Boundary P} {p : Program R B}
    {e : B.Exit} (b : p.ExitBranch e) (i : P) :
    Matrix ((B.system e).reg i) (R.reg i) ℂ :=
  (b.1.partyKraus i).submatrix
    (Equiv.cast (congrArg (fun f => (B.system f).reg i) b.2).symm) id

/-- Transporting a branch's product matrix to its fixed exit gives its path Kraus matrix at that
exit. -/
theorem famKraus_partyKraus_eq {R : MultipartiteSystem P} {B : Boundary P} {p : Program R B}
    {e : B.Exit} (b : p.ExitBranch e) :
    famKraus b.partyKraus =
      b.1.pathKraus.submatrix
        (Equiv.cast (congrArg (fun f => (B.system f).total) b.2).symm) id := by
  rcases b with ⟨b, h⟩
  subst e
  simpa [partyKraus] using b.pathKraus_eq_famKraus.symm

/-- Embedding the transported product matrix into its fixed exit block recovers the program's
common-output Kraus matrix. -/
theorem exitKraus_mul_famKraus_partyKraus {R : MultipartiteSystem P} {B : Boundary P}
    {p : Program R B} {e : B.Exit} (b : p.ExitBranch e) :
    B.exitKraus e * famKraus b.partyKraus = p.kraus b.1 := by
  rcases b with ⟨b, h⟩
  subst e
  rw [famKraus_partyKraus_eq]
  rfl

/-- The Gram matrix of a transported exit-fibre product matrix is the Gram matrix of the
underlying path Kraus matrix. -/
theorem famKraus_partyKraus_gram {R : MultipartiteSystem P} {B : Boundary P} {p : Program R B}
    {e : B.Exit} (b : p.ExitBranch e) :
    (famKraus b.partyKraus)ᴴ * famKraus b.partyKraus =
      b.1.pathKrausᴴ * b.1.pathKraus := by
  rcases b with ⟨b, h⟩
  subst e
  simpa [partyKraus] using
    (congrArg (fun K => Kᴴ * K) b.pathKraus_eq_famKraus).symm

end ExitBranch

end Program

/-! ## Honest separability over a heterogeneous boundary -/

namespace Boundary

/-- A separable instrument presentation over a heterogeneous public boundary.

The Kraus index and the party-local output matrices depend on the public exit `e`; their product
matrix therefore targets the genuine multipartite system `B.system e`.  Only then is it included
into the common classical-quantum output block `B.space`.  The second conjunct is global Kraus
completeness, so this predicate certifies an instrument rather than merely a collection of separable
CP maps.

No party-product structure is assigned to `B.space`.  This dependent formulation is the finite
outcome separable-instrument representation corresponding to the SEP definition and LOCC tree
coarse-graining in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and
Appendix A. -/
def IsSeparableInstrument {R : MultipartiteSystem P} (B : Boundary P)
    (Φ : Op R.total →ₗ[ℂ] Op B.space) : Prop :=
  ∃ (index : B.Exit → Type) (_ : ∀ e, Fintype (index e))
      (K : ∀ e, index e → ∀ i, Matrix ((B.system e).reg i) (R.reg i) ℂ),
    Φ = ∑ e, ∑ x, matrixConjLinear (B.exitKraus e * famKraus (K e x)) ∧
      ∑ e, ∑ x, (famKraus (K e x))ᴴ * famKraus (K e x) = 1

/-- Compress a boundary-valued map to the quantum block at one public exit. -/
noncomputable def exitOperation {R : MultipartiteSystem P} (B : Boundary P) (e : B.Exit)
    (Φ : Op R.total →ₗ[ℂ] Op B.space) :
    Op R.total →ₗ[ℂ] Op (B.system e).total :=
  (matrixConjLinear (B.exitKraus e)ᴴ).comp Φ

end Boundary

namespace Program

/-- The denotation of a program is the sum of its product-Kraus branch operations, grouped by
public exit.

This is the dependent-output/direct-sum analogue of the finite LOCC tree expansion and
public-outcome coarse-graining in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem denote_eq_exitBranchSum {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) :
    p.denote = ∑ e : B.Exit, ∑ b : p.ExitBranch e,
      matrixConjLinear (B.exitKraus e * famKraus b.partyKraus) := by
  rw [p.denote_eq_krausSum]
  calc
    _ = ∑ b : Σ e : B.Exit, p.ExitBranch e,
        matrixConjLinear (B.exitKraus b.1 * famKraus b.2.partyKraus) :=
      (Fintype.sum_equiv p.exitBranchSigmaEquiv _ _ fun b => by
        rw [ExitBranch.exitKraus_mul_famKraus_partyKraus]
        rfl).symm
    _ = ∑ e : B.Exit, ∑ b : p.ExitBranch e,
        matrixConjLinear (B.exitKraus e * famKraus b.partyKraus) :=
      Fintype.sum_sigma _

/-- The product Kraus matrices of all hidden branches, grouped by public exit, satisfy the global
completeness relation.

This is the dependent-output/direct-sum analogue of the branchwise completeness relation for the
finite LOCC tree expansion in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem exitBranch_famKraus_gram_sum {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) :
    (∑ e : B.Exit, ∑ b : p.ExitBranch e,
      (famKraus b.partyKraus)ᴴ * famKraus b.partyKraus) = 1 := by
  calc
    _ = ∑ b : Σ e : B.Exit, p.ExitBranch e,
        (famKraus b.2.partyKraus)ᴴ * famKraus b.2.partyKraus :=
      (Fintype.sum_sigma _).symm
    _ = ∑ b : p.Branch, b.pathKrausᴴ * b.pathKraus :=
      Fintype.sum_equiv p.exitBranchSigmaEquiv _ _ fun b => by
        simpa [exitBranchSigmaEquiv] using
          ExitBranch.famKraus_partyKraus_gram b.2
    _ = 1 := p.pathKraus_complete

/-- Every finite branch-dependent LOCC program denotes a complete separable instrument over its
heterogeneous output boundary.

The proof groups complete hidden histories by public exit and uses
`Program.Branch.pathKraus_eq_famKraus`.  It is the direct typed form of the finite LOCC tree
expansion in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Appendix A. -/
theorem denote_isSeparableInstrument {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) :
    B.IsSeparableInstrument p.denote := by
  let K : ∀ e, p.ExitBranch e → ∀ i, Matrix ((B.system e).reg i) (R.reg i) ℂ :=
    fun _ b => b.partyKraus
  refine ⟨fun e => p.ExitBranch e, fun e => p.instFintypeExitBranch e, K, ?_, ?_⟩
  · simpa [K] using p.denote_eq_exitBranchSum
  · simpa [K] using p.exitBranch_famKraus_gram_sum

/-- The CP operation associated with one public exit of a program. -/
noncomputable def denoteExit {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) (e :
    B.Exit) :
    Op R.total →ₗ[ℂ] Op (B.system e).total :=
  B.exitOperation e p.denote

/-- The operation at a fixed public exit is the sum of the product-Kraus operations of precisely
the hidden branches in that exit fibre.

This is the fixed-exit part of the typed dependent-output/direct-sum generalization of the finite
LOCC tree expansion in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem denoteExit_eq_exitBranchSum {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) (e
    : B.Exit) :
    p.denoteExit e =
      ∑ b : p.ExitBranch e, matrixConjLinear (famKraus b.partyKraus) := by
  apply LinearMap.ext
  intro ρ
  simp only [denoteExit, Boundary.exitOperation, p.denote_eq_exitBranchSum,
    LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single e]
  · apply Finset.sum_congr rfl
    intro b _
    rw [← LinearMap.comp_apply, ← matrixConjLinear_mul]
    congr 1
    rw [← Matrix.mul_assoc, Boundary.exitKraus_conjTranspose_mul_self, Matrix.one_mul]
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro b _
    rw [← LinearMap.comp_apply, ← matrixConjLinear_mul]
    have horth : (B.exitKraus e)ᴴ * B.exitKraus f = 0 :=
      sigmaInclKraus_conjTranspose_mul_of_ne (fun z => (B.system z).total) hfe.symm
    rw [← Matrix.mul_assoc, horth, Matrix.zero_mul]
    simp [matrixConjLinear]
  · simp

/-- Reinserting every fixed-exit operation into its boundary block and summing recovers the full
program denotation.

This is the public-exit reassembly in the typed dependent-output/direct-sum generalization of the
finite LOCC tree coarse-graining in
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and Appendix A. -/
theorem denote_eq_exitKraus_comp_denoteExit_sum {R : MultipartiteSystem P} {B : Boundary P}
    (p : Program R B) :
    p.denote =
      ∑ e : B.Exit, (matrixConjLinear (B.exitKraus e)).comp (p.denoteExit e) := by
  rw [p.denote_eq_exitBranchSum]
  apply Finset.sum_congr rfl
  intro e _
  rw [p.denoteExit_eq_exitBranchSum]
  apply LinearMap.ext
  intro ρ
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← LinearMap.comp_apply, ← matrixConjLinear_mul]

end Program

namespace Boundary.IsSeparableInstrument

/-- Every exit operation of a separable boundary instrument is a separable fixed-system operation.

The result is only a CP exit operation in general.  It is not asserted to be trace preserving:
only the sum over all exits satisfies the global completeness equation in
`Boundary.IsSeparableInstrument`. -/
theorem exitOperation_isSeparable {R : MultipartiteSystem P} {B : Boundary P}
    {Φ : Op R.total →ₗ[ℂ] Op B.space} (h : B.IsSeparableInstrument Φ) (e : B.Exit) :
    IsSeparableOperation (B.exitOperation e Φ) := by
  obtain ⟨index, hindex, K, hΦ, _⟩ := h
  refine ⟨index e, hindex e, K e, ?_⟩
  apply LinearMap.ext
  intro ρ
  simp only [Boundary.exitOperation, hΦ, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single e]
  · apply Finset.sum_congr rfl
    intro x _
    rw [← LinearMap.comp_apply, ← matrixConjLinear_mul]
    congr 1
    rw [← Matrix.mul_assoc, Boundary.exitKraus_conjTranspose_mul_self, Matrix.one_mul]
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro x _
    rw [← LinearMap.comp_apply, ← matrixConjLinear_mul]
    have horth : (B.exitKraus e)ᴴ * B.exitKraus f = 0 :=
      sigmaInclKraus_conjTranspose_mul_of_ne (fun z => (B.system z).total) hfe.symm
    rw [← Matrix.mul_assoc, horth, Matrix.zero_mul]
    simp [matrixConjLinear]
  · simp

end Boundary.IsSeparableInstrument

namespace Program

/-- The operation at every fixed public exit of a program is separable.

It is an individual CP, trace-nonincreasing branch in general; the theorem does not claim that a
single exit is CPTP. -/
theorem denoteExit_isSeparable {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) (e :
    B.Exit) :
    IsSeparableOperation (p.denoteExit e) :=
  (p.denote_isSeparableInstrument).exitOperation_isSeparable e

/-- A map that is not separable cannot be the operation at a specified exit of any program with
the given boundary. -/
theorem not_mem_denoteExit_image_of_not_isSeparable {R : MultipartiteSystem P} {B : Boundary P}
    (e : B.Exit) (Φ : Op R.total →ₗ[ℂ] Op (B.system e).total)
    (hΦ : ¬ IsSeparableOperation Φ) :
    ¬ ∃ p : Program R B, p.denoteExit e = Φ := by
  rintro ⟨p, rfl⟩
  exact hΦ (p.denoteExit_isSeparable e)

/-- Strip the unique public-exit coordinate from a program with a fixed terminal leaf. -/
noncomputable def denoteLeaf {R S : MultipartiteSystem P} (p : Program R (.leaf S)) :
    Op R.total →ₗ[ℂ] Op S.total :=
  p.denoteExit ()

/-- The fixed-leaf denotation of every program is a separable operation. -/
theorem denoteLeaf_isSeparable {R S : MultipartiteSystem P} (p : Program R (.leaf S)) :
    IsSeparableOperation p.denoteLeaf :=
  p.denoteExit_isSeparable ()

/-- A nonseparable fixed-system map is not the fixed-leaf denotation of any program. -/
theorem not_mem_denoteLeaf_image_of_not_isSeparable {R S : MultipartiteSystem P}
    (Φ : Op R.total →ₗ[ℂ] Op S.total) (hΦ : ¬ IsSeparableOperation Φ) :
    ¬ ∃ p : Program R (.leaf S), p.denoteLeaf = Φ := by
  rintro ⟨p, rfl⟩
  exact hΦ p.denoteLeaf_isSeparable

end Program

end TypedLOCC
