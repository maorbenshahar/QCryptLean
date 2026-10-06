import QCryptLean.LOCC.Typed.Channel

/-!
# Operational equivalence of instruments

This module identifies instruments with the same observed completely positive operations.  It is
independent of any program syntax: equality is imposed on physical outcomes, never on the hidden
Kraus representative used to present their CP maps.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace TypedLOCC

namespace Instrument

/-- Two instruments with the same observed outcome type are operationally equivalent when the
completely positive operation attached to every observed outcome is the same.

This is the instrument-level identification used in Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2: protocol branches are indexed by the observed CP maps, not by a
particular Kraus representation of those maps. -/
def OperationallyEquivalent {A B Outcome : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype Outcome]
    (I J : Instrument A B Outcome) : Prop :=
  ∀ o, I.operation o = J.operation o

namespace OperationallyEquivalent

/-- Operationally equivalent instruments denote the same total channel.  This is the sum over
the observed CP maps in arXiv:1210.4583, Section 2. -/
theorem channel_eq {A B Outcome : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype Outcome]
    {I J : Instrument A B Outcome} (hIJ : I.OperationallyEquivalent J) :
    I.channel = J.channel := by
  unfold Instrument.channel
  exact Finset.sum_congr rfl fun o _ => hIJ o

/-- Recording the observed outcome in an output register respects operational equivalence.
This is the outcome-labelled CP-map semantics of an instrument from arXiv:1210.4583, Section 2,
specialized to the explicit `Instrument.keeping` construction. -/
theorem keeping {A B Outcome : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype Outcome] [DecidableEq Outcome]
    {I J : Instrument A B Outcome} (hIJ : I.OperationallyEquivalent J) :
    I.keeping.OperationallyEquivalent J.keeping := by
  intro o
  apply LinearMap.ext
  intro ρ
  ext p q
  have hop := congrArg (fun f => f ρ) (hIJ o)
  have hop_entry := congrFun (congrFun hop p.1) q.1
  simp only [Instrument.operation, LinearMap.sum_apply] at hop_entry ⊢
  by_cases hp : p.2 = o
  · by_cases hq : q.2 = o
    · simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
        Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Instrument.keeping,
        Matrix.of_apply, hp, ↓reduceIte, hq] at hop_entry ⊢
      exact hop_entry
    · simp [Instrument.keeping, matrixConjLinear, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, hq]
  · simp [Instrument.keeping, matrixConjLinear, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hp]

/-- Tensoring every observed CP map with spectator identities and transporting along the same
multipartite system equivalences respects operational equivalence.  This is the local-extension
operation in the LOCC instrument trees of arXiv:1210.4583, Section 2, specialized to
`Instrument.liftAt`. -/
theorem liftAt {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P} (i : P) {HH : Type}
    [Nonempty HH] [Fintype HH] [DecidableEq HH]
    {Outcome : Type} [Fintype Outcome]
    {I J : Instrument (R.reg i) HH Outcome}
    (hIJ : I.OperationallyEquivalent J) :
    (I.liftAt R i).OperationallyEquivalent (J.liftAt R i) := by
  intro o
  apply LinearMap.ext
  intro ρ
  ext a b
  let ρab : Op (R.reg i) :=
    ρ.submatrix
      (fun x => (R.splitAt i).symm (x, ((R.splitAtSet i HH) a).2))
      (fun y => (R.splitAt i).symm (y, ((R.splitAtSet i HH) b).2))
  have hsum (f : R.total → ℂ) :
      (∑ x, f x) =
        ∑ p : R.reg i × R.rest i, f ((R.splitAt i).symm p) := by
    exact (Equiv.sum_comp (R.splitAt i).symm f).symm
  have hlift (L : Instrument (R.reg i) HH Outcome) :
      ((L.liftAt R i).operation o ρ) a b =
        (L.operation o ρab) ((R.splitAtSet i HH) a).1
          ((R.splitAtSet i HH) b).1 := by
    simp only [operation, Instrument.liftAt, matrixConjLinear, LinearMap.coe_sum,
      LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Matrix.sum_apply, Matrix.mul_apply,
      localKrausLift_apply, ite_mul, zero_mul, Matrix.conjTranspose_apply, RCLike.star_def, ρab]
    simp_rw [hsum]
    simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
    simp [apply_ite]
    rfl
  rw [hlift I, hlift J]
  have hop_entry :=
    congrArg
      (fun f => f ρab ((R.splitAtSet i HH) a).1 ((R.splitAtSet i HH) b).1)
      (hIJ o)
  exact hop_entry

end OperationallyEquivalent
end Instrument

variable {A B Outcome : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype Outcome]

/-- Refine every hidden Kraus fibre by a factor of two, replacing each internal operator `K`
by two copies `K / √2`.  The extra Boolean index is representation data, not an observed
instrument outcome. -/
noncomputable def halfSplit (I : Instrument A B Outcome) : Instrument A B Outcome where
  krausIndex o := I.krausIndex o × Bool
  kraus o r := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • I.kraus o r.1
  complete := by
    have hc : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = ((2 : ℂ))⁻¹ := by
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
      norm_num
    have hstep : ∀ (o : Outcome) (r : I.krausIndex o × Bool),
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • I.kraus o r.1)ᴴ *
            ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • I.kraus o r.1)
          = ((2 : ℂ))⁻¹ • ((I.kraus o r.1)ᴴ * I.kraus o r.1) := by
      intro o r
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      simp [← hc]
    have hinner : ∀ (o : Outcome) (r : I.krausIndex o),
        (∑ _b : Bool, ((2 : ℂ))⁻¹ • ((I.kraus o r)ᴴ * I.kraus o r))
          = (I.kraus o r)ᴴ * I.kraus o r := by
      intro o r
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, two_nsmul, ← add_smul]
      norm_num
    simp only [hstep, Fintype.sum_prod_type, hinner]
    exact I.complete

/-- The refinement gives every hidden Kraus fibre twice its previous cardinality while leaving the
observed outcome type unchanged. -/
theorem halfSplit_krausIndex (I : Instrument A B Outcome) (o : Outcome) :
    Fintype.card ((halfSplit I).krausIndex o) = 2 * Fintype.card (I.krausIndex o) := by
  simp [halfSplit, Fintype.card_prod, mul_comm]

/-- Splitting hidden Kraus representatives leaves the completely positive operation attached to
each observed outcome unchanged.  This witnesses invariance under hidden Kraus refinement. -/
theorem halfSplit_operationallyEquivalent (I : Instrument A B Outcome) :
    I.OperationallyEquivalent (halfSplit I) := by
  intro o
  apply LinearMap.ext
  intro ρ
  simp only [Instrument.operation, LinearMap.sum_apply, halfSplit, matrixConjLinear,
    LinearMap.coe_mk, AddHom.coe_mk]
  change (∑ x, I.kraus o x * ρ * (I.kraus o x)ᴴ) =
    ∑ x : I.krausIndex o × Bool,
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • I.kraus o x.1) * ρ *
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • I.kraus o x.1)ᴴ
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have hc : (star (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
      = ((2 : ℂ))⁻¹ := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [hc, two_nsmul, ← add_smul]
  norm_num

end TypedLOCC
