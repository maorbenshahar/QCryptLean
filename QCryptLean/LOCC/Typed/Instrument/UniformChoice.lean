import QCryptLean.LOCC.Typed.Channel

/-!
# Uniform finite choice of a certified instrument

Given a nonempty finite seed type `R` and a family of instruments `I r` with common input,
output, and local outcome types, `Instrument.uniformChoice I` samples `r` uniformly and runs
`I r`.  The observed outcome is the pair `(r, y)`, and the hidden Kraus fibre remains exactly the
hidden fibre of `I r` at `y`.  The instrument alone does not make `(r, y)` public: an enclosing
`AnnouncedAction` can announce `r` or the pair through its announcement function, whereas a
`PrivateAction` exposes no outcome to its continuation.

The construction is the finite-instrument mixture of Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2.  Its intended protocol uses include the publicly announced uniform
permutation in arXiv:0809.3019, `main.tex:447`--`:455` and the public random sampling and
hash choices in arXiv:2403.11851, `main.tex:908`--`:919`.

No inhabitance assumption is imposed on the input, output, or local outcome type.  In particular,
an empty local outcome type is handled by the completeness certificate already carried by each
member of the supplied family.
-/

open scoped Matrix BigOperators
open Matrix

namespace TypedLOCC
namespace Instrument

variable {A B R Y : Type}

/-- The Kraus-amplitude normalization for a uniform choice from `R`. -/
noncomputable def uniformChoiceScale [Fintype R] : ℂ :=
  (1 : ℂ) / (Real.sqrt (Fintype.card R : ℝ) : ℂ)

/-- Squaring the uniform Kraus amplitude gives the probability `1 / |R|`.

The `Nonempty R` hypothesis is exactly what makes the finite cardinality in the denominator
nonzero. -/
theorem uniformChoiceScale_star_mul [Fintype R] [Nonempty R] :
    star (uniformChoiceScale (R := R)) * uniformChoiceScale (R := R) =
      (Fintype.card R : ℂ)⁻¹ := by
  have hcard : 0 < (Fintype.card R : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [uniformChoiceScale, star_div₀, star_one]
  rw [show star ((Real.sqrt (Fintype.card R : ℝ) : ℂ)) =
      (Real.sqrt (Fintype.card R : ℝ) : ℂ) by
        rw [Complex.star_def, Complex.conj_ofReal]]
  rw [one_div, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hcard.le]
  congr 2

/-- The explicit Kraus matrix for observed branch `(r, y)` and hidden Kraus index `t`.

It is the corresponding Kraus matrix of `I r`, scaled by the square root of the uniform
probability on `R`. -/
noncomputable def uniformChoiceKraus [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype Y] (I : R → Instrument A B Y) (r : R) (y : Y)
    (t : (I r).krausIndex y) : Matrix B A ℂ :=
  uniformChoiceScale (R := R) • (I r).kraus y t

/-- The uniformly scaled dependent Kraus family is complete.

For each fixed seed `r`, this uses the completeness certificate of `I r`; summing the identical
identity contribution with weight `1 / |R|` over the nonempty finite type `R` gives the identity.
This is the trace-preserving normalization required of the finite instrument mixture in
arXiv:1210.4583, Section 2. -/
theorem uniformChoiceKraus_complete [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype Y] (I : R → Instrument A B Y) :
    ∑ ry : R × Y, ∑ t : (I ry.1).krausIndex ry.2,
        (uniformChoiceKraus I ry.1 ry.2 t)ᴴ *
          uniformChoiceKraus I ry.1 ry.2 t =
      1 := by
  have hscaled : ∀ (r : R) (y : Y) (t : (I r).krausIndex y),
      (uniformChoiceKraus I r y t)ᴴ * uniformChoiceKraus I r y t =
        ((Fintype.card R : ℂ)⁻¹ • ((I r).kraus y t)ᴴ) *
          (I r).kraus y t := by
    intro r y t
    rw [uniformChoiceKraus, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, uniformChoiceScale_star_mul,
      Matrix.smul_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [hscaled, Matrix.smul_mul, ← Finset.smul_sum]
  simp_rw [(I _).complete]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  simp [Fintype.card_ne_zero]

/-- Choose a seed uniformly, run the corresponding certified instrument, and retain the seed
together with its observed local outcome as the instrument outcome.

The outcome type is `R × Y`; the hidden fibre at `(r, y)` is `(I r).krausIndex y`.  Publication
is a separate choice made by the announcement function of an enclosing `AnnouncedAction`; no
hidden Kraus representative is exposed in either case.
-/
noncomputable def uniformChoice [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype Y] (I : R → Instrument A B Y) : Instrument A B (R × Y) where
  krausIndex ry := (I ry.1).krausIndex ry.2
  kraus ry t := uniformChoiceKraus I ry.1 ry.2 t
  complete := uniformChoiceKraus_complete I

/-- The certified uniform-choice instrument exposes exactly its explicitly scaled Kraus matrix.
-/
@[simp] theorem uniformChoice_kraus [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype Y] (I : R → Instrument A B Y) (r : R) (y : Y)
    (t : (I r).krausIndex y) :
    (uniformChoice I).kraus (r, y) t = uniformChoiceKraus I r y t := by
  rfl

/-- Exact CP operation at the observed branch `(r, y)`.

The equality holds as linear maps on all operators: a fixed branch is the operation of `I r` at
`y`, multiplied by the uniform probability `1 / |R|`. -/
theorem uniformChoice_operation [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype Y] (I : R → Instrument A B Y) (r : R) (y : Y) :
    (uniformChoice I).operation (r, y) =
      (Fintype.card R : ℂ)⁻¹ • (I r).operation y := by
  unfold Instrument.operation
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply LinearMap.ext
  intro rho
  ext b b'
  simp only [uniformChoice, uniformChoiceKraus, matrixConjLinear,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [uniformChoiceScale_star_mul]

/-- The total channel is the uniform average of the channels in the supplied family.

The observed pair `(r, y)` is summed out in `Instrument.channel`; the instrument itself retains
that pair as its outcome. -/
theorem uniformChoice_channel [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype Y] (I : R → Instrument A B Y) :
    (uniformChoice I).channel =
      (Fintype.card R : ℂ)⁻¹ • ∑ r : R, (I r).channel := by
  unfold Instrument.channel
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact uniformChoice_operation I r y

end Instrument
end TypedLOCC
