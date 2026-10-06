import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Hermitianization of Operators — symmetrization, PSD/Hermitian preservation, POVM lifts

Given any operator `A : Op n`, its **symmetrization** or **Hermitianization** is

  `symm A := (1/2 : ℂ) • (A + Aᴴ)`.

Symmetrization is a projection of operators onto Hermitian operators. We do not
introduce a dedicated abbreviation because unfolding the expression is trivial;
all lemmas are stated directly on `(1/2 : ℂ) • (A + Aᴴ)`.

The main use case is to promote a raw POVM-like family `M : X → Op n` satisfying
`∀ x v, 0 ≤ (quadraticForm (M x) v).re` and `∑ x, M x = 1` to a Hermitian, PSD
POVM-like family with an unchanged expected-guessing-probability trace sum.

## Main statements

- `posSemidef_of_isHermitian_of_quadraticForm_re_nonneg`: a Hermitian operator
  whose real quadratic form is nonneg on every vector is Mathlib-`PosSemidef`.
- `isHermitian_real_smul`: real-scalar Hermiticity preservation.
- `isHermitian_symmetrization`: `(1/2) • (A + Aᴴ)` is Hermitian.
- `quadraticForm_symmetrization_re`: the real part of the quadratic form is
  preserved by symmetrization.
- `posSemidef_symmetrization`: symmetrization sends operators with nonneg
  real quadratic form to PSD operators.
- `sum_symmetrization_eq_one`: sum-to-identity is preserved under
  Hermitianization.
- `trace_mul_symmetrization_re_of_isHermitian`: against any Hermitian `B`, the
  real-part trace pairing is unchanged by symmetrization.
-/

namespace Quantum.Operators

open Matrix
open scoped ComplexOrder

/-- Real-scalar Hermiticity preservation. -/
lemma isHermitian_real_smul {n : ℕ} {A : Op n} (hA : A.IsHermitian) (t : ℝ) :
    ((Complex.ofReal t) • A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hA]
  simp [Complex.conj_ofReal]

/-!
## The symmetrization `symm A := (1/2) • (A + Aᴴ)`

We do not introduce an abbreviation because unfolding the expression is trivial
and pinning a name would just cost us `simp`-only unfolds throughout. Instead,
the lemmas below are stated directly on `(1/2 : ℂ) • (A + Aᴴ)`.
-/

/-- The symmetrization `(1/2) • (A + Aᴴ)` is Hermitian. -/
lemma isHermitian_symmetrization {n : ℕ} (A : Op n) :
    ((1/2 : ℂ) • (A + Aᴴ)).IsHermitian := by
  change ((1/2 : ℂ) • (A + Aᴴ))ᴴ = (1/2 : ℂ) • (A + Aᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
  have h_star_half : star ((1/2 : ℂ)) = (1/2 : ℂ) := by simp
  rw [h_star_half, add_comm]

/-- Real-part expansion of `quadraticForm` applied to `(1/2) • (A + Aᴴ)`: it equals
`(quadraticForm A v).re`. -/
lemma quadraticForm_symmetrization_re {n : ℕ} (A : Op n) (v : Fin n → ℂ) :
    (quadraticForm ((1/2 : ℂ) • (A + Aᴴ)) v).re = (quadraticForm A v).re := by
  have hsum : quadraticForm (A + Aᴴ) v = quadraticForm A v + quadraticForm Aᴴ v := by
    unfold quadraticForm
    rw [Matrix.add_mulVec, dotProduct_add]
  have hsmul : quadraticForm ((1/2 : ℂ) • (A + Aᴴ)) v =
      (1/2 : ℂ) * quadraticForm (A + Aᴴ) v := by
    unfold quadraticForm
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hsmul, hsum, Complex.mul_re]
  have h12_re : ((1/2 : ℂ)).re = (1/2 : ℝ) := by norm_num
  have h12_im : ((1/2 : ℂ)).im = 0 := by norm_num
  rw [h12_re, h12_im, zero_mul, sub_zero, Complex.add_re,
      quadraticForm_conjTranspose_re]
  ring

/-- The symmetrization `(1/2) • (A + Aᴴ)` is Mathlib-`PosSemidef` whenever `A`
has nonnegative real quadratic form on all vectors. -/
lemma posSemidef_symmetrization {n : ℕ} (A : Op n)
    (h : ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm A v).re) :
    Matrix.PosSemidef ((1/2 : ℂ) • (A + Aᴴ)) := by
  refine posSemidef_of_isHermitian_of_quadraticForm_re_nonneg
    (isHermitian_symmetrization A) (fun v => ?_)
  rw [quadraticForm_symmetrization_re]
  exact h v

/-- Sum-to-identity is preserved under Hermitianization.

If `∑ x, M x = 1`, then `∑ x, (1/2) • (M x + (M x)ᴴ) = 1`. -/
lemma sum_symmetrization_eq_one {X : Type*} [Fintype X] {n : ℕ}
    (M : X → Op n) (hM : ∑ x : X, M x = 1) :
    ∑ x : X, (1/2 : ℂ) • (M x + (M x)ᴴ) = 1 := by
  rw [← Finset.smul_sum, Finset.sum_add_distrib]
  have h_conj_sum : ∑ x : X, (M x)ᴴ = (1 : Op n) := by
    rw [← Matrix.conjTranspose_sum, hM, Matrix.conjTranspose_one]
  rw [h_conj_sum, hM]
  have h_2 : (1 : Op n) + 1 = (2 : ℂ) • (1 : Op n) := by
    rw [show ((2 : ℂ) • (1 : Op n)) = ((1 : ℂ) + 1) • (1 : Op n) by norm_num,
        add_smul, one_smul]
  rw [h_2, smul_smul]
  norm_num

/-- Against any Hermitian `B`, the real part of the trace of
`((1/2) • (A + Aᴴ)) * B` equals that of `A * B`. -/
lemma trace_mul_symmetrization_re_of_isHermitian {n : ℕ} (A B : Op n)
    (hB : B.IsHermitian) :
    (((1/2 : ℂ) • (A + Aᴴ)) * B).trace.re = (A * B).trace.re := by
  have h_mul : ((1/2 : ℂ) • (A + Aᴴ)) * B =
      (1/2 : ℂ) • (A * B + Aᴴ * B) := by
    rw [Matrix.smul_mul, Matrix.add_mul]
  rw [h_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re]
  have h12_re : ((1/2 : ℂ)).re = (1/2 : ℝ) := by norm_num
  have h12_im : ((1/2 : ℂ)).im = 0 := by norm_num
  rw [h12_re, h12_im, zero_mul, sub_zero]
  -- When `B` is Hermitian, `Tr(Aᴴ * B) = star (Tr(A * B))`, via
  -- `(A*B)ᴴ = B * Aᴴ` and cyclicity of trace.
  have h_conj_trace : (Aᴴ * B).trace = star ((A * B).trace) := by
    have h1 : ((A * B).conjTranspose).trace = star ((A * B).trace) :=
      Matrix.trace_conjTranspose _
    have h2 : (A * B).conjTranspose = B * Aᴴ := by
      rw [Matrix.conjTranspose_mul, hB]
    have h3 : (B * Aᴴ).trace = (Aᴴ * B).trace := Matrix.trace_mul_comm _ _
    rw [← h1, h2, h3]
  rw [Matrix.trace_add, h_conj_trace, Complex.add_re, Complex.star_def,
      Complex.conj_re]
  ring

end Quantum.Operators
