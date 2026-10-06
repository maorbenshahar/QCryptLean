import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import QCryptLean.Quantum.TensorProducts.TensorFamily

/-!
# Tensor-Power Quadratic Forms — tensor vectors and entrywise integral formulas

This module contains quadratic forms on tensor-power test vectors, together with a reusable
entrywise-integral formula for quadratic forms of finite matrices.

## Main definitions
- `tensorPowVec`: flattened tensor power of a vector, the constant case of
  `Quantum.TensorProducts.tensorFamilyVec`.

## Main statements
- `quadraticForm_re_matrix_entry_integral`: quadratic forms commute with entrywise integrals.
- `quadraticForm_tensorPowVec_of_entrywise_prod`: tensor-power quadratic-form factorization.
- `complex_re_pow_of_im_eq_zero`: real parts commute with powers for real-valued complex numbers.
-/

namespace Quantum.TensorProducts

open Quantum.Operators Matrix
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

noncomputable section

/-- The real part of a quadratic form commutes with entrywise integration of a
finite matrix-valued function. -/
lemma quadraticForm_re_matrix_entry_integral
    {α : Type*} [MeasurableSpace α] {m : ℕ}
    (ν : MeasureTheory.Measure α) (F : α → Op m)
    (hF_int : ∀ i j : Fin m, MeasureTheory.Integrable (fun a => F a i j) ν)
    (v : Fin m → ℂ) :
    (quadraticForm
        (Matrix.of fun i j : Fin m => ∫ a : α, F a i j ∂ν) v).re =
      ∫ a : α, (quadraticForm (F a) v).re ∂ν := by
  have h_int_mv : ∀ k : Fin m,
      MeasureTheory.Integrable (fun a : α => ((F a).mulVec v) k) ν := by
    intro k
    change MeasureTheory.Integrable
      (fun a : α => ∑ j, F a k j * v j) ν
    exact MeasureTheory.integrable_finsetSum _ fun j _hj =>
      (hF_int k j).mul_const (v j)
  have h_int_q :
      MeasureTheory.Integrable (fun a : α => quadraticForm (F a) v) ν := by
    change MeasureTheory.Integrable
      (fun a : α => ∑ k, star (v k) * ((F a).mulVec v) k) ν
    exact MeasureTheory.integrable_finsetSum _ fun k _hk =>
      (h_int_mv k).const_mul (star (v k))
  have hcomplex :
      quadraticForm
          (Matrix.of fun i j : Fin m => ∫ a : α, F a i j ∂ν) v =
        ∫ a : α, quadraticForm (F a) v ∂ν := by
    unfold quadraticForm
    have h_mv :
        (Matrix.of fun i j : Fin m => ∫ a : α, F a i j ∂ν).mulVec v =
          fun k => ∫ a : α, ((F a).mulVec v) k ∂ν := by
      ext k
      change ∑ j, (∫ a : α, F a k j ∂ν) * v j =
        ∫ a : α, ∑ j, F a k j * v j ∂ν
      simp_rw [← MeasureTheory.integral_mul_const]
      exact (MeasureTheory.integral_finsetSum _
        (fun j _hj => (hF_int k j).mul_const (v j))).symm
    rw [h_mv]
    change ∑ k, star (v k) * (∫ a : α, ((F a).mulVec v) k ∂ν) =
      ∫ a : α, ∑ k, star (v k) * ((F a).mulVec v) k ∂ν
    simp_rw [← MeasureTheory.integral_const_mul]
    exact (MeasureTheory.integral_finsetSum _
      (fun k _hk => (h_int_mv k).const_mul (star (v k)))).symm
  rw [hcomplex]
  simpa using (integral_re h_int_q).symm

/-- The flat vector corresponding to the tensor power `v ⊗ ... ⊗ v`, encoded
through Mathlib's `finFunctionFinEquiv : (Fin n → Fin d) ≃ Fin (d^n)`: the tensor family of
the constant family `v`. -/
def tensorPowVec {d n : ℕ} (v : Fin d → ℂ) : Fin (d ^ n) → ℂ :=
  tensorFamilyVec fun _ : Fin n => v

@[simp]
lemma tensorPowVec_apply_finFunctionFinEquiv {d n : ℕ}
    (v : Fin d → ℂ) (f : Fin n → Fin d) :
    tensorPowVec v (finFunctionFinEquiv f) = ∏ k : Fin n, v (f k) :=
  tensorFamilyVec_apply_finFunctionFinEquiv _ f

/-- If an operator on `Fin (d^n)` has entries that factor as tensor powers of
the entries of `A`, then its quadratic form on `tensorPowVec v` is the `n`-th
power of the one-round quadratic form. -/
lemma quadraticForm_tensorPowVec_of_entrywise_prod {d n : ℕ}
    [NeZero d] [NeZero (d ^ n)]
    (A : Op d) (M : Op (d ^ n))
    (hM : ∀ f g : Fin n → Fin d,
      M (finFunctionFinEquiv f) (finFunctionFinEquiv g) =
        ∏ k : Fin n, A (f k) (g k))
    (v : Fin d → ℂ) :
    quadraticForm M (tensorPowVec v) = (quadraticForm A v) ^ n := by
  have hMA : M = tensorFamily fun _ : Fin n => A :=
    ext_finFunctionFinEquiv fun f g => by rw [hM, tensorFamily_apply_finFunctionFinEquiv]
  unfold quadraticForm
  rw [hMA, tensorPowVec, tensorFamily_mulVec, star_tensorFamilyVec, dotProduct_tensorFamilyVec,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A complex number with zero imaginary part has real part compatible with
natural powers. -/
lemma complex_re_pow_of_im_eq_zero (z : ℂ) (hz : z.im = 0) (n : ℕ) :
    (z ^ n).re = z.re ^ n := by
  have hz_eq : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hz]
  conv_lhs => rw [hz_eq]
  have h := congrArg Complex.re (Complex.ofReal_pow z.re n)
  rw [Complex.ofReal_re] at h
  exact h.symm

end

end Quantum.TensorProducts
