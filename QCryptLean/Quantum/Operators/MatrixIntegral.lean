import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.Operators.Types
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Matrix-Valued Bochner Integrals — entries, quadratic forms, Hermitian and PSD closure

This file provides low-level facts for integrating finite-dimensional complex
matrices entrywise and for preserving operator structure under Bochner
set-integrals.

## Main definitions
- `DensityOp.integral`: the density operator obtained by a probability mixture.

## Main statements
- `matrix_integral_entry`: Bochner integration commutes with selecting a matrix entry.
- `matrix_setIntegral_entry`: set integration commutes with selecting a matrix entry.
- `matrix_of_setIntegral_eq_setIntegral`: entrywise set integrals assemble to the
  Bochner set integral.
- `matrix_setIntegral_isHermitian`: set integrals of Hermitian operators are Hermitian.
- `matrix_setIntegral_posSemidef`: set integrals of PSD operators are PSD.
- `Quantum.Operators.quadraticForm_re_setIntegral`: real quadratic forms commute with set
integration.
-/

open MeasureTheory Quantum.TensorProducts
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace Quantum.Operators

/-- Bochner integration commutes with selecting a matrix entry. -/
lemma matrix_integral_entry {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {m n : ℕ}
    (F : α → Matrix (Fin m) (Fin n) ℂ)
    (h_int : MeasureTheory.Integrable F μ)
    (i : Fin m) (j : Fin n) :
    (∫ a, F a ∂μ) i j = ∫ a, F a i j ∂μ := by
  let L : Matrix (Fin m) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (L.integral_comp_comm h_int).symm

/-- Bochner set integration commutes with selecting a matrix entry. -/
lemma matrix_setIntegral_entry {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {m n : ℕ}
    (s : Set α)
    (F : α → Matrix (Fin m) (Fin n) ℂ)
    (h_int : MeasureTheory.Integrable F (μ.restrict s))
    (i : Fin m) (j : Fin n) :
    (∫ a in s, F a ∂μ) i j = ∫ a in s, F a i j ∂μ := by
  exact matrix_integral_entry (μ := μ.restrict s) F h_int i j

/-- A matrix whose entries are set integrals is the Bochner set integral of the
matrix-valued function, under integrability. -/
lemma matrix_of_setIntegral_eq_setIntegral {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {m n : ℕ}
    (s : Set α)
    (F : α → Matrix (Fin m) (Fin n) ℂ)
    (h_int : MeasureTheory.Integrable F (μ.restrict s)) :
    (Matrix.of fun i j => ∫ a in s, F a i j ∂μ) =
      ∫ a in s, F a ∂μ := by
  ext i j
  exact (matrix_setIntegral_entry (μ := μ) s F h_int i j).symm

/-- A set integral of Hermitian matrix-valued functions is Hermitian. -/
lemma matrix_setIntegral_isHermitian {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {N : ℕ}
    (s : Set α) (F : α → Op N)
    (h_int : MeasureTheory.Integrable F (μ.restrict s))
    (h_herm : ∀ a, (F a).IsHermitian) :
    (∫ a in s, F a ∂μ).IsHermitian := by
  let ctCLM : Op N →L[ℝ] Op N := {
    toLinearMap := {
      toFun := fun M => M†
      map_add' := fun M N => Matrix.conjTranspose_add M N
      map_smul' := fun r M => by simp [Matrix.conjTranspose_smul, star_trivial]
    }
    cont := continuous_star
  }
  have h := (ctCLM.integral_comp_comm h_int).symm
  simp only [show ∀ M : Op N, ctCLM M = M† from fun _ => rfl] at h
  change (∫ a in s, F a ∂μ)† = ∫ a in s, F a ∂μ
  rw [h]
  congr 1
  funext a
  exact h_herm a

/-- A set integral of PSD matrix-valued functions is PSD. -/
lemma matrix_setIntegral_posSemidef {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {N : ℕ}
    (s : Set α) (F : α → Op N)
    (h_int : MeasureTheory.Integrable F (μ.restrict s))
    (h_psd : ∀ a, (F a).PosSemidef) :
    (∫ a in s, F a ∂μ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · exact matrix_setIntegral_isHermitian s F h_int fun a => (h_psd a).isHermitian
  · intro v
    let Q : Op N →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
      { toFun := fun M => star v ⬝ᵥ M *ᵥ v
        map_add' := fun A B => by simp [Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun r A => by
          change star v ⬝ᵥ (r • A).mulVec v =
            r • (star v ⬝ᵥ A.mulVec v)
          rw [Matrix.smul_mulVec, dotProduct_smul] }
    rw [show star v ⬝ᵥ ((∫ a in s, F a ∂μ) *ᵥ v) =
        ∫ a in s, star v ⬝ᵥ ((F a) *ᵥ v) ∂μ from
      (Q.integral_comp_comm h_int).symm]
    exact MeasureTheory.integral_nonneg_of_ae
      (ae_of_all _ fun a =>
        (Matrix.posSemidef_iff_dotProduct_mulVec.mp (h_psd a)).2 v)

/-- The real quadratic form of a Bochner set-integral is the set-integral of
the real quadratic forms. -/
lemma quadraticForm_re_setIntegral
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {N : ℕ}
    (s : Set α) (F : α → Op N)
    (h_int : MeasureTheory.Integrable F (μ.restrict s))
    (v : Fin N → ℂ) :
    (quadraticForm (∫ a in s, F a ∂μ) v).re =
      ∫ a in s, (quadraticForm (F a) v).re ∂μ := by
  let Q : Op N →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun M => (quadraticForm M v).re
      map_add' := fun A B => by
        unfold quadraticForm
        rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
      map_smul' := fun r A => by
        unfold quadraticForm
        change (star v ⬝ᵥ (r • A).mulVec v).re =
          r • (star v ⬝ᵥ A.mulVec v).re
        rw [Matrix.smul_mulVec, dotProduct_smul]
        simp }
  exact (Q.integral_comp_comm h_int).symm

/-- A probability mixture of density operators, with its integral as the underlying operator. -/
def DensityOp.integral {α : Type*} [MeasurableSpace α] {m : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → DensityOp m)
    (hf : Integrable (fun a => (f a).toOp) μ) : DensityOp m :=
  have hpsd : (∫ a, (f a).toOp ∂μ).PosSemidef := by
    simpa only [Measure.restrict_univ] using
      matrix_setIntegral_posSemidef Set.univ (fun a => (f a).toOp)
        (by simpa only [Measure.restrict_univ] using hf)
        (fun a => posSemidefOp_implies_mathlib (f a).toPosSemidefOp)
  { toOp := ∫ a, (f a).toOp ∂μ
    isHermitian := hpsd.isHermitian
    pos_semidef := posSemidef_re_quadraticForm_nonneg hpsd
    trace_one := by
      have h := (Matrix.traceLinearMap (Fin m) ℂ ℂ).toContinuousLinearMap.integral_comp_comm hf
      simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.traceLinearMap_apply,
        (f _).trace_one, integral_const, probReal_univ, one_smul] using h.symm }

/-- The underlying operator of a density mixture is its Bochner integral. -/
@[simp] lemma DensityOp.integral_toOp {α : Type*} [MeasurableSpace α] {m : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → DensityOp m)
    (hf : Integrable (fun a => (f a).toOp) μ) :
    (DensityOp.integral μ f hf).toOp = ∫ a, (f a).toOp ∂μ := rfl

/-- Partial trace commutes with an integrable operator mixture. -/
lemma partialTraceB_integral {α : Type*} [MeasurableSpace α] {a b : ℕ}
    {μ : Measure α} (f : α → Op (a * b)) (hf : Integrable f μ) :
    partialTraceB (∫ x, f x ∂μ) = ∫ x, partialTraceB (f x) ∂μ := by
  let L : Op (a * b) →ₗ[ℂ] Op a :=
    { toFun := partialTraceB
      map_add' := partialTraceB_add
      map_smul' := partialTraceB_smul }
  exact (L.toContinuousLinearMap.integral_comp_comm hf).symm

end Quantum.Operators

end
