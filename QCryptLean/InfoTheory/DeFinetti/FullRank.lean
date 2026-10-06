import QCryptLean.InfoTheory.DeFinetti.Measure
import QCryptLean.Quantum.TensorProducts.QuadraticForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Full support of tensor-power de Finetti integrals

This module isolates the rank/full-support input for density-operator de Finetti
mixtures with open-positive support.
-/

open Quantum.Operators
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Matrix

/-- A positive-definite square complex matrix on `Fin N` has full matrix rank. -/
theorem PosDef.rank_eq_card_fin {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.PosDef) :
    Matrix.rank A = N := by
  simpa using Matrix.rank_of_isUnit A hA.isUnit

end Matrix

namespace InfoTheory.DeFinetti

private lemma DensityOp.maxMixed_toOp_posDef {d : ℕ} [NeZero d] :
    (DensityOp.maxMixed d).toOp.PosDef := by
  simpa [DensityOp.maxMixed] using
    ((Matrix.PosDef.one : (1 : Op d).PosDef).smul
      (a := (1 / (d : ℂ))) (by
        exact_mod_cast (one_div_pos.mpr
          (Nat.cast_pos.mpr (Nat.pos_of_neZero d)))))

private lemma continuous_quadraticForm_re {m : ℕ} (v : Fin m → ℂ) :
    Continuous (fun A : Op m => (quadraticForm A v).re) := by
  have h_entry : ∀ i j : Fin m, Continuous (fun A : Op m => A i j) := by
    intro i j
    exact (continuous_apply j).comp (continuous_apply i)
  unfold quadraticForm
  apply Complex.continuous_re.comp
  simp only [dotProduct, Matrix.mulVec]
  exact continuous_finsetSum Finset.univ (fun i _ =>
    continuous_const.mul
      (continuous_finsetSum Finset.univ (fun j _ =>
        ((h_entry i j).mul continuous_const))))

private lemma continuous_tensorPowGen_quadraticForm_re
    {d n : ℕ} [NeZero d] [NeZero (d ^ n)] (v : Fin (d ^ n) → ℂ) :
    Continuous (fun σ : DensityOp d =>
      (quadraticForm (σ.tensorPowGen n).toOp v).re) :=
  (continuous_quadraticForm_re v).comp
    (continuous_tensorPowGen_toOp (d := d) (n := n))

private lemma integrable_tensorPowGen_quadraticForm_re
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (μ : DensityMeasure d) (v : Fin (d ^ n) → ℂ) :
    MeasureTheory.Integrable
      (fun σ : DensityOp d => (quadraticForm (σ.tensorPowGen n).toOp v).re)
      μ.measure := by
  have h_entry : ∀ i j : Fin (d ^ n), MeasureTheory.Integrable
      (fun σ : DensityOp d => (σ.tensorPowGen n).toOp i j) μ.measure :=
    fun i j => integrable_tensorPow_entry n i j μ
  have h_int_mv : ∀ k : Fin (d ^ n), MeasureTheory.Integrable
      (fun σ : DensityOp d => ((σ.tensorPowGen n).toOp.mulVec v) k) μ.measure := by
    intro k
    change MeasureTheory.Integrable
      (fun σ : DensityOp d => ∑ j, (σ.tensorPowGen n).toOp k j * v j) μ.measure
    exact MeasureTheory.integrable_finsetSum _ fun j _ =>
      (h_entry k j).mul_const (v j)
  have h_int_q : MeasureTheory.Integrable
      (fun σ : DensityOp d => quadraticForm (σ.tensorPowGen n).toOp v) μ.measure := by
    change MeasureTheory.Integrable
      (fun σ : DensityOp d =>
        ∑ k, star (v k) * ((σ.tensorPowGen n).toOp.mulVec v) k) μ.measure
    exact MeasureTheory.integrable_finsetSum _ fun k _ =>
      (h_int_mv k).const_mul (star (v k))
  exact ContinuousLinearMap.integrable_comp Complex.reCLM h_int_q

private lemma integralTensorPower_quadraticForm_re_eq_integral
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (μ : DensityMeasure d) (v : Fin (d ^ n) → ℂ) :
    (quadraticForm (integralTensorPower n μ).toOp v).re =
      ∫ σ : DensityOp d, (quadraticForm (σ.tensorPowGen n).toOp v).re ∂μ.measure := by
  simpa [integralTensorPower] using
    (Quantum.TensorProducts.quadraticForm_re_matrix_entry_integral
      μ.measure
      (fun σ : DensityOp d => (σ.tensorPowGen n).toOp)
      (fun i j => integrable_tensorPow_entry n i j μ)
      v)

private lemma tensorPowGen_maxMixed_quadraticForm_re_pos
    {d n : ℕ} [NeZero d] (v : Fin (d ^ n) → ℂ) (hv : v ≠ 0) :
    0 < (quadraticForm ((DensityOp.maxMixed d).tensorPowGen n).toOp v).re := by
  have hpd : ((DensityOp.maxMixed d).tensorPowGen n).toOp.PosDef := by
    rw [DensityOp.tensorPowGen_toOp]
    exact (DensityOp.maxMixed_toOp_posDef (d := d)).tensorPow n
  have hq : 0 < quadraticForm ((DensityOp.maxMixed d).tensorPowGen n).toOp v := by
    simpa [quadraticForm] using hpd.dotProduct_mulVec_pos hv
  exact (Complex.pos_iff.mp hq).1

/-- **Analytic full-support leaf for tensor-power de Finetti integrals.**

If the sampling measure on one-system density operators is open-positive, then
the integrated tensor-power density matrix is positive definite.

Proof: for every nonzero vector `x`, test the continuous
nonnegative function `σ ↦ Re ⟪x, σ^⊗n x⟫`.  It is strictly positive at the
maximally mixed state `Quantum.Operators.DensityOp.maxMixed d`; continuity gives
an open neighborhood where it remains positive, and open-positive support of
`μ.measure` makes the integral strictly positive. -/
theorem integralTensorPower_toOp_posDef_of_isOpenPosMeasure
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (μ : DensityMeasure d)
    (hμ : μ.measure.IsOpenPosMeasure) :
    (integralTensorPower n μ).toOp.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (integralTensorPower n μ).toPosSemidefOp.toHermitianOp.isHermitian ?_
  intro v hv
  rw [show star v ⬝ᵥ (integralTensorPower n μ).toOp *ᵥ v =
      quadraticForm (integralTensorPower n μ).toOp v from rfl]
  rw [Complex.pos_iff]
  constructor
  · haveI : MeasureTheory.Measure.IsOpenPosMeasure μ.measure := hμ
    set f : DensityOp d → ℝ :=
      fun σ => (quadraticForm (σ.tensorPowGen n).toOp v).re
    have hf_cont : Continuous f := by
      simpa [f] using continuous_tensorPowGen_quadraticForm_re
        (d := d) (n := n) v
    have hf_int : MeasureTheory.Integrable f μ.measure := by
      simpa [f] using integrable_tensorPowGen_quadraticForm_re
        (d := d) (n := n) μ v
    have hf_nonneg : 0 ≤ f := by
      intro σ
      simpa [f, quadraticForm] using
        density_quadraticForm_nonneg (σ.tensorPowGen n) v
    have hf_nonzero : f (DensityOp.maxMixed d) ≠ 0 := by
      exact ne_of_gt (by
        simpa [f] using
          tensorPowGen_maxMixed_quadraticForm_re_pos (d := d) (n := n) v hv)
    have h_int_pos : 0 < ∫ σ : DensityOp d, f σ ∂μ.measure :=
      MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
        hf_cont hf_int hf_nonneg hf_nonzero
    have h_eq := integralTensorPower_quadraticForm_re_eq_integral
      (d := d) (n := n) μ v
    simpa [f] using h_eq.symm ▸ h_int_pos
  · have hconj := quadraticForm_hermitian_conj_eq_self
      (integralTensorPower n μ).toOp
      (integralTensorPower n μ).toPosSemidefOp.toHermitianOp.isHermitian v
    rw [Complex.ext_iff] at hconj
    simp only [Complex.conj_re, Complex.conj_im] at hconj
    linarith [hconj.2]

/-- A tensor-power de Finetti integral against an open-positive measure has full rank. -/
theorem integralTensorPower_rank_toOp_eq_full_of_isOpenPosMeasure
    {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (μ : DensityMeasure d)
    (hμ : μ.measure.IsOpenPosMeasure) :
    Matrix.rank (integralTensorPower n μ).toOp = d ^ n :=
  Matrix.PosDef.rank_eq_card_fin
    (integralTensorPower_toOp_posDef_of_isOpenPosMeasure μ hμ)

end InfoTheory.DeFinetti

end
