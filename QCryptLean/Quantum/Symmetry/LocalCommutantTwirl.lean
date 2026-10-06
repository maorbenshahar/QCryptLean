import QCryptLean.Quantum.TensorProducts.ReferenceTransport
import QCryptLean.Quantum.TensorProducts.TensorPow
import QCryptLean.Quantum.TensorProducts.FixedMarginalDomination
import QCryptLean.Quantum.Operators.MatrixIntegral
import Mathlib.MeasureTheory.Group.Integral
import QCryptLean.Math.Analysis.CompactSpaceIntegrable

/-!
# Haar moments determined by their marginal

A restricted unitary twirl can be identified without computing its matrix entries.
The representation-theoretic hypothesis is that its commutant, restricted to the
supporting projection, acts by operators on the system register. Under this
hypothesis the system marginal determines the twirl uniquely.
-/

open Quantum.Operators Quantum.TensorProducts Matrix MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Symmetry

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The commutant of a reference action acts locally after restriction to `Q`. -/
def HasLocalCommutant {H : Type*} {a b : ℕ} (U : H → Op b) (Q : Op (a * b)) : Prop :=
  ∀ T : Op (a * b), (∀ g, Commute (Op.tensor (1 : Op a) (U g)) T) →
    ∃ X : Op a, T * Q = Op.tensor X (1 : Op b) * Q

/-- It suffices to check local commutant compression on spanning generators. -/
lemma hasLocalCommutant_of_span {H : Type*} {a b : ℕ} (U : H → Op b)
    (Q : Op (a * b)) (s : Set (Op (a * b)))
    (hspan : ∀ T, (∀ g, Commute (Op.tensor (1 : Op a) (U g)) T) →
      T ∈ Submodule.span ℂ s)
    (hgen : ∀ T ∈ s, ∃ X : Op a, T * Q = Op.tensor X (1 : Op b) * Q) :
    HasLocalCommutant U Q := by
  intro T hT
  have hmem := hspan T hT
  clear hT
  induction hmem using Submodule.span_induction with
  | mem T hT => exact hgen T hT
  | zero =>
      refine ⟨0, ?_⟩
      rw [show (0 : Op a) = (0 : ℂ) • (0 : Op a) from (zero_smul _ _).symm,
        Op.tensor_smul_left, zero_smul, zero_mul]
  | add T₁ T₂ _ _ h₁ h₂ =>
      obtain ⟨X₁, h₁⟩ := h₁
      obtain ⟨X₂, h₂⟩ := h₂
      exact ⟨X₁ + X₂, by rw [add_mul, h₁, h₂, Op.tensor_add_left, add_mul]⟩
  | smul c T _ h =>
      obtain ⟨X, hX⟩ := h
      exact ⟨c • X, by rw [smul_mul_assoc, hX, Op.tensor_smul_left, smul_mul_assoc]⟩

/-- Local commutant compression makes the marginal determine an invariant supported operator. -/
lemma HasLocalCommutant.eq_of_marginal {H : Type*} {a b : ℕ}
    {U : H → Op b} {Q T : Op (a * b)} (hlocal : HasLocalCommutant U Q)
    (hΩ : IsUnit (partialTraceB Q)) (hTQ : T * Q = T)
    (hT : ∀ g, Commute (Op.tensor (1 : Op a) (U g)) T) :
    T = Op.tensor (partialTraceB T * (partialTraceB Q)⁻¹) (1 : Op b) * Q := by
  apply eq_tensor_inverse_marginal_mul_of_local Q T hΩ
  simpa only [hTQ] using hlocal T hT

/-- The reference-side twirl for an arbitrary unitary family and measure. -/
def referenceTwirl {H : Type*} [MeasurableSpace H] {a b : ℕ}
    (μ : Measure H) (U : H → Matrix.unitaryGroup (Fin b) ℂ) (T : Op (a * b)) :
    Op (a * b) :=
  ∫ g, Op.tensor (1 : Op a) (U g : Op b) * T *
    (Op.tensor (1 : Op a) (U g : Op b))ᴴ ∂μ

/-- Continuous unitary orbits over a compact parameter space are integrable. -/
lemma referenceTwirl_integrable {H : Type*} [TopologicalSpace H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] {a b : ℕ} (μ : Measure H) [IsFiniteMeasure μ]
    (U : H → Matrix.unitaryGroup (Fin b) ℂ) (hU : Continuous U) (T : Op (a * b)) :
    Integrable (fun g => Op.tensor (1 : Op a) (U g : Op b) * T *
      (Op.tensor (1 : Op a) (U g : Op b))ᴴ) μ := by
  have hK : Continuous (fun g => Op.tensor (1 : Op a) (U g : Op b)) :=
    Op.continuous_tensor.comp (continuous_const.prodMk (continuous_subtype_val.comp hU))
  exact ((hK.matrix_mul continuous_const).matrix_mul
    hK.matrix_conjTranspose).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Partial trace commutes with an integrable reference-side twirl. -/
lemma partialTraceB_referenceTwirl {H : Type*} [MeasurableSpace H] {a b : ℕ}
    (μ : Measure H) [IsProbabilityMeasure μ]
    (U : H → Matrix.unitaryGroup (Fin b) ℂ) (T : Op (a * b))
    (hint : Integrable (fun g => Op.tensor (1 : Op a) (U g : Op b) * T *
      (Op.tensor (1 : Op a) (U g : Op b))ᴴ) μ) :
    partialTraceB (referenceTwirl μ U T) = partialTraceB T := by
  let L : Op (a * b) →ₗ[ℂ] Op a :=
    { toFun := partialTraceB
      map_add' := partialTraceB_add
      map_smul' := partialTraceB_smul }
  change L.toContinuousLinearMap (∫ g, _ ∂μ) = _
  rw [← L.toContinuousLinearMap.integral_comp_comm hint]
  have htrace (g : H) : L (Op.tensor (1 : Op a) (U g : Op b) * T *
      (Op.tensor (1 : Op a) (U g : Op b))ᴴ) = partialTraceB T := by
    change partialTraceB _ = _
    rw [Op.tensor_conjTranspose, conjTranspose_one]
    apply partialTraceB_one_tensor_sandwich_of_mul_eq_one
    exact (Matrix.mem_unitaryGroup_iff').mp (U g).2
  simp only [LinearMap.coe_toContinuousLinearMap', htrace, integral_const,
    probReal_univ, one_smul]

/-- A left-invariant average is invariant under conjugation by the reference action. -/
lemma referenceTwirl_conj {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
    {a b : ℕ} (μ : Measure H) [μ.IsMulLeftInvariant]
    (U : H →* Matrix.unitaryGroup (Fin b) ℂ) (T : Op (a * b))
    (hint : Integrable (fun g => Op.tensor (1 : Op a) (U g : Op b) * T *
      (Op.tensor (1 : Op a) (U g : Op b))ᴴ) μ) (g : H) :
    Op.tensor (1 : Op a) (U g : Op b) * referenceTwirl μ U T *
      (Op.tensor (1 : Op a) (U g : Op b))ᴴ = referenceTwirl μ U T := by
  let K (g : H) : Op (a * b) := Op.tensor (1 : Op a) (U g : Op b)
  have hK (g h : H) : K (g * h) = K g * K h := by
    simp only [K, map_mul, Submonoid.coe_mul, Op.tensor_mul, one_mul]
  let L := ((LinearMap.mulRight ℂ (K g)ᴴ).comp
    (LinearMap.mulLeft ℂ (K g))).toContinuousLinearMap
  change L (∫ h, K h * T * (K h)ᴴ ∂μ) = ∫ h, K h * T * (K h)ᴴ ∂μ
  rw [← L.integral_comp_comm hint]
  calc
    _ = ∫ h, K (g * h) * T * (K (g * h))ᴴ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with h
      change K g * (K h * T * (K h)ᴴ) * (K g)ᴴ = _
      rw [hK, Matrix.conjTranspose_mul]
      simp only [mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ := μ) (fun h => K h * T * (K h)ᴴ) g

/-- A left-invariant reference twirl lies in the commutant of its unitary action. -/
lemma referenceTwirl_commute {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
    {a b : ℕ} (μ : Measure H) [μ.IsMulLeftInvariant]
    (U : H →* Matrix.unitaryGroup (Fin b) ℂ) (T : Op (a * b))
    (hint : Integrable (fun g => Op.tensor (1 : Op a) (U g : Op b) * T *
      (Op.tensor (1 : Op a) (U g : Op b))ᴴ) μ) (g : H) :
    Commute (Op.tensor (1 : Op a) (U g : Op b)) (referenceTwirl μ U T) := by
  have hunit : (Op.tensor (1 : Op a) (U g : Op b))ᴴ *
      Op.tensor (1 : Op a) (U g : Op b) = 1 := by
    rw [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, one_mul,
      ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').mp (U g).2, Op.tensor_one]
  have h := congrArg (fun X => X * Op.tensor (1 : Op a) (U g : Op b))
    (referenceTwirl_conj μ U T hint g)
  simpa only [mul_assoc, hunit, mul_one] using h

/-- A reference twirl preserves right support on an invariant projection. -/
lemma referenceTwirl_mul_eq {H : Type*} [MeasurableSpace H] {a b : ℕ}
    (μ : Measure H) (U : H → Matrix.unitaryGroup (Fin b) ℂ) (T Q : Op (a * b))
    (hint : Integrable (fun g => Op.tensor (1 : Op a) (U g : Op b) * T *
      (Op.tensor (1 : Op a) (U g : Op b))ᴴ) μ)
    (hQ : Q.IsHermitian) (hTQ : T * Q = T)
    (hcomm : ∀ g, Commute (Op.tensor (1 : Op a) (U g : Op b)) Q) :
    referenceTwirl μ U T * Q = referenceTwirl μ U T := by
  let L := (LinearMap.mulRight ℂ Q).toContinuousLinearMap
  change L (∫ g, _ ∂μ) = ∫ g, _ ∂μ
  rw [← L.integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [] with g
  change (Op.tensor (1 : Op a) (U g : Op b) * T *
    (Op.tensor (1 : Op a) (U g : Op b))ᴴ) * Q = _
  have hstar := congrArg Matrix.conjTranspose (hcomm g).eq
  simp only [Matrix.conjTranspose_mul, hQ.eq] at hstar
  rw [mul_assoc, ← hstar, ← mul_assoc, mul_assoc _ T Q, hTQ]

/-- A restricted Haar moment with identity marginal is the locally normalized projection. -/
theorem referenceTwirl_eq_inverse_marginal_mul
    {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
    {a b : ℕ} (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (U : H →* Matrix.unitaryGroup (Fin b) ℂ) (T Q : Op (a * b))
    (hint : Integrable (fun g => Op.tensor (1 : Op a) (U g : Op b) * T *
      (Op.tensor (1 : Op a) (U g : Op b))ᴴ) μ)
    (hQ : Q.IsHermitian) (hTQ : T * Q = T)
    (hcomm : ∀ g, Commute (Op.tensor (1 : Op a) (U g : Op b)) Q)
    (hlocal : HasLocalCommutant (fun g => (U g : Op b)) Q)
    (hΩ : IsUnit (partialTraceB Q)) (hT : partialTraceB T = 1) :
    referenceTwirl μ U T = Op.tensor (partialTraceB Q)⁻¹ (1 : Op b) * Q := by
  rw [hlocal.eq_of_marginal hΩ (referenceTwirl_mul_eq μ U T Q hint hQ hTQ hcomm)
    (referenceTwirl_commute μ U T hint), partialTraceB_referenceTwirl μ U T hint,
    hT, one_mul]

/-- The local-commutant moment identity in positive square-root sandwich form. -/
theorem referenceTwirl_eq_sqrt_sandwich
    {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
    {a b : ℕ} (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (U : H →* Matrix.unitaryGroup (Fin b) ℂ) (T Q : Op (a * b))
    (hint : Integrable (fun g => Op.tensor (1 : Op a) (U g : Op b) * T *
      (Op.tensor (1 : Op a) (U g : Op b))ᴴ) μ)
    (hQ : Q.IsHermitian) (hTQ : T * Q = T)
    (hcomm : ∀ g, Commute (Op.tensor (1 : Op a) (U g : Op b)) Q)
    (hlocal : HasLocalCommutant (fun g => (U g : Op b)) Q)
    (κ : Op a) (hκ : κ.PosDef) (hκinv : κ⁻¹ = partialTraceB Q)
    (hκcomm : Commute (Op.tensor κ (1 : Op b)) Q) (hT : partialTraceB T = 1) :
    referenceTwirl μ U T =
      Op.tensor (CFC.sqrt κ) (1 : Op b) * Q * Op.tensor (CFC.sqrt κ) (1 : Op b) := by
  letI := hκ.isUnit.invertible
  have hΩ : IsUnit (partialTraceB Q) := hκinv ▸ hκ.inv.isUnit
  rw [referenceTwirl_eq_inverse_marginal_mul μ U T Q hint hQ hTQ hcomm hlocal hΩ hT,
    ← hκinv, Matrix.inv_inv_of_invertible]
  have hsqrt := tensor_sqrt_one_commute hκ.posSemidef hκcomm
  symm
  rw [mul_assoc, ← hsqrt.eq, ← mul_assoc, Op.tensor_mul, mul_one,
    CFC.sqrt_mul_sqrt_self κ (Matrix.nonneg_iff_posSemidef.mpr hκ.posSemidef)]

end Quantum.Symmetry
