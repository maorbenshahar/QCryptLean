import QCryptLean.InfoTheory.Postselection.PairedBlockedOperators
import QCryptLean.InfoTheory.Postselection.Mixture
import QCryptLean.Quantum.Symmetry.LocalCommutantTwirl
import QCryptLean.InfoTheory.DeFinetti.Theorem.UnequalInterleaving
import QCryptLean.Quantum.Operators.MatrixIntegral

/-!
# Fixed-marginal measures from parameterized moments

Measurable families of extensions define probability measures on states.
Their tensor-power moments commute with pushforward and with the partial trace
of a purification. These statements apply to arbitrary probability spaces,
including products of unitary groups equipped with Haar probability measures.
-/

open Quantum.Operators Quantum.TensorProducts InfoTheory.DeFinetti MeasureTheory Matrix
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.Postselection

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-- The distribution of a measurable family of density operators. -/
def densityMeasureOfFamily {α : Type*} [MeasurableSpace α] {d : ℕ}
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → DensityOp d) (hf : Measurable f) :
    DensityMeasure d where
  measure := Measure.map f ν
  isProbability := Measure.isProbabilityMeasure_map hf.aemeasurable

/-- A measurable property holds for the induced measure exactly when it holds almost surely. -/
lemma densityMeasureOfFamily_ae_iff {α : Type*} [MeasurableSpace α] {d : ℕ}
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → DensityOp d) (hf : Measurable f)
    (P : DensityOp d → Prop) (hP : MeasurableSet (setOf P)) :
    (∀ᵐ σ ∂(densityMeasureOfFamily ν f hf).measure, P σ) ↔ ∀ᵐ x ∂ν, P (f x) :=
  ae_map_iff hf.aemeasurable hP

/-- Tensor-power moments of a measurable family are integrable. -/
lemma tensorPower_family_integrable {α : Type*} [MeasurableSpace α] {d n : ℕ}
    [NeZero d] [NeZero n] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → DensityOp d) (hf : Measurable f) :
    Integrable (fun x => ((f x).tensorPowGen n).toOp) ν := by
  haveI : IsProbabilityMeasure (Measure.map f ν) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  exact continuous_tensorPowGen_toOp.integrable_of_compactSpace.comp_measurable hf

/-- The induced measure has the tensor-power moment of its parameterized family. -/
lemma integralTensorPower_densityMeasureOfFamily {α : Type*} [MeasurableSpace α]
    {d n : ℕ} [NeZero d] [NeZero n] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → DensityOp d) (hf : Measurable f) :
    (integralTensorPower n (densityMeasureOfFamily ν f hf)).toOp =
      ∫ x, ((f x).tensorPowGen n).toOp ∂ν := by
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  ext i j
  rw [PureState.integralTensorPower_toOp_apply,
    matrix_integral_entry _ (tensorPower_family_integrable ν f hf)]
  exact integral_map hf.aemeasurable
    (integrable_tensorPow_entry n i j (densityMeasureOfFamily ν f hf)).aestronglyMeasurable

/-- A family of extensions of one marginal induces a fixed-marginal measure. -/
lemma densityMeasureOfFamily_isFixedMarginal {α : Type*} [MeasurableSpace α]
    {a b : ℕ} (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → DensityOp (a * b)) (hf : Measurable f) (σA : DensityOp a)
    (hmarg : ∀ᵐ x ∂ν, (f x).partialTraceB = σA) :
    IsFixedMarginalMeasure σA (densityMeasureOfFamily ν f hf) := by
  exact (densityMeasureOfFamily_ae_iff ν f hf _
    (isClosed_eq partialTraceB_continuous_general continuous_const).measurableSet).mpr hmarg

/-- Linear images of parameterized moments agree with the induced state mixture. -/
lemma linearMap_integral_eq_tensorPower_moment {α : Type*} [MeasurableSpace α]
    {N d n : ℕ} [NeZero d] [NeZero n] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → DensityOp d) (hf : Measurable f) (F : α → Op N) (hF : Integrable F ν)
    (L : Op N →ₗ[ℂ] Op (d ^ n))
    (hmoment : ∀ᵐ x ∂ν, L (F x) = ((f x).tensorPowGen n).toOp) :
    L (∫ x, F x ∂ν) = (integralTensorPower n (densityMeasureOfFamily ν f hf)).toOp := by
  rw [integralTensorPower_densityMeasureOfFamily]
  exact (L.toContinuousLinearMap.integral_comp_comm hF).symm.trans
    (integral_congr_ae hmoment)

/-- Taking the reference marginal commutes with moments of a family of purifications. -/
lemma partialTraceB_family_moment {α : Type*} [MeasurableSpace α]
    {d r n : ℕ} [NeZero d] [NeZero r] [NeZero n]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → DensityOp (d * r)) (hf : Measurable f) :
    partialTraceB (Matrix.reindex (tensorPowerProductEquiv d r n).symm
      (tensorPowerProductEquiv d r n).symm (∫ x, ((f x).tensorPowGen n).toOp ∂ν)) =
      (integralTensorPower n (densityMeasureOfFamily ν (fun x => (f x).partialTraceB)
        (partialTraceB_continuous_general.measurable.comp hf))).toOp := by
  haveI : NeZero (d * r) := ⟨mul_ne_zero (NeZero.ne d) (NeZero.ne r)⟩
  let tr : Op (d ^ n * r ^ n) →ₗ[ℂ] Op (d ^ n) :=
    { toFun := partialTraceB
      map_add' := partialTraceB_add
      map_smul' := partialTraceB_smul }
  let L := tr.comp (Matrix.reindexLinearEquiv ℂ ℂ (tensorPowerProductEquiv d r n).symm
    (tensorPowerProductEquiv d r n).symm).toLinearMap
  exact linearMap_integral_eq_tensorPower_moment ν _
    (partialTraceB_continuous_general.measurable.comp hf) _
    (tensorPower_family_integrable ν f hf) L
    (ae_of_all _ fun x => congrArg (fun ρ : DensityOp (d ^ n) => ρ.toOp)
      (partialTraceB_tensorPow_reindex (n := n) (f x)))

/-- A continuous family of positive trace-one matrices lifts continuously to density operators. -/
lemma exists_continuous_density_family {α : Type*} [TopologicalSpace α] {d : ℕ}
    (F : α → Op d) (hF : Continuous F) (hpos : ∀ x, (F x).PosSemidef)
    (htrace : ∀ x, (F x).trace = 1) :
    ∃ f : α → DensityOp d, Continuous f ∧ ∀ x, (f x).toOp = F x := by
  have hex (x : α) : ∃ σ : DensityOp d, σ.toOp = F x :=
    (Set.ext_iff.mp DensityOp.range_toOp (F x)).mpr ⟨hpos x, htrace x⟩
  choose f hf using hex
  refine ⟨f, DensityOp.isEmbedding_toOp.continuous_iff.mpr ?_, hf⟩
  simpa only [Function.comp_def, hf] using hF

/-- Reference-unitary orbits of an identity-marginal seed give fixed-marginal states. -/
lemma exists_fixedMarginal_referenceOrbit {α : Type*} [TopologicalSpace α] {a b : ℕ}
    (σ : DensityOp a) (T : Op (a * b)) (hT : T.PosSemidef) (hTA : partialTraceB T = 1)
    (U : α → Matrix.unitaryGroup (Fin b) ℂ) (hU : Continuous U) :
    ∃ f : α → DensityOp (a * b), Continuous f ∧
      (∀ x, (f x).toOp = Op.tensor (CFC.sqrt σ.toOp) (U x : Op b) * T *
        (Op.tensor (CFC.sqrt σ.toOp) (U x : Op b))ᴴ) ∧
      ∀ x, (f x).partialTraceB = σ := by
  let K x := Op.tensor (CFC.sqrt σ.toOp) (U x : Op b)
  have hK : Continuous K := Op.continuous_tensor.comp
    (continuous_const.prodMk (continuous_subtype_val.comp hU))
  have hsqrt := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ.toOp)).isHermitian
  have hmarg (x : α) : partialTraceB (K x * T * (K x)ᴴ) = σ.toOp := by
    rw [show (K x)ᴴ = Op.tensor (CFC.sqrt σ.toOp) (U x : Op b)ᴴ by
      change (Op.tensor (CFC.sqrt σ.toOp) (U x : Op b))ᴴ = _
      rw [Op.tensor_conjTranspose, hsqrt.eq], partialTraceB_sandwich_tensor_unitary]
    · rw [hTA, mul_one, CFC.sqrt_mul_sqrt_self _
        (posSemidefOp_implies_mathlib σ.toPosSemidefOp).nonneg]
    · exact Matrix.mem_unitaryGroup_iff'.mp (U x).prop
  obtain ⟨f, hf, hop⟩ := exists_continuous_density_family (fun x => K x * T * (K x)ᴴ)
    ((hK.matrix_mul continuous_const).matrix_mul hK.matrix_conjTranspose)
    (fun x => hT.mul_mul_conjTranspose_same (K x))
    (fun x => by rw [← trace_partialTraceB, hmarg]; exact σ.trace_one)
  exact ⟨f, hf, hop, fun x => DensityOp.ext (by change partialTraceB _ = _; rw [hop, hmarg])⟩

/-- Positive square roots commute with operator tensor powers. -/
lemma sqrt_tensorPow {d : ℕ} (A : Op d) (hA : A.PosSemidef) (n : ℕ) :
    CFC.sqrt (Op.tensorPow A n) = Op.tensorPow (CFC.sqrt A) n := by
  apply CFC.sqrt_unique _ ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).tensorPow n).nonneg
  rw [← Op.mul_tensorPow, CFC.sqrt_mul_sqrt_self A hA.nonneg]

/-- Regrouping tensor powers of a bipartite conjugation separates its two local actions. -/
lemma tensorPow_conjugation_interleaving {a b n : ℕ} [NeZero a] [NeZero b]
    (A : Op a) (U : Op b) (T : Op (a * b)) :
    Matrix.reindex (interleavingEquivGen a b n).symm (interleavingEquivGen a b n).symm
      (Op.tensorPow (Op.tensor A U * T * (Op.tensor A U)ᴴ) n) =
      Op.tensor (Op.tensorPow A n) (1 : Op (b ^ n)) *
        (Op.tensor (1 : Op (a ^ n)) (Op.tensorPow U n) *
          Matrix.reindex (interleavingEquivGen a b n).symm (interleavingEquivGen a b n).symm
            (Op.tensorPow T n) *
          (Op.tensor (1 : Op (a ^ n)) (Op.tensorPow U n))ᴴ) *
        (Op.tensor (Op.tensorPow A n) (1 : Op (b ^ n)))ᴴ := by
  have hK : Matrix.reindex (interleavingEquivGen a b n).symm
      (interleavingEquivGen a b n).symm (Op.tensorPow (Op.tensor A U) n) =
      Op.tensor (Op.tensorPow A n) (Op.tensorPow U n) :=
    by simpa only [Op.tensorPow_eq_tensorFamily] using
      tensorFamily_tensor_interleaving (n := n) (fun _ => A) (fun _ => U)
  rw [Op.mul_tensorPow, Op.mul_tensorPow, ← Op.conjTranspose_tensorPow,
    Matrix.reindex_mul, Matrix.reindex_mul, ← Matrix.conjTranspose_reindex, hK]
  have hfactor : Op.tensor (Op.tensorPow A n) (Op.tensorPow U n) =
      Op.tensor (Op.tensorPow A n) (1 : Op (b ^ n)) *
        Op.tensor (1 : Op (a ^ n)) (Op.tensorPow U n) := by
    rw [Op.tensor_mul, mul_one, one_mul]
  rw [hfactor, Matrix.conjTranspose_mul]
  simp only [mul_assoc]

/-- A reference orbit's tensor moment is the locally filtered reference twirl. -/
lemma referenceOrbit_tensorPower_moment {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] {a b n : ℕ} [NeZero a] [NeZero b] [NeZero n]
    (ν : Measure α) [IsProbabilityMeasure ν] (A : Op a) (T : Op (a * b))
    (U : α → Matrix.unitaryGroup (Fin b) ℂ) (hU : Continuous U)
    (f : α → DensityOp (a * b)) (hf : Measurable f)
    (hop : ∀ x, (f x).toOp = Op.tensor A (U x : Op b) * T * (Op.tensor A (U x : Op b))ᴴ) :
    let S := Op.tensor (Op.tensorPow A n) (1 : Op (b ^ n))
    Matrix.reindex (interleavingEquivGen a b n).symm (interleavingEquivGen a b n).symm
      (∫ x, ((f x).tensorPowGen n).toOp ∂ν) =
      S * (∫ x, Op.tensor (1 : Op (a ^ n)) (Op.tensorPow (U x : Op b) n) *
        Matrix.reindex (interleavingEquivGen a b n).symm (interleavingEquivGen a b n).symm
          (Op.tensorPow T n) *
        (Op.tensor (1 : Op (a ^ n)) (Op.tensorPow (U x : Op b) n))ᴴ ∂ν) * Sᴴ := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  intro S
  let L := (Matrix.reindexLinearEquiv ℂ ℂ (interleavingEquivGen a b n).symm
    (interleavingEquivGen a b n).symm).toLinearMap.toContinuousLinearMap
  let C := ((LinearMap.mulRight ℂ Sᴴ).comp (LinearMap.mulLeft ℂ S)).toContinuousLinearMap
  let F x := Op.tensor (1 : Op (a ^ n)) (Op.tensorPow (U x : Op b) n) *
    Matrix.reindex (interleavingEquivGen a b n).symm (interleavingEquivGen a b n).symm
      (Op.tensorPow T n) * (Op.tensor (1 : Op (a ^ n)) (Op.tensorPow (U x : Op b) n))ᴴ
  have hK : Continuous (fun x => Op.tensor (1 : Op (a ^ n)) (Op.tensorPow (U x : Op b) n)) :=
    Op.continuous_tensor.comp (continuous_const.prodMk
      ((Op.continuous_tensorPow n).comp (continuous_subtype_val.comp hU)))
  have hF : Integrable F ν :=
    ((hK.matrix_mul continuous_const).matrix_mul hK.matrix_conjTranspose).integrable_of_compactSpace
  change L (∫ x, ((f x).tensorPowGen n).toOp ∂ν) = C (∫ x, F x ∂ν)
  refine (L.integral_comp_comm (tensorPower_family_integrable ν f hf)).symm.trans
    (Eq.trans ?_ (C.integral_comp_comm hF))
  apply integral_congr_ae
  filter_upwards [] with x
  change Matrix.reindex _ _ ((f x).tensorPowGen n).toOp = _
  rw [DensityOp.tensorPowGen_toOp, hop]
  exact tensorPow_conjugation_interleaving A (U x : Op b) T

/-- Returning a purification to paired registers and tracing commutes with tensor powers. -/
lemma partialTraceB_pairedToBlocked_tensorPow {a b n : ℕ} [NeZero a] [NeZero b]
    (τ : DensityOp (a * (a * b ^ 2))) :
    let e := finCongr (show a * (a * b ^ 2) = (a * b) * (a * b) by ring)
    partialTraceB (Matrix.reindex (pairedToBlockedEquiv a b n).symm
      (pairedToBlockedEquiv a b n).symm
      (Matrix.reindex (interleavingEquivGen a (a * b ^ 2) n).symm
        (interleavingEquivGen a (a * b ^ 2) n).symm (τ.tensorPowGen n).toOp)) =
      ((densityOp_reindex e τ).partialTraceB.tensorPowGen n).toOp := by
  dsimp only
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  rw [DensityOp.tensorPowGen_toOp, pairedToBlockedEquiv_tensorPow_cast]
  let q := densityOp_reindex
    (finCongr (show a * (a * b ^ 2) = (a * b) * (a * b) by ring)) τ
  have h := congrArg (fun σ => σ.toOp) (partialTraceB_tensorPow_reindex (n := n) q)
  change partialTraceB (Matrix.reindex (tensorPowerProductEquiv (a * b) (a * b) n).symm
    (tensorPowerProductEquiv (a * b) (a * b) n).symm (q.tensorPowGen n).toOp) = _ at h
  rw [DensityOp.tensorPowGen_toOp] at h
  exact h

/-- The partial trace of a regrouped purification moment is its induced state moment. -/
lemma partialTraceB_pairedToBlocked_family_moment {α : Type*} [MeasurableSpace α]
    {a b n : ℕ} [NeZero a] [NeZero b] [NeZero n]
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → DensityOp (a * (a * b ^ 2)))
    (hf : Measurable f) :
    let e := finCongr (show a * (a * b ^ 2) = (a * b) * (a * b) by ring)
    partialTraceB (Matrix.reindex (pairedToBlockedEquiv a b n).symm
      (pairedToBlockedEquiv a b n).symm
      (Matrix.reindex (interleavingEquivGen a (a * b ^ 2) n).symm
        (interleavingEquivGen a (a * b ^ 2) n).symm
        (∫ x, ((f x).tensorPowGen n).toOp ∂ν))) =
      ∫ x, ((densityOp_reindex e (f x)).partialTraceB.tensorPowGen n).toOp ∂ν := by
  haveI : NeZero (a * (a * b ^ 2)) :=
    ⟨mul_ne_zero (NeZero.ne a) (mul_ne_zero (NeZero.ne a) (pow_ne_zero 2 (NeZero.ne b)))⟩
  dsimp only
  let tr : Op ((a * b) ^ n * (a * b) ^ n) →ₗ[ℂ] Op ((a * b) ^ n) :=
    { toFun := partialTraceB
      map_add' := partialTraceB_add
      map_smul' := partialTraceB_smul }
  let L := (tr.comp ((Matrix.reindexLinearEquiv ℂ ℂ (pairedToBlockedEquiv a b n).symm
    (pairedToBlockedEquiv a b n).symm).toLinearMap.comp
    (Matrix.reindexLinearEquiv ℂ ℂ (interleavingEquivGen a (a * b ^ 2) n).symm
      (interleavingEquivGen a (a * b ^ 2) n).symm).toLinearMap)).toContinuousLinearMap
  change L (∫ x, ((f x).tensorPowGen n).toOp ∂ν) = _
  refine (L.integral_comp_comm (tensorPower_family_integrable ν f hf)).symm.trans ?_
  exact integral_congr_ae (ae_of_all _ fun x => partialTraceB_pairedToBlocked_tensorPow (f x))

/-- Tracing Bob and the purification reference leaves the original Alice marginal. -/
lemma partialTraceB_pairedReference_marginal {a b : ℕ}
    (τ : DensityOp (a * (a * b ^ 2))) :
    let e := finCongr (show a * (a * b ^ 2) = (a * b) * (a * b) by ring)
    (densityOp_reindex e τ).partialTraceB.partialTraceB = τ.partialTraceB := by
  dsimp only
  apply DensityOp.ext
  have h := partialTraceB_reindex_assoc_cast
    (show b * (a * b) = a * b ^ 2 by ring)
    (Matrix.reindex (finCongr (show a * (a * b ^ 2) = (a * b) * (a * b) by ring))
      (finCongr (show a * (a * b ^ 2) = (a * b) * (a * b) by ring)) τ.toOp)
  simp only [← Op.castDim_eq_reindex_finCongr, Op.castDim_cancel] at h
  simp only [Op.castDim_eq_reindex_finCongr] at h
  exact h.symm

/-- Reindexing density operators is continuous. -/
lemma continuous_densityOp_reindex {a b : ℕ} (e : Fin a ≃ Fin b) :
    Continuous (densityOp_reindex e) := by
  apply DensityOp.isEmbedding_toOp.continuous_iff.mpr
  exact (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.toContinuousLinearMap.continuous.comp
    DensityOp.continuous_toOp

end InfoTheory.Postselection
