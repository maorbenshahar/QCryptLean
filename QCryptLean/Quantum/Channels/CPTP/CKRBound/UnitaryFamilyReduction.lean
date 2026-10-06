import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity
import QCryptLean.Quantum.Metrics.BlockDiagonalTraceNorm
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD

/-!
# Block-diagonal averaging over a finite unitary family

Generalization of the permutation block-diagonal extension
(`Quantum.Channels.blockDiagExt`, `PermutationReduction.lean`) from the permutation
family to an arbitrary finite family of unitaries `U : Fin k → Op d`: the
block-diagonal extension `blockDiagExtFamily`, its PSD-ness, its `mapTensorId`
block structure and trace norm, the marginal identification
(`blockDiagExtFamily_partialTraceB`), and the resulting existence and
purification-bound statements (`block_diag_extension_exists_family`,
`block_diagonal_purification_bound_family`). The permutation instance is
`blockDiagExt` with
`U i := permutationRepresentation d n ((Fintype.equivFin (Equiv.Perm (Fin n))).symm i)`
(see `blockDiagExt_eq_blockDiagExtFamily` in `PermutationReduction.lean`).

The main consumers are the group-symmetric de Finetti reduction
(`InfoTheory/Postselection/GroupTwirl.lean`, instantiating the family with a
product group representation) and the permutation reduction itself.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The block-diagonal extension over a finite family of unitaries `U : Fin k → Op d`:
the `i`-th diagonal block is `(1/k) • (U i ⊗ 1) ρ (U i ⊗ 1)ᴴ`. Specializing
`U i := permutationRepresentation d n (e i)` recovers `blockDiagExt`. -/
def blockDiagExtFamily {d k : ℕ} [NeZero d] [NeZero k]
    (U : Fin k → Op d) (ρ : Op (d * d)) :
    Op (d * (d * k)) :=
  let c : ℂ := 1 / (k : ℂ)
  Matrix.of fun α β =>
    let p := finProdFinEquiv.symm α
    let ps := finProdFinEquiv.symm p.2
    let q := finProdFinEquiv.symm β
    let qs := finProdFinEquiv.symm q.2
    if ps.2 = qs.2 then
      c * (Op.tensor (U ps.2) (1 : Op d) * ρ *
           (Op.tensor (U ps.2) (1 : Op d))ᴴ)
        (finProdFinEquiv (p.1, ps.1)) (finProdFinEquiv (q.1, qs.1))
    else 0

/-- The block-diagonal extension over a unitary family is PSD (each block is a
nonnegative multiple of a conjugate sandwich of a PSD matrix). -/
lemma blockDiagExtFamily_posSemidef {d k : ℕ} [NeZero d] [NeZero k]
    (U : Fin k → Op d) (ρ : Op (d * d)) (hρ_psd : ρ.PosSemidef) :
    (blockDiagExtFamily U ρ).PosSemidef := by
  set c : ℂ := 1 / (k : ℂ) with hc_def
  set e_reindex : Fin (d * (d * k)) ≃ Fin (d * d) × Fin k :=
    finProdFinEquiv_assoc_right d d k with he_reindex
  set M := fun i : Fin k => c • (Op.tensor (U i) (1 : Op d) * ρ *
      (Op.tensor (U i) (1 : Op d))ᴴ) with hM_def
  suffices h_eq : blockDiagExtFamily U ρ = (blockDiagonal M).submatrix e_reindex e_reindex by
    rw [h_eq]
    exact (posSemidef_submatrix_equiv e_reindex).mpr
      (Matrix.posSemidef_blockDiagonal fun i =>
        ((hρ_psd.mul_mul_conjTranspose_same _).smul (by
          rw [Complex.le_def]
          constructor <;> simp [hc_def])))
  ext α β
  simp only [blockDiagExtFamily, Matrix.of_apply, Matrix.submatrix_apply,
    blockDiagonal_apply, he_reindex, finProdFinEquiv_assoc_right, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq,
    Equiv.prodAssoc_symm_apply, hM_def, Matrix.smul_apply, smul_eq_mul, hc_def]

/-- Applying `mapTensorId` to the block-diagonal extension over a unitary family
keeps the blocks diagonal in the added classical register. -/
lemma mapTensorId_blockDiagExtFamily_eq_blockDiagonal {d k dimOut : ℕ}
    [NeZero d] [NeZero k] [NeZero dimOut]
    (Δ : Op d →ₗ[ℂ] Op dimOut)
    (U : Fin k → Op d) (ρ : Op (d * d)) :
    mapTensorId Δ (blockDiagExtFamily U ρ) =
      (Matrix.blockDiagonal (fun i : Fin k => mapTensorId Δ
        ((1 / (k : ℂ)) • (Op.tensor (U i) (1 : Op d) * ρ *
          (Op.tensor (U i) (1 : Op d))ᴴ)))).submatrix
        (finProdFinEquiv_assoc_right dimOut d k)
        (finProdFinEquiv_assoc_right dimOut d k) := by
  ext p q
  simp only [mapTensorId, Matrix.of_apply, blockDiagExtFamily, Matrix.blockDiagonal_apply,
    Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, Equiv.symm_apply_apply,
    finProdFinEquiv_assoc_right, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_fst, Prod.map_snd, id_eq, Equiv.prodAssoc_symm_apply]
  split_ifs with h
  · rfl
  · simp [mul_zero]

/-- Trace norm of the block-diagonal extension over a unitary family is the sum of
the family-average sandwiches' trace norms. -/
lemma blockDiagExtFamily_traceNorm_as_sum {d k dimOut : ℕ}
    [NeZero d] [NeZero k] [NeZero dimOut]
    (Δ : Op d →ₗ[ℂ] Op dimOut)
    (U : Fin k → Op d) (ρ : Op (d * d)) :
    traceNorm (mapTensorId Δ (blockDiagExtFamily U ρ)) =
    ∑ i : Fin k, ‖(1 : ℂ) / (k : ℂ)‖ *
      traceNorm (mapTensorId Δ
        (Op.tensor (U i) (1 : Op d) * ρ * (Op.tensor (U i) (1 : Op d))ᴴ)) := by
  set c : ℂ := 1 / (k : ℂ) with hc
  set M := fun i : Fin k => c • (Op.tensor (U i) (1 : Op d) * ρ *
      (Op.tensor (U i) (1 : Op d))ᴴ) with hM
  set M' := fun i : Fin k => mapTensorId Δ (M i) with hM'
  set e_out : Fin (dimOut * (d * k)) ≃ Fin (dimOut * d) × Fin k :=
    finProdFinEquiv_assoc_right dimOut d k with he_out
  have h_map_bd : mapTensorId Δ (blockDiagExtFamily U ρ) =
      (Matrix.blockDiagonal M').submatrix e_out e_out := by
    simpa [M', hM', M, hM, e_out, he_out, c, hc] using
      mapTensorId_blockDiagExtFamily_eq_blockDiagonal Δ U ρ
  have h_tn_bd : traceNorm ((Matrix.blockDiagonal M').submatrix e_out e_out) =
      ∑ i, traceNorm (M' i) := by
    exact traceNorm_blockDiagonal_submatrix_finProdAssoc M'
  rw [h_map_bd, h_tn_bd]
  simp only [hM', hM, mapTensorId_smul_basic Δ c,
    Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]

/-- Covariance under conjugation by a single unitary turns an input-side `⊗1`-sandwich
into output-side `mapTensorId` composition (unitary-family analogue of
`mapTensorId_perm_sandwich_eq_comp`). -/
lemma mapTensorId_unitary_sandwich_eq_comp {d k dimOut : ℕ}
    [NeZero d] [NeZero k] [NeZero dimOut]
    (Δ : Op d →ₗ[ℂ] Op dimOut)
    (U : Op d)
    (K : Op dimOut → Op dimOut)
    (hK_lin : IsLinearMap ℂ K)
    (hK_cov : ∀ (ρ : Op d), Δ (U * ρ * Uᴴ) = K (Δ ρ))
    (ρ : Op (d * k)) :
    mapTensorId Δ (Op.tensor U (1 : Op k) * ρ * (Op.tensor U (1 : Op k))ᴴ) =
    mapTensorId (IsLinearMap.mk' K hK_lin) (mapTensorId Δ ρ) := by
  rw [mapTensorId_comp Δ (IsLinearMap.mk' K hK_lin) ρ]
  rw [Op.tensor_conjTranspose, conjTranspose_one]
  ext p q
  simp only [mapTensorId, Matrix.of_apply]
  rw [mapTensorId_entry_eq_apply_block Δ
      (Op.tensor U (1 : Op k) * ρ * Op.tensor Uᴴ (1 : Op k)),
    mapTensorId_entry_eq_apply_block ((IsLinearMap.mk' K hK_lin).comp Δ) ρ]
  simp only [LinearMap.comp_apply, IsLinearMap.mk'_apply]
  rw [tensor_sandwich_block U Uᴴ ρ]
  exact congr_fun₂ (hK_cov _) _ _

/-- Trace-norm invariance of `mapTensorId Δ` under a `⊗1`-sandwich by a unitary whose
conjugation action on `Δ` is implemented by CPTP maps in both directions (unitary-family
analogue of `traceNorm_mapTensorId_perm_invariant`). -/
lemma traceNorm_mapTensorId_unitary_sandwich_invariant {d k dimOut : ℕ}
    [NeZero d] [NeZero k] [NeZero dimOut]
    (Δ : Op d →ₗ[ℂ] Op dimOut)
    (U : Op d) (hu1 : Uᴴ * U = 1) (hu2 : U * Uᴴ = 1)
    (K K' : Op dimOut → Op dimOut)
    (hK_cptp : IsCPTP K) (hK'_cptp : IsCPTP K')
    (hK_cov : ∀ (σ : Op d), Δ (U * σ * Uᴴ) = K (Δ σ))
    (hK'_cov : ∀ (σ : Op d), Δ (Uᴴ * σ * U) = K' (Δ σ))
    (ρ : Op (d * k)) :
    traceNorm (mapTensorId Δ (Op.tensor U (1 : Op k) * ρ * (Op.tensor U (1 : Op k))ᴴ)) =
    traceNorm (mapTensorId Δ ρ) := by
  have h_sandwich_cancel :
      Op.tensor Uᴴ (1 : Op k) * (Op.tensor U (1 : Op k) * ρ * (Op.tensor U (1 : Op k))ᴴ) *
        (Op.tensor Uᴴ (1 : Op k))ᴴ = ρ := by
    simp only [Op.tensor_conjTranspose, conjTranspose_one, conjTranspose_conjTranspose]
    have hAB : Op.tensor Uᴴ (1 : Op k) * Op.tensor U (1 : Op k) = 1 := by
      rw [Op.tensor_mul, mul_one, hu1, Op.tensor_one]
    have hBA : Op.tensor U (1 : Op k) * Op.tensor Uᴴ (1 : Op k) = 1 := by
      rw [Op.tensor_mul, mul_one, hu2, Op.tensor_one]
    calc Op.tensor Uᴴ (1 : Op k) *
          (Op.tensor U (1 : Op k) * ρ * Op.tensor Uᴴ (1 : Op k)) * Op.tensor U (1 : Op k)
        = (Op.tensor Uᴴ (1 : Op k) * Op.tensor U (1 : Op k)) * ρ *
          (Op.tensor Uᴴ (1 : Op k) * Op.tensor U (1 : Op k)) := by noncomm_ring
      _ = ρ := by rw [hAB, one_mul, mul_one]
  rw [mapTensorId_unitary_sandwich_eq_comp Δ U K hK_cptp.1 hK_cov ρ]
  set Y := mapTensorId Δ ρ with hY_def
  have h_fwd : traceNorm (mapTensorId (IsLinearMap.mk' K hK_cptp.1) Y) ≤ traceNorm Y :=
    traceNorm_mapTensorId_cptp_contractive (IsLinearMap.mk' K hK_cptp.1) hK_cptp Y
  -- Restate the adjoint covariance with `(Uᴴ)ᴴ` so it matches the lemma instantiation.
  have hK'cov : ∀ (σ : Op d), Δ (Uᴴ * σ * (Uᴴ)ᴴ) = K' (Δ σ) := by
    intro σ
    simpa using hK'_cov σ
  have h_inv_eq := mapTensorId_unitary_sandwich_eq_comp Δ Uᴴ K' hK'_cptp.1 hK'cov
    (Op.tensor U (1 : Op k) * ρ * (Op.tensor U (1 : Op k))ᴴ)
  rw [h_sandwich_cancel] at h_inv_eq
  rw [mapTensorId_unitary_sandwich_eq_comp Δ U K hK_cptp.1 hK_cov ρ] at h_inv_eq
  rw [← hY_def] at h_inv_eq
  have h_bwd : traceNorm Y ≤ traceNorm (mapTensorId (IsLinearMap.mk' K hK_cptp.1) Y) := by
    have h1 := traceNorm_mapTensorId_cptp_contractive (IsLinearMap.mk' K' hK'_cptp.1)
      hK'_cptp (mapTensorId (IsLinearMap.mk' K hK_cptp.1) Y)
    rw [← h_inv_eq] at h1
    exact h1
  exact le_antisymm h_fwd h_bwd

/-- Trace-norm equality for the block-diagonal extension over a unitary family with
CPTP covariance in both directions (family analogue of `blockDiagExt_traceNorm_mapTensorId`). -/
lemma blockDiagExtFamily_traceNorm_mapTensorId {d k dimOut : ℕ}
    [NeZero d] [NeZero k] [NeZero dimOut]
    (Δ : Op d →ₗ[ℂ] Op dimOut)
    (U : Fin k → Op d)
    (hU_unit : ∀ i : Fin k, (U i)ᴴ * U i = 1 ∧ U i * (U i)ᴴ = 1)
    (hΔ_cov : ∀ i : Fin k, ∃ (K K' : Op dimOut → Op dimOut), IsCPTP K ∧ IsCPTP K' ∧
      (∀ σ : Op d, Δ (U i * σ * (U i)ᴴ) = K (Δ σ)) ∧
      (∀ σ : Op d, Δ ((U i)ᴴ * σ * U i) = K' (Δ σ)))
    (ρ : Op (d * d)) :
    traceNorm (mapTensorId Δ (blockDiagExtFamily U ρ)) =
    traceNorm (mapTensorId Δ ρ) := by
  rw [blockDiagExtFamily_traceNorm_as_sum Δ U ρ]
  have h_term : ∀ i : Fin k, traceNorm (mapTensorId Δ
      (Op.tensor (U i) (1 : Op d) * ρ * (Op.tensor (U i) (1 : Op d))ᴴ)) =
      traceNorm (mapTensorId Δ ρ) := by
    intro i
    obtain ⟨K, K', hK, hK', h_cov, h_cov'⟩ := hΔ_cov i
    exact traceNorm_mapTensorId_unitary_sandwich_invariant Δ (U i) (hU_unit i).1
      (hU_unit i).2 K K' hK hK' h_cov h_cov' ρ
  simp_rw [h_term]
  simp only [one_div, norm_inv, RCLike.norm_natCast, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hk : (k : ℝ) ≠ 0 := by simpa using NeZero.ne k
  -- the scalar prefactor cancels: k * k⁻¹ = 1
  rw [← mul_assoc, mul_inv_cancel₀ hk, one_mul]

/-- The partial trace over the second factor of the block-diagonal extension over a
unitary family is the family average of the sandwiches of the marginal (family analogue
of `partialTraceB_blockDiagExt_eq_avg`). -/
lemma partialTraceB_blockDiagExtFamily_eq_avg {d k : ℕ} [NeZero d] [NeZero k]
    (U : Fin k → Op d) (ρ : Op (d * d)) :
    partialTraceB (blockDiagExtFamily U ρ) =
    (1 / (k : ℂ)) • ∑ i : Fin k, U i * partialTraceB ρ * (U i)ᴴ := by
  have h_sandwich : ∀ i : Fin k,
      partialTraceB ((Op.tensor (U i) (1 : Op d)) * ρ *
        (Op.tensor (U i) (1 : Op d))ᴴ) =
      U i * partialTraceB ρ * (U i)ᴴ := by
    intro i
    rw [Op.tensor_conjTranspose, conjTranspose_one]
    exact partialTraceB_sandwich_tensor_one _ _ _
  suffices h : partialTraceB (blockDiagExtFamily U ρ) =
    (1 / (k : ℂ)) • ∑ i : Fin k,
      partialTraceB ((Op.tensor (U i) (1 : Op d)) * ρ *
        (Op.tensor (U i) (1 : Op d))ᴴ) by
    rw [h]
    simp_rw [h_sandwich]
  ext a a'
  simp only [partialTraceB, blockDiagExtFamily, Matrix.of_apply, Matrix.smul_apply,
    Finset.smul_sum, Matrix.sum_apply]
  simp only [Equiv.symm_apply_apply, ite_true, smul_eq_mul]
  rw [Finset.sum_comm]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp_rw [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]

/-- The marginal of the block-diagonal extension over a unitary family is `ρ.trace` times
the family-twirl of the normalized marginal `σ_A` (family analogue of
`blockDiagExt_partialTraceB`; the result is the group-twirl, not yet the permutation
symmetrization). -/
lemma blockDiagExtFamily_partialTraceB {d k : ℕ} [NeZero d] [NeZero k]
    (U : Fin k → Op d) (ρ : Op (d * d))
    (hρ_psd : ρ.PosSemidef)
    (hρ_nz : ρ ≠ 0)
    (σ_A : DensityOp d)
    (hσ_A : σ_A.toOp = (1 / ρ.trace) • partialTraceB ρ) :
    partialTraceB (blockDiagExtFamily U ρ) =
    ρ.trace • ((1 / (k : ℂ)) • ∑ i : Fin k, U i * σ_A.toOp * (U i)ᴴ) := by
  rw [partialTraceB_blockDiagExtFamily_eq_avg]
  have h_trace_nz : ρ.trace ≠ 0 := by
    intro h
    exact hρ_nz (hρ_psd.trace_eq_zero_iff.mp h)
  have h_ptB : partialTraceB ρ = ρ.trace • σ_A.toOp := by
    rw [hσ_A, smul_smul, mul_div_cancel₀ _ h_trace_nz, one_smul]
  rw [h_ptB]
  have h_factor : ∀ i : Fin k, U i * (ρ.trace • σ_A.toOp) * (U i)ᴴ =
      ρ.trace • (U i * σ_A.toOp * (U i)ᴴ) := by
    intro i
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [show (∑ i : Fin k, U i * (ρ.trace • σ_A.toOp) * (U i)ᴴ) =
    ∑ i, ρ.trace • (U i * σ_A.toOp * (U i)ᴴ)
    from Finset.sum_congr rfl (fun i _ => h_factor i)]
  rw [← Finset.smul_sum, smul_comm]

/-- The family-twirl average `(1/k) ∑ i, U i * σ * (U i)ᴴ` of a PSD matrix over a finite
unitary family is PSD. -/
lemma twirlFamily_posSemidef {d k : ℕ} [NeZero k]
    (U : Fin k → Op d) (σ : Op d) (hσ : σ.PosSemidef) :
    ((1 / (k : ℂ)) • ∑ i : Fin k, U i * σ * (U i)ᴴ).PosSemidef := by
  have him : (1 / (k : ℂ)).im = 0 := by
    rw [Complex.div_im, Complex.one_im, Complex.natCast_im, Complex.one_re,
      zero_mul, zero_div]
    simp
  apply posSemidef_smul_of_nonneg_re
  · -- each conjugate sandwich is PSD; a sum of PSD matrices is PSD
    refine Finset.sum_induction (fun (i : Fin k) => U i * σ * (U i)ᴴ) Matrix.PosSemidef
      (fun _ _ => Matrix.PosSemidef.add) Matrix.PosSemidef.zero ?_
    intro i _
    exact hσ.mul_mul_conjTranspose_same (U i)
  · simp
  · exact him

/-- Existence of a block-diagonal extension over a unitary family with the required
marginal domination (family analogue of `block_diag_extension_exists`). -/
lemma block_diag_extension_exists_family {d k dimOut : ℕ}
    [NeZero d] [NeZero k] [NeZero dimOut]
    (Δ : Op d →ₗ[ℂ] Op dimOut)
    (U : Fin k → Op d)
    (hU_unit : ∀ i : Fin k, (U i)ᴴ * U i = 1 ∧ U i * (U i)ᴴ = 1)
    (hΔ_cov : ∀ i : Fin k, ∃ (K K' : Op dimOut → Op dimOut), IsCPTP K ∧ IsCPTP K' ∧
      (∀ σ : Op d, Δ (U i * σ * (U i)ᴴ) = K (Δ σ)) ∧
      (∀ σ : Op d, Δ ((U i)ᴴ * σ * U i) = K' (Δ σ)))
    (ρ : Op (d * d))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1)
    (hρ_nz : ρ ≠ 0)
    (σ_A : DensityOp d)
    (hσ_A : σ_A.toOp = (1 / ρ.trace) • partialTraceB ρ)
    (Ψ : DensityOp (d * d))
    (hΨ_marginal : partialTraceB Ψ.toOp =
      (1 / (k : ℂ)) • ∑ i : Fin k, U i * σ_A.toOp * (U i)ᴴ) :
    ∃ (dimK : ℕ) (_ : NeZero dimK) (ρ_ext : Op (d * dimK)),
        ρ_ext.PosSemidef ∧
        traceNorm (mapTensorId Δ ρ_ext) = traceNorm (mapTensorId Δ ρ) ∧
        ((1 : ℂ) • Ψ.partialTraceB.toOp - partialTraceB ρ_ext).PosSemidef := by
  refine ⟨d * k, inferInstance, blockDiagExtFamily U ρ,
    blockDiagExtFamily_posSemidef U ρ hρ_psd,
    blockDiagExtFamily_traceNorm_mapTensorId Δ U hU_unit hΔ_cov ρ, ?_⟩
  rw [blockDiagExtFamily_partialTraceB U ρ hρ_psd hρ_nz σ_A hσ_A]
  have h_marginal_eq : Ψ.partialTraceB.toOp =
      (1 / (k : ℂ)) • ∑ i : Fin k, U i * σ_A.toOp * (U i)ᴴ := by
    change partialTraceB Ψ.toOp = _
    exact hΨ_marginal
  rw [h_marginal_eq, one_smul]
  rw [show (1 / (k : ℂ)) • ∑ i : Fin k, U i * σ_A.toOp * (U i)ᴴ -
      ρ.trace • ((1 / (k : ℂ)) • ∑ i : Fin k, U i * σ_A.toOp * (U i)ᴴ) =
      (1 - ρ.trace) • ((1 / (k : ℂ)) • ∑ i : Fin k, U i * σ_A.toOp * (U i)ᴴ) from by
    rw [sub_smul, one_smul]]
  apply posSemidef_smul_of_nonneg_re
  · exact twirlFamily_posSemidef U σ_A.toOp
      (posSemidefOp_implies_mathlib σ_A.toPosSemidefOp)
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
  · simp only [Complex.sub_im, Complex.one_im, zero_sub]
    have h_sa : IsSelfAdjoint ρ.trace := isSelfAdjoint_trace_of_isHermitian hρ_psd.isHermitian
    rw [Complex.conj_eq_iff_im.mp h_sa]
    ring

/-- The generic block-diagonal averaging over a unitary family plus purification bound
(family analogue of `block_diagonal_purification_bound`). -/
lemma block_diagonal_purification_bound_family {d k dimOut : ℕ}
    [NeZero d] [NeZero k] [NeZero dimOut]
    (Δ : Op d →ₗ[ℂ] Op dimOut)
    (U : Fin k → Op d)
    (hU_unit : ∀ i : Fin k, (U i)ᴴ * U i = 1 ∧ U i * (U i)ᴴ = 1)
    (hΔ_cov : ∀ i : Fin k, ∃ (K K' : Op dimOut → Op dimOut), IsCPTP K ∧ IsCPTP K' ∧
      (∀ σ : Op d, Δ (U i * σ * (U i)ᴴ) = K (Δ σ)) ∧
      (∀ σ : Op d, Δ ((U i)ᴴ * σ * U i) = K' (Δ σ)))
    (ρ : Op (d * d))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1)
    (hρ_nz : ρ ≠ 0)
    (σ_norm : DensityOp d)
    (hσ_norm : σ_norm.toOp = (1 / ρ.trace) • partialTraceB ρ)
    (Ψ : DensityOp (d * d))
    (hΨ_pure : Ψ.IsPure)
    (hΨ_marginal : partialTraceB Ψ.toOp =
      (1 / (k : ℂ)) • ∑ i : Fin k, U i * σ_norm.toOp * (U i)ᴴ) :
    traceNorm (mapTensorId Δ ρ) ≤ traceNorm (mapTensorId Δ Ψ.toOp) := by
  obtain ⟨dimK, hNZ_K, ρ_ext, hρ_ext_psd, h_traceNorm_eq, h_marginal_dom⟩ :=
    block_diag_extension_exists_family Δ U hU_unit hΔ_cov ρ hρ_psd hρ_trace hρ_nz
      σ_norm hσ_norm Ψ hΨ_marginal
  have h_dom' : ((↑(1 : ℝ) : ℂ) • Ψ.partialTraceB.toOp - partialTraceB ρ_ext).PosSemidef := by
    rw [Complex.ofReal_one]
    exact h_marginal_dom
  have h_bound := traceNorm_mapTensorId_substate_bound Δ
    ρ_ext hρ_ext_psd Ψ hΨ_pure 1 one_pos h_dom'
  rw [h_traceNorm_eq] at h_bound
  linarith

end Quantum.Channels
