import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity
import QCryptLean.Quantum.Channels.CPTP.CKRBound.UnitaryFamilyReduction
import QCryptLean.InfoTheory.DeFinetti.Purification
import QCryptLean.Quantum.Metrics.BlockDiagonalTraceNorm
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.Combinatorics.FinProductEquiv

/-!
# CKR Permutation Reduction — block-diagonal averaging, symmetrized marginals, trace-norm bounds

This file develops the generic permutation-averaging reduction used in the CKR bound.
It builds the block-diagonal permutation extension, identifies its symmetrized marginal,
and proves the corresponding `mapTensorId` trace-norm bounds under permutation covariance.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Product coordinates recover a flattened finite product index. -/
lemma finProdFinEquiv_divNat_modNat {n m : ℕ} [NeZero m] (j : Fin (n * m)) :
    j = finProdFinEquiv (j.divNat, j.modNat) := by
  ext
  simp [finProdFinEquiv, Fin.coe_divNat, Fin.coe_modNat, Nat.mod_add_div]

/-- A matrix-unit entry on the first product coordinate is the corresponding
full product-coordinate matrix-unit entry with the second coordinates fixed. -/
lemma matrix_single_apply_divNat_eq_single_prod_modNat {n m : ℕ} [NeZero m]
    (a b : Fin n) (p q : Fin (n * m)) (c : ℂ) :
    Matrix.single a b c p.divNat q.divNat =
      Matrix.single (finProdFinEquiv (a, p.modNat)) (finProdFinEquiv (b, q.modNat)) c p q := by
  rw [show p = finProdFinEquiv (p.divNat, p.modNat) from
      finProdFinEquiv_divNat_modNat p]
  rw [show q = finProdFinEquiv (q.divNat, q.modNat) from
      finProdFinEquiv_divNat_modNat q]
  have hp_div :
      (finProdFinEquiv (p.divNat, p.modNat)).divNat = p.divNat := by
    have h := finProdFinEquiv.symm_apply_apply (p.divNat, p.modNat)
    rw [finProdFinEquiv_symm_apply] at h
    exact congrArg Prod.fst h
  have hp_mod :
      (finProdFinEquiv (p.divNat, p.modNat)).modNat = p.modNat := by
    have h := finProdFinEquiv.symm_apply_apply (p.divNat, p.modNat)
    rw [finProdFinEquiv_symm_apply] at h
    exact congrArg Prod.snd h
  have hq_div :
      (finProdFinEquiv (q.divNat, q.modNat)).divNat = q.divNat := by
    have h := finProdFinEquiv.symm_apply_apply (q.divNat, q.modNat)
    rw [finProdFinEquiv_symm_apply] at h
    exact congrArg Prod.fst h
  have hq_mod :
      (finProdFinEquiv (q.divNat, q.modNat)).modNat = q.modNat := by
    have h := finProdFinEquiv.symm_apply_apply (q.divNat, q.modNat)
    rw [finProdFinEquiv_symm_apply] at h
    exact congrArg Prod.snd h
  by_cases hp : a = p.divNat <;> by_cases hq : b = q.divNat <;>
    simp [hp, hq, hp_div, hp_mod, hq_div, hq_mod]

/-- A conditional matrix unit on the first product coordinate can be read as a
conditional matrix unit on the full product coordinate with fixed second
coordinates. -/
lemma matrix_ite_single_apply_divNat_eq_single_prod_modNat {n m : ℕ} [NeZero m]
    (P : Prop) [Decidable P] (a b : Fin n) (p q : Fin (n * m)) (c : ℂ) :
    (if P then Matrix.single a b c else 0) p.divNat q.divNat =
      (if P then
        Matrix.single (finProdFinEquiv (a, p.modNat)) (finProdFinEquiv (b, q.modNat)) c
      else 0) p q := by
  by_cases h : P
  · simp [h, matrix_single_apply_divNat_eq_single_prod_modNat]
  · simp [h]

/-- Covariance turns permutation input sandwiches into output-side `mapTensorId`. -/
lemma mapTensorId_perm_sandwich_eq_comp {d n dimOut k : ℕ}
    [NeZero d] [NeZero dimOut] [NeZero k]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (π : Equiv.Perm (Fin n))
    (K : Op dimOut → Op dimOut)
    (hK_lin : IsLinearMap ℂ K)
    (hK_cov : ∀ (ρ : Op (d ^ n)),
      Δ (permutationRepresentation d n π * ρ *
        (permutationRepresentation d n π)ᴴ) = K (Δ ρ))
    (ρ : Op (d ^ n * k)) :
    mapTensorId Δ (Op.tensor (permutationRepresentation d n π) (1 : Op k) * ρ *
      (Op.tensor (permutationRepresentation d n π) (1 : Op k))ᴴ) =
    mapTensorId (IsLinearMap.mk' K hK_lin) (mapTensorId Δ ρ) := by
  rw [mapTensorId_comp Δ (IsLinearMap.mk' K hK_lin) ρ]
  set P := permutationRepresentation d n π with hP_def
  rw [Op.tensor_conjTranspose, conjTranspose_one]
  ext p q
  simp only [mapTensorId, Matrix.of_apply]
  rw [mapTensorId_entry_eq_apply_block Δ
      (Op.tensor P (1 : Op k) * ρ * Op.tensor Pᴴ (1 : Op k)),
    mapTensorId_entry_eq_apply_block ((IsLinearMap.mk' K hK_lin).comp Δ) ρ]
  simp only [LinearMap.comp_apply, IsLinearMap.mk'_apply]
  rw [tensor_sandwich_block P Pᴴ ρ]
  exact congr_fun₂ (hK_cov _) _ _

/-- Entry form for a first-factor tensor sandwich, using `divNat`/`modNat`
coordinates for the flattened product indices. -/
lemma tensor_sandwich_apply_eq_block {n k : ℕ} [NeZero n] [NeZero k]
    (P Q : Op n) (ρ : Op (n * k)) (p q : Fin (n * k)) :
    (Op.tensor P (1 : Op k) * ρ * Op.tensor Q (1 : Op k)) p q =
      (P * (Matrix.of fun i j =>
          ρ (finProdFinEquiv (i, p.modNat)) (finProdFinEquiv (j, q.modNat))) * Q)
        p.divNat q.divNat := by
  rw [show p = finProdFinEquiv (p.divNat, p.modNat) from
      finProdFinEquiv_divNat_modNat p]
  rw [show q = finProdFinEquiv (q.divNat, q.modNat) from
      finProdFinEquiv_divNat_modNat q]
  simpa [finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat] using
    congr_fun₂ (tensor_sandwich_block P Q ρ p.modNat q.modNat) p.divNat q.divNat

/-- A covariance identity on the first tensor factor lifts through
`mapTensorIdLinear`, leaving the second tensor factor untouched. -/
theorem mapTensorIdLinear_left_conj_of_conj {a b k : ℕ}
    [NeZero a] [NeZero b] [NeZero k]
    (Φ : Op a →ₗ[ℂ] Op b)
    (U : Op a) (V : Op b)
    (hΦ : ∀ X : Op a, Φ (U * X * Uᴴ) = V * Φ X * Vᴴ)
    (X : Op (a * k)) :
    mapTensorIdLinear Φ
        (Op.tensor U (1 : Op k) * X * (Op.tensor U (1 : Op k))ᴴ) =
      Op.tensor V (1 : Op k) * mapTensorIdLinear Φ X *
        (Op.tensor V (1 : Op k))ᴴ := by
  ext p q
  change mapTensorId Φ
      (Op.tensor U (1 : Op k) * X * (Op.tensor U (1 : Op k))ᴴ) p q =
    (Op.tensor V (1 : Op k) * mapTensorId Φ X *
      (Op.tensor V (1 : Op k))ᴴ) p q
  rw [Op.tensor_conjTranspose, conjTranspose_one]
  rw [mapTensorId_apply_eq_apply_block]
  rw [tensor_sandwich_block U Uᴴ X]
  rw [hΦ]
  rw [Op.tensor_conjTranspose, conjTranspose_one]
  rw [tensor_sandwich_apply_eq_block V Vᴴ (mapTensorId Φ X) p q]
  simp only [finProdFinEquiv_symm_apply, mapTensorId_apply_eq_apply_block,
    finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]
  congr 1

/-- Trace-norm invariance under permutation covariance. -/
lemma traceNorm_mapTensorId_perm_invariant {d n dimOut : ℕ}
    [NeZero d] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ_cov : ∀ (π : Equiv.Perm (Fin n)),
      ∃ (K_π : Op dimOut → Op dimOut), IsCPTP K_π ∧
        ∀ (ρ : Op (d ^ n)),
          Δ (permutationRepresentation d n π * ρ *
            (permutationRepresentation d n π)ᴴ) = K_π (Δ ρ))
    (π : Equiv.Perm (Fin n))
    (ρ : Op (d ^ n * (d ^ n))) :
    traceNorm (mapTensorId Δ (Op.tensor (permutationRepresentation d n π) (1 : Op (d ^ n)) * ρ *
      (Op.tensor (permutationRepresentation d n π) (1 : Op (d ^ n)))ᴴ)) =
    traceNorm (mapTensorId Δ ρ) := by
  obtain ⟨K, hK_cptp, hK_cov⟩ := hΔ_cov π
  obtain ⟨K', hK'_cptp, hK'_cov⟩ := hΔ_cov π⁻¹
  set K_lin := IsLinearMap.mk' K hK_cptp.1
  rw [mapTensorId_perm_sandwich_eq_comp Δ π K hK_cptp.1 hK_cov ρ]
  set K'_lin := IsLinearMap.mk' K' hK'_cptp.1
  set Y := mapTensorId Δ ρ with hY_def
  have h_fwd : traceNorm (mapTensorId K_lin Y) ≤ traceNorm Y :=
    traceNorm_mapTensorId_cptp_contractive K_lin hK_cptp Y
  set P := permutationRepresentation d n π with hP_def
  set P' := permutationRepresentation d n π⁻¹ with hP'_def
  have hP'_eq : P' = Pᴴ := by
    rw [hP'_def, hP_def, permutationRepresentation_inv]
  have hPu := (permutationRepresentation_unitary d n π).1
  have h_sandwich_cancel :
      Op.tensor P' 1 * (Op.tensor P 1 * ρ * (Op.tensor P 1)ᴴ) * (Op.tensor P' 1)ᴴ = ρ := by
    rw [hP'_eq]
    simp only [Op.tensor_conjTranspose, conjTranspose_conjTranspose, conjTranspose_one]
    simp only [Matrix.mul_assoc]
    rw [Op.tensor_mul, mul_one, hPu, Op.tensor_one, mul_one]
    rw [← Matrix.mul_assoc, Op.tensor_mul, mul_one, hPu, Op.tensor_one, one_mul]
  have h_inv_eq := mapTensorId_perm_sandwich_eq_comp Δ π⁻¹ K' hK'_cptp.1 hK'_cov
    (Op.tensor P 1 * ρ * (Op.tensor P 1)ᴴ)
  rw [h_sandwich_cancel] at h_inv_eq
  have h_fwd_eq := mapTensorId_perm_sandwich_eq_comp Δ π K hK_cptp.1 hK_cov ρ
  rw [h_fwd_eq] at h_inv_eq
  rw [← hY_def] at h_inv_eq
  have h_bwd : traceNorm Y ≤ traceNorm (mapTensorId K_lin Y) := by
    have h1 := traceNorm_mapTensorId_cptp_contractive K'_lin hK'_cptp (mapTensorId K_lin Y)
    rw [← h_inv_eq] at h1
    exact h1
  exact le_antisymm h_fwd h_bwd

/-- Construct a `DensityOp` from a PSD operator with positive trace. -/
lemma densityOp_of_psd_pos_trace {m : ℕ}
    (A : Op m)
    (hA_psd : A.PosSemidef)
    (hA_trace_pos : (0 : ℝ) < A.trace.re) :
    ∃ (σ : DensityOp m), σ.toOp = (1 / A.trace) • A := by
  have hA_herm : A.IsHermitian := hA_psd.isHermitian
  have h_trace_sa : IsSelfAdjoint A.trace := isSelfAdjoint_trace_of_isHermitian hA_herm
  have h_c_sa : IsSelfAdjoint (1 / A.trace) :=
    IsSelfAdjoint.div (.one ℂ) h_trace_sa
  have h_trace_ne_zero : A.trace ≠ 0 := by
    intro h
    rw [h] at hA_trace_pos
    simp at hA_trace_pos
  exact ⟨{
    toOp := (1 / A.trace) • A
    isHermitian := (h_c_sa.smul hA_herm.isSelfAdjoint).isHermitian
    pos_semidef := by
      intro x
      apply InfoTheory.DeFinetti.quadraticForm_re_nonneg_of_nonnegReal_smul _ _ _ hA_psd
      · rw [one_div, Complex.inv_re]
        exact div_nonneg hA_trace_pos.le (Complex.normSq_nonneg _)
      · rw [one_div, Complex.inv_im, Complex.conj_eq_iff_im.mp h_trace_sa]
        ring
    trace_one := by
      rw [Matrix.trace_smul, smul_eq_mul, one_div]
      exact inv_mul_cancel₀ h_trace_ne_zero
  }, rfl⟩

/-- The generic block-diagonal permutation extension. -/
noncomputable def blockDiagExt {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : Op (d ^ n * d ^ n)) :
    Op (d ^ n * (d ^ n * Fintype.card (Equiv.Perm (Fin n)))) :=
  let k := Fintype.card (Equiv.Perm (Fin n))
  let c : ℂ := 1 / (k : ℂ)
  let e := (Fintype.equivFin (Equiv.Perm (Fin n))).symm
  Matrix.of fun α β =>
    let p := finProdFinEquiv.symm α
    let ps := finProdFinEquiv.symm p.2
    let q := finProdFinEquiv.symm β
    let qs := finProdFinEquiv.symm q.2
    if ps.2 = qs.2 then
      let P := permutationRepresentation d n (e ps.2)
      c * (Op.tensor P (1 : Op (d ^ n)) * ρ *
           (Op.tensor P (1 : Op (d ^ n)))ᴴ)
        (finProdFinEquiv (p.1, ps.1)) (finProdFinEquiv (q.1, qs.1))
    else 0

/-- The permutation block-diagonal extension `blockDiagExt` is the unitary-family
extension (`UnitaryFamilyReduction.lean`) at the permutation representation, indexed
through `Fintype.equivFin`. -/
lemma blockDiagExt_eq_blockDiagExtFamily {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : Op (d ^ n * d ^ n)) :
    blockDiagExt ρ =
      blockDiagExtFamily
        (fun i : Fin (Fintype.card (Equiv.Perm (Fin n))) =>
          Math.RepresentationTheory.permutationRepresentation d n
            ((Fintype.equivFin (Equiv.Perm (Fin n))).symm i)) ρ := by
  have : NeZero (Fintype.card (Equiv.Perm (Fin n))) :=
    ⟨by simp [Fintype.card_perm, Nat.factorial_ne_zero]⟩
  rfl

/-- The block-diagonal extension is PSD. -/
lemma blockDiagExt_posSemidef {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : Op (d ^ n * d ^ n)) (hρ_psd : ρ.PosSemidef) :
    (blockDiagExt ρ).PosSemidef := by
  have : NeZero (Fintype.card (Equiv.Perm (Fin n))) :=
    ⟨by simp [Fintype.card_perm, Nat.factorial_ne_zero]⟩
  rw [blockDiagExt_eq_blockDiagExtFamily]
  exact blockDiagExtFamily_posSemidef _ ρ hρ_psd

/-- Applying `mapTensorId` to the block-diagonal extension keeps the permutation
blocks diagonal in the added classical register. -/
lemma mapTensorId_blockDiagExt_eq_blockDiagonal {d n dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (ρ : Op (d ^ n * d ^ n)) :
    let k := Fintype.card (Equiv.Perm (Fin n))
    let c : ℂ := 1 / (k : ℂ)
    let e_perm := (Fintype.equivFin (Equiv.Perm (Fin n))).symm
    let M := fun i : Fin k => mapTensorId Δ
      (c • (Op.tensor (permutationRepresentation d n (e_perm i))
        (1 : Op (d ^ n)) * ρ *
        (Op.tensor (permutationRepresentation d n (e_perm i)) (1 : Op (d ^ n)))ᴴ))
    mapTensorId Δ (blockDiagExt ρ) =
      (Matrix.blockDiagonal M).submatrix
        (finProdFinEquiv_assoc_right dimOut (d ^ n) k)
        (finProdFinEquiv_assoc_right dimOut (d ^ n) k) := by
  have : NeZero (Fintype.card (Equiv.Perm (Fin n))) :=
    ⟨by simp [Fintype.card_perm, Nat.factorial_ne_zero]⟩
  dsimp only
  rw [blockDiagExt_eq_blockDiagExtFamily]
  exact mapTensorId_blockDiagExtFamily_eq_blockDiagonal Δ
    (fun i : Fin (Fintype.card (Equiv.Perm (Fin n))) =>
      permutationRepresentation d n ((Fintype.equivFin (Equiv.Perm (Fin n))).symm i)) ρ

/-- Trace norm equality for the block-diagonal permutation extension, derived from the
unitary-family version via `blockDiagExt_eq_blockDiagExtFamily`. -/
lemma blockDiagExt_traceNorm_mapTensorId {d n dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ_cov : ∀ (π : Equiv.Perm (Fin n)),
      ∃ (K_π : Op dimOut → Op dimOut), IsCPTP K_π ∧
        ∀ (ρ : Op (d ^ n)),
          Δ (permutationRepresentation d n π * ρ *
            (permutationRepresentation d n π)ᴴ) = K_π (Δ ρ))
    (ρ : Op (d ^ n * d ^ n)) :
    traceNorm (mapTensorId Δ (blockDiagExt ρ)) =
    traceNorm (mapTensorId Δ ρ) := by
  have : NeZero (Fintype.card (Equiv.Perm (Fin n))) :=
    ⟨by simp [Fintype.card_perm, Nat.factorial_ne_zero]⟩
  rw [blockDiagExt_eq_blockDiagExtFamily]
  refine blockDiagExtFamily_traceNorm_mapTensorId Δ
    (fun i : Fin (Fintype.card (Equiv.Perm (Fin n))) =>
      permutationRepresentation d n ((Fintype.equivFin (Equiv.Perm (Fin n))).symm i)) ?_ ?_ ρ
  · intro i
    exact permutationRepresentation_unitary d n _
  · intro i
    obtain ⟨K, hK_cptp, hK_cov⟩ := hΔ_cov _
    obtain ⟨K', hK'_cptp, hK'_cov⟩ := hΔ_cov _⁻¹
    refine ⟨K, K', hK_cptp, hK'_cptp, hK_cov, ?_⟩
    -- the inverse-permutation covariance is exactly the adjoint-direction covariance
    rw [permutationRepresentation_inv] at hK'_cov
    intro σ
    simpa using hK'_cov σ

/-- Partial trace of the block-diagonal extension, derived from the unitary-family
version via `blockDiagExt_eq_blockDiagExtFamily` (sum reindexed to `Equiv.Perm`). -/
lemma partialTraceB_blockDiagExt_eq_avg {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : Op (d ^ n * d ^ n)) :
    partialTraceB (blockDiagExt ρ) =
    (1 / (Fintype.card (Equiv.Perm (Fin n)) : ℂ)) •
    ∑ π : Equiv.Perm (Fin n),
      permutationRepresentation d n π * partialTraceB ρ *
      (permutationRepresentation d n π)ᴴ := by
  have : NeZero (Fintype.card (Equiv.Perm (Fin n))) :=
    ⟨by simp [Fintype.card_perm, Nat.factorial_ne_zero]⟩
  rw [blockDiagExt_eq_blockDiagExtFamily]
  rw [partialTraceB_blockDiagExtFamily_eq_avg
    (fun i : Fin (Fintype.card (Equiv.Perm (Fin n))) =>
      permutationRepresentation d n ((Fintype.equivFin (Equiv.Perm (Fin n))).symm i)) ρ]
  congr 1
  exact Equiv.sum_comp ((Fintype.equivFin (Equiv.Perm (Fin n))).symm)
    (fun σ => permutationRepresentation d n σ * partialTraceB ρ *
      (permutationRepresentation d n σ)ᴴ)

/-- Partial trace of the block-diagonal extension equals the symmetrized marginal. -/
lemma blockDiagExt_partialTraceB {d n : ℕ} [NeZero d] [NeZero n]
    (ρ : Op (d ^ n * d ^ n))
    (hρ_psd : ρ.PosSemidef)
    (hρ_nz : ρ ≠ 0)
    (σ_A : DensityOp (d ^ n))
    (hσ_A : σ_A.toOp = (1 / ρ.trace) • partialTraceB ρ) :
    partialTraceB (blockDiagExt ρ) =
    ρ.trace • (Quantum.Symmetry.symmetrize σ_A).toOp := by
  rw [partialTraceB_blockDiagExt_eq_avg]
  have h_trace_nz : ρ.trace ≠ 0 := by
    intro h
    exact hρ_nz (hρ_psd.trace_eq_zero_iff.mp h)
  have h_ptB : partialTraceB ρ = ρ.trace • σ_A.toOp := by
    rw [hσ_A, smul_smul, mul_div_cancel₀ _ h_trace_nz, one_smul]
  rw [h_ptB]
  have h_factor : ∀ (π : Equiv.Perm (Fin n)),
      permutationRepresentation d n π * (ρ.trace • σ_A.toOp) *
      (permutationRepresentation d n π)ᴴ =
      ρ.trace • (permutationRepresentation d n π * σ_A.toOp *
      (permutationRepresentation d n π)ᴴ) := by
    intro π
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [show (∑ π : Equiv.Perm (Fin n),
      permutationRepresentation d n π * (ρ.trace • σ_A.toOp) *
      (permutationRepresentation d n π)ᴴ) =
    ∑ π, ρ.trace • (permutationRepresentation d n π * σ_A.toOp *
      (permutationRepresentation d n π)ᴴ)
    from Finset.sum_congr rfl (fun π _ => h_factor π)]
  rw [← Finset.smul_sum, smul_comm]
  congr 1
  congr 1
  congr 1
  simp [Fintype.card_perm, Fintype.card_fin]

/-- Existence of a block-diagonal extension with the required marginal domination. -/
lemma block_diag_extension_exists {d n dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ_cov : ∀ (π : Equiv.Perm (Fin n)),
      ∃ (K_π : Op dimOut → Op dimOut), IsCPTP K_π ∧
        ∀ (ρ : Op (d ^ n)),
          Δ (permutationRepresentation d n π * ρ *
            (permutationRepresentation d n π)ᴴ) = K_π (Δ ρ))
    (ρ : Op (d ^ n * d ^ n))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1)
    (hρ_nz : ρ ≠ 0)
    (σ_A : DensityOp (d ^ n))
    (hσ_A : σ_A.toOp = (1 / ρ.trace) • partialTraceB ρ)
    (Ψ : DensityOp (d ^ n * d ^ n))
    (hΨ_marginal : partialTraceB Ψ.toOp = (Quantum.Symmetry.symmetrize σ_A).toOp) :
    ∃ (dimK : ℕ) (_ : NeZero dimK) (ρ_ext : Op (d ^ n * dimK)),
        ρ_ext.PosSemidef ∧
        traceNorm (mapTensorId Δ ρ_ext) = traceNorm (mapTensorId Δ ρ) ∧
        ((1 : ℂ) • Ψ.partialTraceB.toOp - partialTraceB ρ_ext).PosSemidef := by
  set k := Fintype.card (Equiv.Perm (Fin n)) with hk_def
  have hk_ne : NeZero k := ⟨by
    simp only [hk_def, Fintype.card_perm, Fintype.card_fin]
    exact (Nat.factorial_pos n).ne'⟩
  refine ⟨d ^ n * k, inferInstance, blockDiagExt ρ,
    blockDiagExt_posSemidef ρ hρ_psd,
    blockDiagExt_traceNorm_mapTensorId Δ hΔ_cov ρ, ?_⟩
  rw [blockDiagExt_partialTraceB ρ hρ_psd hρ_nz σ_A hσ_A]
  have h_marginal_eq : Ψ.partialTraceB.toOp = (Quantum.Symmetry.symmetrize σ_A).toOp := by
    change partialTraceB Ψ.toOp = _
    exact hΨ_marginal
  rw [h_marginal_eq, one_smul]
  rw [show (Quantum.Symmetry.symmetrize σ_A).toOp -
      ρ.trace • (Quantum.Symmetry.symmetrize σ_A).toOp =
      (1 - ρ.trace) • (Quantum.Symmetry.symmetrize σ_A).toOp from by
    rw [sub_smul, one_smul]]
  apply posSemidef_smul_of_nonneg_re
  · exact posSemidefOp_implies_mathlib (Quantum.Symmetry.symmetrize σ_A).toPosSemidefOp
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
  · simp only [Complex.sub_im, Complex.one_im, zero_sub]
    have h_sa : IsSelfAdjoint ρ.trace := isSelfAdjoint_trace_of_isHermitian hρ_psd.isHermitian
    rw [Complex.conj_eq_iff_im.mp h_sa]
    ring

/-- The generic block-diagonal averaging plus purification bound. -/
lemma block_diagonal_purification_bound {d n dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ_cov : ∀ (π : Equiv.Perm (Fin n)),
      ∃ (K_π : Op dimOut → Op dimOut), IsCPTP K_π ∧
        ∀ (ρ : Op (d ^ n)),
          Δ (permutationRepresentation d n π * ρ *
            (permutationRepresentation d n π)ᴴ) = K_π (Δ ρ))
    (ρ : Op (d ^ n * d ^ n))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1)
    (hρ_nz : ρ ≠ 0)
    (σ_norm : DensityOp (d ^ n))
    (hσ_norm : σ_norm.toOp = (1 / ρ.trace) • partialTraceB ρ)
    (Ψ : DensityOp (d ^ n * d ^ n))
    (hΨ_pure : Ψ.IsPure)
    (hΨ_marginal : partialTraceB Ψ.toOp = (Quantum.Symmetry.symmetrize σ_norm).toOp) :
    traceNorm (mapTensorId Δ ρ) ≤ traceNorm (mapTensorId Δ Ψ.toOp) := by
  obtain ⟨dimK, hNZ_K, ρ_ext, hρ_ext_psd, h_traceNorm_eq, h_marginal_dom⟩ :=
    block_diag_extension_exists Δ hΔ_cov ρ hρ_psd hρ_trace hρ_nz
      σ_norm hσ_norm Ψ hΨ_marginal
  have h_dom' : ((↑(1 : ℝ) : ℂ) • Ψ.partialTraceB.toOp - partialTraceB ρ_ext).PosSemidef := by
    rw [Complex.ofReal_one]
    exact h_marginal_dom
  have h_bound := traceNorm_mapTensorId_substate_bound Δ
    ρ_ext hρ_ext_psd Ψ hΨ_pure 1 one_pos h_dom'
  rw [h_traceNorm_eq] at h_bound
  linarith

/-!
## Structural facts about the combined `blockDiagExt`/Bell-registered marginal

These three helpers are channel-independent (no reference to any BB84-specific channel), so they
are shared by every consumer of the `blockDiagExt`/Bell-twirl postselection engine rather than
re-derived locally.
-/

/-- Conjugation invariance upgrades to commutation, via unitarity of the permutation
representation: for a permutation representation `U_σ` and any `A` fixed by conjugation
(`U_σ · A · U_σ† = A`), `A` in fact commutes with `U_σ`. -/
theorem perm_commute_of_conjInvariant (n : ℕ) [NeZero n] (σ : Equiv.Perm (Fin n))
    (A : Op (4 ^ n))
    (h : permutationRepresentation 4 n σ * A * (permutationRepresentation 4 n σ)ᴴ = A) :
    permutationRepresentation 4 n σ * A = A * permutationRepresentation 4 n σ := by
  have hu : (permutationRepresentation 4 n σ)ᴴ * permutationRepresentation 4 n σ = 1 :=
    (permutationRepresentation_unitary 4 n σ).1
  calc permutationRepresentation 4 n σ * A
         = permutationRepresentation 4 n σ * A *
          ((permutationRepresentation 4 n σ)ᴴ * permutationRepresentation 4 n σ) := by
        rw [hu, Matrix.mul_one]
    _ = (permutationRepresentation 4 n σ * A * (permutationRepresentation 4 n σ)ᴴ) *
          permutationRepresentation 4 n σ := by
        rw [← Matrix.mul_assoc]
    _ = A * permutationRepresentation 4 n σ := by rw [h]

/-- The perm-symmetrized `blockDiagExt` marginal is invariant under permutation conjugation
(the symmetrization average is a permutation fixed point). -/
theorem blockDiagExt_marginal_permConjInvariant (n : ℕ) [NeZero n]
    (W0 : Op (4 ^ n * 4 ^ n)) (σ : Equiv.Perm (Fin n)) :
    permutationRepresentation 4 n σ * partialTraceB (Quantum.Channels.blockDiagExt W0) *
        (permutationRepresentation 4 n σ)ᴴ =
      partialTraceB (Quantum.Channels.blockDiagExt W0) := by
  rw [partialTraceB_blockDiagExt_eq_avg, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul]
  have hterm : ∀ π : Equiv.Perm (Fin n),
      permutationRepresentation 4 n σ *
          (permutationRepresentation 4 n π * partialTraceB W0 *
            (permutationRepresentation 4 n π)ᴴ) * (permutationRepresentation 4 n σ)ᴴ =
        permutationRepresentation 4 n (σ * π) * partialTraceB W0 *
          (permutationRepresentation 4 n (σ * π))ᴴ := by
    intro π
    rw [← permutationRepresentation_mul 4 n σ π, Matrix.conjTranspose_mul]
    noncomm_ring
  rw [Finset.sum_congr rfl (fun π _ => hterm π)]
  exact Equiv.sum_comp (Equiv.mulLeft σ)
    (fun τ => permutationRepresentation 4 n τ * partialTraceB W0 *
      (permutationRepresentation 4 n τ)ᴴ)

/-- The perm-symmetrized `blockDiagExt` marginal preserves the trace of the input operator. -/
theorem blockDiagExt_marginal_trace (n : ℕ) [NeZero n] (W0 : Op (4 ^ n * 4 ^ n)) :
    (partialTraceB (Quantum.Channels.blockDiagExt W0)).trace = W0.trace := by
  rw [partialTraceB_blockDiagExt_eq_avg, Matrix.trace_smul, Matrix.trace_sum]
  have hterm : ∀ π : Equiv.Perm (Fin n),
      (permutationRepresentation 4 n π * partialTraceB W0 *
        (permutationRepresentation 4 n π)ᴴ).trace = (partialTraceB W0).trace := by
    intro π
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, (permutationRepresentation_unitary 4 n π).1,
      Matrix.one_mul]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    smul_eq_mul, ← mul_assoc, one_div,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_mul, trace_partialTraceB]

end Quantum.Channels
