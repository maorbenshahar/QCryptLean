import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.Channels.CPTP.CKRBound.MapTensorIdAncilla
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import QCryptLean.Quantum.Metrics.WatrousFactorization

/-!
# Kitaev-Watrous Contraction Support — polar decomposition, ancilla absorption, Holder bounds

Support lemmas for the non-Hermitian step in the square-ancilla
Kitaev-Watrous theorem. This file isolates the polar-decomposition,
ancilla-commutation, and Holder-norm estimates used by `KitaevWatrous.lean`.

## Main definitions
- `kw_polar_decomposition`: polar decomposition wrapper with PSD trace control

## Main statements
- `kw_mapTensorId_left_ancilla_mul`: `(Φ ⊗ id)` commutes with left ancilla factors
- `kw_mapTensorId_right_ancilla_mul`: `(Φ ⊗ id)` commutes with right ancilla factors
- `opNorm_tensor_one_le`: `‖I ⊗ A‖ ≤ ‖A‖`
- `kw_contraction_absorption_calc`: two-sided Holder estimate for absorbed ancilla factors
- `kw_left_ancilla_absorption`: one-sided Holder estimate for absorbed ancilla factors
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics.KitaevWatrousContraction

/-- Polar decomposition for the Kitaev-Watrous reduction, obtained from the
shared Watrous factorization infrastructure by discarding the contraction bound. -/
lemma kw_polar_decomposition {d : ℕ} [NeZero d] (X : Op d) :
    ∃ (V P : Op d), P.PosSemidef ∧ X = V * P ∧
      P.trace.re = traceNorm X := by
  obtain ⟨V, P, hP_psd, hVP, hP_trace, _hV_norm⟩ :=
    WatrousFactorization.polar_decomposition_norm X
  exact ⟨V, P, hP_psd, hVP, hP_trace⟩

-- The four lemmas `single_eq_tensor`, `single_eq_tensor_symm`,
-- `kw_mapTensorId_left_ancilla_mul`, `kw_mapTensorId_right_ancilla_mul` are declared, in this
-- namespace, in `Quantum/Channels/CPTP/CKRBound/MapTensorIdAncilla.lean`.

section HolderNorm

open scoped Matrix.Norms.L2Operator

/-- Tensor with identity sends diagonal to diagonal. -/
private lemma tensor_one_diagonal {d k : ℕ} (v : Fin k → ℂ) :
    Op.tensor (1 : Op d) (diagonal v) =
      diagonal (fun i => v (finProdFinEquiv.symm i).2) := by
  ext i j
  simp only [Op.tensor, reindex_apply, submatrix_apply, kroneckerMap_apply,
    one_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : finProdFinEquiv.symm i ≠ finProdFinEquiv.symm j :=
      fun h => hij (finProdFinEquiv.symm.injective h)
    simp only [hij, ↓reduceIte]
    cases Decidable.em ((finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1) with
    | inl h1 =>
      have h2 : (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 :=
        fun h2 => hne (Prod.ext h1 h2)
      simp only [h1, ↓reduceIte, h2, mul_zero]
    | inr h1 =>
      simp only [h1, ↓reduceIte, zero_mul]

/-- `Op.tensor 1 (diagonal v)` has the same L2 operator norm as `diagonal v`. -/
private lemma opNorm_tensor_one_diagonal {d k : ℕ} [NeZero d] [NeZero k]
    (v : Fin k → ℂ) :
    ‖Op.tensor (1 : Op d) (diagonal v)‖ = ‖diagonal v‖ := by
  rw [tensor_one_diagonal, Matrix.l2_opNorm_diagonal, Matrix.l2_opNorm_diagonal]
  simp only [Pi.norm_def, NNReal.coe_inj]
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    exact Finset.le_sup (f := fun j => ‖v j‖₊) (Finset.mem_univ _)
  · apply Finset.sup_le
    intro j _
    have : ∃ i : Fin (d * k), (finProdFinEquiv.symm i).2 = j := by
      exact ⟨finProdFinEquiv (⟨0, NeZero.pos d⟩, j), by simp⟩
    obtain ⟨i, hi⟩ := this
    rw [← hi]
    exact Finset.le_sup (f := fun i => ‖v (finProdFinEquiv.symm i).2‖₊) (Finset.mem_univ _)

/-- Unitary matrices have L2 operator norm `1`. -/
private lemma opNorm_unitary_eq_one {n : ℕ} [NeZero n]
    (U : Op n) (hU : U.conjTranspose * U = 1) : ‖U‖ = 1 := by
  have h1 : ‖U‖ * ‖U‖ = 1 * 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hU, norm_one, one_mul]
  exact (mul_self_inj (norm_nonneg U) zero_le_one).1 h1

private lemma opNorm_tensor_one_unitary_eq_one {d k : ℕ} [NeZero d] [NeZero k]
    (U : Op k) (hU : U.conjTranspose * U = 1) :
    ‖Op.tensor (1 : Op d) U‖ = 1 := by
  apply opNorm_unitary_eq_one
  rw [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, one_mul, hU, Op.tensor_one]

/-- Operator norm of tensor with identity on the left. -/
lemma opNorm_tensor_one_le {d k : ℕ} [NeZero d] [NeZero k]
    (A : Op k) :
    ‖Op.tensor (1 : Op d) A‖ ≤ ‖A‖ := by
  -- Both norms are nonnegative, so it suffices to compare `‖X‖ * ‖X‖ = ‖Xᴴ * X‖`;
  -- this turns the goal into `‖1 ⊗ B‖ ≤ ‖B‖` for the Hermitian `B = Aᴴ * A`.
  refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 ?_
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self,
    ← Matrix.l2_opNorm_conjTranspose_mul_self,
    Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, one_mul]
  set B := A.conjTranspose * A
  have hBH : B.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  -- Spectral decomposition `B = U * D * star U` with `U` unitary and `D` diagonal.
  set U : Op k := hBH.eigenvectorUnitary.val
  set D : Op k := diagonal (RCLike.ofReal ∘ hBH.eigenvalues)
  have hB_spec : B = U * D * star U := hBH.spectral_theorem
  have hUstarU : star U * U = 1 :=
    Matrix.UnitaryGroup.star_mul_self hBH.eigenvectorUnitary
  have hUctU : U.conjTranspose * U = 1 := hUstarU
  have hU_norm : ‖U‖ = 1 := opNorm_unitary_eq_one _ hUctU
  have hU_star_norm : ‖star U‖ = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose, hU_norm]
  -- `D = star U * B * U`, so `‖D‖ ≤ ‖B‖`.
  have hD_eq : D = star U * B * U := by
    rw [hB_spec, Matrix.mul_assoc, Matrix.mul_assoc, hUstarU, Matrix.mul_one,
      ← Matrix.mul_assoc, hUstarU, Matrix.one_mul]
  -- Tensoring with `1` preserves the factorization, the unitary `1 ⊗ U` and `‖D‖`.
  have h_factor : Op.tensor (1 : Op d) B =
      Op.tensor 1 U * Op.tensor 1 D * star (Op.tensor 1 U) := by
    rw [Matrix.star_eq_conjTranspose, Op.tensor_conjTranspose, conjTranspose_one,
      Op.tensor_mul, Op.tensor_mul, one_mul, one_mul, ← Matrix.star_eq_conjTranspose,
      ← hB_spec]
  have hTU_norm : ‖Op.tensor (1 : Op d) U‖ = 1 :=
    opNorm_tensor_one_unitary_eq_one _ hUctU
  have hTU_star_norm : ‖star (Op.tensor (1 : Op d) U)‖ = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose, hTU_norm]
  have hD_norm : ‖Op.tensor (1 : Op d) D‖ = ‖D‖ :=
    opNorm_tensor_one_diagonal _
  calc ‖Op.tensor (1 : Op d) B‖
      = ‖Op.tensor 1 U * Op.tensor 1 D * star (Op.tensor 1 U)‖ := by rw [h_factor]
    _ ≤ ‖Op.tensor 1 U‖ * ‖Op.tensor 1 D‖ * ‖star (Op.tensor 1 U)‖ := norm_mul₃_le
    _ = ‖D‖ := by rw [hTU_norm, hD_norm, hTU_star_norm, one_mul, mul_one]
    _ = ‖star U * B * U‖ := by rw [← hD_eq]
    _ ≤ ‖star U‖ * ‖B‖ * ‖U‖ := norm_mul₃_le
    _ = ‖B‖ := by rw [hU_star_norm, hU_norm, one_mul, mul_one]

end HolderNorm

open scoped Matrix.Norms.L2Operator

private lemma traceNorm_nonneg {d : ℕ} [NeZero d] (X : Op d) :
    0 ≤ traceNorm X := by
  unfold traceNorm
  exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)

/-- Holder chain for the absorbed ancilla factors. -/
lemma kw_contraction_absorption_calc {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ) (hB : 0 ≤ B)
    (hPSD : ∀ (ρ : Op (n * n)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (A₀ B₀ : Op n) (σ : Op (n * n))
    (hσ_psd : σ.PosSemidef) (hσ_tr : σ.trace.re ≤ 1)
    (hA₀ : ‖A₀‖ ≤ 1) (hB₀ : ‖B₀‖ ≤ 1) :
    traceNorm (Op.tensor (1 : Op m) A₀ * mapTensorId Φ σ * Op.tensor (1 : Op m) B₀) ≤ B := by
  have h_right : traceNorm (Op.tensor (1 : Op m) A₀ * mapTensorId Φ σ *
      Op.tensor (1 : Op m) B₀) ≤
    traceNorm (Op.tensor (1 : Op m) A₀ * mapTensorId Φ σ) *
      ‖Op.tensor (1 : Op m) B₀‖ :=
    TraceNormHoelder.traceNorm_mul_le_traceNorm_mul_opNorm _ _
  have h_left : traceNorm (Op.tensor (1 : Op m) A₀ * mapTensorId Φ σ) ≤
    ‖Op.tensor (1 : Op m) A₀‖ * traceNorm (mapTensorId Φ σ) :=
    TraceNormHoelder.traceNorm_mul_le_opNorm_mul_traceNorm _ _
  have hA₀' : ‖Op.tensor (1 : Op m) A₀‖ ≤ ‖A₀‖ := opNorm_tensor_one_le A₀
  have hB₀' : ‖Op.tensor (1 : Op m) B₀‖ ≤ ‖B₀‖ := opNorm_tensor_one_le B₀
  have hσ_bound : traceNorm (mapTensorId Φ σ) ≤ B := hPSD σ hσ_psd hσ_tr
  have htn_nn : 0 ≤ traceNorm (mapTensorId Φ σ) := traceNorm_nonneg _
  calc traceNorm (Op.tensor (1 : Op m) A₀ * mapTensorId Φ σ * Op.tensor (1 : Op m) B₀)
      ≤ traceNorm (Op.tensor (1 : Op m) A₀ * mapTensorId Φ σ) *
          ‖Op.tensor (1 : Op m) B₀‖ := h_right
    _ ≤ (‖Op.tensor (1 : Op m) A₀‖ * traceNorm (mapTensorId Φ σ)) *
          ‖Op.tensor (1 : Op m) B₀‖ := by
        apply mul_le_mul_of_nonneg_right h_left (norm_nonneg _)
    _ ≤ (‖A₀‖ * traceNorm (mapTensorId Φ σ)) * ‖B₀‖ := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hA₀' htn_nn) hB₀'
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) htn_nn)
    _ ≤ (1 * B) * 1 := by
        apply mul_le_mul (mul_le_mul hA₀ hσ_bound htn_nn (by linarith))
          hB₀ (norm_nonneg _) (mul_nonneg (by linarith) hB)
    _ = B := by ring

/-- Left ancilla multiplication by a contraction preserves the PSD KW bound. -/
lemma kw_left_ancilla_absorption {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ)
    (hPSD : ∀ (ρ : Op (n * n)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (A₀ : Op n) (σ : Op (n * n))
    (hσ_psd : σ.PosSemidef) (hσ_tr : σ.trace.re ≤ 1)
    (hA₀ : ‖A₀‖ ≤ 1) :
    traceNorm (Op.tensor (1 : Op m) A₀ * mapTensorId Φ σ) ≤ B := by
  have hB : 0 ≤ B := by
    have h0 := hPSD (0 : Op (n * n)) Matrix.PosSemidef.zero (by simp)
    simpa [mapTensorId_zero, traceNorm_zero] using h0
  simpa using kw_contraction_absorption_calc Φ B hB hPSD A₀ 1 σ hσ_psd hσ_tr hA₀
    (by simp)

end Quantum.Metrics.KitaevWatrousContraction
