import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.KLCoarsening
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.Basic.Basic

/-!
# Projective DPI — projector-adapted ONB, projective measurement data processing

Construction of a projector-adapted orthonormal basis via spectral decomposition
of H = ∑ y • P_y, and the projective measurement data processing inequality
(DPI) which bounds measurement KL divergence by quantum relative entropy.

## Main statements
- `projector_adapted_onb_exists`: ONB adapted to orthogonal projectors {P_y}
- `projective_measurement_dpi_of_ker_sub`: real-valued projective DPI from kernel containment
- `projective_measurement_dpi_with_support`: support-based wrapper around
`projective_measurement_dpi_of_ker_sub`
- `projective_measurement_dpi`:
  ENNReal wrapper around the totalized real projective KL expression

## Helper lemmas
- `unitary_column_ne_zero`: a column of a unitary matrix is nonzero
- `projector_mul_eigenvector_unitary_eq_zero_of_ne`:
  off-fiber columns are annihilated by each projector
- `trace_indicator_diagonal_mul`: indicator diagonals pick out filtered diagonal entries
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-- H = ∑ y, y • P_y is Hermitian when each P_y is Hermitian. -/
lemma projector_sum_isHermitian {N m : ℕ}
    (P : Fin m → Op N)
    (h_herm : ∀ y, (P y).conjTranspose = P y) :
    (∑ y : Fin m, (y.val : ℂ) • P y).IsHermitian := by
  apply isSelfAdjoint_sum
  intro y _
  apply IsSelfAdjoint.smul
  · change starRingEnd ℂ (↑↑y : ℂ) = ↑↑y
    simp
  · exact h_herm y

/-- H * P_y = y • P_y for orthogonal projectors. -/
lemma projector_sum_mul_right {N m : ℕ}
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (y : Fin m) :
    (∑ y' : Fin m, (y'.val : ℂ) • P y') * P y = (y.val : ℂ) • P y := by
  rw [Finset.sum_mul]
  rw [show ∑ y' : Fin m, (y'.val : ℂ) • P y' * P y =
    ∑ y' : Fin m, (y'.val : ℂ) • (P y' * P y) from by
    congr 1; ext1 y'; rw [smul_mul_assoc]]
  rw [Finset.sum_eq_single y]
  · rw [h_proj y]
  · intro y' _ hy'; rw [h_ortho y' y hy', smul_zero]
  · simp

/-- P_y * H = y • P_y for orthogonal projectors. -/
lemma projector_sum_mul_left {N m : ℕ}
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (y : Fin m) :
    P y * (∑ y' : Fin m, (y'.val : ℂ) • P y') = (y.val : ℂ) • P y := by
  rw [Finset.mul_sum]
  rw [show ∑ y' : Fin m, P y * ((y'.val : ℂ) • P y') =
    ∑ y' : Fin m, (y'.val : ℂ) • (P y * P y') from by
    congr 1; ext1 y'; rw [mul_smul_comm]]
  rw [Finset.sum_eq_single y]
  · rw [h_proj y]
  · intro y' _ hy'; rw [h_ortho y y' (Ne.symm hy'), smul_zero]
  · simp

/-- A column of a unitary matrix is nonzero. -/
lemma unitary_column_ne_zero {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (hU : star U * U = 1) (j : Fin N) :
    U.mulVec (Pi.single j 1) ≠ 0 := by
  intro h_eq
  have h1 : (star U * U) j j = 1 := by
    rw [hU]; exact Matrix.one_apply_eq j
  have h2 : (star U * U) j j = 0 := by
    simp only [Matrix.mul_apply, star_apply]
    apply Finset.sum_eq_zero; intro k _
    have hk : U k j = 0 := by
      have := congr_fun h_eq k
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply,
        Pi.zero_apply] at this
      rwa [Finset.sum_eq_single j
        (fun b _ hb => by simp only [if_neg hb, mul_zero])
        (fun habs => (habs (Finset.mem_univ _)).elim),
        if_pos rfl, mul_one] at this
    rw [hk, mul_zero]
  linarith

/-- Each eigenvalue of H = ∑ y • P_y is in {0, ..., m-1}.
    Proof: If Hv = λv, then (y - λ)P_y v = 0 for all y (from HP_y = yP_y).
    Since ∑ P_y = I, some P_y v ≠ 0, so λ = y.val. -/
lemma projector_sum_eigenvalue_in_fin {N m : ℕ} [NeZero N] [NeZero m]
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (h_complete : ∑ y, P y = 1)
    (hH : (∑ y : Fin m, (y.val : ℂ) • P y).IsHermitian)
    (j : Fin N) :
    ∃ y : Fin m, hH.eigenvalues j = (y.val : ℝ) := by
  have hPH : ∀ y, P y * (∑ y' : Fin m, (y'.val : ℂ) • P y') = (y.val : ℂ) • P y :=
    projector_sum_mul_left P h_proj h_ortho
  set U := (hH.eigenvectorUnitary.val : Op N)
  have hUstarU : star U * U = 1 :=
    Unitary.coe_star_mul_self hH.eigenvectorUnitary
  set v_j := U.mulVec (Pi.single j 1) with hv_def
  -- `v_j = U e_j` is the `j`-th eigenvector of `H`
  have h_eigvec : (∑ y : Fin m, (y.val : ℂ) • P y).mulVec v_j =
      (hH.eigenvalues j : ℂ) • v_j := by
    rw [hv_def, hH.eigenvectorUnitary_mulVec, hH.mulVec_eigenvectorBasis]
    exact RCLike.real_smul_eq_coe_smul _ _
  have h_key : ∀ y : Fin m,
      ((hH.eigenvalues j : ℂ) - (y.val : ℂ)) • (P y).mulVec v_j = 0 := by
    intro y
    have h1 : (P y).mulVec ((∑ y' : Fin m, (y'.val : ℂ) • P y').mulVec v_j) =
        (hH.eigenvalues j : ℂ) • (P y).mulVec v_j := by
      rw [h_eigvec, Matrix.mulVec_smul]
    have h2 : (P y).mulVec ((∑ y' : Fin m, (y'.val : ℂ) • P y').mulVec v_j) =
        (y.val : ℂ) • (P y).mulVec v_j := by
      rw [Matrix.mulVec_mulVec, hPH y, Matrix.smul_mulVec]
    rw [sub_smul, ← h1, h2, sub_self]
  have hv_ne : v_j ≠ 0 := unitary_column_ne_zero U hUstarU j
  have h_sum_v : ∑ y : Fin m, (P y).mulVec v_j = v_j := by
    rw [← Matrix.sum_mulVec, h_complete, Matrix.one_mulVec]
  by_contra h_none; push_neg at h_none
  exact hv_ne (by
    rw [← h_sum_v]
    exact Finset.sum_eq_zero fun y _ =>
      (smul_eq_zero.mp (h_key y)).resolve_left
        (sub_ne_zero.mpr (by exact_mod_cast fun h => h_none y h)))

/-- Columns of the eigenvector unitary outside the `y'`-eigenspace are annihilated by `P y'`. -/
lemma projector_mul_eigenvector_unitary_eq_zero_of_ne {N m : ℕ} [NeZero N] [NeZero m]
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (hH : (∑ y : Fin m, (y.val : ℂ) • P y).IsHermitian)
    (g : Fin N → Fin m)
    (hg : ∀ j, hH.eigenvalues j = ((g j).val : ℝ))
    {y' : Fin m} {j : Fin N} (hgj : g j ≠ y') :
    ∀ i : Fin N, (P y' * hH.eigenvectorUnitary.val) i j = 0 := by
  set U := (hH.eigenvectorUnitary.val : Op N)
  have h_spec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  have hHU : (∑ y' : Fin m, (y'.val : ℂ) • P y') * U =
      U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    have h1 := congr_arg (· * U) h_spec
    simp only [mul_assoc] at h1
    rw [show star U * U = 1 from Unitary.coe_star_mul_self hH.eigenvectorUnitary,
      mul_one] at h1
    exact h1
  intro i
  have h_B_diag : P y' * U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      (y'.val : ℂ) • (P y' * U) := by
    calc
      P y' * U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
          = P y' * (U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) := by
              rw [mul_assoc]
      _ = P y' * ((∑ y'' : Fin m, (y''.val : ℂ) • P y'') * U) := by
            rw [hHU]
      _ = (P y' * (∑ y'' : Fin m, (y''.val : ℂ) • P y'')) * U := by
            rw [mul_assoc]
      _ = ((y'.val : ℂ) • P y') * U := by
            rw [projector_sum_mul_left P h_proj h_ortho y']
      _ = (y'.val : ℂ) • (P y' * U) := by
            rw [smul_mul_assoc]
  have h_entry : (P y' * U) i j * (hH.eigenvalues j : ℂ) =
      (y'.val : ℂ) * (P y' * U) i j := by
    have h := congr_fun (congr_fun h_B_diag i) j
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, smul_apply, smul_eq_mul] at h
    rw [Finset.sum_eq_single j] at h
    · simpa using h
    · intro b _ hb
      rw [if_neg hb, mul_zero]
    · exact absurd (Finset.mem_univ j)
  have hne : (hH.eigenvalues j : ℂ) ≠ (y'.val : ℂ) := by
    rw [hg j]
    simp only [Complex.ofReal_natCast]
    exact_mod_cast Fin.val_ne_of_ne hgj
  have h2 : (P y' * U) i j * ((hH.eigenvalues j : ℂ) - (y'.val : ℂ)) = 0 := by
    rw [mul_sub, h_entry, mul_comm, sub_self]
  exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hne)

/-- Key identity: P_y * U = U * D_y where D_y is the indicator diagonal matrix.
    Proof: P_y * H = y * P_y combined with H * U = U * diag(λ) gives
    (P_y * U) * diag(λ) = y * (P_y * U). Entry-wise, this forces P_y * U
    to be zero in columns where eigenvalue ≠ y. Completeness ∑ P_y = I
    forces the remaining columns to equal those of U. -/
lemma projector_adapted_column_identity {N m : ℕ} [NeZero N] [NeZero m]
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (h_complete : ∑ y, P y = 1)
    (hH : (∑ y : Fin m, (y.val : ℂ) • P y).IsHermitian)
    (g : Fin N → Fin m)
    (hg : ∀ j, hH.eigenvalues j = ((g j).val : ℝ))
    (y : Fin m) :
    P y * hH.eigenvectorUnitary.val =
      hH.eigenvectorUnitary.val *
        Matrix.diagonal (fun j : Fin N => if g j = y then (1 : ℂ) else 0) := by
  set U := (hH.eigenvectorUnitary.val : Op N)
  have h_vanish_gen : ∀ (y' : Fin m) (j : Fin N), g j ≠ y' →
      ∀ (i : Fin N), (P y' * U) i j = 0 := by
    intro y' j hgj
    simpa [U] using projector_mul_eigenvector_unitary_eq_zero_of_ne P h_proj h_ortho hH g hg hgj
  have h_sum_eq : ∑ y' : Fin m, P y' * U = U := by
    rw [← Finset.sum_mul, h_complete, one_mul]
  have h_identity : ∀ j, g j = y → ∀ i, (P y * U) i j = U i j := by
    intro j hgj i
    have h_sum := congr_fun (congr_fun h_sum_eq i) j
    rw [Finset.sum_apply, Finset.sum_apply] at h_sum
    rw [Finset.sum_eq_single y] at h_sum
    · exact h_sum
    · intro y' _ hy'
      exact h_vanish_gen y' j (hgj ▸ hy'.symm) i
    · exact absurd (Finset.mem_univ y)
  apply Matrix.ext; intro i j
  have h_lhs : (P y * U) i j = if g j = y then U i j else 0 := by
    by_cases hgj : g j = y
    · rw [if_pos hgj, h_identity j hgj i]
    · rw [if_neg hgj, h_vanish_gen y j hgj i]
  have h_rhs : (U * Matrix.diagonal
      (fun j => if g j = y then (1 : ℂ) else 0)) i j =
      if g j = y then U i j else 0 := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · rw [Matrix.diagonal_apply, if_pos rfl]
      split_ifs <;> simp
    · intro b _ hb; rw [Matrix.diagonal_apply, if_neg hb, mul_zero]
    · exact absurd (Finset.mem_univ j)
  rw [h_lhs, h_rhs]

/-- Each projector is diagonal in the eigenbasis of `∑ y, y • P y`, with an indicator
diagonal selecting the columns labeled by `y`. -/
lemma projector_eq_eigenvector_unitary_mul_indicator_diagonal_mul_star
    {N m : ℕ} [NeZero N] [NeZero m]
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (h_complete : ∑ y, P y = 1)
    (hH : (∑ y : Fin m, (y.val : ℂ) • P y).IsHermitian)
    (g : Fin N → Fin m)
    (hg : ∀ j, hH.eigenvalues j = ((g j).val : ℝ))
    (y : Fin m) :
    P y = hH.eigenvectorUnitary.val *
      Matrix.diagonal (fun j : Fin N => if g j = y then (1 : ℂ) else 0) *
        star hH.eigenvectorUnitary.val := by
  set U := (hH.eigenvectorUnitary.val : Op N)
  have hUstarU : U * star U = 1 := by
    have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simp only [Unitary.coe_star] at h
    exact h
  have h_col := projector_adapted_column_identity P h_proj h_ortho h_complete hH g hg y
  have h1 : P y * (U * star U) =
      (U * Matrix.diagonal (fun j => if g j = y then (1 : ℂ) else 0)) * star U := by
    conv_lhs => rw [← mul_assoc, h_col]
  rw [hUstarU, mul_one] at h1
  simpa [U] using h1

/-- The trace of the indicator diagonal matrix for the fiber `g ⁻¹' {y}` picks out the
diagonal entries of `M` indexed by that fiber. -/
lemma trace_indicator_diagonal_mul {N m : ℕ}
    (g : Fin N → Fin m) (y : Fin m) (M : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.diagonal (fun j : Fin N => if g j = y then (1 : ℂ) else 0) * M).trace =
      ∑ j ∈ Finset.univ.filter (fun j => g j = y), M j j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [show ∑ i : Fin N,
      ∑ x, (if i = x then if g i = y then (1 : ℂ) else 0 else 0) * M x i =
      ∑ i : Fin N, (if g i = y then 1 else 0) * M i i from by
    congr 1
    ext i
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), zero_mul]
    · exact absurd (Finset.mem_univ i)]
  rw [show ∑ i : Fin N, (if g i = y then (1 : ℂ) else 0) * M i i =
      ∑ i ∈ Finset.univ.filter (fun i => g i = y), M i i from by
    rw [Finset.sum_filter]
    congr 1
    ext i
    split_ifs <;> simp]

/-- Existence of a projector-adapted ONB.

    For orthogonal projectors {P_y} summing to I, there exists a unitary W
    and a grouping function g : Fin N → Fin m such that for any operator A:
    Tr(P_y A) = Σ_{j : g(j) = y} (W A W†)_{jj}

    This is constructed via spectral decomposition of H = ∑ y • P_y. -/
lemma projector_adapted_onb_exists {N m : ℕ} [NeZero N] [NeZero m]
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_herm : ∀ y, (P y).conjTranspose = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (h_complete : ∑ y, P y = 1) :
    ∃ (W : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → Fin m),
      W * W.conjTranspose = 1 ∧
      W.conjTranspose * W = 1 ∧
      ∀ (A : Matrix (Fin N) (Fin N) ℂ) (y : Fin m),
        (P y * A).trace =
          ∑ j ∈ Finset.univ.filter (fun j => g j = y),
            (W * A * W.conjTranspose) j j := by
  set H := ∑ y : Fin m, (y.val : ℂ) • P y
  have hH : H.IsHermitian := projector_sum_isHermitian P h_herm
  let U := hH.eigenvectorUnitary.val
  set W := star U
  have h_eig_range : ∀ j, ∃ y : Fin m, hH.eigenvalues j = (y.val : ℝ) :=
    projector_sum_eigenvalue_in_fin P h_proj h_ortho h_complete hH
  let g : Fin N → Fin m := fun j => (h_eig_range j).choose
  have hg : ∀ j, (hH.eigenvalues j : ℝ) = ((g j).val : ℝ) :=
    fun j => (h_eig_range j).choose_spec
  have hWU : W * W.conjTranspose = 1 := by
    change star U * star (star U) = 1
    rw [star_star]
    exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hWU' : W.conjTranspose * W = 1 := by
    change star (star U) * star U = 1
    rw [star_star]
    have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simp only [Unitary.coe_star] at h
    exact h
  have h_P_decomp : ∀ y, P y = U *
      Matrix.diagonal (fun j => if g j = y then (1 : ℂ) else 0) * star U := by
    intro y
    simpa using
      projector_eq_eigenvector_unitary_mul_indicator_diagonal_mul_star
        P h_proj h_ortho h_complete hH g hg y
  have h_trace : ∀ (A : Matrix (Fin N) (Fin N) ℂ) (y : Fin m),
      (P y * A).trace =
        ∑ j ∈ Finset.univ.filter (fun j => g j = y),
          (W * A * W.conjTranspose) j j := by
    intro A y
    rw [h_P_decomp y]
    rw [mul_assoc, mul_assoc]
    rw [Matrix.trace_mul_comm U]
    rw [mul_assoc]
    have hWconj : W.conjTranspose = U := by
      change star (star U) = U; exact star_star _
    simp only [hWconj]
    set M := star U * A * U
    simpa [M] using trace_indicator_diagonal_mul g y M
  exact ⟨W, g, hWU, hWU', h_trace⟩

/-- Projective measurement data processing inequality under kernel containment.

This real-valued form matches `generalized_klein_diagonal_bound` and the
`relativeEntropyReal` API. -/
lemma projective_measurement_dpi_of_ker_sub {N m : ℕ} [NeZero N] [NeZero m]
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_herm : ∀ y, (P y).conjTranspose = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (h_complete : ∑ y, P y = 1)
    (ρ σ : DensityOp N)
    (h_ker : ∀ v : Fin N → ℂ,
      σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    (∑ y : Fin m,
      if ((P y * ρ.toOp).trace).re = 0 then 0
      else ((P y * ρ.toOp).trace).re *
        Real.log (((P y * ρ.toOp).trace).re / ((P y * σ.toOp).trace).re)) ≤
    relativeEntropyReal ρ σ := by
  obtain ⟨W, g, hWU, hWU', h_trace_eq⟩ :=
    projector_adapted_onb_exists P h_proj h_herm h_ortho h_complete
  set d : Fin N → ℝ := fun j => ((W * ρ.toOp * W.conjTranspose) j j).re
  set mq : Fin N → ℝ := fun j => ((W * σ.toOp * W.conjTranspose) j j).re
  have h_support : ∀ j, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j = 0 →
      diagonalOfRhoInSigmaBasis ρ σ j = 0 :=
    (eigenvalue_support_iff_ker_sub ρ σ).mpr h_ker
  have hW_inj : Function.Injective W.mulVec :=
    mulVec_injective_of_conjTranspose_mul_eq_one W hWU'
  have h_basis_supp : ∀ j, mq j = 0 → d j = 0 :=
    support_containment_any_basis W hW_inj ρ σ h_support
  have h_meas_rho : ∀ y, ((P y * ρ.toOp).trace).re =
      ∑ j ∈ Finset.univ.filter (fun j => g j = y), d j := by
    intro y
    have h1 := h_trace_eq ρ.toOp y
    simp only [d]
    conv_lhs => rw [h1]
    simp [Complex.re_sum]
  have h_meas_sigma : ∀ y, ((P y * σ.toOp).trace).re =
      ∑ j ∈ Finset.univ.filter (fun j => g j = y), mq j := by
    intro y
    have h1 := h_trace_eq σ.toOp y
    simp only [mq]
    conv_lhs => rw [h1]
    simp [Complex.re_sum]
  have h_lhs_eq : (∑ y : Fin m,
      if ((P y * ρ.toOp).trace).re = 0 then 0
      else ((P y * ρ.toOp).trace).re *
        Real.log (((P y * ρ.toOp).trace).re /
          ((P y * σ.toOp).trace).re)) =
    (∑ y : Fin m,
      let py := ∑ j ∈ Finset.univ.filter (fun j => g j = y), d j
      let qy := ∑ j ∈ Finset.univ.filter (fun j => g j = y), mq j
      if py = 0 then 0 else py * Real.log (py / qy)) := by
    apply Finset.sum_congr rfl; intro y _
    rw [h_meas_rho y, h_meas_sigma y]
  have hd_nonneg : ∀ j, 0 ≤ d j := fun j =>
    psd_conj_diag_nonneg (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) W j
  have hmq_nonneg : ∀ j, 0 ≤ mq j := fun j =>
    psd_conj_diag_nonneg (posSemidefOp_implies_mathlib σ.toPosSemidefOp) W j
  have h_ker : ∀ v : Fin N → ℂ, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0 :=
    ker_sigma_sub_ker_rho_of_eigenvalue_support ρ σ h_support
  calc (∑ y : Fin m,
        if ((P y * ρ.toOp).trace).re = 0 then 0
        else ((P y * ρ.toOp).trace).re *
          Real.log (((P y * ρ.toOp).trace).re /
            ((P y * σ.toOp).trace).re))
      = (∑ y : Fin m,
          let py := ∑ j ∈ Finset.univ.filter (fun j => g j = y), d j
          let qy := ∑ j ∈ Finset.univ.filter (fun j => g j = y), mq j
          if py = 0 then 0 else py * Real.log (py / qy)) := h_lhs_eq
    _ ≤ (∑ j : Fin N,
          if d j = 0 then 0 else d j * Real.log (d j / mq j)) :=
        kl_divergence_coarsening d mq hd_nonneg hmq_nonneg g h_basis_supp
    _ ≤ relativeEntropyReal ρ σ :=
        generalized_klein_diagonal_bound W hWU' ρ σ h_ker

/-- Projective measurement data processing inequality in the finite-valued support case.

    For orthogonal projectors `{P_y}` summing to `I`, this bounds the real-valued
    totalized measurement KL expression by `relativeEntropyReal ρ σ`.

    The explicit support condition `supp(ρ) ⊆ supp(σ)` is part of the theorem:
    it is what ensures the left-hand side matches the intended finite-valued
    classical KL quantity. -/
lemma projective_measurement_dpi_with_support {N m : ℕ} [NeZero N] [NeZero m]
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_herm : ∀ y, (P y).conjTranspose = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (h_complete : ∑ y, P y = 1)
    (ρ σ : DensityOp N)
    (h_support : ∀ j, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j = 0 →
      diagonalOfRhoInSigmaBasis ρ σ j = 0) :
    (∑ y : Fin m,
      if ((P y * ρ.toOp).trace).re = 0 then 0
      else ((P y * ρ.toOp).trace).re *
        Real.log (((P y * ρ.toOp).trace).re / ((P y * σ.toOp).trace).re)) ≤
    relativeEntropyReal ρ σ := by
  exact projective_measurement_dpi_of_ker_sub P h_proj h_herm h_ortho h_complete ρ σ
    (ker_sigma_sub_ker_rho_of_eigenvalue_support ρ σ h_support)

/-- ENNReal projective DPI for the totalized real measurement formula.

    This theorem wraps the same finite real expression used in
    `projective_measurement_dpi_with_support` in `ENNReal.ofReal` and compares it to
    `relativeEntropy ρ σ`.

    In the bad-support branch the proof only uses `relativeEntropy ρ σ = ⊤`, so this
    is not yet a genuine extended-valued classical KL divergence formula on the
    left-hand side. -/
lemma projective_measurement_dpi {N m : ℕ} [NeZero N] [NeZero m]
    (P : Fin m → Op N)
    (h_proj : ∀ y, P y * P y = P y)
    (h_herm : ∀ y, (P y).conjTranspose = P y)
    (h_ortho : ∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0)
    (h_complete : ∑ y, P y = 1)
    (ρ σ : DensityOp N) :
    ENNReal.ofReal (∑ y : Fin m,
      if ((P y * ρ.toOp).trace).re = 0 then 0
      else ((P y * ρ.toOp).trace).re *
        Real.log (((P y * ρ.toOp).trace).re / ((P y * σ.toOp).trace).re)) ≤
    relativeEntropy ρ σ := by
  by_cases h_supp : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
      diagonalOfRhoInSigmaBasis ρ σ i = 0
  · rw [relativeEntropy_eq_ofReal_of_support ρ σ h_supp]
    apply ENNReal.ofReal_le_ofReal
    exact projective_measurement_dpi_with_support P h_proj h_herm h_ortho h_complete ρ σ h_supp
  · rw [relativeEntropy_eq_top ρ σ h_supp]
    exact le_top

end InfoTheory.RelativeEntropy

end
