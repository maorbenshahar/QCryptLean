import QCryptLean.InfoTheory.DistanceBounds.Basic
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity

/-!
# Eigenvalue–Trace Distance Bound — max eigenvalue vs trace distance

Shows that the maximum eigenvalue of a density operator is at least `1 - D(ρ, σ)` for
any pure state σ, combining fidelity lower bounds with spectral decomposition.

## Main statements
- `max_eigenvalue_ge_one_sub_traceDistance`: ∃ i, λᵢ(ρ) ≥ 1 - D(ρ, σ)
-/

open Quantum.Operators Quantum.TensorProducts Matrix InfoTheory.VonNeumannEntropy Quantum.Metrics

noncomputable section

namespace Quantum.Metrics

/-- **Fidelity lower bound via eigenvalue perturbation.** For a pure state `σ = |ψ⟩⟨ψ|`, the
    squared fidelity of `ρ` with `σ` is at least `1 - D(ρ, σ)`: the difference `A = ρ - σ` is
    traceless with eigenvalues in `[-D, D]`, so `⟨ψ|A|ψ⟩ ≥ -D` and `F² = 1 + ⟨ψ|A|ψ⟩ ≥ 1 - D`. -/
private lemma fidelitySq_ge_one_sub_traceDistance {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) ≥
      1 - traceDistance ρ.toOp (DensityOp.fromPure ψ hψ).toOp := by
  set σ := DensityOp.fromPure ψ hψ with hσ_def
  rw [fidelitySq_fromPure]
  -- Step 1: Set up eigenvalue decomposition of A = ρ - σ
  set A := ρ.toOp - σ.toOp with hA_def
  have hA := densityOp_sub_isHermitian ρ σ
  have h_ev_sum_zero := densityOp_sub_pure_eigenvalues_sum_zero ρ ψ hψ
  set evA := hA.eigenvalues with hevA_def
  set UA := hA.eigenvectorUnitary.val with hUA_def
  have hUA : UA† * UA = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUA' : UA * UA† = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  -- Step 2: ⟨ψ|A|ψ⟩ = ∑ᵢ evA_i · |⟨u_i|ψ⟩|² (spectral quadratic form)
  have h_A_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_A_spec
  set pA := fun i => Complex.normSq (UA†.mulVec ψ.vec i) with hpA_def
  have h_pA_nonneg : ∀ i, 0 ≤ pA i := fun i => Complex.normSq_nonneg _
  -- ∑ pA_i = 1 (ONB completeness with normalized ψ)
  have h_pA_sum : ∑ i, pA i = 1 := by
    have h1 : ∑ i, pA i = (star (UA†.mulVec ψ.vec) ⬝ᵥ (UA†.mulVec ψ.vec)).re := by
      rw [show star (UA†.mulVec ψ.vec) ⬝ᵥ (UA†.mulVec ψ.vec) =
          ∑ i, star (UA†.mulVec ψ.vec i) * (UA†.mulVec ψ.vec i) from rfl]
      rw [Complex.re_sum]
      congr 1; ext i
      rw [show star (UA†.mulVec ψ.vec i) = (starRingEnd ℂ) (UA†.mulVec ψ.vec i) from rfl,
          RCLike.conj_mul]
      simp only [pA, Complex.normSq_eq_norm_sq]; norm_cast
    have h2 : star (UA†.mulVec ψ.vec) ⬝ᵥ (UA†.mulVec ψ.vec) =
        star ψ.vec ⬝ᵥ ψ.vec := by
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose,
          Matrix.vecMul_vecMul]
      rw [show Matrix.vecMul (star ψ.vec) (UA * UA†) = star ψ.vec from by
          rw [hUA', Matrix.vecMul_one]]
    have h3 : star ψ.vec ⬝ᵥ ψ.vec = 1 := by
      simp only [bra_mul_ket_eq, Ket.dag_vec] at hψ
      rw [show star ψ.vec ⬝ᵥ ψ.vec = ∑ i, star (ψ.vec i) * ψ.vec i from rfl]
      simp_rw [show ∀ i, star (ψ.vec i) = (starRingEnd ℂ) (ψ.vec i) from fun _ => rfl]
      exact hψ
    rw [h1, h2, h3, Complex.one_re]
  -- ⟨ψ|A|ψ⟩ as spectral form
  have h_braAket : (ψ.dag * A * ψ).re = ∑ i, evA i * pA i := by
    have h_eq : ψ.dag * A * ψ = quadraticForm A ψ.vec := by
      rw [braop_mul_ket]
      simp only [bra_mul_ket_eq, op_mul_ket_vec, Ket.dag_vec]
      unfold quadraticForm dotProduct; rfl
    rw [h_eq]; unfold quadraticForm
    change (star ψ.vec ⬝ᵥ (ρ.toOp - σ.toOp).mulVec ψ.vec).re = _
    rw [h_A_spec]
    exact spectral_quadratic_form_re UA evA ψ.vec
  -- Step 3: Each eigenvalue of A is ≥ -D
  -- Positive eigenvalue sum = D (half trace norm for trace-zero operator)
  set pos_sum_A := ∑ i, max 0 (evA i) with hpos_sum_A_def
  -- D = pos_sum_A (trace distance = sum of positive eigenvalues for trace-0 Hermitian)
  have h_td_eq_pos_sum : traceDistance ρ.toOp σ.toOp = pos_sum_A := by
    rw [traceDistance_densityOp_eq_traceNormHermitian ρ σ]
    unfold traceNormHermitian
    -- sum |ev_i| = 2 * pos_sum (since trace = 0, positive and negative parts balance)
    have h_pos_neg_eq : pos_sum_A = ∑ i, max 0 (-evA i) := by
      have h1 : (∑ i, evA i : ℝ) =
          ∑ i, (max 0 (evA i) - max 0 (-evA i)) := by
        congr 1; ext i
        by_cases hx : 0 ≤ evA i
        · rw [max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), sub_zero]
        · push_neg at hx
          rw [max_eq_left (le_of_lt hx), max_eq_right (neg_pos.mpr hx).le, zero_sub, neg_neg]
      rw [h_ev_sum_zero, Finset.sum_sub_distrib] at h1; linarith only [h1]
    have h_abs_split : ∀ i, |evA i| = max 0 (evA i) + max 0 (-evA i) := by
      intro i
      by_cases hx : 0 ≤ evA i
      · rw [abs_of_nonneg hx, max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), add_zero]
      · push_neg at hx
        rw [abs_of_neg hx, max_eq_left (le_of_lt hx), zero_add,
            max_eq_right (neg_pos.mpr hx).le]
    have h_sum_abs : ∑ i, |evA i| = pos_sum_A + ∑ i, max 0 (-evA i) := by
      conv_lhs => rw [show ∑ i, |evA i| =
          ∑ i, (max 0 (evA i) + max 0 (-evA i)) from
          Finset.sum_congr rfl (fun i _ => h_abs_split i)]
      rw [Finset.sum_add_distrib]
    rw [h_sum_abs, h_pos_neg_eq, ← two_mul]; ring
  -- Step 4: ⟨ψ|A|ψ⟩ ≥ -D
  -- Key: evA_i * pA_i ≥ evA_i for all i (since 0 ≤ pA_i ≤ 1)
  -- Proof: if evA_i ≥ 0, then evA_i * pA_i ≥ 0 ≥ evA_i * 1 only when evA_i = 0,
  --        but more generally evA_i * pA_i ≥ min(0, evA_i) = min(0, evA_i)
  -- Actually: ∑ evA_i * pA_i ≥ ∑ min(0, evA_i) = ∑ evA_i - ∑ max(0, evA_i) = 0 - D = -D
  have h_pA_le_one : ∀ i, pA i ≤ 1 := by
    intro i; calc pA i ≤ ∑ j, pA j :=
          Finset.single_le_sum (fun j _ => h_pA_nonneg j) (Finset.mem_univ i)
      _ = 1 := h_pA_sum
  -- Each term: evA_i * pA_i ≥ min(0, evA_i) because:
  -- If evA_i ≥ 0: evA_i * pA_i ≥ 0 = min(0, evA_i) (since pA_i ≥ 0)
  -- If evA_i < 0: evA_i * pA_i ≥ evA_i = min(0, evA_i) (since pA_i ≤ 1)
  have h_term_bound : ∀ i, evA i * pA i ≥ min 0 (evA i) := by
    intro i
    by_cases h : 0 ≤ evA i
    · calc evA i * pA i ≥ 0 := mul_nonneg h (h_pA_nonneg i)
        _ ≥ min 0 (evA i) := by simp [min_eq_left h]
    · push_neg at h
      have : min 0 (evA i) = evA i := min_eq_right (le_of_lt h)
      rw [this]
      have hle : evA i * pA i ≥ evA i * 1 :=
        mul_le_mul_of_nonpos_left (h_pA_le_one i) (le_of_lt h)
      linarith only [hle]
  -- ∑ min(0, evA_i) = ∑ evA_i - ∑ max(0, evA_i) = 0 - D = -D
  have h_min_sum : ∑ i, min 0 (evA i) = -pos_sum_A := by
    have h_split : ∀ i, evA i = max 0 (evA i) + min 0 (evA i) := by
      intro i; simp [max_def, min_def]; split_ifs <;> linarith
    have h1 : ∑ i, evA i = ∑ i, (max 0 (evA i) + min 0 (evA i)) :=
      Finset.sum_congr rfl (fun i _ => h_split i)
    rw [h_ev_sum_zero, Finset.sum_add_distrib] at h1
    linarith only [h1]
  have h_braAket_ge : (ψ.dag * A * ψ).re ≥ -traceDistance ρ.toOp σ.toOp := by
    rw [h_braAket, h_td_eq_pos_sum]
    calc ∑ i, evA i * pA i ≥ ∑ i, min 0 (evA i) :=
          Finset.sum_le_sum (fun i _ => h_term_bound i)
      _ = -pos_sum_A := h_min_sum
  -- Step 5: F² = ⟨ψ|ρ|ψ⟩ = ⟨ψ|σ|ψ⟩ + ⟨ψ|A|ψ⟩ = 1 + ⟨ψ|A|ψ⟩ ≥ 1 - D
  -- ⟨ψ|ρ|ψ⟩ = ⟨ψ|A+σ|ψ⟩ = ⟨ψ|A|ψ⟩ + ⟨ψ|σ|ψ⟩
  have h_ρ_split : ρ.toOp = A + σ.toOp := by simp [hA_def, sub_add_cancel]
  -- ⟨ψ|σ|ψ⟩ = 1
  have h_ψσ : (ψ.dag * σ.toOp * ψ).re = 1 := by
    have hσ_def' : σ.toOp = ψ * ψ.dag := rfl
    rw [hσ_def']
    have h2 : ψ.dag * (ψ * ψ.dag) = (ψ.dag * ψ) • ψ.dag := bra_mul_ketbra ψ.dag ψ ψ.dag
    simp only [h2, hψ]
    have h_smul : (1 : ℂ) • ψ.dag = ψ.dag := by ext i; simp [Bra.smul_vec, one_mul]
    simp only [h_smul, hψ, Complex.one_re]
  -- Combine
  have h_sum_re : (ψ.dag * ρ.toOp * ψ).re =
      (ψ.dag * A * ψ).re + (ψ.dag * σ.toOp * ψ).re := by
    conv_lhs => rw [h_ρ_split]
    rw [braop_mul_ket, add_op_mul_ket, bra_mul_add_ket, ← braop_mul_ket, ← braop_mul_ket]
    rfl
  linarith only [h_sum_re, h_braAket_ge, h_ψσ]

/-- The maximum eigenvalue of a density operator is at least 1 - traceDistance to any pure state.

    For any density operator ρ and any pure state σ = |ψ⟩⟨ψ|:
    max_eigenvalue(ρ) ≥ 1 - traceDistance(ρ, σ)

    **Proof**: For D = 1, we have 1 - D = 0, and any eigenvalue is ≥ 0.
    For D ≥ 1 - 1/n, we use λ_max ≥ 1/n (from sum = 1).
    For D < 1 - 1/n, we use the fidelity lower bound F² ≥ 1 - D (from
    eigenvalue perturbation) combined with F² ≤ λ_max (spectral decomposition). -/
lemma max_eigenvalue_ge_one_sub_traceDistance {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    ∃ i, eigenvaluesOf ρ i ≥ 1 - traceDistance ρ.toOp (DensityOp.fromPure ψ hψ).toOp := by
  -- Setup
  set σ := DensityOp.fromPure ψ hψ with hσ_def
  have hspec := eigenvaluesOf_spec ρ
  obtain ⟨h_eig_nonneg, h_eig_sum, _, _⟩ := hspec
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  obtain ⟨i_max, _, hi_max_is_max⟩ :=
    Finset.exists_max_image Finset.univ (eigenvaluesOf ρ) hnonempty
  use i_max
  have h_td_nonneg := traceDistance_nonneg ρ.toOp σ.toOp
  have h_td_le_one := traceDistance_le_one ρ σ
  have h_eig_max_nonneg := h_eig_nonneg i_max
  -- Case D = 1: trivial since 1 - 1 = 0 ≤ λ_max
  by_cases h_td_eq_one : traceDistance ρ.toOp σ.toOp = 1
  · rw [h_td_eq_one, sub_self]; exact h_eig_max_nonneg
  have h_td_lt_one : traceDistance ρ.toOp σ.toOp < 1 := lt_of_le_of_ne h_td_le_one h_td_eq_one
  -- Key: max eigenvalue ≥ 1/n (pigeonhole from sum = 1)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hn_nonneg : (0 : ℝ) ≤ n := le_of_lt hn_pos
  have h_one_div_n_le_max : (1 : ℝ) / n ≤ eigenvaluesOf ρ i_max := by
    have h_sum_le : ∑ i, eigenvaluesOf ρ i ≤ n * eigenvaluesOf ρ i_max := by
      calc ∑ i, eigenvaluesOf ρ i
          ≤ ∑ _i : Fin n, eigenvaluesOf ρ i_max := by
            apply Finset.sum_le_sum; intro i _; exact hi_max_is_max i (Finset.mem_univ i)
        _ = n * eigenvaluesOf ρ i_max := by simp [Finset.sum_const]
    calc (1 : ℝ) / n = (∑ i, eigenvaluesOf ρ i) / n := by rw [h_eig_sum]
      _ ≤ (n * eigenvaluesOf ρ i_max) / n := by
          apply div_le_div_of_nonneg_right h_sum_le hn_nonneg
      _ = eigenvaluesOf ρ i_max := by field_simp
  -- For D ≥ 1 - 1/n: 1 - D ≤ 1/n ≤ λ_max
  by_cases h_D_large : traceDistance ρ.toOp σ.toOp ≥ 1 - 1 / n
  · calc eigenvaluesOf ρ i_max ≥ 1 / n := h_one_div_n_le_max
      _ ≥ 1 - traceDistance ρ.toOp σ.toOp := by linarith only [h_D_large]
  -- For D < 1 - 1/n (small trace distance): use F² ≤ λ_max and F² ≥ 1-D
  push_neg at h_D_large
  -- Part 1: F² ≥ 1 - D via eigenvalue perturbation
  -- A = ρ - σ has trace 0 and trace norm 2D, so eigenvalues in [-D, D]
  -- ⟨ψ|A|ψ⟩ ≥ -D and F² = ⟨ψ|ρ|ψ⟩ = ⟨ψ|σ|ψ⟩ + ⟨ψ|A|ψ⟩ = 1 + ⟨ψ|A|ψ⟩ ≥ 1 - D
  have h_fid_ge : DensityOp.fidelitySq ρ σ ≥ 1 - traceDistance ρ.toOp σ.toOp :=
    fidelitySq_ge_one_sub_traceDistance ρ ψ hψ
  -- Part 2: F² ≤ λ_max (use spectral decomposition directly)
  have h_fid_le_max : DensityOp.fidelitySq ρ σ ≤ eigenvaluesOf ρ i_max := by
    rw [fidelitySq_fromPure]
    -- Set up spectral decomposition of ρ
    let hH := ρ.toPosSemidefOp.toHermitianOp.isHermitian
    let ev := hH.eigenvalues
    -- ev = eigenvaluesOf ρ by definition
    have hev_eq : ev = eigenvaluesOf ρ := rfl
    have h_ev_bounds := density_eigenvalues_bound ρ
    have h_ev_nonneg : ∀ i, 0 ≤ ev i := fun i => (h_ev_bounds i).1
    have h_spec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_spec
    let U := hH.eigenvectorUnitary.val
    have hUU : U† * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have hUU' : U * U† = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    set φ_vec := U†.mulVec ψ.vec with hφ_def
    set a := fun i => Complex.normSq (φ_vec i) with ha_def
    have h_a_nonneg : ∀ i, 0 ≤ a i := fun i => Complex.normSq_nonneg _
    -- ∑ a_i = 1
    have h_a_sum : ∑ i, a i = 1 := by
      have h1 : ∑ i, a i = (star φ_vec ⬝ᵥ φ_vec).re := by
        rw [show star φ_vec ⬝ᵥ φ_vec = ∑ i, star (φ_vec i) * φ_vec i from rfl,
            Complex.re_sum]
        congr 1; ext i
        rw [show star (φ_vec i) = (starRingEnd ℂ) (φ_vec i) from rfl, RCLike.conj_mul]
        simp only [a, Complex.normSq_eq_norm_sq]; norm_cast
      have h2 : star φ_vec ⬝ᵥ φ_vec = star ψ.vec ⬝ᵥ ψ.vec := by
        rw [hφ_def, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
            Matrix.conjTranspose_conjTranspose, Matrix.vecMul_vecMul]
        rw [show Matrix.vecMul (star ψ.vec) (U * U†) = star ψ.vec from by
            rw [hUU', Matrix.vecMul_one]]
      have h3 : star ψ.vec ⬝ᵥ ψ.vec = 1 := by
        simp only [bra_mul_ket_eq, Ket.dag_vec] at hψ
        rw [show star ψ.vec ⬝ᵥ ψ.vec = ∑ i, star (ψ.vec i) * ψ.vec i from rfl]
        simp_rw [show ∀ i, star (ψ.vec i) = (starRingEnd ℂ) (ψ.vec i) from fun _ => rfl]
        exact hψ
      rw [h1, h2, h3, Complex.one_re]
    -- ⟨ψ|ρ|ψ⟩ = ∑ ev_i * a_i
    have h_expect : (ψ.dag * ρ.toOp * ψ).re = ∑ i, ev i * a i := by
      have h_eq : ψ.dag * ρ.toOp * ψ = quadraticForm ρ.toOp ψ.vec := by
        rw [braop_mul_ket]
        simp only [bra_mul_ket_eq, op_mul_ket_vec, Ket.dag_vec]
        unfold quadraticForm dotProduct; rfl
      rw [h_eq]; unfold quadraticForm; rw [h_spec]
      convert spectral_quadratic_form_re U ev ψ.vec using 2
    -- ∑ ev_i * a_i ≤ ev_max * ∑ a_i = ev_max
    rw [h_expect]
    -- Each ev_i ≤ eigenvaluesOf ρ i_max
    have h_ev_le_max : ∀ i, ev i ≤ eigenvaluesOf ρ i_max := by
      intro i; exact hi_max_is_max i (Finset.mem_univ i)
    calc ∑ i, ev i * a i ≤ ∑ i, eigenvaluesOf ρ i_max * a i := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_right (h_ev_le_max i) (h_a_nonneg i)
      _ = eigenvaluesOf ρ i_max * ∑ i, a i := by rw [Finset.mul_sum]
      _ = eigenvaluesOf ρ i_max := by rw [h_a_sum, mul_one]
  -- Final: λ_max ≥ F² ≥ 1 - D
  linarith only [h_fid_ge, h_fid_le_max]

end Quantum.Metrics

end
