import QCryptLean.InfoTheory.DistanceBounds.Basic
import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity

/-!
# Fuchs–van de Graaf Inequality — fidelity-trace distance conversion

Relates trace distance and fidelity for pure states:
D(ρ, |ψ⟩⟨ψ|) ≤ √(1 - F²(ρ,ψ)), with equality when both states are pure.

## Main definitions
- `densityOp_sub_pure_sq_trace`: Tr((ρ - |ψ⟩⟨ψ|)²) = Tr(ρ²) + 1 - 2F²

## Main statements
- `traceDistance_from_fidelity_dim2`: D(ρ, |ψ⟩⟨ψ|) ≤ √(1 - F²) for n = 2
- `traceDistance_sq_le_one_sub_fidelityPureSq`: D² ≤ 1 - F² (squared form)
- `traceDistance_sq_eq_one_sub_fidelityPureSq_pure_pure`: D² = 1 - F² for two pure states
- `traceDistance_from_fidelity`: D(ρ, |ψ⟩⟨ψ|) ≤ √(1 - F²)
-/

open Quantum.Operators Quantum.TensorProducts Matrix InfoTheory.VonNeumannEntropy Quantum.Metrics

noncomputable section

namespace Quantum.Metrics

/-!
## Fuchs-van de Graaf Helper Lemmas

These lemmas establish the key properties needed to prove the Fuchs-van de Graaf
inequality: D(ρ, |ψ⟩⟨ψ|) ≤ √(1 - F²(ρ,ψ)).

The proof strategy works in the eigenbasis of ρ where ρ = diag(p₁,...,pₙ) and
|ψ⟩ = Σᵢ αᵢ|eᵢ⟩. The matrix A = ρ - |ψ⟩⟨ψ| = diag(p) - |α⟩⟨α| has special
structure that allows direct eigenvalue analysis.
-/

/-- For a pure state |ψ⟩⟨ψ|, the quadratic form ⟨v|(|ψ⟩⟨ψ|)|v⟩ equals |⟨v|ψ⟩|². -/
private lemma pure_quadratic_form {n : ℕ} (ψ : Ket n) (v : Fin n → ℂ) :
    (star v ⬝ᵥ ((ψ * ψ.dag).mulVec v)).re = Complex.normSq (star v ⬝ᵥ ψ.vec) := by
  simp only [dotProduct, mulVec, ket_mul_bra_apply, Ket.dag_vec,
             Pi.star_apply, starRingEnd_apply]
  have h_factor : ∑ x, star (v x) * ∑ x_1, ψ.vec x * star (ψ.vec x_1) * v x_1 =
      (∑ i, star (v i) * ψ.vec i) * (∑ j, star (ψ.vec j) * v j) := by
    rw [Finset.sum_mul]
    congr 1; ext i
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1; ext j; ring
  rw [h_factor]
  have h_conj : (∑ j, star (ψ.vec j) * v j) = star (∑ i, star (v i) * ψ.vec i) := by
    simp only [star_sum, star_mul', star_star]
    congr 1; ext i; ring
  rw [h_conj]
  let c := ∑ i, star (v i) * ψ.vec i
  have h_mul_conj : c * star c = (Complex.normSq c : ℂ) := Complex.mul_conj c
  rw [h_mul_conj, Complex.ofReal_re]

/-- Tr((ρ - |ψ⟩⟨ψ|)²) = Tr(ρ²) + 1 - 2F²(ρ,ψ).

    Key identity for relating trace distance to fidelity. -/
lemma densityOp_sub_pure_sq_trace {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    let σ := DensityOp.fromPure ψ hψ
    ((ρ.toOp - σ.toOp) * (ρ.toOp - σ.toOp)).trace.re =
      (ρ.toOp * ρ.toOp).trace.re + 1 - 2 * DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
  intro σ
  -- Use fidelitySq_fromPure to reduce to the bra-ket form
  rw [fidelitySq_fromPure]
  -- σ.toOp = ψ * ψ.dag (pure state outer product)
  have hσ_def : σ.toOp = ψ * ψ.dag := rfl
  -- Step 1: Expand (ρ - σ)² = ρ² - ρσ - σρ + σ²
  have h_expand : (ρ.toOp - σ.toOp) * (ρ.toOp - σ.toOp) =
      ρ.toOp * ρ.toOp - ρ.toOp * σ.toOp - σ.toOp * ρ.toOp + σ.toOp * σ.toOp := by
    noncomm_ring
  rw [h_expand]
  -- Step 2: Trace is linear
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
  -- Step 3: Compute Tr(σ²) = Tr(|ψ⟩⟨ψ|·|ψ⟩⟨ψ|) = Tr(|ψ⟩⟨ψ|) = 1
  -- Use ketbra_mul_ketbra: (ψ * ψ.dag) * (ψ * ψ.dag) = (ψ.dag * ψ) • (ψ * ψ.dag)
  have hσ_sq : σ.toOp * σ.toOp = σ.toOp := by
    rw [hσ_def, ketbra_mul_ketbra, hψ, one_smul]
  have hσ_sq_tr : (σ.toOp * σ.toOp).trace = 1 := by
    rw [hσ_sq, σ.trace_one]
  -- Step 4: Compute Tr(ρσ) = Tr(ρ · |ψ⟩⟨ψ|) = ⟨ψ|ρ|ψ⟩
  -- Use cyclic property: Tr(ρ · |ψ⟩⟨ψ|) = Tr(|ψ⟩⟨ψ| · ρ) = ⟨ψ|ρ|ψ⟩
  have hρσ_tr : (ρ.toOp * σ.toOp).trace = ψ.dag * ρ.toOp * ψ := by
    rw [hσ_def, Matrix.trace_mul_comm]
    exact trace_ketbra_mul ψ ρ.toOp
  -- Step 5: Compute Tr(σρ) = Tr(|ψ⟩⟨ψ| · ρ) = ⟨ψ|ρ|ψ⟩
  have hσρ_tr : (σ.toOp * ρ.toOp).trace = ψ.dag * ρ.toOp * ψ := by
    rw [hσ_def]
    exact trace_ketbra_mul ψ ρ.toOp
  -- Step 6: Combine everything
  rw [hσ_sq_tr, hρσ_tr, hσρ_tr]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
  ring

/-- For the 2D case: direct proof of trace distance bound.

    When n = 2, the eigenvalues of A = ρ - |ψ⟩⟨ψ| are ±λ (trace-zero 2×2 Hermitian),
    so D = |λ|. The bound D² ≤ 1 - F² follows from det(A) analysis and 0 ≤ pᵢ ≤ 1. -/
lemma traceDistance_from_fidelity_dim2 (ρ : DensityOp 2) (ψ : Ket 2)
    (hψ : (ψ.dag * ψ) = 1) :
    traceDistance ρ.toOp (DensityOp.fromPure ψ hψ).toOp ≤
      Real.sqrt (1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ)) := by
  -- In 2D, A = ρ - |ψ⟩⟨ψ| has Tr(A) = 0, so eigenvalues are {λ, -λ}
  -- D = ½(|λ| + |-λ|) = |λ|
  -- Tr(A²) = 2λ², so D² = Tr(A²)/2
  -- From densityOp_sub_pure_sq_trace: Tr(A²).re = Tr(ρ²).re + 1 - 2F²
  -- Since Tr(ρ²) ≤ 1: D² ≤ (2 - 2F²)/2 = 1 - F²
  let σ := DensityOp.fromPure ψ hψ
  let A := ρ.toOp - σ.toOp
  let hA := densityOp_sub_isHermitian ρ σ
  let ev := hA.eigenvalues
  -- Key fact: eigenvalues sum to 0, so ev 0 + ev 1 = 0
  have h_sum_zero : ev 0 + ev 1 = 0 := by
    have h := densityOp_sub_pure_eigenvalues_sum_zero ρ ψ hψ
    simpa only [Fin.sum_univ_two] using h
  -- In 2D with trace 0: ev 1 = -ev 0
  have h_ev1_neg : ev 1 = -ev 0 := by linarith only [h_sum_zero]
  -- Trace distance = (1/2)(|ev 0| + |ev 1|) = (1/2)(|ev 0| + |-ev 0|) = |ev 0|
  have h_td : traceDistance ρ.toOp σ.toOp = |ev 0| := by
    have : NeZero 2 := ⟨two_ne_zero⟩
    rw [traceDistance_densityOp_eq_traceNormHermitian ρ σ]
    simp only [traceNormHermitian]
    -- The eigenvalues are the same by definition
    have h_ev_eq : (densityOp_sub_isHermitian ρ σ).eigenvalues = ev := rfl
    simp only [h_ev_eq]
    -- Sum over Fin 2: ∑ x, |ev x| = |ev 0| + |ev 1|
    rw [Fin.sum_univ_two, h_ev1_neg, abs_neg]
    ring
  -- Key: Tr(A²) = Σ ev_i² = ev 0² + ev 1² = 2 * ev 0²
  -- For Hermitian, Tr(A²) = Σ λᵢ² (sum of eigenvalue squares)
  have h_A_sq_trace : (A * A).trace.re = 2 * (ev 0)^2 := by
    -- This uses that Tr(A²) = Σᵢ λᵢ² for Hermitian matrices
    -- For the spectral decomposition A = U D U†, we have A² = U D² U†
    -- and Tr(A²) = Tr(D²) = Σᵢ λᵢ²
    have h_eq : (A * A).trace.re = ∑ i : Fin 2, (ev i)^2 := by
      -- Use the spectral theorem: A = U * D * U†
      let U := hA.eigenvectorUnitary.val
      let D := Matrix.diagonal (fun i => (ev i : ℂ))
      -- For diagonal matrix: D² = diag(λᵢ²), so Tr(D²) = Σλᵢ²
      have h_D_sq : D * D = Matrix.diagonal (fun i => ((ev i : ℂ)^2)) := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1; ext i; ring
      have h_D_sq_trace : (D * D).trace = ∑ i, ((ev i : ℂ)^2) := by
        rw [h_D_sq, Matrix.trace_diagonal]
      -- Use spectral theorem: A = U * D * U†
      -- Then Tr(A²) = Tr((U*D*U†)²) = Tr(U*D²*U†) = Tr(D²) by cyclic property
      -- Spectral theorem: A = U * D * U†
      have h_spectral := hA.spectral_theorem
      -- We need: Tr(A²) = Tr(D²)
      -- A² = (U * D * U†)² = U * D * U† * U * D * U† = U * D² * U† (since U† * U = 1)
      -- Tr(A²) = Tr(U * D² * U†) = Tr(D²) by cyclic property
      have h_U_unitary : U† * U = 1 := by
        have h_mem := hA.eigenvectorUnitary.2
        simp only [mem_unitaryGroup_iff] at h_mem
        -- h_mem gives U * U† = 1, we need U† * U = 1
        -- For unitary matrices, both hold
        have h_star_mem := hA.eigenvectorUnitary.2
        simp only [mem_unitaryGroup_iff'] at h_star_mem
        exact h_star_mem
      -- A * A = (U * D * U†) * (U * D * U†) = U * D * (U† * U) * D * U† = U * D² * U†
      have h_A_eq : A = U * D * U† := by
        -- spectral_theorem gives A = conjStarAlgAut U (diag(λ)) = U * diag(λ) * U†
        conv_lhs => rw [show A = ρ.toOp - σ.toOp from rfl, h_spectral]
        rw [Unitary.conjStarAlgAut_apply]
        -- Now need: U * diag(RCLike.ofReal ∘ eigenvalues) * star U = U * D * U†
        -- D = diag(fun i => (ev i : ℂ)) and star U = U†
        -- These are definitionally equal
        rfl
      have h_A_sq : A * A = U * D * D * U† := by
        calc A * A = (U * D * U†) * (U * D * U†) := by rw [h_A_eq]
          _ = U * D * (U† * U) * D * U† := by noncomm_ring
          _ = U * D * 1 * D * U† := by rw [h_U_unitary]
          _ = U * D * D * U† := by noncomm_ring
      -- Tr(U * D² * U†) = Tr(D²) by cyclic property
      have h_trace_eq : (U * D * D * U†).trace = (D * D).trace := by
        -- Use cyclic property: Tr(ABC) = Tr(BCA) = Tr(CAB)
        -- Tr(U * D * D * U†) = Tr(U† * U * D * D) = Tr(D * D)
        calc (U * D * D * U†).trace = (U† * (U * D * D)).trace := Matrix.trace_mul_comm _ _
          _ = (U† * U * D * D).trace := by noncomm_ring
          _ = (1 * D * D).trace := by rw [h_U_unitary]
          _ = (D * D).trace := by rw [Matrix.one_mul]
      calc (A * A).trace.re = (U * D * D * U†).trace.re := by rw [h_A_sq]
        _ = (D * D).trace.re := by rw [h_trace_eq]
        _ = (∑ i, ((ev i : ℂ)^2)).re := by rw [h_D_sq_trace]
        _ = ∑ i, (ev i)^2 := by
            simp only [Complex.re_sum]
            congr 1; ext i
            -- (ev i : ℂ)² = (ev i)² as reals
            have h : ((ev i : ℂ)^2).re = (ev i)^2 := by
              simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                         mul_zero, sub_zero]
            exact h
    rw [h_eq, Fin.sum_univ_two, h_ev1_neg, neg_sq]
    ring
  -- From densityOp_sub_pure_sq_trace: Tr(A²).re = Tr(ρ²).re + 1 - 2F²
  have h_trace_eq := densityOp_sub_pure_sq_trace ρ ψ hψ
  -- Purity bound: Tr(ρ²) ≤ 1
  have h_purity_le := (DensityOp.purity_bounds ρ).2
  -- Unfold purity definition: purity = (ρ.toOp * ρ.toOp).trace.re
  have h_purity_def : ρ.purity = (ρ.toOp * ρ.toOp).trace.re := rfl
  rw [h_purity_def] at h_purity_le
  -- Therefore: Tr(A²).re ≤ 2 - 2F², so 2*ev₀² ≤ 2(1-F²), so ev₀² ≤ 1-F²
  have h_fid_nonneg : 0 ≤ DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) :=
    fidelityPureSq_nonneg ρ ψ hψ
  have h_fid_le_one : DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) ≤ 1 :=
    fidelityPureSq_le_one ρ ψ hψ
  have h_ev0_sq_le : (ev 0)^2 ≤ 1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
    have h1 : (A * A).trace.re ≤ 2 - 2 * DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
      calc (A * A).trace.re
          = (ρ.toOp * ρ.toOp).trace.re + 1 - 2 * DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) :=
            h_trace_eq
        _ ≤ 1 + 1 - 2 * DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by linarith only
            [h_purity_le]
        _ = 2 - 2 * DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by ring
    have h2 : 2 * (ev 0)^2 ≤ 2 - 2 * DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
      rw [← h_A_sq_trace]; exact h1
    linarith only [h2]
  have h_one_sub_fid_nonneg : 0 ≤ 1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
    linarith only [h_fid_le_one]
  -- D = |ev 0| ≤ √(1 - F²)
  rw [h_td]
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact h_ev0_sq_le

/-- **Endgame of the rank-1 perturbation bound (pure real arithmetic).** Given eigenvalue/overlap
    data `ev, β` with `∑ ev = 0`, `β ≥ 0`, `∑ β = 1`, the per-index key bound
    `ev i · (ev i + 2 β i - 1) ≤ 0`, the identity `1 - F² = -∑ ev·β`, and `∑ max(0, ev) ≤ 1`,
    the positive-eigenvalue sum obeys `(∑ max(0, ev))² ≤ 1 - F²`. At most one eigenvalue is
    negative, and it drives the bound. -/
private lemma pos_sum_sq_le_of_key_bounds {n : ℕ} [NeZero n]
    (ev β : Fin n → ℝ) (F2 : ℝ)
    (h_sum_zero : ∑ i, ev i = 0)
    (h_β_nonneg : ∀ i, 0 ≤ β i)
    (h_β_sum : ∑ i, β i = 1)
    (h_key_bound : ∀ i, ev i * (ev i + 2 * β i - 1) ≤ 0)
    (h_one_sub_fid : 1 - F2 = -(∑ i, ev i * β i))
    (h_fid_le : F2 ≤ 1)
    (h_pos_sum_le : ∑ i, max 0 (ev i) ≤ 1) :
    (∑ i, max 0 (ev i)) ^ 2 ≤ 1 - F2 := by
  set pos_sum := ∑ i, max 0 (ev i) with hpos_sum_def
  have h_neg_β_gt : ∀ i, ev i < 0 → 1 / 2 < β i := by
    intro i h_neg
    have h := h_key_bound i
    -- ev_i < 0 and ev_i * (ev_i + 2β_i - 1) ≤ 0
    -- Since ev_i < 0, dividing flips: ev_i + 2β_i - 1 ≥ 0
    nlinarith only [h, h_neg]
  -- === Main proof by cases ===
  by_cases h_all_nonneg : ∀ i, 0 ≤ ev i
  · -- Case 1: All eigenvalues ≥ 0. Since they sum to 0, all are 0.
    have h_all_zero : ∀ i, ev i = 0 := by
      intro i
      have hi := h_all_nonneg i
      -- ev_i ≤ ∑ ev_j = 0 (since all terms non-negative)
      have h2 : ev i ≤ ∑ j, ev j := by
        calc ev i ≤ ev i + ∑ j ∈ Finset.univ.erase i, ev j :=
              le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => h_all_nonneg j))
          _ = ∑ j, ev j := by rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      linarith only [h2, hi, h_sum_zero]
    have h_pos_sum_zero : pos_sum = 0 := by
      have h_max : ∀ i, max 0 (ev i) = 0 := by intro i; rw [h_all_zero i]; simp
      exact Finset.sum_eq_zero (fun i _ => h_max i)
    rw [h_pos_sum_zero, zero_pow (by norm_num : 2 ≠ 0)]
    linarith [h_fid_le]
  · -- Case 2: There exists a negative eigenvalue
    push Not at h_all_nonneg
    obtain ⟨k, h_k_neg⟩ := h_all_nonneg
    -- At most one negative eigenvalue: if β_k > 1/2 for each negative k,
    -- and ∑ β = 1 with β ≥ 0, there can be at most one.
    -- So there is EXACTLY one negative eigenvalue at index k.
    have h_unique_neg : ∀ j, ev j < 0 → j = k := by
      intro j h_j_neg
      by_contra h_ne
      -- Both β_j > 1/2 and β_k > 1/2
      have hj := h_neg_β_gt j h_j_neg
      have hk := h_neg_β_gt k h_k_neg
      -- β_j + β_k > 1
      have h_sum_gt : β j + β k > 1 := by linarith only [hj, hk]
      -- But ∑ β = 1 and all β ≥ 0, so β_j + β_k ≤ 1
      have h_sum_le : β j + β k ≤ ∑ i, β i := by
        have h_rest_nn := Finset.sum_nonneg
          (fun i (_ : i ∈ (Finset.univ.erase j).erase k) => h_β_nonneg i)
        have h_split_j := Finset.add_sum_erase Finset.univ (fun i => β i) (Finset.mem_univ j)
        have h_split_k := Finset.add_sum_erase (Finset.univ.erase j) (fun i => β i)
          (Finset.mem_erase.mpr ⟨Ne.symm h_ne, Finset.mem_univ k⟩)
        linarith only [h_rest_nn, h_split_j, h_split_k]
      linarith only [h_sum_gt, h_sum_le, h_β_sum]
    -- All non-k eigenvalues are ≥ 0
    have h_rest_nonneg : ∀ j, j ≠ k → 0 ≤ ev j := by
      intro j h_ne; by_contra h_neg; push Not at h_neg
      exact h_ne (h_unique_neg j h_neg)
    -- Since trace = 0 and only k is negative: pos_sum = |ev k| = -ev k
    have h_neg_sum : ev k = -(∑ j ∈ Finset.univ.erase k, ev j) := by
      have := h_sum_zero
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at this
      linarith only [this]
    have h_pos_sum_eq : pos_sum = -ev k := by
      -- pos_sum = ∑ max(0, ev_j) = ∑_{j≠k} ev_j + 0 (since ev_k < 0, max(0, ev_k) = 0)
      have h1 : max 0 (ev k) = 0 := max_eq_left (le_of_lt h_k_neg)
      have h2 : ∀ j, j ≠ k → max 0 (ev j) = ev j := by
        intro j h_ne; exact max_eq_right (h_rest_nonneg j h_ne)
      calc pos_sum = ∑ j, max 0 (ev j) := rfl
        _ = max 0 (ev k) + ∑ j ∈ Finset.univ.erase k, max 0 (ev j) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
        _ = 0 + ∑ j ∈ Finset.univ.erase k, ev j := by
            rw [h1]; congr 1
            exact Finset.sum_congr rfl (fun j hj => h2 j (Finset.mem_erase.mp hj).1)
        _ = ∑ j ∈ Finset.univ.erase k, ev j := by ring
        _ = -ev k := by linarith only [h_neg_sum]
    -- β_k ≥ (1 + pos_sum)/2  (from the key bound with ev_k = -pos_sum)
    have h_β_k_bound : (1 + pos_sum) / 2 ≤ β k := by
      have h := h_key_bound k
      rw [h_pos_sum_eq]
      -- ev k * (ev k + 2 * β k - 1) ≤ 0 with ev k < 0
      -- So ev k + 2 * β k - 1 ≥ 0, i.e., β_k ≥ (1 - ev_k)/2
      nlinarith only [h, h_k_neg]
    -- Bound: ∑_{j≠k} ev_j · β_j ≤ pos_sum · (1 - β_k)
    -- Each ev_j ≤ pos_sum (for j ≠ k, ev_j ≥ 0 and ∑_{j≠k} ev_j = pos_sum)
    have h_pos_bound : ∑ j ∈ Finset.univ.erase k, ev j * β j ≤
        pos_sum * (1 - β k) := by
      have h_each_le : ∀ j ∈ Finset.univ.erase k, ev j ≤ pos_sum := by
        intro j hj
        have h_ne := (Finset.mem_erase.mp hj).1
        have h_nn := h_rest_nonneg j h_ne
        calc ev j ≤ ev j + ∑ l ∈ (Finset.univ.erase k).erase j, ev l :=
              le_add_of_nonneg_right (Finset.sum_nonneg (fun l hl =>
                h_rest_nonneg l (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1))
          _ = ∑ l ∈ Finset.univ.erase k, ev l := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h_ne, Finset.mem_univ j⟩)]
          _ = pos_sum := by rw [h_pos_sum_eq]; linarith only [h_neg_sum]
      have h_β_rest_sum : ∑ j ∈ Finset.univ.erase k, β j = 1 - β k := by
        have := h_β_sum
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at this
        linarith only [this]
      calc ∑ j ∈ Finset.univ.erase k, ev j * β j
          ≤ ∑ j ∈ Finset.univ.erase k, pos_sum * β j := by
            apply Finset.sum_le_sum; intro j hj
            exact mul_le_mul_of_nonneg_right (h_each_le j hj)
              (h_β_nonneg j)
        _ = pos_sum * ∑ j ∈ Finset.univ.erase k, β j := by
            rw [Finset.mul_sum]
        _ = pos_sum * (1 - β k) := by rw [h_β_rest_sum]
    -- 1 - F² = -(∑ ev_i β_i) = -ev_k · β_k - ∑_{j≠k} ev_j · β_j
    --        = pos_sum · β_k - ∑_{j≠k} ev_j · β_j
    --        ≥ pos_sum · β_k - pos_sum · (1 - β_k)
    --        = pos_sum · (2β_k - 1) ≥ pos_sum · pos_sum = pos_sum²
    have h_split_sum : ∑ i, ev i * β i =
        ev k * β k + ∑ j ∈ Finset.univ.erase k, ev j * β j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    rw [h_one_sub_fid, h_split_sum]
    -- Goal: pos_sum ^ 2 ≤ -(ev k * β k + ∑ j ∈ ..., ev j * β j)
    rw [h_pos_sum_eq]
    -- Goal: (-ev k) ^ 2 ≤ -(ev k * β k + ∑ ...)
    -- Equivalent to: ev k ^ 2 ≤ -ev k * β k - ∑ ...
    nlinarith [h_pos_bound, h_β_k_bound, h_k_neg, h_β_nonneg k, h_pos_sum_le]

/-- **Quadratic form of `ρ²` on an eigenvector of `A = ρ - σ`.** With `σ² = σ` and `u i` a unit
    `A`-eigenvector of eigenvalue `ev i` and overlap `β i = ⟨u i|σ|u i⟩`, expanding
    `ρ² = A² + Aσ + σA + σ` gives `⟨u i|ρ²|u i⟩ = ev i² + 2·ev i·β i + β i`. -/
private lemma rhoSq_quadraticForm_eigenvector {n : ℕ}
    (ρ σ A : Op n) (u : Fin n → (Fin n → ℂ)) (ev β : Fin n → ℝ)
    (hA_herm : A = Aᴴ) (hA_def : A = ρ - σ) (h_σ_sq : σ * σ = σ)
    (h_orth : ∀ i, star (u i) ⬝ᵥ u i = 1)
    (h_eigen : ∀ i, A.mulVec (u i) = (ev i : ℂ) • u i)
    (h_β_eq : ∀ i, β i = (star (u i) ⬝ᵥ (σ.mulVec (u i))).re) :
    ∀ i, (star (u i) ⬝ᵥ ((ρ * ρ).mulVec (u i))).re =
      ev i ^ 2 + 2 * ev i * β i + β i := by
  intro i
  have h_ρ_split : ρ = A + σ := by rw [hA_def]; abel
  have h_ρ_sq : ρ * ρ = A * A + A * σ + σ * A + σ := by
    rw [h_ρ_split, add_mul, mul_add, mul_add, h_σ_sq]; abel
  rw [h_ρ_sq, add_mulVec, add_mulVec, add_mulVec,
      dotProduct_add, dotProduct_add, dotProduct_add,
      Complex.add_re, Complex.add_re, Complex.add_re]
  have h_A_sq : (star (u i) ⬝ᵥ ((A * A).mulVec (u i))).re = ev i ^ 2 := by
    have h1 : (A * A).mulVec (u i) = ((ev i : ℂ) ^ 2) • u i := by
      rw [← mulVec_mulVec, h_eigen i, mulVec_smul, h_eigen i, smul_smul]
      congr 1; ring
    rw [h1, dotProduct_smul, smul_eq_mul, h_orth i, mul_one]; norm_cast
  have h_σA : (star (u i) ⬝ᵥ ((σ * A).mulVec (u i))).re = ev i * β i := by
    rw [← mulVec_mulVec, h_eigen i, mulVec_smul, dotProduct_smul, smul_eq_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1; exact (h_β_eq i).symm
  have h_Aσ : (star (u i) ⬝ᵥ ((A * σ).mulVec (u i))).re = ev i * β i := by
    rw [← mulVec_mulVec, dotProduct_mulVec]
    rw [hA_herm]
    have h_vecmul_conj : star (u i) ᵥ* Aᴴ = star (A.mulVec (u i)) := by
      ext j
      simp only [vecMul, dotProduct, Pi.star_apply, conjTranspose_apply, mulVec]
      change ∑ k, starRingEnd ℂ (u i k) * starRingEnd ℂ (A j k) =
             starRingEnd ℂ (∑ k, A j k * u i k)
      rw [map_sum]; congr 1; ext k; rw [map_mul]; ring
    rw [h_vecmul_conj, h_eigen i, star_smul, smul_dotProduct, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_ofReal,
               Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1; exact (h_β_eq i).symm
  have h_σ_qf : (star (u i) ⬝ᵥ (σ.mulVec (u i))).re = β i := (h_β_eq i).symm
  linarith [h_A_sq, h_Aσ, h_σA, h_σ_qf]

/-- Helper lemma: For A = ρ - |ψ⟩⟨ψ| where ρ is a density operator and ψ is normalized,
    if A has eigenvalues summing to 0 and pos_sum = Σᵢ max(0, λᵢ), then pos_sum² ≤ 1 - F².

    This requires the secular equation analysis for rank-1 perturbations:
    In the eigenbasis of ρ with eigenvalues {pᵢ} (satisfying 0 ≤ pᵢ ≤ 1, Σpᵢ = 1),
    we can write A = diag(p₁,...,pₙ) - |α⟩⟨α| where |α⟩ = Σᵢ αᵢ|eᵢ⟩ with Σ|αᵢ|² = 1.

    The unique negative eigenvalue μ satisfies the secular equation:
      1 = Σᵢ |αᵢ|²/(pᵢ - μ)

    Setting xᵢ := |αᵢ|²/(pᵢ - μ), we have:
    - Σxᵢ = 1 (secular equation)
    - Σxᵢpᵢ = 1 + μ (from Σ|αᵢ|² = 1)
    - F² = Σpᵢ|αᵢ|² = Σxᵢpᵢ² - μ(1 + μ)

    Therefore: 1 - F² = 1 - Σxᵢpᵢ² + μ + μ² = Σxᵢpᵢ(1-pᵢ) + μ²

    Since xᵢ ≥ 0, pᵢ ≥ 0, and (1-pᵢ) ≥ 0 (as 0 ≤ pᵢ ≤ 1), we get μ² ≤ 1 - F². -/
private lemma rank1_perturbation_pos_sum_bound {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    let σ := DensityOp.fromPure ψ hψ
    let hA := densityOp_sub_isHermitian ρ σ
    let ev := hA.eigenvalues
    let pos_sum := ∑ i, max 0 (ev i)
    pos_sum ^ 2 ≤ 1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
  -- Establish basic facts we'll need
  let σ := DensityOp.fromPure ψ hψ
  let A := ρ.toOp - σ.toOp
  let hA := densityOp_sub_isHermitian ρ σ
  let ev := hA.eigenvalues
  let pos_sum := ∑ i, max 0 (ev i)
  -- Strip let-wrappers from the goal so rw/gcongr work on bare pos_sum
  change pos_sum ^ 2 ≤ 1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ)
  -- Rewrite fidelitySq using fidelitySq_fromPure
  rw [fidelitySq_fromPure]
  -- 1. Eigenvalues sum to 0
  have h_sum_zero : ∑ i, ev i = 0 := densityOp_sub_pure_eigenvalues_sum_zero ρ ψ hψ
  -- 2. Trace of A² relates to fidelity
  have h_trace_sq := densityOp_sub_pure_sq_trace ρ ψ hψ
  simp only [fidelitySq_fromPure] at h_trace_sq
  -- 3. Purity bound: Tr(ρ²) ≤ 1
  have h_purity_le := (DensityOp.purity_bounds ρ).2
  have h_purity_def : ρ.purity = (ρ.toOp * ρ.toOp).trace.re := rfl
  rw [h_purity_def] at h_purity_le
  -- 4. Bound on Tr(A²)
  have h_trace_bound : (A * A).trace.re ≤ 2 - 2 * (ψ.dag * ρ.toOp * ψ).re := by
    calc (A * A).trace.re = (ρ.toOp * ρ.toOp).trace.re + 1 - 2 * (ψ.dag * ρ.toOp * ψ).re :=
          h_trace_sq
      _ ≤ 1 + 1 - 2 * (ψ.dag * ρ.toOp * ψ).re := by linarith only [h_purity_le]
      _ = 2 - 2 * (ψ.dag * ρ.toOp * ψ).re := by ring
  -- === Proof using ρ²≤ρ approach ===
  -- Set up eigenvector machinery for A
  let U := hA.eigenvectorUnitary.val
  have h_UU : U† * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h_UU' : U * U† = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  let u := fun i => (U · i : Fin n → ℂ)
  -- σ.toOp = ψ * ψ.dag (pure state outer product)
  have h_σ_def : σ.toOp = ψ * ψ.dag := rfl
  -- Define β_i = |⟨u_i|ψ⟩|² (overlap of eigenvectors of A with ψ)
  let β := fun i => Complex.normSq (star (u i) ⬝ᵥ ψ.vec)
  -- β_i = ⟨u_i|σ|u_i⟩ (quadratic form of pure state)
  have h_β_eq : ∀ i, β i = (star (u i) ⬝ᵥ (σ.toOp.mulVec (u i))).re := by
    intro i; rw [h_σ_def]; exact (pure_quadratic_form ψ (u i)).symm
  have h_β_nonneg : ∀ i, 0 ≤ β i := fun i => Complex.normSq_nonneg _
  -- ∑ β_i = 1 (eigenvectors form ONB, ψ is normalized)
  have h_β_sum : ∑ i, β i = 1 := by
    have h1 : ∑ i, β i = ∑ i, (star (u i) ⬝ᵥ (σ.toOp.mulVec (u i))).re :=
      Finset.sum_congr rfl (fun i _ => h_β_eq i)
    rw [h1, sum_eigenbasis_quadraticForm_eq_trace σ hA]
    simp [σ.trace_one, Complex.one_re]
  -- ev_i = ⟨u_i|A|u_i⟩ (eigenvector property)
  have h_ev_eq : ∀ i, ev i = (star (u i) ⬝ᵥ (A.mulVec (u i))).re :=
    fun i => (eigenvector_quadraticForm_eq_eigenvalue hA i).symm
  -- q_i := ⟨u_i|ρ|u_i⟩ = ev_i + β_i (since A = ρ - σ)
  have h_q_eq : ∀ i, (star (u i) ⬝ᵥ (ρ.toOp.mulVec (u i))).re = ev i + β i := by
    intro i
    have h_split : ρ.toOp = A + σ.toOp := by simp only [A, sub_add_cancel]
    rw [h_split, add_mulVec, dotProduct_add, Complex.add_re, ← h_ev_eq i, ← h_β_eq i]
  -- q_i ≥ 0 (ρ is PSD)
  have h_q_nonneg : ∀ i, 0 ≤ ev i + β i := by
    intro i; rw [← h_q_eq i]; exact density_quadraticForm_nonneg ρ (u i)
  -- 1 - F² = -∑ ev_i β_i
  have h_one_sub_fid : 1 - (ψ.dag * ρ.toOp * ψ).re = -(∑ i, ev i * β i) := by
    -- F² = ⟨ψ|ρ|ψ⟩ = ⟨ψ|(A+σ)|ψ⟩ = ⟨ψ|A|ψ⟩ + ⟨ψ|σ|ψ⟩
    -- ⟨ψ|A|ψ⟩ = ∑ ev_i β_i (by spectral_quadratic_form_re with ψ as the vector)
    -- ⟨ψ|σ|ψ⟩ = |⟨ψ|ψ⟩|² = 1
    have h_ρ_split : ρ.toOp = A + σ.toOp := by simp only [A, sub_add_cancel]
    -- ⟨ψ|A|ψ⟩ in spectral form
    have h_A_spec := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_A_spec
    have h_ψA : (ψ.dag * A * ψ).re = ∑ i, ev i * β i := by
      have h_eq : ψ.dag * A * ψ = quadraticForm A ψ.vec := by
        rw [braop_mul_ket]
        simp only [bra_mul_ket_eq, op_mul_ket_vec, Ket.dag_vec]
        unfold quadraticForm dotProduct; rfl
      rw [h_eq]; unfold quadraticForm
      -- Unfold the let binding A for rewriting
      change (star ψ.vec ⬝ᵥ (ρ.toOp - σ.toOp).mulVec ψ.vec).re = _
      rw [h_A_spec]
      exact spectral_quadratic_form_re U ev ψ.vec
    -- ⟨ψ|σ|ψ⟩ = 1 (following working pattern from traceDistance_sq_le_one_sub_fidelityPureSq)
    have h_ψσ : (ψ.dag * σ.toOp * ψ).re = 1 := by
      rw [h_σ_def]
      have h2 : ψ.dag * (ψ * ψ.dag) = (ψ.dag * ψ) • ψ.dag := bra_mul_ketbra ψ.dag ψ ψ.dag
      simp only [h2, hψ]
      have h_smul : (1 : ℂ) • ψ.dag = ψ.dag := by ext i; simp [Bra.smul_vec, one_mul]
      simp only [h_smul, hψ, Complex.one_re]
    -- Combine: ρ = A + σ so ⟨ψ|ρ|ψ⟩ = ⟨ψ|A|ψ⟩ + ⟨ψ|σ|ψ⟩
    have h_sum : ψ.dag * ρ.toOp * ψ = ψ.dag * A * ψ + ψ.dag * σ.toOp * ψ := by
      conv_lhs => rw [h_ρ_split]
      rw [braop_mul_ket, add_op_mul_ket, bra_mul_add_ket, ← braop_mul_ket, ← braop_mul_ket]
    have h_re_sum : (ψ.dag * ρ.toOp * ψ).re =
        (ψ.dag * A * ψ).re + (ψ.dag * σ.toOp * ψ).re := by rw [h_sum]; rfl
    linarith [h_re_sum, h_ψA, h_ψσ]
  -- Fidelity bounds
  have h_fid_nn : 0 ≤ (ψ.dag * ρ.toOp * ψ).re := by
    have := fidelityPureSq_nonneg ρ ψ hψ
    rw [fidelitySq_fromPure] at this; exact this
  have h_fid_le : (ψ.dag * ρ.toOp * ψ).re ≤ 1 := by
    have := fidelityPureSq_le_one ρ ψ hψ
    rw [fidelitySq_fromPure] at this; exact this
  have h_pos_sum_le := sum_positive_eigenvalues_le_one ρ σ hA
  -- Key bound from ρ²≤ρ: ⟨u_i|ρ²|u_i⟩ ≤ ⟨u_i|ρ|u_i⟩
  -- Compute: ⟨u_i|ρ²|u_i⟩ = ev_i² + 2·ev_i·β_i + β_i
  -- Using ρ = A + σ, ρ² = A² + Aσ + σA + σ² = A² + Aσ + σA + σ (since σ²=σ)
  have h_σ_sq : σ.toOp * σ.toOp = σ.toOp := by
    rw [h_σ_def, ketbra_mul_ketbra, hψ, one_smul]
  -- Orthonormality of A's eigenvectors: ⟨u_i|u_i⟩ = 1
  have h_orth : ∀ i, star (u i) ⬝ᵥ u i = 1 := by
    intro i
    have h : (U† * U) i i = (1 : Matrix _ _ ℂ) i i := by rw [h_UU]
    simp only [mul_apply, conjTranspose_apply, one_apply, ite_true] at h
    exact h
  -- Quadratic form of ρ² on u_i: ⟨u_i|ρ²|u_i⟩ = ev_i² + 2·ev_i·β_i + β_i
  have h_ρ_sq_qf : ∀ i,
      (star (u i) ⬝ᵥ ((ρ.toOp * ρ.toOp).mulVec (u i))).re =
        ev i ^ 2 + 2 * ev i * β i + β i :=
    rhoSq_quadraticForm_eigenvector ρ.toOp σ.toOp A u ev β hA.symm rfl h_σ_sq h_orth
      (fun i => eigenvector_mulVec_eq hA i) h_β_eq
  -- The key bound: ev_i(ev_i + 2β_i - 1) ≤ 0
  have h_key_bound : ∀ i, ev i * (ev i + 2 * β i - 1) ≤ 0 := by
    intro i
    have h_ρsq_le := density_sq_quadform_le ρ (u i)
    rw [h_ρ_sq_qf i, h_q_eq i] at h_ρsq_le
    -- h_ρsq_le : ev i ^ 2 + 2 * ev i * β i + β i ≤ ev i + β i
    -- Simplifies to: ev i ^ 2 + 2 * ev i * β i ≤ ev i
    -- i.e., ev i * (ev i + 2 * β i - 1) ≤ 0
    nlinarith only [h_ρsq_le]
  exact pos_sum_sq_le_of_key_bounds ev β ((ψ.dag * ρ.toOp * ψ).re)
    h_sum_zero h_β_nonneg h_β_sum h_key_bound h_one_sub_fid h_fid_le h_pos_sum_le

/-- Main inequality in squared form: D² ≤ 1 - F².

    For A = ρ - |ψ⟩⟨ψ| with eigenvalues summing to 0, the trace distance
    D = (1/2)Σ|λᵢ| satisfies D² ≤ 1 - F²(ρ,ψ).

    The proof uses that A is a rank-1 perturbation of the diagonal matrix
    diag(p₁,...,pₙ) (in the eigenbasis of ρ), which constrains the eigenvalue
    structure. Specifically, A has at most one negative eigenvalue, and the
    bound follows from the constraint 0 ≤ pᵢ ≤ 1. -/
lemma traceDistance_sq_le_one_sub_fidelityPureSq {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    traceDistance ρ.toOp (DensityOp.fromPure ψ hψ).toOp ^ 2 ≤
      1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
  -- Set up key objects
  let σ := DensityOp.fromPure ψ hψ
  let A := ρ.toOp - σ.toOp
  let hA := densityOp_sub_isHermitian ρ σ
  let ev := hA.eigenvalues
  -- Established facts:
  -- 1. Eigenvalues of A sum to 0
  have h_sum_zero : ∑ i, ev i = 0 := densityOp_sub_pure_eigenvalues_sum_zero ρ ψ hψ
  -- 2. Tr(A²) = Tr(ρ²) + 1 - 2F²
  have h_trace_sq := densityOp_sub_pure_sq_trace ρ ψ hψ
  -- 3. Tr(ρ²) ≤ 1 (purity bounds)
  have h_purity_le := (DensityOp.purity_bounds ρ).2
  have h_purity_def : ρ.purity = (ρ.toOp * ρ.toOp).trace.re := rfl
  rw [h_purity_def] at h_purity_le
  -- 4. Hence Tr(A²) ≤ 2 - 2F²
  have h_fid_nn := fidelityPureSq_nonneg ρ ψ hψ
  have h_fid_le := fidelityPureSq_le_one ρ ψ hψ
  have h_one_sub_nn : 0 ≤ 1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
    linarith only [h_fid_le]
  have h_td_nn := traceDistance_nonneg ρ.toOp σ.toOp
  -- 6. D = sum of positive eigenvalues (since trace = 0)
  let pos_sum := ∑ i, max 0 (ev i)
  let neg_sum := ∑ i, max 0 (-ev i)
  have h_pos_neg_eq : pos_sum = neg_sum := by
    have h1 : (∑ i, ev i : ℝ) = ∑ i, (max 0 (ev i) - max 0 (-ev i)) := by
      congr 1; ext i
      by_cases hx : 0 ≤ ev i
      · rw [max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), sub_zero]
      · push Not at hx
        rw [max_eq_left (le_of_lt hx), max_eq_right (neg_pos.mpr hx).le, zero_sub, neg_neg]
    rw [h_sum_zero, Finset.sum_sub_distrib] at h1
    linarith only [h1]
  have h_td_eq_pos : traceDistance ρ.toOp σ.toOp = pos_sum := by
    have h_abs_split : ∀ i, |ev i| = max 0 (ev i) + max 0 (-ev i) := by
      intro i
      by_cases hx : 0 ≤ ev i
      · rw [abs_of_nonneg hx, max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), add_zero]
      · push Not at hx
        rw [abs_of_neg hx, max_eq_left (le_of_lt hx), zero_add, max_eq_right (neg_pos.mpr hx).le]
    have h_sum_abs : ∑ i, |ev i| = pos_sum + neg_sum := by
      conv_lhs => rw [show ∑ i, |ev i| = ∑ i, (max 0 (ev i) + max 0 (-ev i)) from
          Finset.sum_congr rfl (fun i _ => h_abs_split i)]
      rw [Finset.sum_add_distrib]
    rw [traceDistance_densityOp_eq_traceNormHermitian ρ σ]
    simp only [traceNormHermitian]
    -- The eigenvalues match by definition
    have h_ev_eq : (densityOp_sub_isHermitian ρ σ).eigenvalues = ev := rfl
    rw [show ∑ i, |(densityOp_sub_isHermitian ρ σ).eigenvalues i| =
        ∑ i, |ev i| from Finset.sum_congr rfl (fun i _ => by rfl)]
    rw [h_sum_abs, h_pos_neg_eq, ← two_mul]
    ring
  -- With h_td_eq_pos, rewrite goal to pos_sum² ≤ 1 - fidelityPureSq
  rw [h_td_eq_pos]
  -- Apply the rank-1 perturbation bound
  exact rank1_perturbation_pos_sum_bound ρ ψ hψ

/-- **Fuchs-van de Graaf equality for two pure states**: D(|φ⟩⟨φ|, |ψ⟩⟨ψ|)² = 1 - F²(φ,ψ).

    When BOTH states are pure, the Fuchs-van de Graaf bound becomes an equality.
    This is stronger than `traceDistance_sq_le_one_sub_fidelityPureSq` which only gives ≤.

    **Mathematical fact**: For pure states |φ⟩ and |ψ⟩:
    - D(|φ⟩⟨φ|, |ψ⟩⟨ψ|) = √(1 - |⟨φ|ψ⟩|²)

    **Proof sketch**:
    For two pure states with overlap c = |⟨φ|ψ⟩|, the difference A = |φ⟩⟨φ| - |ψ⟩⟨ψ|
    lives in a 2D subspace (spanned by |φ⟩ and |ψ⟩), and in this subspace:
    - A is traceless (Tr(A) = 1 - 1 = 0)
    - Eigenvalues are ±√(1 - c²)
    - Trace distance D = (1/2)(2√(1 - c²)) = √(1 - c²)

    Note: The general inequality D² ≤ 1 - F² for arbitrary ρ is NOT an equality.
    Counterexample: ρ = I/2 (maximally mixed), |ψ⟩ = |0⟩ gives
    D = 1/2 but √(1 - F²) = √(1/2) ≈ 0.707. -/
lemma traceDistance_sq_eq_one_sub_fidelityPureSq_pure_pure {n : ℕ} [NeZero n]
    (φ : Ket n) (hφ : (φ.dag * φ) = 1)
    (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    traceDistance (DensityOp.fromPure φ hφ).toOp (DensityOp.fromPure ψ hψ).toOp ^ 2 =
      1 - DensityOp.fidelitySq (DensityOp.fromPure φ hφ) (DensityOp.fromPure ψ hψ) := by
  -- For two pure states, the trace distance has an exact formula
  -- D = √(1 - |⟨φ|ψ⟩|²)
  let ρ := DensityOp.fromPure φ hφ
  let σ := DensityOp.fromPure ψ hψ
  let A := ρ.toOp - σ.toOp
  let hA := densityOp_sub_isHermitian ρ σ
  let ev := hA.eigenvalues
  -- Key facts:
  -- 1. A = |φ⟩⟨φ| - |ψ⟩⟨ψ| has trace 0
  have h_sum_zero : ∑ i, ev i = 0 := densityOp_sub_pure_eigenvalues_sum_zero ρ ψ hψ
  -- 2. For pure ρ = |φ⟩⟨φ|: Tr(ρ²) = 1
  have h_rho_pure : ρ.toOp * ρ.toOp = ρ.toOp := by
    change (φ * φ.dag) * (φ * φ.dag) = φ * φ.dag
    rw [ketbra_mul_ketbra, hφ, one_smul]
  have h_rho_sq_trace : (ρ.toOp * ρ.toOp).trace.re = 1 := by
    rw [h_rho_pure]
    have h := ρ.trace_one
    simp only [Complex.one_re, h]
  -- 3. From densityOp_sub_pure_sq_trace with pure ρ:
  -- Tr(A²) = Tr(ρ²) + 1 - 2F² = 1 + 1 - 2F² = 2(1 - F²)
  have h_trace_sq := densityOp_sub_pure_sq_trace ρ ψ hψ
  rw [fidelitySq_fromPure] at h_trace_sq
  have h_trace_A_sq : (A * A).trace.re = 2 * (1 - (ψ.dag * ρ.toOp * ψ).re) := by
    calc (A * A).trace.re = (ρ.toOp * ρ.toOp).trace.re + 1 - 2 * (ψ.dag * ρ.toOp * ψ).re :=
          h_trace_sq
      _ = 1 + 1 - 2 * (ψ.dag * ρ.toOp * ψ).re := by rw [h_rho_sq_trace]
      _ = 2 * (1 - (ψ.dag * ρ.toOp * ψ).re) := by ring
  -- 4. Upper bound from inequality lemma
  have h_le := traceDistance_sq_le_one_sub_fidelityPureSq ρ ψ hψ
  -- Rewrite h_le in terms of braket form
  rw [fidelitySq_fromPure] at h_le
  have h_fid_nn : 0 ≤ (ψ.dag * ρ.toOp * ψ).re := by
    have := fidelityPureSq_nonneg ρ ψ hψ; rw [fidelitySq_fromPure] at this; exact this
  have h_fid_le : (ψ.dag * ρ.toOp * ψ).re ≤ 1 := by
    have := fidelityPureSq_le_one ρ ψ hψ; rw [fidelitySq_fromPure] at this; exact this
  have h_one_sub_nn : 0 ≤ 1 - (ψ.dag * ρ.toOp * ψ).re := by linarith only [h_fid_le]
  have h_td_nn := traceDistance_nonneg ρ.toOp σ.toOp
  -- Now rewrite goal in terms of braket
  rw [fidelitySq_fromPure]
  -- The proof requires showing that the eigenvalue structure of A = |φ⟩⟨φ| - |ψ⟩⟨ψ|
  -- is exactly {√(1-F²), -√(1-F²), 0, ..., 0} (with n-2 zeros).
  apply le_antisymm h_le
  -- Lower bound: 1 - F² ≤ D². Uses nonneg cross terms to avoid rank theory:
  -- ∑λᵢ² ≤ 2·pos_sum² (from expanding (∑max(0,λᵢ))²), and ∑λᵢ² = 2(1-F²).
  -- Step 1: Tr(A²) = ∑ (ev i)²
  have h_trace_eq_sum_sq : (A * A).trace.re = ∑ i, (ev i) ^ 2 :=
    hermitian_trace_sq_eq_sum_eigenvalues_sq hA
  -- Step 2: ∑ (ev i)² = 2(1-F²)
  have h_sum_sq_eq : ∑ i, (ev i) ^ 2 = 2 * (1 - (ψ.dag * ρ.toOp * ψ).re) := by
    linarith [h_trace_A_sq, h_trace_eq_sum_sq]
  -- Step 3: Express D as pos_sum
  let pos_sum := ∑ i, max 0 (ev i)
  let neg_sum := ∑ i, max 0 (-ev i)
  have h_pos_neg_eq : pos_sum = neg_sum := by
    have h1 : (∑ i, ev i : ℝ) = ∑ i, (max 0 (ev i) - max 0 (-ev i)) := by
      congr 1; ext i
      by_cases hx : 0 ≤ ev i
      · rw [max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), sub_zero]
      · push Not at hx
        rw [max_eq_left (le_of_lt hx), max_eq_right (neg_pos.mpr hx).le, zero_sub, neg_neg]
    rw [h_sum_zero, Finset.sum_sub_distrib] at h1
    linarith only [h1]
  have h_td_eq_pos : traceDistance ρ.toOp σ.toOp = pos_sum := by
    have h_abs_split : ∀ i, |ev i| = max 0 (ev i) + max 0 (-ev i) := by
      intro i
      by_cases hx : 0 ≤ ev i
      · rw [abs_of_nonneg hx, max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), add_zero]
      · push Not at hx
        rw [abs_of_neg hx, max_eq_left (le_of_lt hx), zero_add,
            max_eq_right (neg_pos.mpr hx).le]
    have h_sum_abs : ∑ i, |ev i| = pos_sum + neg_sum := by
      conv_lhs => rw [show ∑ i, |ev i| = ∑ i, (max 0 (ev i) + max 0 (-ev i)) from
          Finset.sum_congr rfl (fun i _ => h_abs_split i)]
      rw [Finset.sum_add_distrib]
    rw [traceDistance_densityOp_eq_traceNormHermitian ρ σ]
    simp only [traceNormHermitian]
    have h_ev_eq : (densityOp_sub_isHermitian ρ σ).eigenvalues = ev := rfl
    rw [show ∑ i, |(densityOp_sub_isHermitian ρ σ).eigenvalues i| =
        ∑ i, |ev i| from Finset.sum_congr rfl (fun i _ => by rfl)]
    rw [h_sum_abs, h_pos_neg_eq, ← two_mul]
    ring
  -- Step 4: ∑ (ev i)² ≤ 2 · pos_sum² via nonneg cross terms
  have h_lower : ∑ i, (ev i) ^ 2 ≤ 2 * pos_sum ^ 2 := by
    have h_split : ∑ i, (ev i) ^ 2 =
        ∑ i, (max 0 (ev i)) ^ 2 + ∑ i, (max 0 (-ev i)) ^ 2 := by
      conv_lhs => rw [show ∑ i, (ev i) ^ 2 = ∑ i, ((max 0 (ev i)) ^ 2 + (max 0 (-ev i)) ^ 2)
        from Finset.sum_congr rfl (fun i _ => by
          by_cases hx : 0 ≤ ev i
          · rw [max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx)]; ring
          · push Not at hx
            rw [max_eq_left (le_of_lt hx), max_eq_right (neg_pos.mpr hx).le]; ring)]
      rw [Finset.sum_add_distrib]
    have h_pos_sq : ∑ i, (max 0 (ev i)) ^ 2 ≤ pos_sum ^ 2 :=
      sum_sq_le_sq_sum_of_nonneg _ (fun i => le_max_left 0 (ev i))
    have h_neg_sq : ∑ i, (max 0 (-ev i)) ^ 2 ≤ neg_sum ^ 2 :=
      sum_sq_le_sq_sum_of_nonneg _ (fun i => le_max_left 0 (-ev i))
    rw [← h_pos_neg_eq] at h_neg_sq
    linarith [h_split]
  -- Step 5: Combine: 2(1-F²) ≤ 2·D², so 1-F² ≤ D²
  rw [h_td_eq_pos]
  linarith [h_sum_sq_eq, h_lower]

/-- Fidelity and trace distance relation (Fuchs-van de Graaf inequality).

    For a pure state σ = |ψ⟩⟨ψ|, the trace distance to ρ is bounded by
    the square root of the infidelity.

    **Proof sketch**: For pure σ = |ψ⟩⟨ψ|, we have:
    - ρ - σ = ρ - |ψ⟩⟨ψ|
    - The eigenvalues of this difference can be computed using the spectral decomposition
    - D(ρ, |ψ⟩⟨ψ|) = (1/2) · Σᵢ|λᵢ| where λᵢ are eigenvalues of ρ - |ψ⟩⟨ψ|
    - F²(ρ,ψ) = ⟨ψ|ρ|ψ⟩
    - The inequality D ≤ √(1-F²) follows from eigenvalue analysis

    **Proof strategy**: Uses spectral decomposition ρ = Σᵢ pᵢ |eᵢ⟩⟨eᵢ| and expresses
    ψ in the eigenbasis. The bound follows from `traceDistance_sq_le_one_sub_fidelityPureSq`
    and `Real.sqrt_le_sqrt`. -/
theorem traceDistance_from_fidelity {n : ℕ} [NeZero n] (ρ : DensityOp n) (ψ : Ket n)
    (hψ : (ψ.dag * ψ) = 1) :
    traceDistance ρ.toOp (DensityOp.fromPure ψ hψ).toOp ≤
      Real.sqrt (1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ)) := by
  -- This is the Fuchs-van de Graaf inequality: D(ρ, |ψ⟩⟨ψ|) ≤ √(1 - F²(ρ,ψ))
  -- Use the squared bound and take square roots
  have h_fsq_nn := fidelityPureSq_nonneg ρ ψ hψ
  have h_fsq_le := fidelityPureSq_le_one ρ ψ hψ
  have h_td_nn := traceDistance_nonneg ρ.toOp (DensityOp.fromPure ψ hψ).toOp
  have h_one_sub_nn : 0 ≤ 1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
    linarith only [h_fsq_le]
  -- Key lemma: D² ≤ 1 - F²
  have h_sq := traceDistance_sq_le_one_sub_fidelityPureSq ρ ψ hψ
  -- Take square roots: D ≤ √(1 - F²)
  -- Since D ≥ 0 and 1 - F² ≥ 0, we have D = √(D²) ≤ √(1 - F²)
  calc traceDistance ρ.toOp (DensityOp.fromPure ψ hψ).toOp
      = Real.sqrt (traceDistance ρ.toOp (DensityOp.fromPure ψ hψ).toOp ^ 2) := by
          rw [Real.sqrt_sq h_td_nn]
    _ ≤ Real.sqrt (1 - DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ)) := by
          apply Real.sqrt_le_sqrt
          exact h_sq

end Quantum.Metrics

end
