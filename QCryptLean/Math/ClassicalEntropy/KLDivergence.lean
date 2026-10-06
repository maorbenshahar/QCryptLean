import QCryptLean.Math.ClassicalEntropy.Entropy

/-!
# Classical KL Divergence — Gibbs inequality, variational principle, entropy product rule

Kullback-Leibler divergence and Shannon entropy structural theorems.

## Main definitions
- `classicalKLDiv`: D(p‖q) = Σᵢ pᵢ log(pᵢ/qᵢ)

## Main statements
- `log_sum_inequality`: D(p‖q) ≥ 0 (Gibbs inequality)
- `classical_gibbs_variational`: H(r) + Σ rᵢ αᵢ ≤ log(Σ exp(αᵢ))
- `shannonEntropy_product`: H(p ⊗ q) = H(p) + H(q)
- `shannonEntropy_2x2_subadditivity`: H(X,Y) ≤ H(X) + H(Y)
-/

noncomputable section

namespace Math.ClassicalEntropy

/-!
## Classical KL Divergence

Kullback-Leibler divergence between probability distributions.
-/

/-- Classical KL divergence between two distributions. -/
def classicalKLDiv {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i)

/-- Classical log-sum inequality: Σᵢ pᵢ log(pᵢ/qᵢ) ≥ 0 for probability distributions.

    This is the classical version of Klein's inequality (Gibbs inequality). -/
theorem log_sum_inequality {k : ℕ} [NeZero k]
    (p q : Fin k → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hq_support : ∀ i, p i > 0 → q i > 0) :
    0 ≤ ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i) := by
  -- Main proof using Jensen's inequality
  -- Let S = {i | p i > 0}
  let S := Finset.univ.filter (fun i => p i ≠ 0)
  -- Helper to extract p i ≠ 0 from i ∈ S
  have hS_mem : ∀ i, i ∈ S ↔ p i ≠ 0 := fun i => by simp [S]
  -- The sum simplifies to Σ_{i ∈ S} p i * log(p i / q i)
  have h_eq : ∑ i, (if p i = 0 then 0 else p i * Real.log (p i / q i)) =
      ∑ i ∈ S, p i * Real.log (p i / q i) := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr
    · ext i; simp [S]
    · intro i _; rfl
  rw [h_eq]
  -- p i * log(p i / q i) = -p i * log(q i / p i)
  have h_rewrite : ∑ i ∈ S, p i * Real.log (p i / q i) =
      -∑ i ∈ S, p i * Real.log (q i / p i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hpi_ne : p i ≠ 0 := (hS_mem i).mp hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi_ne)
    have hqi : 0 < q i := hq_support i hpi
    have h : Real.log (p i / q i) = -Real.log (q i / p i) := by
      rw [Real.log_div (ne_of_gt hpi) (ne_of_gt hqi)]
      rw [Real.log_div (ne_of_gt hqi) (ne_of_gt hpi)]
      ring
    rw [h]
    ring
  rw [h_rewrite]
  -- Now apply Jensen: Σ p_i log(q_i/p_i) ≤ log(Σ p_i * q_i/p_i) = log(Σ q_i) ≤ 0
  rw [neg_nonneg]
  -- Need: Σ_{i ∈ S} p i * log(q i / p i) ≤ 0
  -- By Jensen with concave log: Σ p_i log(x_i) ≤ log(Σ p_i x_i) when Σ p_i = 1
  -- First establish that Σ_{i ∈ S} p_i = 1
  have hS_sum : ∑ i ∈ S, p i = 1 := by
    have h_full : ∑ i, p i = ∑ i ∈ S, p i + ∑ i ∈ (Finset.univ \ S), p i := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff)]
      congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    rw [hp_sum] at h_full
    have h_zero : ∑ i ∈ (Finset.univ \ S), p i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      have : ¬(p i ≠ 0) := fun h => hi ((hS_mem i).mpr h)
      push_neg at this
      exact this
    linarith
  -- Apply Jensen: Σ p_i log(q_i/p_i) ≤ log(Σ p_i * q_i/p_i)
  have hconcave : ConcaveOn ℝ (Set.Ioi 0) Real.log := strictConcaveOn_log_Ioi.concaveOn
  -- All q_i / p_i > 0 for i ∈ S
  have h_in_domain : ∀ i ∈ S, q i / p i ∈ Set.Ioi 0 := by
    intro i hi
    have hpi_ne : p i ≠ 0 := (hS_mem i).mp hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi_ne)
    have hqi : 0 < q i := hq_support i hpi
    exact div_pos hqi hpi
  -- All weights are non-negative
  have h_weights_nonneg : ∀ i ∈ S, 0 ≤ p i := by
    intro i _; exact hp_nonneg i
  -- Jensen gives: Σ p_i log(q_i/p_i) ≤ log(Σ p_i * (q_i/p_i))
  have hJensen := hconcave.le_map_sum h_weights_nonneg hS_sum h_in_domain
  -- Simplify: Σ p_i * (q_i / p_i) = Σ q_i (over S)
  have h_simplify : ∑ i ∈ S, p i * (q i / p i) = ∑ i ∈ S, q i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hpi : p i ≠ 0 := (hS_mem i).mp hi
    field_simp
  -- Weighted average: Σ p_i • (q_i / p_i) = Σ q_i (over S)
  have h_smul_eq : ∑ i ∈ S, p i • (q i / p i) = ∑ i ∈ S, q i := by
    simp only [smul_eq_mul]; exact h_simplify
  -- The sum over S is at most 1
  have h_sum_le : ∑ i ∈ S, q i ≤ 1 := by
    calc ∑ i ∈ S, q i ≤ ∑ i, q i := Finset.sum_le_univ_sum_of_nonneg (fun i => hq_nonneg i)
      _ = 1 := hq_sum
  -- Combine: log(Σ_{S} q_i) ≤ log 1 = 0
  calc ∑ i ∈ S, p i * Real.log (q i / p i)
      = ∑ i ∈ S, p i • Real.log (q i / p i) := by simp only [smul_eq_mul]
    _ ≤ Real.log (∑ i ∈ S, p i • (q i / p i)) := hJensen
    _ = Real.log (∑ i ∈ S, q i) := by rw [h_smul_eq]
    _ ≤ Real.log 1 := Real.log_le_log (by
        have hne : S.Nonempty := by
          by_contra h
          simp only [Finset.not_nonempty_iff_eq_empty] at h
          have : ∑ i ∈ S, p i = 0 := by rw [h]; simp
          rw [hS_sum] at this
          exact one_ne_zero this
        obtain ⟨i, hi⟩ := hne
        apply Finset.sum_pos' (fun j _ => hq_nonneg j)
        have hpi_ne : p i ≠ 0 := (hS_mem i).mp hi
        have hpi : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hpi_ne)
        exact ⟨i, hi, hq_support i hpi⟩
      ) h_sum_le
    _ = 0 := Real.log_one

/-- KL divergence is non-negative (alternate form). -/
theorem classicalKLDiv_nonneg {k : ℕ} [NeZero k]
    (p q : Fin k → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hq_support : ∀ i, p i > 0 → q i > 0) :
    0 ≤ classicalKLDiv p q := by
  unfold classicalKLDiv
  exact log_sum_inequality p q hp_nonneg hq_nonneg hp_sum hq_sum hq_support

/-!
## Helper Lemmas
-/

/-- Characterization: x² = x iff x = 0 or x = 1. -/
lemma sq_eq_self_iff_zero_or_one (x : ℝ) : x^2 = x ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have h' : x * (x - 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h' with hx | hx
    · left; exact hx
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-!
## Product Distributions
-/

/-- Shannon entropy is additive for product distributions.

For probability distributions p : Fin n → ℝ and q : Fin m → ℝ,
the product distribution p × q over Fin (n * m) ≃ Fin n × Fin m
satisfies: H(p × q) = H(p) + H(q)

**Proof**: Uses logarithm property log(xy) = log(x) + log(y). -/
theorem shannonEntropy_product {n m : ℕ} (p : Fin n → ℝ) (q : Fin m → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_nonneg : ∀ j, 0 ≤ q j)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ j, q j = 1) :
    shannonEntropy (fun k : Fin (n * m) =>
      let ⟨i, j⟩ := finProdFinEquiv.symm k
      p i * q j) =
    shannonEntropy p + shannonEntropy q := by
  -- Unfold Shannon entropy as -Σ pᵢ log pᵢ
  rw [shannonEntropy_eq_neg_sum_mul_log,
      shannonEntropy_eq_neg_sum_mul_log,
      shannonEntropy_eq_neg_sum_mul_log]
  -- Convert sum over Fin (n*m) to nested sums using Fintype.sum_prod_type
  -- First reindex through finProdFinEquiv
  have h_reindex : (∑ k : Fin (n * m),
      (let ⟨i, j⟩ := finProdFinEquiv.symm k; p i * q j) *
      Real.log (let ⟨i, j⟩ := finProdFinEquiv.symm k; p i * q j)) =
    ∑ k : Fin n × Fin m, (p k.1 * q k.2) * Real.log (p k.1 * q k.2) := by
    apply Fintype.sum_equiv finProdFinEquiv.symm
    intro k; simp [finProdFinEquiv]
  rw [h_reindex]
  -- Convert product type sum to nested sums
  rw [Fintype.sum_prod_type]
  -- Goal: -∑ᵢ ∑ⱼ (pᵢqⱼ) log(pᵢqⱼ) = -(∑ᵢ pᵢ log pᵢ) - (∑ⱼ qⱼ log qⱼ)
  -- Use log(xy) = log(x) + log(y) when x, y > 0
  -- First, expand log(p i * q j) inside the double sum
  have h_expand : ∑ i : Fin n, ∑ j : Fin m, (p i * q j) * Real.log (p i * q j) =
      ∑ i : Fin n, ∑ j : Fin m, ((p i * q j) * Real.log (p i) + (p i * q j) * Real.log (q j)) := by
    congr 1; ext i; congr 1; ext j
    by_cases hp : p i = 0
    · simp [hp]
    by_cases hq : q j = 0
    · simp [hq]
    have hpi_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hp)
    have hqj_pos : 0 < q j := lt_of_le_of_ne (hq_nonneg j) (Ne.symm hq)
    rw [Real.log_mul (ne_of_gt hpi_pos) (ne_of_gt hqj_pos)]
    ring
  rw [h_expand]
  -- Split the double sum
  simp only [Finset.sum_add_distrib]
  rw [neg_add]
  congr 1
  -- First term: ∑ᵢ ∑ⱼ (p i * q j) * log(p i) = ∑ᵢ p i * log(p i)
  · have h1 : ∑ i : Fin n, ∑ j : Fin m, (p i * q j) * Real.log (p i) =
        ∑ i : Fin n, p i * Real.log (p i) := by
      congr 1; ext i
      -- Goal: ∑ⱼ (p i * q j) * log(p i) = p i * log(p i)
      calc ∑ j : Fin m, (p i * q j) * Real.log (p i)
          = ∑ j : Fin m, p i * Real.log (p i) * q j := by congr 1; ext j; ring
        _ = (p i * Real.log (p i)) * ∑ j : Fin m, q j := by rw [← Finset.mul_sum]
        _ = (p i * Real.log (p i)) * 1 := by rw [hq_sum]
        _ = p i * Real.log (p i) := by ring
    rw [h1]
  -- Second term: ∑ᵢ ∑ⱼ (p i * q j) * log(q j) = ∑ⱼ q j * log(q j)
  · have h2 : ∑ i : Fin n, ∑ j : Fin m, (p i * q j) * Real.log (q j) =
        ∑ j : Fin m, q j * Real.log (q j) := by
      rw [Finset.sum_comm]
      congr 1; ext j
      -- Goal: ∑ᵢ (p i * q j) * log(q j) = q j * log(q j)
      calc ∑ i : Fin n, (p i * q j) * Real.log (q j)
          = ∑ i : Fin n, p i * (q j * Real.log (q j)) := by
            congr 1; ext i; ring
        _ = (∑ i : Fin n, p i) * (q j * Real.log (q j)) := by
            rw [← Finset.sum_mul]
        _ = 1 * (q j * Real.log (q j)) := by rw [hp_sum]
        _ = q j * Real.log (q j) := by ring
    rw [h2]

/-- **Shannon entropy subadditivity for 2×2 joint distribution**

For a joint distribution over X,Y with marginals:
- pX = (px0, px1) where px0 = p00 + p10, px1 = p01 + p11
- pY = (py0, py1) where py0 = p00 + p01, py1 = p10 + p11

We have: H(X,Y) ≤ H(X) + H(Y)

This is equivalent to mutual information I(X;Y) = D_KL(p_XY || p_X ⊗ p_Y) ≥ 0.
-/
theorem shannonEntropy_2x2_subadditivity (p00 p01 p10 p11 : ℝ)
    (h00 : 0 ≤ p00) (h01 : 0 ≤ p01) (h10 : 0 ≤ p10) (h11 : 0 ≤ p11)
    (h_sum : p00 + p01 + p10 + p11 = 1) :
    shannonEntropy ![p00, p01, p10, p11] ≤
      binaryEntropy (p01 + p11) + binaryEntropy (p10 + p11) := by
  -- Gibbs bound for one cell `a` lying below its two marginals `x`, `y`:
  -- `η(a) ≤ -a log x - a log y + (x y - a)`, from `log t ≤ t - 1` at `t = x y / a`.
  have cell : ∀ a x y : ℝ, 0 ≤ a → a ≤ x → a ≤ y →
      Real.negMulLog a ≤ -(a * Real.log x) - a * Real.log y + (x * y - a) := by
    intro a x y ha hax hay
    rcases ha.eq_or_lt with rfl | ha
    · linarith [mul_nonneg hax hay, Real.negMulLog_zero]
    · have hx : 0 < x := ha.trans_le hax
      have hy : 0 < y := ha.trans_le hay
      have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos hx hy) ha)
      rw [Real.log_div (mul_pos hx hy).ne' ha.ne', Real.log_mul hx.ne' hy.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog ha.le
      have hcancel : a * (x * y / a) = x * y := mul_div_cancel₀ (x * y) ha.ne'
      rw [Real.negMulLog]
      linarith
  -- the four cells, against the marginals `P(X = i) = p0i + p1i` and `P(Y = j) = pj0 + pj1`
  have k00 := cell p00 (p00 + p10) (p00 + p01) h00
    (le_add_of_nonneg_right h10) (le_add_of_nonneg_right h01)
  have k01 := cell p01 (p01 + p11) (p00 + p01) h01
    (le_add_of_nonneg_right h11) (le_add_of_nonneg_left h00)
  have k10 := cell p10 (p00 + p10) (p10 + p11) h10
    (le_add_of_nonneg_left h00) (le_add_of_nonneg_right h11)
  have k11 := cell p11 (p01 + p11) (p10 + p11) h11
    (le_add_of_nonneg_left h01) (le_add_of_nonneg_left h10)
  -- the product of the marginals is normalized
  have hprod : (p00 + p10) * (p00 + p01) + (p01 + p11) * (p00 + p01)
      + (p00 + p10) * (p10 + p11) + (p01 + p11) * (p10 + p11) = 1 := by
    linear_combination (p00 + p01 + p10 + p11 + 1) * h_sum
  -- both sides as sums of `η = negMulLog` of nonnegative weights
  have hX0 : 1 - (p01 + p11) = p00 + p10 := by linarith
  have hY0 : 1 - (p10 + p11) = p00 + p01 := by linarith
  simp only [shannonEntropy, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, binaryEntropy,
    hX0, hY0]
  rw [entropyTerm_eq_negMulLog _ h00, entropyTerm_eq_negMulLog _ h01,
    entropyTerm_eq_negMulLog _ h10, entropyTerm_eq_negMulLog _ h11,
    entropyTerm_eq_negMulLog _ (add_nonneg h01 h11),
    entropyTerm_eq_negMulLog _ (add_nonneg h00 h10),
    entropyTerm_eq_negMulLog _ (add_nonneg h10 h11),
    entropyTerm_eq_negMulLog _ (add_nonneg h00 h01)]
  -- sum the four cell bounds: the `log`-weights regroup into the marginal entropies
  simp only [Real.negMulLog] at k00 k01 k10 k11 ⊢
  linarith

/-- **Classical Gibbs variational principle**: For a probability distribution r and reals α,
    H(r) + Σ rᵢ αᵢ ≤ log(Σ exp(αᵢ)).

    Proof: Define qᵢ = exp(αᵢ)/Z. Then D_KL(r‖q) = -H(r) - Σ rᵢ αᵢ + log Z ≥ 0. -/
lemma classical_gibbs_variational {N : ℕ} [NeZero N]
    (r : Fin N → ℝ) (α : Fin N → ℝ)
    (hr_nonneg : ∀ i, 0 ≤ r i) (hr_sum : ∑ i, r i = 1) :
    shannonEntropy r + ∑ i, r i * α i ≤
    Real.log (∑ i, Real.exp (α i)) := by
  -- Define Z = Σ exp(αᵢ) and q = exp(α)/Z (Gibbs distribution)
  set Z := ∑ i, Real.exp (α i) with hZ_def
  have hZ_pos : 0 < Z := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  set q := (fun i => Real.exp (α i) / Z) with hq_def
  have hq_nonneg : ∀ i, 0 ≤ q i := fun i => div_nonneg (Real.exp_pos _).le hZ_pos.le
  have hq_sum : ∑ i, q i = 1 := by
    simp only [hq_def]; rw [← Finset.sum_div]; exact div_self (ne_of_gt hZ_pos)
  have hq_pos : ∀ i, 0 < q i := fun i => div_pos (Real.exp_pos _) hZ_pos
  -- Apply log-sum inequality: D_KL(r‖q) ≥ 0
  have hKL := log_sum_inequality r q hr_nonneg hq_nonneg hr_sum hq_sum
    (fun i _ => hq_pos i)
  -- Key: rewrite each KL term as rᵢ log rᵢ - rᵢ αᵢ + rᵢ log Z
  have hterm : ∀ i, (if r i = 0 then 0 else r i * Real.log (r i / q i)) =
      (if r i = 0 then (0 : ℝ) else r i * Real.log (r i)) +
      (- r i * α i + r i * Real.log Z) := by
    intro i
    by_cases hri : r i = 0
    · simp [hri]
    · simp only [hri, ↓reduceIte]
      have hri_pos : 0 < r i := lt_of_le_of_ne (hr_nonneg i) (Ne.symm hri)
      rw [hq_def, Real.log_div hri_pos.ne' (ne_of_gt (hq_pos i))]
      rw [Real.log_div (Real.exp_pos _).ne' (ne_of_gt hZ_pos)]
      rw [Real.log_exp]; ring
  -- Sum the expanded terms
  simp_rw [hterm, Finset.sum_add_distrib] at hKL
  -- hKL: 0 ≤ Σ(if rᵢ=0 then 0 else rᵢ log rᵢ) + (Σ -rᵢ αᵢ + Σ rᵢ log Z)
  -- Simplify Σ rᵢ log Z = log Z
  have hlogZ : ∑ x, r x * Real.log Z = Real.log Z := by
    rw [← Finset.sum_mul, hr_sum, one_mul]
  rw [hlogZ] at hKL
  -- Simplify Σ -rᵢ αᵢ = -Σ rᵢ αᵢ
  have hneg_sum : ∑ x, -r x * α x = -(∑ x, r x * α x) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext; ring
  rw [hneg_sum] at hKL
  -- Simplify Σ(if rᵢ=0 then 0 else rᵢ log rᵢ) = -shannonEntropy r
  have hH : ∑ x, (if r x = 0 then (0 : ℝ) else r x * Real.log (r x)) =
      -shannonEntropy r := by
    unfold shannonEntropy entropyTerm
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    by_cases hri : r i = 0 <;> simp [hri]
  rw [hH] at hKL
  -- hKL : 0 ≤ -shannonEntropy r + (-Σ rᵢ αᵢ + log Z)
  linarith

end Math.ClassicalEntropy

