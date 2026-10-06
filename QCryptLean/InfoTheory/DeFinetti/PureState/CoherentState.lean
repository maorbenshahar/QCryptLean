import QCryptLean.InfoTheory.DeFinetti.Measure
import QCryptLean.InfoTheory.DistanceBounds.TraceNormContraction
import QCryptLean.Quantum.Channels.CPTP.Basic

/-!
# Coherent States and Dimension Ratio Bound

Definitions, tensor product structure and permutation invariance.  This module
provides the coherent state infrastructure for the pure-state quantum
de Finetti theorem (CKMR 2007). Starting from a unitary g ∈ U(d), the coherent
state |v^g_n⟩ = (g|0⟩)^⊗n is the n-fold tensor power of the first column of g.

## Main definitions
- `coherentStateKet`: The coherent state ket |v^g_n⟩ ∈ (ℂᵈ)^⊗n
- `coherentSingleCopy`: The single-copy pure state |g₀⟩⟨g₀|
- `coherentStateDensityOp`: The density operator |v^g_n⟩⟨v^g_n|

## Main statements
- `dim_ratio_bound`: 1 - dk/n ≤ C(n-k+d-1,d-1) / C(n+d-1,d-1)
- `coherentStateKet_normalized`: ⟨v^g|v^g⟩ = 1
- `coherentState_perm_invariant`: Coherent states are permutation invariant
- `coherentState_is_tensorPow`: |v^g_n⟩⟨v^g_n| = (|g₀⟩⟨g₀|)^⊗n
- `partialTraceToFirstK_coherent`: Partial trace of coherent state = coherent state on fewer copies

## References
- Christandl, König, Mitchison, Renner (2007) "One-and-a-Half Quantum de Finetti
  Theorems", Comm. Math. Phys. 273(2), 473-498
- Harrow (2013) "The Church of the Symmetric Subspace", arXiv:1308.6595
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Symmetry MeasureTheory
open Math.HaarMeasure
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

-- Matrix-valued Bochner integration requires a NormedAddCommGroup instance.
-- Frobenius norm provides this for Op n = Matrix (Fin n) (Fin n) ℂ.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.DeFinetti.PureState

/-- The ratio of binomial coefficients equals a falling product:
    C(n-k+d-1,d-1) / C(n+d-1,d-1) = ∏_{i=0}^{d-2} (n-k+1+i)/(n+1+i).

    Each factor in the numerator decreases by k relative to the denominator,
    giving an explicit expression suitable for bounding. -/
lemma choose_ratio_eq_prod (d n k : ℕ) (hd : 1 ≤ d) (hk : k ≤ n) :
    (Nat.choose (n - k + d - 1) (d - 1) : ℝ) / Nat.choose (n + d - 1) (d - 1) =
      (Finset.range (d - 1)).prod (fun i => ((n - k + 1 + i : ℝ) / (n + 1 + i))) := by
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  simp only [show r + 1 - 1 = r from by omega]
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : n - k + (r + 1 + 1) - 1 = (n - k + r + 1) := by omega
    have h2 : n + (r + 1 + 1) - 1 = (n + r + 1) := by omega
    rw [h1, h2, Finset.prod_range_succ]
    have ih' := ih (by omega)
    have h3 : n - k + (r + 1) - 1 = n - k + r := by omega
    have h4 : n + (r + 1) - 1 = n + r := by omega
    rw [h3, h4] at ih'
    rw [← ih']
    -- Pascal's rule `(m+1)·C(m, r) = C(m+1, r+1)·(r+1)`, solved for `C(m+1, r+1)` over `ℝ`,
    -- in the numerator (`m = n-k+r`) and the denominator (`m = n+r`)
    have hr : ((r + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.succ_ne_zero
    have eqA : (↑((n - k + r + 1).choose (r + 1)) : ℝ) =
        ↑(n - k + r + 1) * ↑((n - k + r).choose r) / ↑(r + 1 : ℕ) :=
      eq_div_of_mul_eq hr (by exact_mod_cast (Nat.add_one_mul_choose_eq (n - k + r) r).symm)
    have eqB : (↑((n + r + 1).choose (r + 1)) : ℝ) =
        ↑(n + r + 1) * ↑((n + r).choose r) / ↑(r + 1 : ℕ) :=
      eq_div_of_mul_eq hr (by exact_mod_cast (Nat.add_one_mul_choose_eq (n + r) r).symm)
    have cast1 : (↑(n - k + r + 1) : ℝ) = ↑n - ↑k + 1 + ↑r := by
      rw [show (n - k + r + 1 : ℕ) = (n - k) + (r + 1) from by omega,
          Nat.cast_add, Nat.cast_sub hk]; push_cast; ring
    have cast2 : (↑(n + r + 1) : ℝ) = ↑n + 1 + ↑r := by push_cast; ring
    -- the common `1/(r+1)` cancels, leaving the previous ratio times the new factor
    rw [eqA, eqB, div_div_div_cancel_right₀ hr, mul_div_mul_comm, mul_comm, cast1, cast2]

/-- Each factor in the product is at least (n-k+1)/(n+1).
    Since (n-k+1+i)/(n+1+i) is increasing in i (for fixed n,k), the minimum
    is attained at i=0. -/
lemma ratio_factor_lower_bound (n k i : ℕ) (hk : k ≤ n) :
    (n - k + 1 : ℝ) / (n + 1) ≤ (n - k + 1 + i : ℝ) / (n + 1 + i) := by
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ↑n + 1)
    (by positivity : (0:ℝ) < ↑n + 1 + ↑i)]
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg' i
  have hk' : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk
  nlinarith

/-!
## Section 1: Dimension Ratio Bound

Pure combinatorics: the ratio C(n-k+d-1,d-1) / C(n+d-1,d-1) is at least 1 - dk/n.
This controls how close the post-measurement state is to the coherent state.
-/

/-- **Dimension ratio bound** (CKMR, used in Theorem II.2 proof).
    1 - dk/n ≤ C(n-k+d-1,d-1) / C(n+d-1,d-1).

    Proof: Each of the (d-1) factors is ≥ (n-k+1)/(n+1) = 1 - k/(n+1),
    so the product is ≥ (1 - k/(n+1))^{d-1} ≥ 1 - (d-1)k/(n+1) ≥ 1 - (d-1)k/n ≥ 1 - dk/n. -/
theorem dim_ratio_bound (d n k : ℕ) (hd : 1 ≤ d) (hn : 0 < n) (hk : k ≤ n) :
    1 - (d * k : ℝ) / n ≤
      (Nat.choose (n - k + d - 1) (d - 1) : ℝ) / Nat.choose (n + d - 1) (d - 1) := by
  -- The proof shows 1 - (d-1)k/n ≤ ratio, then relaxes to 1 - dk/n ≤ ratio
  suffices h : 1 - ((d - 1) * k : ℝ) / n ≤
      (Nat.choose (n - k + d - 1) (d - 1) : ℝ) / Nat.choose (n + d - 1) (d - 1) by
    have hk_nn : (0 : ℝ) ≤ (↑k : ℝ) := Nat.cast_nonneg k
    have : (↑d - 1 : ℝ) * ↑k ≤ (↑d : ℝ) * ↑k :=
      mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) hk_nn
    have : (↑d - 1 : ℝ) * ↑k / (↑n : ℝ) ≤ ↑d * ↑k / ↑n :=
      div_le_div_of_nonneg_right this (Nat.cast_nonneg n)
    linarith
  rw [choose_ratio_eq_prod d n k hd hk]
  set x := (↑n - ↑k + 1 : ℝ) / (↑n + 1) with hx_def
  have hn_pos : (0 : ℝ) < ↑n + 1 := by positivity
  have hk_cast : (↑k : ℝ) ≤ ↑n := Nat.cast_le.mpr hk
  have hx_nonneg : 0 ≤ x := div_nonneg (by linarith only [hk_cast]) hn_pos.le
  -- Step 1: Product ≥ x^(d-1) since each factor ≥ x
  have hprod_lb : x ^ (d - 1) ≤
      (Finset.range (d - 1)).prod (fun i => ((↑n - ↑k + 1 + ↑i : ℝ) / (↑n + 1 + ↑i))) := by
    rw [show x ^ (d - 1) = (Finset.range (d - 1)).prod (fun _ => x) from
      by rw [Finset.prod_const, Finset.card_range]]
    apply Finset.prod_le_prod (f := fun _ => x)
    · intro i _; exact hx_nonneg
    · intro i _; exact ratio_factor_lower_bound n k i hk
  -- Step 2: x - 1 = -k/(n+1)
  have hx_sub : x - 1 = -(↑k : ℝ) / (↑n + 1) := by
    simp only [hx_def]
    rw [div_sub_one hn_pos.ne']
    ring
  -- Step 3: Bernoulli's inequality: 1 + (d-1)*(x-1) ≤ x^(d-1)
  have hbernoulli : 1 + ↑(d - 1) * (x - 1) ≤ x ^ (d - 1) :=
    one_add_mul_sub_le_pow
      (show (-1 : ℝ) ≤ x by linarith) (d - 1)
  -- Step 4: Bridge ↑(d-1) and (↑d - 1 : ℝ)
  have hcast : (↑(d - 1) : ℝ) = ↑d - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  have hn_pos' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  -- Step 5: 1 - (d-1)k/n ≤ 1 + (d-1)(x-1) = 1 - (d-1)k/(n+1)
  -- because k/(n+1) ≤ k/n (bigger denominator → smaller fraction)
  have hchain : 1 - (↑d - 1 : ℝ) * ↑k / ↑n ≤ 1 + ↑(d - 1) * (x - 1) := by
    rw [hx_sub, hcast]
    -- Goal: 1 - (↑d-1)*↑k/↑n ≤ 1 + (↑d-1)*(-↑k/(↑n+1))
    -- Normalize: (↑d-1)*(-↑k/(↑n+1)) = -((↑d-1)*↑k/(↑n+1))
    have key : (↑d - 1 : ℝ) * (-↑k / (↑n + 1)) = -((↑d - 1) * ↑k / (↑n + 1)) := by ring
    rw [key]
    -- Goal: 1 - (↑d-1)*↑k/↑n ≤ 1 - (↑d-1)*↑k/(↑n+1)
    -- i.e., (↑d-1)*↑k/(↑n+1) ≤ (↑d-1)*↑k/↑n (bigger denominator → smaller fraction)
    have hineq : (↑d - 1 : ℝ) * ↑k / (↑n + 1) ≤ (↑d - 1) * ↑k / ↑n := by
      have hd_ge : (0 : ℝ) ≤ (↑d : ℝ) - 1 := by rw [← hcast]; exact Nat.cast_nonneg' (d - 1)
      exact div_le_div_of_nonneg_left (mul_nonneg hd_ge (Nat.cast_nonneg' k)) hn_pos'
        (le_add_of_nonneg_right zero_le_one)
    exact sub_le_sub_left hineq 1
  -- Chain: 1-(d-1)k/n ≤ 1+(d-1)(x-1) ≤ x^(d-1) ≤ prod
  exact hchain.trans (hbernoulli.trans hprod_lb)

/-- The dimension ratio is at most `1`.

    This is the monotonicity half of the binomial-ratio control used in the CKMR
    approximation argument. -/
lemma dim_ratio_le_one {d n k : ℕ} (hk : k ≤ n) :
    (Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
      Nat.choose (n + d - 1) (d - 1) ≤ 1 := by
  rw [div_le_one (by exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1))]
  exact_mod_cast Nat.choose_le_choose (d - 1) (by omega)

/-!
## Section 2: Coherent States

A coherent state |v^g_n⟩ for g ∈ U(d) is the tensor product state (g|0⟩)^⊗n.
These form an overcomplete basis for the symmetric subspace when integrated
over the Haar measure on U(d).
-/

/-- The coherent state ket |v^g_n⟩ ∈ (ℂᵈ)^⊗n for g ∈ U(d).

    This is the n-fold tensor product of g|0⟩ (first column of g).
    The entry at multi-index f : Fin n → Fin d is ∏ⱼ g_{f(j),0}.

    We encode multi-indices via `Fin.val` and digit extraction in big-endian
    order to match `tensorPowGen`: the j-th component of the multi-index for
    i : Fin (d^n) is (i / d^(n-1-j)) % d. This way tensor factor 0 (the
    outermost in `tensorPowGen`) corresponds to the most significant digit.

    **Reference**: CKMR definetti.tex line 346. -/
noncomputable def coherentStateKet {d : ℕ} [NeZero d]
    (g : unitaryGroup (Fin d) ℂ) (n : ℕ) [NeZero n] : Ket (d ^ n) :=
  ⟨fun i =>
    -- Decode i : Fin (d^n) as a multi-index f : Fin n → Fin d (big-endian)
    -- f(j) = (i.val / d^(n-1-j)) % d, matching tensorPowGen convention
    ∏ j : Fin n, (g : Matrix (Fin d) (Fin d) ℂ)
      ⟨(i.val / d ^ (n - 1 - j.val)) % d,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩ 0⟩

/-- Big-endian digit extraction matches `finFunctionFinEquiv.symm` with reversed index:
    the j-th digit of x in base d (big-endian) equals `finFunctionFinEquiv.symm x (Fin.rev j)`.
    This bridges the explicit digit formula in `coherentStateKet` with the
    `Fin n → Fin d` multi-index used by `tensorPowGen`. -/
lemma bigEndian_digit_eq_finFunctionFinEquiv {d n : ℕ} (hd_pos : 0 < d)
    (x : Fin (d ^ n)) (j : Fin n) :
    (⟨x.val / d ^ (n - 1 - j.val) % d, Nat.mod_lt _ hd_pos⟩ : Fin d) =
      finFunctionFinEquiv.symm x (Fin.rev j) := by
  ext
  simp only [finFunctionFinEquiv_symm_apply_val, Fin.val_rev]
  congr 1
  rw [Nat.sub_sub]
  ring_nf

/-- The coherent state ket is normalized: ⟨v^g|v^g⟩ = 1.
    Follows from unitarity of g: each factor has |g_{i,0}|² summing to 1. -/
lemma coherentStateKet_normalized {d : ℕ} [NeZero d]
    (g : unitaryGroup (Fin d) ℂ) (n : ℕ) [NeZero n] :
    (coherentStateKet g n).dag * coherentStateKet g n = 1 := by
  -- Unfold to ∑_x conj(∏_j g_{digit(x,j), 0}) * ∏_j g_{digit(x,j), 0}
  simp only [bra_mul_ket_eq, coherentStateKet, Ket.dag]
  -- Distribute conj into product and combine: ∑_x ∏_j (conj(g_{..}) * g_{..})
  simp_rw [map_prod, ← Finset.prod_mul_distrib]
  -- Unitarity: ∑_a conj(g_{a,0}) * g_{a,0} = 1 (column 0 is unit vector)
  have hunit : ∑ a : Fin d,
      (starRingEnd ℂ) ((g : Matrix (Fin d) (Fin d) ℂ) a 0) *
        (g : Matrix (Fin d) (Fin d) ℂ) a 0 = 1 := by
    have hU := UnitaryGroup.star_mul_self g
    have h00 := congr_fun (congr_fun hU 0) 0
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h00
    exact h00
  -- Key step: the sum over Fin(d^n) of products equals (∑_a h(a))^n = 1^n = 1
  -- by reindexing via finFunctionFinEquiv and using Fintype.prod_sum
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  simp_rw [bigEndian_digit_eq_finFunctionFinEquiv hd_pos]
  -- Reindex inner product: ∏_j f(Fin.rev j) = ∏_j f(j) (reversal is a bijection)
  -- Reindex: ∏_j f(j.rev) = ∏_j f(j) (reversal is a bijection on Fin n)
  set gm := (g : Matrix (Fin d) (Fin d) ℂ) with hgm
  have hprod_rev : ∀ (x : Fin (d ^ n)),
      (∏ j : Fin n,
        (starRingEnd ℂ) (gm (finFunctionFinEquiv.symm x j.rev) 0) *
          gm (finFunctionFinEquiv.symm x j.rev) 0) =
      (∏ j : Fin n,
        (starRingEnd ℂ) (gm (finFunctionFinEquiv.symm x j) 0) *
          gm (finFunctionFinEquiv.symm x j) 0) := by
    intro x
    refine Finset.prod_equiv Fin.revPerm (by simp) (fun j _ => ?_)
    simp [Fin.revPerm_apply]
  simp_rw [hprod_rev]
  -- Reindex outer sum: ∑_{x:Fin(d^n)} F(equiv.symm x) = ∑_{f:Fin n→Fin d} F(f)
  have hreindex := Equiv.sum_comp finFunctionFinEquiv.symm
      (fun f : Fin n → Fin d => ∏ j : Fin n,
        (starRingEnd ℂ) (gm (f j) 0) * gm (f j) 0)
  rw [hreindex]
  -- Apply Fintype.prod_sum: ∑_f ∏_j h(f(j)) = ∏_j (∑_a h(a))
  rw [← Fintype.prod_sum (f := fun (_ : Fin n) (a : Fin d) =>
      (starRingEnd ℂ) (gm a 0) * gm a 0)]
  -- Each factor = 1 by unitarity
  simp [hunit]

/-- The single-copy pure state |g₀⟩⟨g₀| where g₀ is the first column of g ∈ U(d). -/
noncomputable def coherentSingleCopy {d : ℕ} [NeZero d]
    (g : unitaryGroup (Fin d) ℂ) : DensityOp d :=
  DensityOp.fromPure
    (⟨fun i => (g : Matrix (Fin d) (Fin d) ℂ) i 0⟩ : Ket d)
    (by
      simp only [bra_mul_ket_eq, Ket.dag]
      have hU := UnitaryGroup.star_mul_self g
      have h00 := congr_fun (congr_fun hU 0) 0
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h00
      exact h00)

/-- The map `g ↦ coherentSingleCopy g` is measurable from `U(d)` to `DensityOp d`. -/
lemma coherentSingleCopy_measurable {d : ℕ} [NeZero d] :
    Measurable (fun g : unitaryGroup (Fin d) ℂ => coherentSingleCopy g) := by
  apply Continuous.measurable
  have hcont : Continuous (fun g : unitaryGroup (Fin d) ℂ => (coherentSingleCopy g).toOp) := by
    apply continuous_matrix
    intro i j
    simp only [coherentSingleCopy, DensityOp.fromPure, Ket.dag]
    apply Continuous.mul
    · exact continuous_subtype_val.matrix_elem i 0
    · apply Continuous.comp continuous_star
      exact continuous_subtype_val.matrix_elem j 0
  exact continuous_induced_rng.mpr hcont

/-- The coherent state density operator |v^g_n⟩⟨v^g_n| as a DensityOp. -/
noncomputable def coherentStateDensityOp {d : ℕ} [NeZero d]
    (g : unitaryGroup (Fin d) ℂ) (n : ℕ) [NeZero n] :
    DensityOp (d ^ n) :=
  DensityOp.fromPure (coherentStateKet g n) (coherentStateKet_normalized g n)

/-- Coherent states are permutation invariant.
    Since |v^g⟩ = (g|0⟩)^⊗n, any permutation of tensor factors leaves it unchanged. -/
lemma coherentState_perm_invariant {d n : ℕ} [NeZero d] [NeZero n]
    (g : unitaryGroup (Fin d) ℂ) :
    IsPermutationInvariant (coherentStateDensityOp g n) := by
  -- Proof: U_σ|v⟩ = |v⟩ (product state invariant under factor permutation),
  -- then U_σ|v⟩⟨v|U_σ† = |v⟩⟨v|.
  unfold IsPermutationInvariant
  intro σ
  set v := coherentStateKet g n
  set U := Math.RepresentationTheory.permutationRepresentation d n σ
  change U * (v * v.dag) * U† = v * v.dag
  -- Step 1: Reduce U(vv†)U† = vv† to U*v = v using ket-bra algebra
  suffices hUv : U * v = v by
    rw [op_mul_ketbra U v v.dag, ketbra_mul_op (U * v) v.dag U†, hUv]
    congr 1
    -- Show v.dag * U† = v.dag (dual of hUv)
    ext i
    simp only [Ket.dag]
    change ∑ x, (starRingEnd ℂ) (v.vec x) * (starRingEnd ℂ) (U i x) = (starRingEnd ℂ) (v.vec i)
    rw [show ∑ x, (starRingEnd ℂ) (v.vec x) * (starRingEnd ℂ) (U i x) =
        (starRingEnd ℂ) (∑ x, U i x * v.vec x) from by
      rw [map_sum]; congr 1; ext x; rw [map_mul, mul_comm]]
    congr 1
    exact congr_fun (congr_arg Ket.vec hUv) i
  -- Step 2: Prove U_σ * v = v (permutation acts trivially on product state)
  ext ⟨i, hi⟩
  simp only [op_mul_ket_vec, Matrix.mulVec, dotProduct]
  simp only [v, coherentStateKet, U, Math.RepresentationTheory.permutationRepresentation,
    Matrix.of_apply]
  set e := @finFunctionFinEquiv d n
  set f_i := e.symm ⟨i, hi⟩
  set x₀ := e (f_i ∘ ⇑σ) with hx₀_def
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  -- Collapse permutation matrix sum to single nonzero term at x₀
  rw [Finset.sum_eq_single x₀]
  · -- Main term: the if-condition holds, giving 1 * prod = prod at x₀
    simp only [show e.symm x₀ = f_i ∘ ⇑σ from by simp [x₀],
      show (f_i ∘ ⇑σ) ∘ ⇑σ.symm = f_i from by ext k; simp,
      if_true, one_mul]
    -- Remaining: ∏_j g(digit(x₀, j), 0) = ∏_j g(digit(i, j), 0)
    -- Both equal ∏_m g(f_i(m), 0) by reindexing via Fin.rev and σ
    -- Convert digit extraction to finFunctionFinEquiv
    conv_lhs =>
      arg 2; ext j
      rw [show (⟨↑(e (f_i ∘ ⇑σ)) / d ^ (n - 1 - ↑j) % d, _⟩ : Fin d) =
          finFunctionFinEquiv.symm (e (f_i ∘ ⇑σ)) (Fin.rev j) from
            bigEndian_digit_eq_finFunctionFinEquiv hd_pos _ j]
    conv_rhs =>
      arg 2; ext j
      rw [show (⟨i / d ^ (n - 1 - ↑j) % d, _⟩ : Fin d) =
          finFunctionFinEquiv.symm ⟨i, hi⟩ (Fin.rev j) from
            bigEndian_digit_eq_finFunctionFinEquiv hd_pos ⟨i, hi⟩ j]
    -- Simplify: e = finFunctionFinEquiv, so e.symm (e (f_i ∘ σ)) = f_i ∘ σ
    simp only [e, Equiv.symm_apply_apply,
      Function.comp_apply, f_i]
    -- Goal: ∏ x, g(f_i(σ(x.rev))) 0 = ∏ j, g(f_i(j.rev)) 0
    -- Both sides equal ∏_m g(f_i(m)) 0 by reindexing
    trans ∏ m : Fin n, (g : Matrix (Fin d) (Fin d) ℂ) (finFunctionFinEquiv.symm ⟨i, hi⟩ m) 0
    · exact Finset.prod_equiv (Fin.revPerm.trans σ) (fun _ => by simp)
        (fun j _ => by simp [Fin.revPerm_apply, Equiv.trans_apply])
    · symm
      exact Finset.prod_equiv Fin.revPerm (fun _ => by simp)
        (fun j _ => by simp [Fin.revPerm_apply])
  · -- Other terms vanish (permutation matrix has at most one nonzero entry per row)
    intro x _ hx
    simp only [ite_mul, one_mul, zero_mul]
    rw [if_neg]
    intro h; exact hx (show x = x₀ by
      have heq : e.symm x = f_i ∘ ⇑σ := by
        funext k
        have h1 := congr_fun h (σ k)
        simp only [Function.comp_apply, Equiv.symm_apply_apply] at h1
        exact h1.symm
      calc x = e (e.symm x) := (e.apply_symm_apply x).symm
        _ = e (f_i ∘ ⇑σ) := by rw [heq])
  · intro h; exact absurd (Finset.mem_univ _) h

lemma coherentState_is_tensorPow {d n : ℕ} [NeZero d] [NeZero n]
    (g : unitaryGroup (Fin d) ℂ) :
    (coherentStateDensityOp g n).toOp =
      ((coherentSingleCopy g).tensorPowGen n).toOp := by
  ext i j
  -- RHS: use tensorPowGen_toOp_eq_prod to get product formula
  have hRHS := tensorPowGen_toOp_eq_prod (coherentSingleCopy g)
    (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j)
  simp only [Equiv.apply_symm_apply] at hRHS
  rw [hRHS]; clear hRHS
  -- Goal: (coherentStateDensityOp g n).toOp i j = ∏ k, (coherentSingleCopy g).toOp (fi k) (fj k)
  -- LHS: unfold to ket * bra
  simp only [coherentStateDensityOp, DensityOp.fromPure]
  -- Goal: (ket * ket.dag) i j = ∏ k, ρ(fi k)(fj k)
  -- LHS = ket.vec i * conj(ket.vec j)
  -- ket.vec i = ∏_l g_{digit(i,l), 0}
  -- ρ(a)(b) = g_{a,0} * conj(g_{b,0})
  -- RHS = ∏_k g_{fi(k),0} * conj(g_{fj(k),0}) = (∏ g_{fi(k),0}) * (∏ conj(g_{fj(k),0}))
  simp only [ket_mul_bra_apply, Ket.dag_vec,
    coherentStateKet, coherentSingleCopy, DensityOp.fromPure]
  -- Goal: (∏ j, g_{digit(i,j), 0}) * conj(∏ j, g_{digit(j,j), 0})
  --     = ∏ x, g_{fi(x), 0} * conj(g_{fj(x), 0})
  -- Step 1: Distribute conj over product
  rw [map_prod]
  -- Step 2: Combine products
  rw [← Finset.prod_mul_distrib]
  -- Step 3: Relate big-endian digit extraction to finFunctionFinEquiv.symm
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  simp_rw [bigEndian_digit_eq_finFunctionFinEquiv hd_pos]
  -- Step 4: Reindex via Fin.revPerm: ∏_k f(k.rev) = ∏_k f(k)
  refine Finset.prod_equiv Fin.revPerm (fun _ => by simp) (fun k _ => ?_)
  simp [Fin.revPerm_apply]

/-- Partial trace of coherent states: Tr_{k+1..n}[|v^g_n⟩⟨v^g_n|] = |v^g_k⟩⟨v^g_k|.
    Tracing out the last n-k copies of a product state yields the first k copies.

    Follows from `coherentState_is_tensorPow` and
    `InfoTheory.DeFinetti.partialTraceToFirstK_tensorPowGen`. -/
lemma partialTraceToFirstK_coherent {d n : ℕ} [NeZero d] [NeZero n]
    (g : unitaryGroup (Fin d) ℂ) (k : ℕ) [NeZero k] (hk : k ≤ n) :
    InfoTheory.DeFinetti.partialTraceToFirstK k hk (coherentStateDensityOp g n) =
      coherentStateDensityOp g k := by
  -- Reduce to tensorPowGen via coherentState_is_tensorPow
  have heq_n : coherentStateDensityOp g n = (coherentSingleCopy g).tensorPowGen n :=
    DensityOp.ext (coherentState_is_tensorPow g)
  have heq_k : coherentStateDensityOp g k = (coherentSingleCopy g).tensorPowGen k :=
    DensityOp.ext (coherentState_is_tensorPow g)
  rw [heq_n, InfoTheory.DeFinetti.partialTraceToFirstK_tensorPowGen (coherentSingleCopy g) n k hk]
  exact heq_k.symm

end InfoTheory.DeFinetti.PureState
