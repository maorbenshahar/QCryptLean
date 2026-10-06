import QCryptLean.InfoTheory.DeFinetti.PureState.SchurLemma.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Haar Moment Vanishing and Coherent State Separation — torus arguments, DFT, polynomial vanishing

This module establishes the Haar moment vanishing lemmas (off-diagonal moments
integrate to zero by invariance under diagonal phase rotations), the polynomial
and torus-monomial independence arguments, and the key `coherent_states_separate_symn`
theorem: coherent states span the symmetric subspace.

These results form the technical backbone of the irreducibility argument used
in the Schur lemma proof.

## Main statements
- `haar_product_vanishing_first_col`: ∫ k₀₀ⁿ · ∏ conj(k_{p(i),0}) dk = 0 when some p(i) ≠ 0
- `monomial_indep_torus`: multivariate monomial independence on the d-torus
- `exists_unitary_nonzero_first_col`: DFT matrix has nonzero first column
- `coherent_states_separate_symn`: if w ∈ Sym^n and ⟨w, v_g⟩ = 0 for all g, then w = 0

## References
- Christandl, König, Mitchison, Renner (2007), Comm. Math. Phys. 273(2), 473-498
- Harrow (2013) "The Church of the Symmetric Subspace", arXiv:1308.6595 §3
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Symmetry MeasureTheory
open Math.HaarMeasure
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.DeFinetti.PureState

/-- A diagonal matrix with entries on the unit circle is unitary. -/
lemma diagonal_unitCircle_mem_unitary {d : ℕ} (f : Fin d → ℂ)
    (hf : ∀ i, ‖f i‖ = 1) :
    Matrix.diagonal f ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', show star (Matrix.diagonal f) = (Matrix.diagonal f)ᴴ from rfl]
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i k
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h; simp only [Pi.star_apply]
    have := Complex.mul_conj' (f i)
    rw [starRingEnd_apply] at this
    rw [mul_comm, this, hf i]; simp
  · rfl

/-- Left-multiplying by a diagonal unitary transforms the (i,0) entry by f i. -/
lemma diagonal_mul_entry {d : ℕ} (f : Fin d → ℂ)
    (k : unitaryGroup (Fin d) ℂ)
    (hf : ∀ i, ‖f i‖ = 1) (i : Fin d) (c : Fin d) :
    (⟨Matrix.diagonal f, diagonal_unitCircle_mem_unitary f hf⟩ *
      k : unitaryGroup (Fin d) ℂ).val i c = f i * k.val i c := by
  change (Matrix.diagonal f * k.val) i c = _
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

/-- If m > 0 and ω = exp(2πi/(m+1)), then conj(ω)^m ≠ 1. Used in Haar torus vanishing. -/
lemma conj_primitive_root_pow_ne_one (m : ℕ) (hm : 0 < m) :
    (starRingEnd ℂ (Complex.exp (↑(2 * Real.pi / (↑m + 1)) * Complex.I))) ^ m ≠ 1 := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      ← Complex.exp_nat_mul]
  intro h_abs
  rw [Complex.exp_eq_one_iff] at h_abs
  obtain ⟨k, hk⟩ := h_abs
  have h2piI_ne : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hm1_ne : (↑m + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < ↑m + 1 by positivity))
  have h_factor : (↑m : ℂ) * -(↑(2 * Real.pi / (↑m + 1)) * Complex.I) =
    -(↑m / (↑m + 1)) * (2 * ↑Real.pi * Complex.I) := by push_cast; ring
  rw [h_factor] at hk
  have h_eq := mul_right_cancel₀ h2piI_ne hk
  have h_int : -(m : ℤ) = k * ((m : ℤ) + 1) := by
    have := congr_arg (· * (↑m + 1 : ℂ)) h_eq
    simp only [neg_mul, div_mul_cancel₀ _ hm1_ne] at this
    exact_mod_cast this
  have hm_int : (0 : ℤ) < ↑m := Nat.cast_pos.mpr hm
  by_cases hk : 0 ≤ k
  · linarith [mul_nonneg hk (show (0 : ℤ) ≤ ↑m + 1 by linarith)]
  · push Not at hk; nlinarith

/-- **Haar moment vanishing**: For j ≥ 1, ∫ k₀₀^n · conj(k_{j0})^m dk = 0.

    Proof: By Haar left-invariance under diagonal phase D_j(ω) with ω = exp(2πi/(m+1)):
    the integrand picks up conj(ω)^m = ω^{-m} = ω ≠ 1 as a factor.
    So I = ω · I and (1-ω)I = 0, hence I = 0. -/
lemma haar_moment_vanishing_first_col (d n : ℕ) [NeZero d]
    (j : Fin d) (hj : j ≠ 0) (m : ℕ) (hm : 0 < m) :
    ∫ k : unitaryGroup (Fin d) ℂ,
      (k.val 0 0) ^ n * (starRingEnd ℂ (k.val j 0)) ^ m
      ∂(haarProbUnitary d) = 0 := by
  -- Define the integral value I
  set I := ∫ k : unitaryGroup (Fin d) ℂ,
    (k.val 0 0) ^ n * (starRingEnd ℂ (k.val j 0)) ^ m ∂(haarProbUnitary d)
  -- Choose ω = exp(2πi/(m+1) * I), a primitive (m+1)-th root of unity with |ω| = 1
  set θ : ℝ := 2 * Real.pi / (↑m + 1)
  set ω : ℂ := Complex.exp (↑θ * Complex.I)
  have hω_norm : ‖ω‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  -- Construct diagonal phase D_j(ω): diagonal with ω at position j, 1 elsewhere
  set f : Fin d → ℂ := fun i => if i = j then ω else 1
  have hf_norm : ∀ i, ‖f i‖ = 1 := by
    intro i; simp only [f]; split_ifs <;> simp [*]
  set D : unitaryGroup (Fin d) ℂ := ⟨Matrix.diagonal f,
    diagonal_unitCircle_mem_unitary f hf_norm⟩
  -- Haar left-invariance: ∫ F(k) dk = ∫ F(D·k) dk
  have : (haarProbUnitary d).IsMulLeftInvariant := by
    unfold haarProbUnitary haarOnUnitary; infer_instance
  set F := fun k : unitaryGroup (Fin d) ℂ =>
    (k.val 0 0) ^ n * (starRingEnd ℂ (k.val j 0)) ^ m
  have h_inv : I = ∫ k, F (D * k) ∂(haarProbUnitary d) := by
    change (∫ k, F k ∂(haarProbUnitary d)) = ∫ k, F (D * k) ∂(haarProbUnitary d)
    rw [integral_mul_left_eq_self F D]
  -- Compute how D·k transforms the entries
  -- D·k at (0,0): f(0) = 1 (since 0 ≠ j), so (D·k)₀₀ = k₀₀
  have h_D0 : ∀ k : unitaryGroup (Fin d) ℂ, (D * k).val 0 0 = k.val 0 0 := by
    intro k; rw [diagonal_mul_entry f k hf_norm]; simp [f, Ne.symm hj]
  -- D·k at (j,0): f(j) = ω, so (D·k)_{j,0} = ω · k_{j,0}
  have h_Dj : ∀ k : unitaryGroup (Fin d) ℂ, (D * k).val j 0 = ω * k.val j 0 := by
    intro k; rw [diagonal_mul_entry f k hf_norm]; simp [f]
  -- F(D*k) = k₀₀^n · conj(ω)^m · conj(k_{j0})^m = conj(ω)^m · F(k)
  have h_FDk : ∀ k : unitaryGroup (Fin d) ℂ,
      F (D * k) = (starRingEnd ℂ ω) ^ m * F k := by
    intro k; simp only [F, h_D0, h_Dj, map_mul, mul_pow]; ring
  simp_rw [h_FDk] at h_inv
  rw [MeasureTheory.integral_const_mul] at h_inv
  -- Fold back: ∫ F dk = I
  have hFI : (∫ a, F a ∂(haarProbUnitary d)) = I := rfl
  rw [hFI] at h_inv
  -- h_inv: I = conj(ω)^m * I, so (1 - conj(ω)^m) * I = 0
  -- Need: conj(ω)^m ≠ 1, i.e., ω^m ≠ 1
  have hω_pow_ne : (starRingEnd ℂ ω) ^ m ≠ 1 :=
    conj_primitive_root_pow_ne_one m hm
  -- Algebraic conclusion: from I = c*I with c ≠ 1, get I = 0
  -- I = c*I → I - c*I = 0 → (1-c)*I = 0
  set c := (starRingEnd ℂ ω) ^ m
  -- From I = c * I, get (1-c)*I = 0
  have h_sub : (1 - c) * I = 0 := by
    have : I - c * I = 0 := sub_eq_zero.mpr h_inv
    linear_combination this
  rcases mul_eq_zero.mp h_sub with h | h
  · -- 1 - c = 0 contradicts c ≠ 1
    exact absurd (eq_of_sub_eq_zero h).symm hω_pow_ne
  · exact h

/-- **General Haar equivariant vanishing**: If F(D·k) = c·F(k) for some D ∈ U(d)
    with c ≠ 1, then ∫ F dk = 0 by Haar left-invariance. -/
lemma haar_equivariant_integral_zero (d : ℕ) [NeZero d]
    (F : unitaryGroup (Fin d) ℂ → ℂ) (D : unitaryGroup (Fin d) ℂ)
    (c : ℂ) (hc : c ≠ 1)
    (h_equi : ∀ k, F (D * k) = c * F k) :
    ∫ k, F k ∂(haarProbUnitary d) = 0 := by
  have : (haarProbUnitary d).IsMulLeftInvariant := by
    unfold haarProbUnitary haarOnUnitary; infer_instance
  set I := ∫ k, F k ∂(haarProbUnitary d)
  have h_inv : I = c * I := by
    change (∫ k, F k ∂(haarProbUnitary d)) = c * (∫ k, F k ∂(haarProbUnitary d))
    conv_lhs => rw [(integral_mul_left_eq_self F D).symm]
    simp_rw [h_equi]; exact MeasureTheory.integral_const_mul c _
  have h_sub : (1 - c) * I = 0 := by
    have : I - c * I = 0 := sub_eq_zero.mpr h_inv
    linear_combination this
  rcases mul_eq_zero.mp h_sub with h | h
  · exact absurd (eq_of_sub_eq_zero h).symm hc
  · exact h

/-- **Product torus vanishing**: If p : Fin m → Fin d has some p(i) ≠ 0,
    then ∫ k₀₀^n · ∏_i conj(k_{p(i),0}) dk = 0. -/
lemma haar_product_vanishing_first_col (d n : ℕ) [NeZero d]
    (m : ℕ) (p : Fin m → Fin d) (hp : ∃ i, p i ≠ 0) :
    ∫ k : unitaryGroup (Fin d) ℂ,
      (k.val 0 0) ^ n * ∏ i, (starRingEnd ℂ (k.val (p i) 0))
      ∂(haarProbUnitary d) = 0 := by
  obtain ⟨i₀, hi₀⟩ := hp
  set j := p i₀
  set cnt := Finset.card (Finset.univ.filter (fun i => p i = j))
  have hcnt : 0 < cnt := by
    simp only [cnt]; rw [Finset.card_pos]
    exact ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  -- Build diagonal phase matrix D_j(ω)
  set θ : ℝ := 2 * Real.pi / (↑cnt + 1)
  set ω : ℂ := Complex.exp (↑θ * Complex.I)
  have hω_norm : ‖ω‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  set f : Fin d → ℂ := fun i => if i = j then ω else 1
  have hf_norm : ∀ i, ‖f i‖ = 1 := by intro i; simp only [f]; split_ifs <;> simp [*]
  set D : unitaryGroup (Fin d) ℂ := ⟨Matrix.diagonal f,
    diagonal_unitCircle_mem_unitary f hf_norm⟩
  -- Equivariance: the product transforms by conj(ω)^cnt
  set F := fun k : unitaryGroup (Fin d) ℂ =>
    (k.val 0 0) ^ n * ∏ i, (starRingEnd ℂ (k.val (p i) 0))
  have h_equi : ∀ k, F (D * k) = (starRingEnd ℂ ω) ^ cnt * F k := by
    intro k
    simp only [F]
    have h_D0 : (D * k).val 0 0 = k.val 0 0 := by
      rw [diagonal_mul_entry f k hf_norm]; simp [f, Ne.symm hi₀]
    have hp : ∀ i, (D * k).val (p i) 0 = f (p i) * k.val (p i) 0 :=
      fun i => diagonal_mul_entry f k hf_norm (p i) 0
    simp_rw [h_D0, hp, map_mul, Finset.prod_mul_distrib]
    suffices h : ∏ i : Fin m, (starRingEnd ℂ) (f (p i)) = (starRingEnd ℂ ω) ^ cnt by
      rw [h]; ring
    have : ∀ i : Fin m, (starRingEnd ℂ) (f (p i)) =
        if i ∈ Finset.univ.filter (fun i => p i = j) then starRingEnd ℂ ω else 1 := by
      intro i; simp only [f, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp [*]
    simp_rw [this]
    rw [Finset.prod_ite_mem_eq, Finset.prod_const]
  -- conj(ω)^cnt ≠ 1 (same argument as in haar_moment_vanishing_first_col)
  have hω_pow_ne : (starRingEnd ℂ ω) ^ cnt ≠ 1 :=
    conj_primitive_root_pow_ne_one cnt hcnt
  exact haar_equivariant_integral_zero d F D _ hω_pow_ne h_equi

/-- The unit circle in ℂ is infinite (needed for polynomial root arguments). -/
lemma unit_circle_infinite : Set.Infinite (Set.ofPred (fun z : ℂ => ‖z‖ = 1)) := by
  apply (Set.infinite_range_of_injective
    (f := fun n : ℕ => Complex.exp (↑(n : ℝ) * Complex.I))
    (fun a b hab => ?_)).mono
  · rintro _ ⟨n, rfl⟩; exact Complex.norm_exp_ofReal_mul_I n
  · rw [Complex.exp_eq_exp_iff_exists_int] at hab
    obtain ⟨k, hk⟩ := hab
    -- Take imaginary parts: ↑a = ↑b + k * (2 * π), so (a - b : ℝ) = 2πk
    have him : (a : ℝ) = (b : ℝ) + ↑k * (2 * Real.pi) := by
      have := congr_arg Complex.im hk
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            Complex.add_im, Complex.mul_im] at this
      linarith
    -- Since π is irrational, k = 0
    have hk0 : k = 0 := by
      by_contra hk_ne
      exact irrational_pi ⟨((a : ℚ) - b) / (2 * k), by push_cast; field_simp; linarith⟩
    subst hk0; simp only [Int.cast_zero, zero_mul, add_zero] at him; exact_mod_cast him

/-- A polynomial over ℂ vanishing on the unit circle must be zero, since the unit circle
    is infinite and a nonzero polynomial has finitely many roots. -/
lemma polynomial_zero_of_vanish_unit_circle {p : Polynomial ℂ}
    (hp : ∀ z : ℂ, ‖z‖ = 1 → p.eval z = 0) : p = 0 := by
  by_contra h
  exact (Polynomial.finite_setOfPred_isRoot h).not_infinite
    (unit_circle_infinite.mono (fun z hz => hp z hz))

private lemma dft_column_ortho_diag (d : ℕ) [NeZero d]
    (ω : ℂ) (hω_ne : ω ≠ 0) (k : Fin d) :
    (∑ j : Fin d, ω⁻¹ ^ (j.val * k.val) * ω ^ (j.val * k.val)) =
    ↑(Real.sqrt d) * ↑(Real.sqrt d) := by
  simp only [inv_pow]
  simp only [inv_mul_cancel₀ (pow_ne_zero _ hω_ne), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg' d)]

private lemma dft_column_ortho_offdiag (d : ℕ) [NeZero d]
    (ω : ℂ) (hprim : IsPrimitiveRoot ω d) (hω_ne : ω ≠ 0) (hωd : ω ^ d = 1)
    (k₁ k₂ : Fin d) (h : k₁ ≠ k₂) :
    (∑ j : Fin d, ω⁻¹ ^ (j.val * k₁.val) * ω ^ (j.val * k₂.val)) = 0 := by
  have hζ1 : ω ^ k₂.val * (ω⁻¹) ^ k₁.val ≠ 1 := by
    intro heq
    have : ω ^ k₂.val = ω ^ k₁.val := by
      rwa [inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ hω_ne)] at heq
    exact h (Fin.ext (hprim.pow_inj k₁.prop k₂.prop this.symm))
  have hζd : (ω ^ k₂.val * (ω⁻¹) ^ k₁.val) ^ d = 1 := by
    have hinvd : ω⁻¹ ^ d = 1 := by rw [inv_pow, hωd, inv_one]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k₂.val d, mul_comm k₁.val d,
      pow_mul ω d, pow_mul ω⁻¹ d, hωd, hinvd, one_pow, one_pow, mul_one]
  have key : ∀ j : Fin d,
      ω⁻¹ ^ (j.val * k₁.val) * ω ^ (j.val * k₂.val) =
      (ω ^ k₂.val * (ω⁻¹) ^ k₁.val) ^ j.val := by
    intro j
    rw [mul_comm j.val k₁.val, mul_comm j.val k₂.val,
      mul_comm, mul_pow, ← pow_mul, ← pow_mul]
  simp_rw [key, Fin.sum_univ_eq_sum_range, geom_sum_eq hζ1 d, hζd, sub_self, zero_div]

-- DFT column orthogonality involves large symbolic expansions of geometric sums and roots of unity.
/-- Column orthogonality for the DFT matrix: ∑_j conj(F(j,k₁)) F(j,k₂) = δ(k₁,k₂). -/
lemma dft_column_ortho (d : ℕ) [NeZero d] :
    let ω := Complex.exp (2 * ↑Real.pi * Complex.I / ↑d)
    let F : Matrix (Fin d) (Fin d) ℂ := fun j k => ω ^ (j.val * k.val) / ↑(Real.sqrt d)
    ∀ k₁ k₂ : Fin d,
      (∑ j : Fin d, star (F j k₁) * F j k₂) = if k₁ = k₂ then 1 else 0 := by
  intro ω F k₁ k₂
  have hprim : IsPrimitiveRoot ω d := Complex.isPrimitiveRoot_exp d (NeZero.ne d)
  have hωd : ω ^ d = 1 := hprim.pow_eq_one
  have hω_ne : ω ≠ 0 := by
    intro h; rw [h, zero_pow (NeZero.ne d)] at hωd; exact one_ne_zero hωd.symm
  have hω_star : star ω = ω⁻¹ := by
    have : ω * star ω = 1 := by
      change ω * (starRingEnd ℂ) ω = 1
      rw [Complex.mul_conj']; simp [hprim.norm'_eq_one (NeZero.ne d)]
    exact eq_inv_of_mul_eq_one_right this
  have hsd_ne : (↑(Real.sqrt d) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d)))))
  have hsd_star : star (↑(Real.sqrt d) : ℂ) = ↑(Real.sqrt d) := by
    exact_mod_cast RCLike.conj_ofReal (Real.sqrt d)
  simp only [F, star_div₀, div_mul_div_comm, star_pow, hω_star, hsd_star]
  rw [← Finset.sum_div, div_eq_iff (mul_ne_zero hsd_ne hsd_ne)]
  split
  · case isTrue h =>
    subst h; rw [one_mul]; exact dft_column_ortho_diag d ω hω_ne k₁
  · case isFalse h =>
    rw [zero_mul]; exact dft_column_ortho_offdiag d ω hprim hω_ne hωd k₁ k₂ h

/-- There exists a unitary matrix in U(d) whose first column has all entries nonzero.
    Construction: the d×d DFT matrix has first column (1/√d, ..., 1/√d). -/
lemma exists_unitary_nonzero_first_col (d : ℕ) [NeZero d] :
    ∃ g₀ : unitaryGroup (Fin d) ℂ, ∀ a : Fin d, g₀.val a 0 ≠ 0 := by
  set ω := Complex.exp (2 * ↑Real.pi * Complex.I / ↑d)
  have hsd_ne : (↑(Real.sqrt d) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d)))))
  let F : Matrix (Fin d) (Fin d) ℂ := fun j k => ω ^ (j.val * k.val) / ↑(Real.sqrt d)
  have hF : F ∈ unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']; ext k₁ k₂
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply]
    exact dft_column_ortho d k₁ k₂
  exact ⟨⟨F, hF⟩, fun a => by
    change ω ^ (a.val * 0) / ↑(Real.sqrt d) ≠ 0
    rw [Nat.mul_zero, pow_zero]; exact div_ne_zero one_ne_zero hsd_ne⟩

/-- Univariate polynomial coefficient extraction from S¹ vanishing:
    if a finite sum ∑_{k ∈ S} a_k z^k vanishes on S¹, each a_k = 0. -/
lemma coeff_zero_of_vanish_circle (S : Finset ℕ) (a : ℕ → ℂ)
    (hv : ∀ z : ℂ, ‖z‖ = 1 → ∑ k ∈ S, a k * z ^ k = 0) :
    ∀ k ∈ S, a k = 0 := by
  -- Build the formal polynomial p = ∑_{k ∈ S} C(a_k) * X^k
  set p : Polynomial ℂ := ∑ k ∈ S, Polynomial.C (a k) * Polynomial.X ^ k with hp_def
  -- p evaluates to the original sum on S¹
  have hp_eval : ∀ z : ℂ, ‖z‖ = 1 → p.eval z = 0 := by
    intro z hz
    have : p.eval z = ∑ k ∈ S, a k * z ^ k := by
      simp only [hp_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
                 Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [this]; exact hv z hz
  have hp_zero : p = 0 := polynomial_zero_of_vanish_unit_circle hp_eval
  intro k hk
  have h_coeff : p.coeff k = a k := by
    simp only [hp_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single k
      (fun j _ hjk => ite_eq_right (Ne.symm hjk))
      (fun hk' => absurd hk hk')]
    simp
  rw [← h_coeff, hp_zero]; simp

/-- Multivariate monomial linear independence on the d-torus:
    if a sum of distinct monomials vanishes on T^d, each coefficient is 0.
    Proved by induction on d, using `coeff_zero_of_vanish_circle` at each step. -/
lemma monomial_indep_torus : ∀ (d : ℕ),
    ∀ (S : Finset (Fin d → ℕ)) (a : (Fin d → ℕ) → ℂ),
    (∀ z : Fin d → ℂ, (∀ i, ‖z i‖ = 1) →
      ∑ t ∈ S, a t * ∏ i, z i ^ t i = 0) →
    ∀ t ∈ S, a t = 0 := by
  intro d
  induction d with
  | zero =>
    intro S a hv t ht
    have h := hv Fin.elim0 (fun i => i.elim0)
    -- S ⊆ {Fin.elim0} since Fin 0 → ℕ has exactly one element
    have : S = {t} := by
      ext s; constructor
      · intro hs; simp only [Finset.mem_singleton]; ext i; exact i.elim0
      · intro hs; simp only [Finset.mem_singleton] at hs; rw [hs]; exact ht
    rw [this] at h; simp only [Finset.sum_singleton, Fintype.prod_empty, mul_one] at h; exact h
  | succ d ih =>
    intro S a hv t ht
    -- Strategy: group by last exponent, apply coeff_zero_of_vanish_circle, then ih
    -- Step 1: Split the product ∏ i : Fin(d+1) into (∏ i : Fin d) * z_last^k
    -- Step 2: For fixed z' on T^d, the sum is a polynomial in z_last vanishing on S¹
    -- Step 3: By coeff_zero_of_vanish_circle, each z_last-coefficient vanishes
    -- Step 4: Each z_last-coefficient is a sum of monomials in d variables
    --         By ih, each summand's coefficient vanishes
    -- The set of last-exponent values
    set K := S.image (fun s => s (Fin.last d)) with hK_def
    -- For each k and fixed z', the inner sum
    set inner := fun (k : ℕ) (z' : Fin d → ℂ) =>
      ∑ s ∈ S.filter (fun s => s (Fin.last d) = k),
        a s * ∏ i : Fin d, z' i ^ s (Fin.castSucc i) with inner_def
    -- The grouping identity: original sum = ∑_k inner(k)(z') * z_last^k
    have h_group : ∀ z : Fin (d + 1) → ℂ,
        ∑ s ∈ S, a s * ∏ i, z i ^ s i =
        ∑ k ∈ K, inner k (z ∘ Fin.castSucc) * z (Fin.last d) ^ k := by
      intro z
      -- Split the product and reassociate
      simp_rw [Fin.prod_univ_castSucc, ← mul_assoc]
      -- Group by the last exponent using fiberwise sum
      rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun s => s (Fin.last d)) (t := K)
        (fun s hs => Finset.mem_image.mpr ⟨s, hs, rfl⟩)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      -- Within each fiber: s(last d) = k, so z(last d)^s(last d) = z(last d)^k
      rw [show ∑ i ∈ S.filter (fun s => s (Fin.last d) = k),
            (a i * ∏ j : Fin d, z (Fin.castSucc j) ^ i (Fin.castSucc j)) *
              z (Fin.last d) ^ i (Fin.last d) =
          (∑ i ∈ S.filter (fun s => s (Fin.last d) = k),
            a i * ∏ j : Fin d, (z ∘ Fin.castSucc) j ^ i (Fin.castSucc j)) *
              z (Fin.last d) ^ k from by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun s hs => ?_)
        simp only [Function.comp]
        rw [(Finset.mem_filter.mp hs).2]]
    -- Step 2-3: inner(k)(z') = 0 for all z' on T^d and k ∈ K
    have h_inner_zero : ∀ z' : Fin d → ℂ, (∀ i, ‖z' i‖ = 1) →
        ∀ k ∈ K, inner k z' = 0 := by
      intro z' hz'
      apply coeff_zero_of_vanish_circle K
      intro w hw
      -- Build z : Fin (d+1) → ℂ from z' and w
      let zz : Fin (d + 1) → ℂ := fun i =>
        if h : i.val < d then z' ⟨i.val, h⟩ else w
      have hz : ∀ i : Fin (d + 1), ‖zz i‖ = 1 := by
        intro i; simp only [zz]
        split_ifs with h
        · exact hz' ⟨i.val, h⟩
        · exact hw
      have := hv zz hz
      rw [h_group] at this
      -- Show zz ∘ Fin.castSucc = z' and zz (Fin.last d) = w
      have hzz_cast : zz ∘ Fin.castSucc = z' := by
        ext i; simp only [Function.comp, zz, Fin.val_castSucc]
        rw [dite_eq_left i.isLt]
      have hzz_last : zz (Fin.last d) = w := by
        simp only [zz, Fin.val_last]; rw [dite_eq_right (lt_irrefl d)]
      rw [hzz_cast, hzz_last] at this; exact this
    -- Step 4: Apply ih to the inner sum for k = t(Fin.last d)
    have htK : t (Fin.last d) ∈ K := Finset.mem_image.mpr ⟨t, ht, rfl⟩
    set k := t (Fin.last d)
    set S_k := S.filter (fun s => s (Fin.last d) = k) with hSk_def
    -- Restriction map: s ↦ s ∘ castSucc is injective on S_k
    set restr := fun (s : Fin (d + 1) → ℕ) (i : Fin d) => s (Fin.castSucc i)
    -- Extension map: for t' : Fin d → ℕ, extend back to Fin(d+1) → ℕ
    set ext_fn := fun (t' : Fin d → ℕ) (i : Fin (d + 1)) =>
      if h : i.val < d then t' ⟨i.val, h⟩ else k with hext_def
    -- restr and ext_fn are inverses on S_k
    have h_restr_ext : ∀ s ∈ S_k, ext_fn (restr s) = s := by
      intro s hs; ext i; simp only [ext_fn, restr]
      split_ifs with h
      · rfl
      · have hi : i = Fin.last d := by ext; simp [Fin.val_last]; omega
        rw [hi]; exact (Finset.mem_filter.mp hs).2.symm
    -- t is in S_k
    have ht_Sk : t ∈ S_k := Finset.mem_filter.mpr ⟨ht, rfl⟩
    -- The image S' and t' = restr t
    set S' := S_k.image restr with hS'_def
    have ht'_S' : restr t ∈ S' := Finset.mem_image.mpr ⟨t, ht_Sk, rfl⟩
    -- inner k z' = ∑ t' ∈ S', a(ext_fn t') * ∏ i, z' i ^ t' i
    have h_inner_rewrite : ∀ z' : Fin d → ℂ,
        inner k z' = ∑ t' ∈ S', a (ext_fn t') * ∏ i, z' i ^ t' i := by
      intro z'
      simp only [inner_def]
      rw [Finset.sum_image (fun s₁ hs₁ s₂ hs₂ h => by
        have := congr_arg ext_fn h
        rw [h_restr_ext s₁ hs₁, h_restr_ext s₂ hs₂] at this; exact this)]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [h_restr_ext s hs]
    -- Apply ih: a(ext_fn t') = 0 for all t' ∈ S'
    have := ih S' (a ∘ ext_fn) (fun z' hz' => by
      simp only [Function.comp]
      rw [← h_inner_rewrite]; exact h_inner_zero z' hz' k htK) (restr t) ht'_S'
    -- a(ext_fn (restr t)) = a t
    simp only [Function.comp] at this
    rwa [h_restr_ext t ht_Sk] at this

/-- The permutation representation acts on vectors by composing the multi-index with σ:
    (U_σ *ᵥ w)(enc p) = w(enc(p ∘ σ)). -/
lemma perm_rep_mulVec_apply {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n)) (w : Fin (d ^ n) → ℂ) (p : Fin n → Fin d) :
    (Math.RepresentationTheory.permutationRepresentation d n σ *ᵥ w)
      (finFunctionFinEquiv p) = w (finFunctionFinEquiv (p ∘ ↑σ)) := by
  simp only [Matrix.mulVec, dotProduct,
    Math.RepresentationTheory.permutationRepresentation, Matrix.of_apply]
  rw [Finset.sum_eq_single (finFunctionFinEquiv (p ∘ ↑σ))]
  · simp only [Equiv.symm_apply_apply,
      show (p ∘ ↑σ) ∘ ↑σ.symm = p from by ext k; simp, ite_true, one_mul]
  · intro j _ hj
    rw [ite_mul, one_mul, zero_mul, ite_eq_right]
    intro heq
    apply hj
    simp only [Equiv.symm_apply_apply] at heq
    have : finFunctionFinEquiv.symm j = p ∘ ↑σ := by
      funext k; have := congr_fun heq (σ k); simp at this; exact this.symm
    rw [← finFunctionFinEquiv.apply_symm_apply j, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- If w lies in the symmetric subspace (P_sym *ᵥ w = w), then w is invariant under
    every permutation representation U_σ. Proof: U_σ * P = P by left-invariance of the
    group sum, so U_σ w = U_σ (P w) = (U_σ P) w = P w = w. -/
lemma perm_invariant_of_symProj (d n : ℕ) [NeZero d] [NeZero n]
    (w : Fin (d ^ n) → ℂ) (hw : symmetricProjector d n *ᵥ w = w)
    (σ : Equiv.Perm (Fin n)) :
    Math.RepresentationTheory.permutationRepresentation d n σ *ᵥ w = w := by
  have key : Math.RepresentationTheory.permutationRepresentation d n σ *
      Math.RepresentationTheory.symmetricProjectorRep d n =
      Math.RepresentationTheory.symmetricProjectorRep d n := by
    simp only [Math.RepresentationTheory.symmetricProjectorRep]
    rw [Matrix.mul_smul, Finset.mul_sum]
    simp_rw [Math.RepresentationTheory.permutationRepresentation_mul]
    congr 1
    exact Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ) _ _ (fun _ => rfl)
  calc Math.RepresentationTheory.permutationRepresentation d n σ *ᵥ w
      = Math.RepresentationTheory.permutationRepresentation d n σ *ᵥ
          (symmetricProjector d n *ᵥ w) := by rw [hw]
    _ = (Math.RepresentationTheory.permutationRepresentation d n σ *
          symmetricProjector d n) *ᵥ w := by rw [Matrix.mulVec_mulVec]
    _ = symmetricProjector d n *ᵥ w := by
        change (Math.RepresentationTheory.permutationRepresentation d n σ *
            Math.RepresentationTheory.symmetricProjectorRep d n) *ᵥ w =
          Math.RepresentationTheory.symmetricProjectorRep d n *ᵥ w
        rw [key]
    _ = w := hw

/-- Functions with the same type (fiber cardinalities) are related by a permutation. -/
lemma same_type_exists_perm {n d : ℕ} (p q : Fin n → Fin d)
    (h : ∀ a : Fin d, (Finset.univ.filter (fun j => p j = a)).card =
                      (Finset.univ.filter (fun j => q j = a)).card) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j, p j = q (σ j) := by
  have e : ∀ a, { j // p j = a } ≃ { j // q j = a } :=
    fun a => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]; exact h a)
  exact ⟨Equiv.ofFiberEquiv e, fun j => (Equiv.ofFiberEquiv_map e j).symm⟩

/-- Coherent states separate Sym^n: if w ∈ Sym^n and ⟨w, v_g⟩ = 0 for all g ∈ U(d),
    then w = 0. Equivalently, coherent states span Sym^n.

    **Proof**: Evaluate hw_orth at g = diag(z) · k₀ for z on the d-torus and k₀ a unitary
    with nonzero first column. The resulting equation ∑_x c_x · ∏_a z_a^{type_a(x)} = 0
    on the torus forces each type coefficient to vanish. Since k₀ has nonzero first column
    and w is symmetric (constant on permutation orbits), this gives w = 0. -/
lemma coherent_states_separate_symn (d n : ℕ) [NeZero d] [NeZero n]
    (w : Fin (d ^ n) → ℂ)
    (hw_sym : symmetricProjector d n *ᵥ w = w)
    (hw_orth : ∀ g : unitaryGroup (Fin d) ℂ,
      ∑ x, starRingEnd ℂ (w x) * (coherentStateKet g n).vec x = 0) :
    w = 0 := by
  obtain ⟨k₀, hk₀⟩ := exists_unitary_nonzero_first_col d
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  -- Type function: τ(p)(a) = |{j : Fin n | p j = a}|
  set τ : (Fin n → Fin d) → (Fin d → ℕ) :=
    fun p a => (Finset.univ.filter (fun j => p j = a)).card with hτ_def
  -- Coefficient function: c(p) = conj(w(enc p)) * ∏_j k₀(p j, 0)
  set c : (Fin n → Fin d) → ℂ :=
    fun p => starRingEnd ℂ (w (finFunctionFinEquiv p)) *
      ∏ j : Fin n, k₀.val (p j) 0 with hc_def
  -- STEP 1: For all z on T^d, ∑_p c(p) * ∏_j z(p j) = 0
  -- (from hw_orth at g = diag(z) * k₀, expanding coherentStateKet, reindexing)
  have h_vanish : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ = 1) →
      ∑ p : Fin n → Fin d, c p * ∏ j : Fin n, z (p j) = 0 := by
    intro z hz
    -- Construct g = diag(z) * k₀
    have h_diag_mem := diagonal_unitCircle_mem_unitary z hz
    set g : unitaryGroup (Fin d) ℂ :=
      ⟨Matrix.diagonal z, h_diag_mem⟩ * k₀
    have h0 := hw_orth g
    -- h0: ∑ x, conj(w x) * (coherentStateKet g n).vec x = 0
    -- Reindex x → p via finFunctionFinEquiv
    rw [← Equiv.sum_comp finFunctionFinEquiv] at h0
    -- Now h0: ∑ p, conj(w(enc p)) * (coherentStateKet g n).vec (enc p) = 0
    -- Expand coherentStateKet and simplify
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro p _
    -- Need: c p * ∏ j, z (p j) = conj(w(enc p)) * (coherentStateKet g n).vec (enc p)
    -- Suffices: vec (enc p) = (∏ j, k₀(p j, 0)) * (∏ j, z(p j))
    suffices hvec : (coherentStateKet g n).vec (finFunctionFinEquiv p) =
        (∏ j : Fin n, k₀.val (p j) 0) * ∏ j : Fin n, z (p j) by
      simp only [hc_def]; rw [hvec]; ring
    -- Expand coherentStateKet definition
    change (∏ j : Fin n, (↑g : Matrix (Fin d) (Fin d) ℂ)
      ⟨((finFunctionFinEquiv p).val / d ^ (n - 1 - j.val)) % d, _⟩ 0) = _
    -- digit(enc p, j) = p(rev j) by bigEndian_digit_eq_finFunctionFinEquiv
    simp_rw [bigEndian_digit_eq_finFunctionFinEquiv hd_pos (finFunctionFinEquiv p),
             Equiv.symm_apply_apply]
    -- g.val(p(rev j), 0) = z(p(rev j)) * k₀(p(rev j), 0)
    simp_rw [show ∀ j : Fin n, (↑g : Matrix (Fin d) (Fin d) ℂ) (p (Fin.rev j)) 0 =
      z (p (Fin.rev j)) * k₀.val (p (Fin.rev j)) 0 from
      fun j => diagonal_mul_entry z k₀ hz (p (Fin.rev j)) 0]
    rw [Finset.prod_mul_distrib]
    -- Reindex via rev: ∏_j f(p(rev j)) = ∏_j f(p j)
    rw [show ∏ j : Fin n, z (p (Fin.rev j)) = ∏ j : Fin n, z (p j) from
      Finset.prod_equiv Fin.revPerm (by simp) (fun j _ => by simp [Fin.revPerm_apply])]
    rw [show ∏ j : Fin n, k₀.val (p (Fin.rev j)) 0 = ∏ j : Fin n, k₀.val (p j) 0 from
      Finset.prod_equiv Fin.revPerm (by simp) (fun j _ => by simp [Fin.revPerm_apply])]
    ring
  -- STEP 2: Rewrite ∏_j z(p j) = ∏_a z(a)^{τ(p)(a)} using Finset.prod_comp
  have h_prod_type : ∀ (z : Fin d → ℂ) (p : Fin n → Fin d),
      ∏ j : Fin n, z (p j) = ∏ a : Fin d, z a ^ τ p a := by
    intro z p
    rw [Finset.prod_comp z p]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro a _ ha
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at ha
    have : (Finset.univ.filter (fun j => p j = a)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun j _ => ha j
    rw [this, pow_zero]
  -- STEP 3: Group by type and apply monomial_indep_torus
  -- Each type coefficient = 0
  have h_type_coeff : ∀ t ∈ Finset.univ.image τ,
      ∑ p ∈ Finset.univ.filter (fun p => τ p = t), c p = 0 := by
    -- Rewrite the vanishing sum using h_prod_type
    have h_vanish_typed : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ = 1) →
        ∑ t ∈ Finset.univ.image τ,
          (∑ p ∈ Finset.univ.filter (fun p => τ p = t), c p) *
          ∏ a : Fin d, z a ^ t a = 0 := by
      intro z hz
      have h0 := h_vanish z hz
      -- Replace ∏_j z(p j) by ∏_a z(a)^{τ p a} in h0
      simp_rw [h_prod_type z] at h0
      -- Group by type: ∑_p f(p) = ∑_t ∑_{p : τ p = t} f(p)
      rw [← Finset.sum_fiberwise_of_maps_to (fun p _ => Finset.mem_image_of_mem τ
        (Finset.mem_univ p))] at h0
      -- Factor out the monomial from each fiber (it's constant since τ p = t)
      convert h0 using 1
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    exact monomial_indep_torus d _ _ h_vanish_typed
  -- STEP 4: Extract w = 0 from type coefficient vanishing
  -- Within each type fiber, c(p) is constant:
  -- - w(enc p) is constant by symmetry (hw_sym)
  -- - ∏_j k₀(p j, 0) is constant (depends only on type by commutativity)
  -- Since K(t) = ∏_a k₀(a,0)^{t a} ≠ 0 and |fiber| > 0, we get w = 0
  funext x
  change w x = 0
  set p₀ := finFunctionFinEquiv.symm x with hp₀_def
  have hx_enc : x = finFunctionFinEquiv p₀ := (Equiv.apply_symm_apply _ x).symm
  rw [hx_enc]
  set t₀ := τ p₀ with ht₀_def
  have ht₀_mem : t₀ ∈ Finset.univ.image τ :=
    Finset.mem_image_of_mem τ (Finset.mem_univ p₀)
  have h0 := h_type_coeff t₀ ht₀_mem
  -- Step 4a: ∏_j k₀(p j, 0) is constant on the type fiber
  -- It equals ∏_a k₀(a,0)^{t₀ a} by Finset.prod_comp
  set K := ∏ a : Fin d, k₀.val a 0 ^ t₀ a with hK_def
  have hK_eq : ∀ p, τ p = t₀ → ∏ j : Fin n, k₀.val (p j) 0 = K := by
    intro p hp
    rw [hK_def, h_prod_type (fun a => k₀.val a 0) p, hp]
  -- Step 4b: w(enc p) is constant on the type fiber (by symmetry hw_sym)
  -- If τ p = τ p₀, then p is a permutation of p₀, and w is symmetric
  have hW : ∀ p, τ p = t₀ → w (finFunctionFinEquiv p) = w (finFunctionFinEquiv p₀) := by
    intro p hp
    -- p and p₀ have the same type, so p = p₀ ∘ σ for some permutation σ
    have htype : ∀ a : Fin d, (Finset.univ.filter (fun j => p j = a)).card =
        (Finset.univ.filter (fun j => p₀ j = a)).card := by
      intro a; change τ p a = τ p₀ a; rw [hp]
    obtain ⟨σ, hσ⟩ := same_type_exists_perm p p₀ htype
    -- p = p₀ ∘ σ
    have hp_eq : p = p₀ ∘ ↑σ := funext hσ
    rw [hp_eq]
    -- w(enc(p₀ ∘ σ)) = (U_σ *ᵥ w)(enc(p₀)) by perm_rep_mulVec_apply
    rw [← perm_rep_mulVec_apply σ w p₀]
    -- U_σ *ᵥ w = w by perm_invariant_of_symProj
    rw [perm_invariant_of_symProj d n w hw_sym σ]
  -- Step 4c: c is constant on the fiber with value conj(w₀) * K
  set w₀ := w (finFunctionFinEquiv p₀) with hw₀_def
  have hc_const : ∀ p ∈ Finset.univ.filter (fun p => τ p = t₀),
      c p = starRingEnd ℂ w₀ * K := by
    intro p hp
    simp only [hc_def, hW p (Finset.mem_filter.mp hp).2, hK_eq p (Finset.mem_filter.mp hp).2]
  -- Step 4d: Sum = |fiber| * conj(w₀) * K = 0
  rw [Finset.sum_congr rfl hc_const, Finset.sum_const, nsmul_eq_mul] at h0
  -- h0: ↑|fiber| * (conj(w₀) * K) = 0
  have hK_ne : K ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => pow_ne_zero _ (hk₀ a))
  have h_card_pos : 0 < (Finset.univ.filter (fun p => τ p = t₀)).card :=
    Finset.card_pos.mpr ⟨p₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have h_card_ne : ((Finset.univ.filter (fun p => τ p = t₀)).card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr h_card_pos.ne'
  -- Extract w₀ = 0
  have h1 : starRingEnd ℂ w₀ * K = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h h_card_ne
    · exact h
  have h2 : starRingEnd ℂ w₀ = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hK_ne
  rw [hw₀_def, map_eq_zero] at h2
  exact h2

end InfoTheory.DeFinetti.PureState
