import QCryptLean.InfoTheory.DeFinetti.PureState.SchurLemma.HaarVanishing
import QCryptLean.Quantum.Operators.BraKet.Projector

/-!
# Schur's Lemma for the Symmetric Subspace — resolution of identity, Haar integrals, proportionality

This module proves Schur's lemma for the symmetric representation:
the Haar integral of coherent-state density operators is proportional to the
symmetric projector. This is the core analytic ingredient for the pure-state
quantum de Finetti theorem.

Two independent proofs are given:
1. **Irreducibility proof** (`coherent_integral_proportional_irred`): via the bilinear
   form identity and coherent state separation.
2. **Frobenius norm proof** (`coherent_integral_proportional_irred`): via Tr(I²) = 1/dim
   and expansion of ‖I - cP‖²_F.

## Main statements
- `schur_lemma_symmetric`: ∫ dim(Sym^n) · |v^g⟩⟨v^g| dg = P_sym
- `schur_integral_trace`: ∫ dim(Sym^n) · Tr(|v^g⟩⟨v^g| · Ψ) dg = 1
- `coherent_integral_eq_inv_dim_smul_symProj_schur`: ∫ |v^g⟩⟨v^g| dg = (1/dim) · P_sym
- `haar_entry_moment_pow`: ∫ |g₀₀|^{2n} dg = 1/C(n+d-1,d-1)

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

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-- **Bilinear form identity**: ⟨v_g, I v_h⟩ = I(0,0) · ⟨v_g, v_h⟩ for all g, h ∈ U(d).

    Here the bilinear form is expressed as: for the Haar integral operator I and
    any g, h ∈ U(d), the matrix element v_g† · I · v_h equals I(0,0) times
    the overlap v_g† · v_h.

    **Proof**: After Haar shift k → gk, the integral becomes
    ∫ k₀₀^n · (∑_i (g†h)_{i0} conj(k_{i0}))^n dk. By torus vanishing
    (invariance under k → diag(1,...,e^{iθ},...,1)·k for each coordinate j ≥ 1),
    only the term with all weight on coordinate 0 survives in the multinomial expansion:
    = (g†h)₀₀^n · ∫ |k₀₀|^{2n} dk = ⟨v_g, v_h⟩ · I(0,0). -/
lemma coherent_bilinear_form_identity (d n : ℕ) [NeZero d] [NeZero n]
    (g h : unitaryGroup (Fin d) ℂ) :
    let I_op := ∫ k : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp k n).toOp ∂(haarProbUnitary d)
    dotProduct (star (coherentStateKet g n).vec)
      (I_op *ᵥ (coherentStateKet h n).vec) =
    I_op 0 0 * ((coherentStateKet g n).dag * coherentStateKet h n) := by
  intro I_op
  -- Step 1: Pull Bochner integral through dotProduct and mulVec:
  -- LHS = ∫ ⟨v_g|v_k⟩·⟨v_k|v_h⟩ dk
  -- (uses ContinuousLinearMap.integral_comp_comm for mulVec then dotProduct)
  have h_as_integral : dotProduct (star (coherentStateKet g n).vec)
      (I_op *ᵥ (coherentStateKet h n).vec) =
    ∫ k : unitaryGroup (Fin d) ℂ,
      ((coherentStateKet g n).dag * coherentStateKet k n) *
      ((coherentStateKet k n).dag * coherentStateKet h n)
      ∂(haarProbUnitary d) := by
    haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
    have h_int := coherentStateDensityOp_integrable d n
    -- CLM 1: M ↦ M *ᵥ (coherentStateKet h n).vec
    let C1 : Op (d ^ n) →L[ℝ] (Fin (d ^ n) → ℂ) := LinearMap.toContinuousLinearMap
      { toFun := fun M => M *ᵥ (coherentStateKet h n).vec
        map_add' := fun M₁ M₂ => Matrix.add_mulVec M₁ M₂ _
        map_smul' := fun r M => by
          ext i; simp [Matrix.mulVec, dotProduct, Finset.smul_sum, mul_assoc] }
    have h1 : I_op *ᵥ (coherentStateKet h n).vec =
        ∫ k, (coherentStateDensityOp k n).toOp *ᵥ (coherentStateKet h n).vec
        ∂(haarProbUnitary d) := (C1.integral_comp_comm h_int).symm
    -- CLM 2: w ↦ star(vg) ⬝ᵥ w
    let C2 : (Fin (d ^ n) → ℂ) →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
      { toFun := fun w => dotProduct (star (coherentStateKet g n).vec) w
        map_add' := fun _ _ => dotProduct_add _ _ _
        map_smul' := fun r w => by
          simp only [dotProduct, Pi.star_apply, Pi.smul_apply, Complex.real_smul]
          conv_lhs =>
            arg 2; ext x
            rw [show star ((coherentStateKet g n).vec x) * (↑r * w x) =
              ↑r * (star ((coherentStateKet g n).vec x) * w x) from by ring]
          rw [← Finset.mul_sum]; simp [RingHom.id_apply] }
    have h_int2 : Integrable (fun k : unitaryGroup (Fin d) ℂ =>
        (coherentStateDensityOp k n).toOp *ᵥ (coherentStateKet h n).vec)
        (haarProbUnitary d) := C1.integrable_comp h_int
    have h2 : dotProduct (star (coherentStateKet g n).vec)
        (∫ k, (coherentStateDensityOp k n).toOp *ᵥ (coherentStateKet h n).vec
          ∂(haarProbUnitary d)) =
      ∫ k, dotProduct (star (coherentStateKet g n).vec)
          ((coherentStateDensityOp k n).toOp *ᵥ (coherentStateKet h n).vec)
        ∂(haarProbUnitary d) := (C2.integral_comp_comm h_int2).symm
    rw [h1, h2]
    -- Simplify integrand: star(vg) ⬝ᵥ (|vk⟩⟨vk| *ᵥ vh) = ⟨vg|vk⟩ * ⟨vk|vh⟩
    congr 1; ext k
    simp only [coherentStateDensityOp, DensityOp.fromPure, Ket.dag,
      bra_mul_ket_eq, dotProduct, Matrix.mulVec, Pi.star_apply]
    -- Unfold of wrapper and factor sums
    change ∑ x, star ((coherentStateKet g n).vec x) *
      ∑ x_1, ((coherentStateKet k n).vec x * (starRingEnd ℂ) ((coherentStateKet k n).vec x_1)) *
        (coherentStateKet h n).vec x_1 = _
    simp_rw [show ∀ (x x1 : Fin (d ^ n)),
      (coherentStateKet k n).vec x *
        (starRingEnd ℂ) ((coherentStateKet k n).vec x1) *
        (coherentStateKet h n).vec x1 =
      (coherentStateKet k n).vec x *
        ((starRingEnd ℂ) ((coherentStateKet k n).vec x1) *
        (coherentStateKet h n).vec x1)
      from fun _ _ => by ring]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul_sum]
    congr 1; ext x
    simp only [starRingEnd_apply, ← Finset.mul_sum]
    ring
  rw [h_as_integral]
  -- Step 2: Haar shift k → g*k and overlap simplification:
  -- ⟨v_g|v_{gk}⟩ = k₀₀^n (by overlap_hg_h_eq_conj_entry_pow)
  -- ⟨v_{gk}|v_h⟩ = ((gk)†h)₀₀^n = (∑_b k̄_{b0}(g†h)_{b0})^n
  haveI : (haarProbUnitary d).IsMulLeftInvariant := by
    unfold haarProbUnitary haarOnUnitary; infer_instance
  -- After Haar shift and using overlap formulas:
  have h_shifted :
    ∫ k : unitaryGroup (Fin d) ℂ,
      ((coherentStateKet g n).dag * coherentStateKet k n) *
      ((coherentStateKet k n).dag * coherentStateKet h n)
      ∂(haarProbUnitary d) =
    ∫ k : unitaryGroup (Fin d) ℂ,
      (k.val 0 0) ^ (n : ℕ) *
      (∑ b : Fin d, (starRingEnd ℂ) (k.val b 0) *
        ((g.val)ᴴ * h.val) b 0) ^ (n : ℕ)
      ∂(haarProbUnitary d) := by
    -- Use Haar left-invariance: ∫ f(k) dk = ∫ f(g*k) dk
    conv_lhs =>
      rw [(MeasureTheory.integral_mul_left_eq_self (fun k =>
        ((coherentStateKet g n).dag * coherentStateKet k n) *
        ((coherentStateKet k n).dag * coherentStateKet h n)) g).symm]
    congr 1; ext k
    -- Use overlap formula on both factors
    rw [coherentState_overlap_eq_entry_pow g (g * k) n,
        coherentState_overlap_eq_entry_pow (g * k) h n]
    -- ↑(g * k) = ↑g * ↑k as matrices
    have hmul : (↑(g * k) : Matrix (Fin d) (Fin d) ℂ) = g.val * k.val :=
      Matrix.UnitaryGroup.mul_apply g k
    congr 1
    · -- First factor: (∑ a, conj(g_a0) * (gk)_a0)^n = k₀₀^n
      congr 1
      simp_rw [hmul]
      conv_lhs => arg 2; ext a; rw [starRingEnd_apply, ← Matrix.conjTranspose_apply]
      rw [← Matrix.mul_apply, ← mul_assoc]
      -- Goal: ((↑g)ᴴ * ↑g * ↑k) 0 0 = ↑k 0 0
      rw [show (g.val).conjTranspose * g.val = 1 from by
        rw [← Matrix.star_eq_conjTranspose]; exact Matrix.UnitaryGroup.star_mul_self g]
      simp
    · -- Second factor: (∑ a, conj((gk)_a0) * h_a0)^n = (∑ b, conj(k_b0) * (g†h)_{b0})^n
      congr 1
      simp_rw [hmul]
      conv_lhs => arg 2; ext a; rw [starRingEnd_apply, ← Matrix.conjTranspose_apply]
      conv_rhs => arg 2; ext b; rw [starRingEnd_apply, ← Matrix.conjTranspose_apply]
      rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.conjTranspose_mul, mul_assoc]
  rw [h_shifted]
  -- Step 3: Expand (∑)^n using Fintype.sum_pow, apply product vanishing.
  -- Only p = const 0 survives, giving ((g†h)₀₀)^n * ∫ |k₀₀|^{2n} dk
  set c : Fin d → ℂ := fun b => ((g.val)ᴴ * h.val) b 0
  -- By Fintype.sum_pow: (∑ b, f(b))^n = ∑_{p : Fin n → Fin d} ∏_i f(p(i))
  -- Interchange sum and integral, apply haar_product_vanishing_first_col
  -- for each p with some p(i) ≠ 0. Only p = const 0 survives.
  have h_computation :
    ∫ k : unitaryGroup (Fin d) ℂ,
      (k.val 0 0) ^ (n : ℕ) *
      (∑ b : Fin d, (starRingEnd ℂ) (k.val b 0) * c b) ^ (n : ℕ)
      ∂(haarProbUnitary d) =
    c 0 ^ (n : ℕ) * ∫ k : unitaryGroup (Fin d) ℂ,
      (k.val 0 0) ^ (n : ℕ) * (starRingEnd ℂ (k.val 0 0)) ^ (n : ℕ)
      ∂(haarProbUnitary d) := by
    -- Expand (∑ b, conj(k_b0) * c_b)^n as ∑_p ∏_i using Fintype.prod_sum
    have h_rearrange : ∀ k : unitaryGroup (Fin d) ℂ,
        k.val 0 0 ^ (n : ℕ) * (∑ b, starRingEnd ℂ (k.val b 0) * c b) ^ (n : ℕ) =
        ∑ p : Fin n → Fin d, (∏ i, c (p i)) *
          (k.val 0 0 ^ (n : ℕ) * ∏ i, starRingEnd ℂ (k.val (p i) 0)) := by
      intro k
      conv_lhs =>
        arg 2
        rw [← Finset.card_fin n, ← Finset.prod_const (s := Finset.univ)]
        rw [Fintype.prod_sum (f := fun _ b => starRingEnd ℂ (k.val b 0) * c b)]
      simp_rw [Finset.prod_mul_distrib, Finset.mul_sum]
      congr 1; ext p; ring
    simp_rw [h_rearrange]
    -- Interchange ∫ and ∑ (finite sum)
    haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
    rw [MeasureTheory.integral_finsetSum _ (fun p _ => by
      apply Continuous.integrable_of_hasCompactSupport
      · exact continuous_const.mul ((continuous_subtype_val.matrix_elem 0 0).pow n |>.mul
          (continuous_finsetProd Finset.univ fun i _ =>
            (continuous_subtype_val.matrix_elem (p i) 0).star))
      · exact HasCompactSupport.of_compactSpace _)]
    -- Factor constants out of integral: ∫ c_p * f(k) dk = c_p * ∫ f(k) dk
    simp_rw [MeasureTheory.integral_const_mul]
    -- Apply vanishing: only p = const 0 survives
    rw [Finset.sum_eq_single_of_mem (fun _ => (0 : Fin d)) (Finset.mem_univ _)]
    · -- Surviving term: p = const 0
      simp only [Finset.prod_const, Finset.card_fin]
    · -- Vanishing: for p ≠ const 0, the integral is 0
      intro p _ hp
      have ⟨i₀, hi₀⟩ : ∃ i, p i ≠ 0 := by
        by_contra h; push Not at h; exact hp (funext fun i => by ext; simp [h i])
      rw [haar_product_vanishing_first_col d n n p ⟨i₀, hi₀⟩, mul_zero]
  rw [h_computation]
  -- Step 4: Identify the terms with I_op(0,0) and the overlap ⟨v_g|v_h⟩
  -- I_op(0,0) = ∫ |v_k(0)|² dk = ∫ |k₀₀^n|² dk = ∫ k₀₀^n * conj(k₀₀)^n dk
  -- ⟨v_g|v_h⟩ = ((g†h)₀₀)^n = (∑_a g̅_{a0} h_{a0})^n = c(0)^n
  -- (by coherentState_overlap_eq_entry_pow)
  -- Step 4a: Rewrite the overlap ⟨v_g|v_h⟩ as c 0 ^ n
  have hc0_eq_sum : c 0 = ∑ a : Fin d, starRingEnd ℂ (g.val a 0) * h.val a 0 := by
    simp only [c, Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply]
  rw [coherentState_overlap_eq_entry_pow g h n, ← hc0_eq_sum]
  -- Goal: c 0 ^ n * ∫ k₀₀^n * conj(k₀₀)^n dk = I_op 0 0 * c 0 ^ n
  rw [mul_comm (c 0 ^ n)]
  -- Goal: (∫ k₀₀^n * conj(k₀₀)^n dk) * c 0 ^ n = I_op 0 0 * c 0 ^ n
  congr 1
  -- Goal: ∫ k₀₀^n * conj(k₀₀)^n dk = I_op 0 0
  -- Step 4b: I_op 0 0 = ∫ (coh k n).toOp 0 0 dk (CLM interchange)
  haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
  have h_int := coherentStateDensityOp_integrable d n
  let L : Op (d ^ n) →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M (0 : Fin (d ^ n)) (0 : Fin (d ^ n))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hI00 : I_op 0 0 = ∫ k : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp k n).toOp 0 0 ∂(haarProbUnitary d) :=
    (L.integral_comp_comm h_int).symm
  rw [hI00]
  -- Goal: ∫ k₀₀^n * conj(k₀₀)^n dk = ∫ (coh k).toOp 0 0 dk
  congr 1; ext k
  -- Goal: k₀₀^n * conj(k₀₀)^n = (coh k).toOp 0 0
  -- Inline coherentDensityOp_entry_zero_eq: (coh k).toOp 0 0 = |k₀₀^n|² = k₀₀^n * conj(k₀₀)^n
  simp only [coherentStateDensityOp, DensityOp.fromPure, ket_mul_bra_apply, Ket.dag_vec,
    starRingEnd_apply, coherentStateKet]
  have hdigit : ∀ j : Fin n,
      (⟨((0 : Fin (d ^ n)).val / d ^ (n - 1 - j.val)) % d,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩ : Fin d) = 0 := by
    intro j; ext; simp
  simp_rw [hdigit]
  rw [Finset.prod_const, Finset.card_fin, star_pow]

/-- **Schur's lemma for Sym^n(ℂ^d)**: the coherent-state Haar integral
    is proportional to the symmetric projector.

    **Proof**: Set c = I(0,0).re. By the bilinear form identity,
    ⟨v_g, (I - c·P) v_h⟩ = 0 for all g, h. For each h, (I-cP)v_h ∈ Sym^n
    and is orthogonal to all coherent states, so by separation it vanishes.
    Then for general w ∈ Sym^n, (I-cP)w ∈ Sym^n satisfies
    ⟨v_g, (I-cP)w⟩ = ⟨(I-cP)v_g, w⟩ = 0, so (I-cP)w = 0 by separation.
    On ker(P): I = 0 (since IP = I) and cP = 0, so (I-cP) = 0.

    **Reference**: Harrow arXiv:1308.6595 §3, Theorem sym-irrep + Prop twirl. -/
lemma coherent_integral_proportional_irred (d n : ℕ) [NeZero d] [NeZero n] :
    ∃ c : ℝ, ∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d) =
      c • symmetricProjector d n := by
  set I_op := ∫ g : unitaryGroup (Fin d) ℂ,
    (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d) with hI_def
  set P := symmetricProjector d n with hP_def
  -- Key properties of I and P
  have hPI : P * I_op = I_op := symProj_mul_coherent_integral d n
  have hIP : I_op * P = I_op := coherent_integral_mul_symProj d n
  have hI_herm : I_op.conjTranspose = I_op := coherent_integral_hermitian d n
  obtain ⟨hPP, hPH⟩ := symmetricProjector_is_projector d n
  -- I(0,0) is real since I is Hermitian: conj(I(0,0)) = I†(0,0) = I(0,0)
  have hI00_conj : starRingEnd ℂ (I_op 0 0) = I_op 0 0 := by
    have := congr_fun (congr_fun hI_herm 0) 0
    simpa [conjTranspose_apply] using this
  have hI00_real : (I_op 0 0).im = 0 := Complex.conj_eq_iff_im.mp hI00_conj
  -- Proportionality constant c = I(0,0).re
  refine ⟨(I_op 0 0).re, ?_⟩
  -- We'll show I = I(0,0) • P (complex scalar), then convert to real scalar
  set c := I_op 0 0
  -- First prove I = c • P (complex smul), then convert
  suffices h_cpx : I_op = c • P by
    rw [h_cpx, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    congr 1
    apply Complex.ext <;> simp [hI00_real]
  -- Helper: P * (I - c•P) = I - c•P (since PI = I and P² = P)
  have hP_comm : P * (I_op - c • P) = I_op - c • P := by
    rw [mul_sub, mul_smul_comm, hPI, hPP]
  -- Helper: (I - c•P)† = I - c•P (Hermitianity, c real)
  have hD_herm : (I_op - c • P).conjTranspose = I_op - c • P := by
    rw [conjTranspose_sub, hI_herm, conjTranspose_smul,
        show (star c : ℂ) = starRingEnd ℂ c from rfl, hI00_conj, hPH]
  -- Step 1: For coherent states, (I - c•P)*v_h = 0
  -- From bilinear identity: ⟨v_g | I v_h⟩ = c * ⟨v_g | v_h⟩ for all g
  -- So ⟨v_g | (I-cP) v_h⟩ = 0, and (I-cP)v_h ∈ Sym^n, so by separation = 0
  have h_on_coherent : ∀ hu : unitaryGroup (Fin d) ℂ,
      (I_op - c • P) *ᵥ (coherentStateKet hu n).vec = 0 := by
    intro hu
    apply coherent_states_separate_symn d n
    · -- (I-cP)*v_h ∈ Sym^n: P*((I-cP)*v_h) = (I-cP)*v_h
      rw [mulVec_mulVec, hP_comm]
    · -- ⟨(I-cP)v_h | v_g⟩ = conj(⟨v_g | (I-cP) v_h⟩) = 0
      intro g
      -- The bilinear form identity gives:
      -- dotProduct (star v_g) (I *ᵥ v_h) = c * (v_g.dag * v_h)
      have h_bil := coherent_bilinear_form_identity d n g hu
      -- Goal: ∑ x, conj(((I-cP)*v_hu) x) * v_g x = 0
      -- = conj(dotProduct (star v_g) ((I-cP)*v_hu))
      -- From bilinear identity + P*v_hu = v_hu, this is 0
      set w := (I_op - c • P) *ᵥ (coherentStateKet hu n).vec
      -- P * v_hu = v_hu (coherent states are in Sym^n)
      have hPvhu : P *ᵥ (coherentStateKet hu n).vec = (coherentStateKet hu n).vec := by
        have := congr_arg Ket.vec (symProj_mul_coherentStateKet (d := d) (n := n) hu)
        simpa using this
      -- dag product = dotProduct of star vectors
      have h_dag_eq : (coherentStateKet g n).dag * coherentStateKet hu n =
          dotProduct (star (coherentStateKet g n).vec) (coherentStateKet hu n).vec := by
        rw [bra_mul_ket_eq]; rfl
      -- h_bil with the let-bound I_op unfolded to our I_op
      have h_bil' : dotProduct (star (coherentStateKet g n).vec)
          (I_op *ᵥ (coherentStateKet hu n).vec) =
          c * dotProduct (star (coherentStateKet g n).vec) (coherentStateKet hu n).vec := by
        -- h_bil has a let-binding; unfold it to match our goal
        simp only [c]
        rw [h_dag_eq] at h_bil
        exact h_bil
      -- Show dotProduct (star v_g) w = 0
      have h_dp_zero : dotProduct (star (coherentStateKet g n).vec) w = 0 := by
        change dotProduct (star (coherentStateKet g n).vec)
          ((I_op - c • P) *ᵥ (coherentStateKet hu n).vec) = 0
        rw [sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, hPvhu,
            h_bil', smul_eq_mul]; ring
      -- Goal: ∑ x, conj(w x) * v_g x = 0
      -- = conj(dotProduct (star v_g) w) = conj(0) = 0
      simp only [dotProduct] at h_dp_zero ⊢
      have : starRingEnd ℂ (∑ i, star (coherentStateKet g n).vec i * w i) = 0 := by
        rw [h_dp_zero]; simp
      simp only [map_sum, map_mul] at this
      convert this using 1
      congr 1; ext i; simp [mul_comm]
  -- Step 2: For all w ∈ Sym^n, (I-cP)*w = 0
  -- Via adjoint: ⟨v_g | (I-cP) w⟩ = ⟨(I-cP)† v_g | w⟩ = ⟨(I-cP) v_g | w⟩ = ⟨0 | w⟩ = 0
  have h_on_symn : ∀ w, P *ᵥ w = w → (I_op - c • P) *ᵥ w = 0 := by
    intro w hw
    apply coherent_states_separate_symn d n
    · rw [mulVec_mulVec, hP_comm]
    · intro g
      -- ⟨(I-cP)w | v_g⟩ = dotProduct (star ((I-cP)*w)) v_g
      -- = conj(dotProduct (star v_g) ((I-cP)*w))
      -- By adjoint: dotProduct (star v_g) ((I-cP)*w) = dotProduct (star ((I-cP)†*v_g)) w
      -- = dotProduct (star ((I-cP)*v_g)) w = dotProduct (star 0) w = 0
      -- So conj(0) = 0
      -- Use: dotProduct (star a) (B *ᵥ b) = dotProduct (star (B† *ᵥ a)) b
      have h_adj : dotProduct (star (coherentStateKet g n).vec)
          ((I_op - c • P) *ᵥ w) =
          dotProduct (star ((I_op - c • P).conjTranspose *ᵥ (coherentStateKet g n).vec)) w := by
        rw [dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]
      rw [hD_herm, h_on_coherent g] at h_adj
      -- h_adj : dotProduct (star v_g) ((I-cP)*w) = dotProduct (star 0) w = 0
      simp only [star_zero, zero_dotProduct] at h_adj
      -- Now: ∑ conj(w' x) * v_g x = conj(∑ conj(v_g x) * w' x) where w' = (I-cP)*w
      -- Since dotProduct (star v_g) w' = 0, conj is also 0
      simp only [dotProduct] at h_adj ⊢
      have : starRingEnd ℂ (∑ i, star (coherentStateKet g n).vec i *
        ((I_op - c • P) *ᵥ w) i) = 0 := by rw [h_adj]; simp
      simp only [map_sum, map_mul] at this
      convert this using 1
      congr 1; ext i; simp [mul_comm]
  -- Step 3: For any v, (I-cP)*v = 0
  -- Decompose: I*v = I*(P*v) (from IP=I) and (I-cP)*(Pv) = 0 (from step 2)
  suffices h_all : ∀ v, (I_op - c • P) *ᵥ v = 0 by
    have h_eq : I_op - c • P = 0 := by
      ext i j
      have := congr_fun (h_all (Pi.single j 1)) i
      -- (D *ᵥ e_j) i = ∑ k, D i k * e_j k = D i j
      have h_ej : ((I_op - c • P) *ᵥ Pi.single j 1) i = (I_op - c • P) i j := by
        simp [mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
      rw [← h_ej]; exact this
    exact sub_eq_zero.mp h_eq
  intro v
  have hPv_sym : P *ᵥ (P *ᵥ v) = P *ᵥ v := by
    rw [mulVec_mulVec, hPP]
  have h_zero := h_on_symn (P *ᵥ v) hPv_sym
  -- h_zero : (I-cP)*(Pv) = 0, i.e., I*(Pv) = c*(Pv)
  -- Goal: (I-cP)*v = I*v - c*(P*v). Use I*v = I*(Pv) from IP=I.
  have : (I_op - c • P) *ᵥ v = (I_op - c • P) *ᵥ (P *ᵥ v) := by
    simp only [sub_mulVec, Matrix.smul_mulVec]
    congr 1
    · -- I*v = I*(Pv): from IP=I
      conv_lhs => rw [show I_op = I_op * P from hIP.symm]
      rw [mulVec_mulVec]
    · -- c*(P*v) = c*(P*(Pv)): from P²=P
      congr 1; rw [mulVec_mulVec, hPP]
  rw [this]; exact h_zero

/-- **Schur's lemma for Sym^n(ℂ^d)**: the coherent-state Haar integral
    equals `(1/dim) · P_sym`.

    The proportionality constant is determined by Tr(I) = 1:
    I = c·P implies Tr(I) = c·dim = 1, so c = 1/dim.

    **Reference**: CKMR definetti.tex lines 346-351, Harrow arXiv:1308.6595 §3. -/
lemma coherent_integral_eq_inv_dim_smul_symProj_schur (d n : ℕ) [NeZero d] [NeZero n] :
    ∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d) =
    ((Nat.choose (n + d - 1) (d - 1) : ℝ)⁻¹) • symmetricProjector d n := by
  -- Step 1: By Schur's lemma (irreducibility of Sym^n), the integral is proportional to P
  obtain ⟨c, hc⟩ := coherent_integral_proportional_irred d n
  -- Step 2: Determine the constant c from Tr(I) = 1
  set dim_n := Nat.choose (n + d - 1) (d - 1)
  have h_dim_ne : dim_n ≠ 0 := ne_of_gt (Nat.choose_pos (by omega))
  have hI_tr : (∫ g : unitaryGroup (Fin d) ℂ,
    (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d)).trace = 1 :=
    coherent_integral_trace d n
  have hP_tr : (symmetricProjector d n).trace = (dim_n : ℂ) :=
    symmetricProjector_trace d n
  rw [hc, Matrix.trace_smul, hP_tr] at hI_tr
  -- hI_tr : (c : ℂ) * ↑dim_n = 1
  rw [hc]; congr 1
  have h_dim_pos : (0 : ℝ) < (dim_n : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have h_rc : c * (↑dim_n : ℝ) = 1 := by
    have h1 : (c : ℂ) * (↑dim_n : ℂ) = 1 := by rwa [Algebra.smul_def] at hI_tr
    exact_mod_cast h1
  field_simp; linarith [mul_comm c (↑dim_n : ℝ)]

/-- The (0,0) entry of the coherent-state density operator equals `Complex.normSq(g₀₀)^n`.
    At index 0 : Fin(d^n), all big-endian digits are 0, so the coherent ket entry is g₀₀^n
    and the density operator entry is |g₀₀^n|² = Complex.normSq(g₀₀)^n. -/
lemma coherentDensityOp_entry_zero_eq {d n : ℕ} [NeZero d] [NeZero n]
    (g : unitaryGroup (Fin d) ℂ) :
    (coherentStateDensityOp g n).toOp (0 : Fin (d ^ n)) (0 : Fin (d ^ n)) =
    ↑(Complex.normSq (g.val 0 0) ^ n) := by
  -- ρ_g = |v^g⟩⟨v^g|, so entry (0,0) = v(0) * star(v(0))
  simp only [coherentStateDensityOp, DensityOp.fromPure, ket_mul_bra_apply, Ket.dag_vec,
    starRingEnd_apply]
  -- v(0) = ∏_j g_{digit_j(0), 0} = ∏_j g_{0, 0} = g₀₀^n
  simp only [coherentStateKet]
  -- All digits of 0 are 0: (0 / d^k) % d = 0
  have hdigit : ∀ j : Fin n,
      (⟨((0 : Fin (d ^ n)).val / d ^ (n - 1 - j.val)) % d,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩ : Fin d) = 0 := by
    intro j; ext; simp
  simp_rw [hdigit]
  -- Now: (∏ j, g 0 0) * star (∏ j, g 0 0) = g₀₀^n * conj(g₀₀^n) = normSq(g₀₀)^n
  rw [Finset.prod_const, Finset.card_fin, star_pow, ← mul_pow]
  -- Goal: (↑g 0 0 * star (↑g 0 0)) ^ n = ↑(Complex.normSq (↑g 0 0) ^ n)
  simp only [← starRingEnd_apply, Complex.mul_conj, ← Complex.ofReal_pow]

/-- The symmetric projector has entry 1 at position (0,0).
    The all-zeros standard basis vector e₀^⊗n is in the symmetric subspace:
    every permutation of tensor factors maps it to itself. -/
lemma symmetricProjector_entry_zero (d n : ℕ) [NeZero d] [NeZero n] :
    symmetricProjector d n (0 : Fin (d ^ n)) (0 : Fin (d ^ n)) = 1 := by
  -- P_sym = (1/n!) ∑_σ U_σ, and (U_σ)_{0,0} = 1 for all σ
  -- because σ permutes tensor factors but the all-zeros index is fixed by all permutations.
  unfold symmetricProjector Math.RepresentationTheory.symmetricProjectorRep
  simp only [Matrix.smul_apply, smul_eq_mul]
  -- Need: (∑ σ, U_σ 0 0) applied via 1/n! gives 1
  -- Each (U_σ)_{0,0} = 1 because permuting digits of 0 gives 0
  have h_perm_zero : ∀ σ : Equiv.Perm (Fin n),
      Math.RepresentationTheory.permutationRepresentation d n σ
        (0 : Fin (d ^ n)) (0 : Fin (d ^ n)) = 1 := by
    intro σ
    simp only [Math.RepresentationTheory.permutationRepresentation]
    simp only [Matrix.of_apply]
    -- Goal: if finFunctionFinEquiv.symm 0 = (finFunctionFinEquiv.symm 0) ∘ σ.symm then 1 else 0 = 1
    rw [if_pos]
    -- Goal: finFunctionFinEquiv.symm 0 = (finFunctionFinEquiv.symm 0) ∘ σ.symm
    ext j
    simp [finFunctionFinEquiv_symm_apply_val]
  rw [Matrix.sum_apply]
  simp_rw [h_perm_zero, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, mul_one, one_div]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- **Haar moment formula** for the (0,0) entry of U(d): ∫ |g₀₀|^{2n} dg = 1/C(n+d-1, d-1).

    **Proof**: The integrand `|g₀₀|^{2n}` equals the (0,0) entry of `|v^g⟩⟨v^g|`
    (by `coherentDensityOp_entry_zero_eq`). Pulling entry selection through the
    Bochner integral gives `(∫ ρ_g dg)_{0,0}`. By Schur's lemma for Sym^n(ℂ^d)
    (`coherent_integral_eq_inv_dim_smul_symProj_schur`), this equals
    `(1/dim) · (P_sym)_{0,0} = 1/dim` since e₀^⊗n ∈ Sym^n. -/
lemma haar_entry_moment_pow (d n : ℕ) [NeZero d] [NeZero n] :
    ∫ g : unitaryGroup (Fin d) ℂ,
      (↑(Complex.normSq (g.val 0 0) ^ n) : ℂ)
    ∂(haarProbUnitary d) =
    (↑(Nat.choose (n + d - 1) (d - 1)) : ℂ)⁻¹ := by
  -- Step 1: Rewrite integrand as the (0,0) entry of ρ_g
  have h_entry : ∀ g : unitaryGroup (Fin d) ℂ,
      (↑(Complex.normSq (g.val 0 0) ^ n) : ℂ) =
      (coherentStateDensityOp g n).toOp (0 : Fin (d ^ n)) (0 : Fin (d ^ n)) :=
    fun g => (coherentDensityOp_entry_zero_eq g).symm
  simp_rw [h_entry]
  -- Step 2: Pull entry selection through the Bochner integral using ContinuousLinearMap
  haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
  have h_int := coherentStateDensityOp_integrable d n
  let L : Op (d ^ n) →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M (0 : Fin (d ^ n)) (0 : Fin (d ^ n))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- The integral of entries = entry of integral (via CLM.integral_comp_comm)
  have h_interchange :
      ∫ g, (coherentStateDensityOp g n).toOp 0 0 ∂haarProbUnitary d =
      (∫ g, (coherentStateDensityOp g n).toOp ∂haarProbUnitary d) 0 0 := by
    exact L.integral_comp_comm h_int
  rw [h_interchange]
  -- Step 3: Apply Schur proportionality
  rw [coherent_integral_eq_inv_dim_smul_symProj_schur d n]
  -- Step 4: Evaluate (c • P_sym)_{0,0} = c · (P_sym)_{0,0} = c · 1 = c
  simp only [Matrix.smul_apply, symmetricProjector_entry_zero d n, Algebra.smul_def, mul_one,
    map_inv₀, map_natCast]

/-- The Haar moment integral: ∫∫ |⟨v_g, v_h⟩|² dg dh = 1/C(n+d-1, d-1).

    By Haar left-invariance (g → hg), the inner integral becomes
    ∫ |⟨v_{hg}, v_h⟩|² dg = ∫ |g₀₀|^{2n} dg. The Haar moment formula
    for U(d) gives ∫ |g₀₀|^{2n} dg = n!(d-1)!/(n+d-1)! = 1/C(n+d-1, d-1). -/
lemma haar_moment_overlap_integral (d n : ℕ) [NeZero d] [NeZero n] :
    ∫ h : unitaryGroup (Fin d) ℂ,
      ∫ g : unitaryGroup (Fin d) ℂ,
        (↑(Complex.normSq ((coherentStateKet g n).dag * (coherentStateKet h n))) : ℂ)
      ∂(haarProbUnitary d)
    ∂(haarProbUnitary d) =
    (↑(Nat.choose (n + d - 1) (d - 1)) : ℂ)⁻¹ := by
  haveI : IsProbabilityMeasure (haarProbUnitary d) :=
    haarProbUnitary_isProbability d
  have hLI : (haarProbUnitary d).IsMulLeftInvariant := by
    unfold haarProbUnitary haarOnUnitary; infer_instance
  -- Step 1: For each h, apply Haar left-invariance (g → h * g) to the inner integral.
  have h_shift : ∀ h₀ : unitaryGroup (Fin d) ℂ,
      ∫ g, (↑(Complex.normSq ((coherentStateKet g n).dag * coherentStateKet h₀ n)) : ℂ)
        ∂haarProbUnitary d =
      ∫ g, (↑(Complex.normSq ((coherentStateKet (h₀ * g) n).dag * coherentStateKet h₀ n)) : ℂ)
        ∂haarProbUnitary d := by
    intro h₀
    rw [← integral_mul_left_eq_self
        (fun g => (↑(Complex.normSq ((coherentStateKet g n).dag * coherentStateKet h₀ n)) : ℂ))
        h₀]
  -- Step 2: After the shift, the integrand simplifies to |g₀₀|^{2n}.
  have h_simp : ∀ h₀ : unitaryGroup (Fin d) ℂ,
      ∫ g, (↑(Complex.normSq ((coherentStateKet (h₀ * g) n).dag * coherentStateKet h₀ n)) : ℂ)
        ∂haarProbUnitary d =
      ∫ g, (↑(Complex.normSq (g.val 0 0) ^ n) : ℂ)
        ∂haarProbUnitary d := by
    intro h₀
    congr 1; ext g
    rw [normSq_overlap_hg_h g h₀ n]
  -- Step 3: The inner integral is now constant in h.
  have h_const : ∀ h₀ : unitaryGroup (Fin d) ℂ,
      ∫ g, (↑(Complex.normSq ((coherentStateKet g n).dag * coherentStateKet h₀ n)) : ℂ)
        ∂haarProbUnitary d =
      ∫ g, (↑(Complex.normSq (g.val 0 0) ^ n) : ℂ)
        ∂haarProbUnitary d := by
    intro h₀; rw [h_shift h₀, h_simp h₀]
  simp_rw [h_const]
  -- Step 4-5: The outer integral of a constant equals the constant (probability measure).
  -- Then convert to ℝ integral and apply the Haar moment formula.
  have h_intK : ∀ (K : ℂ),
      ∫ _ : unitaryGroup (Fin d) ℂ, K ∂haarProbUnitary d = K := by
    intro K; simp [integral_const]
  rw [h_intK]
  exact haar_entry_moment_pow d n

/-- Double Haar integral of `Tr(ρ_g · ρ_h)` equals `1 / dim(Sym^n)`.
    Reduces to `haar_moment_overlap_integral` via `trace_pure_mul_pure`. -/
lemma coherent_overlap_double_integral (d n : ℕ) [NeZero d] [NeZero n] :
    ∫ h : unitaryGroup (Fin d) ℂ,
      ∫ g : unitaryGroup (Fin d) ℂ,
        ((coherentStateDensityOp g n).toOp *
          (coherentStateDensityOp h n).toOp).trace
      ∂(haarProbUnitary d)
    ∂(haarProbUnitary d) =
    (↑(Nat.choose (n + d - 1) (d - 1)) : ℂ)⁻¹ := by
  -- Rewrite trace of product of pure-state projectors to squared overlap
  have h_trace : ∀ (g h : unitaryGroup (Fin d) ℂ),
      ((coherentStateDensityOp g n).toOp * (coherentStateDensityOp h n).toOp).trace =
      ↑(Complex.normSq ((coherentStateKet g n).dag * (coherentStateKet h n))) := by
    intro g h
    show ((coherentStateDensityOp g n).toOp * (coherentStateDensityOp h n).toOp).trace = _
    simp only [coherentStateDensityOp, DensityOp.fromPure]
    exact trace_pure_mul_pure (coherentStateKet g n) (coherentStateKet h n)
  simp_rw [h_trace]
  exact haar_moment_overlap_integral d n

/-- Frobenius norm squared of the coherent-state integral: trace(I²) = 1/dim.
    Decomposed as: Tr(I²) = ∫∫ Tr(ρ_g · ρ_h) dg dh = 1/dim.
    The first equality uses linearity of trace and matrix multiplication
    with the Bochner integral (via ContinuousLinearMap.integral_comp_comm).
    The second is the Haar moment computation in `coherent_overlap_double_integral`. -/
lemma coherent_integral_frobenius_sq (d n : ℕ) [NeZero d] [NeZero n] :
    let I_op := ∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d)
    (I_op * I_op).trace = (↑(Nat.choose (n + d - 1) (d - 1)) : ℂ)⁻¹ := by
  intro I_op
  have h_int := coherentStateDensityOp_integrable d n
  -- Step 1: Tr(I²) = ∫∫ Tr(ρ_g · ρ_h) dg dh
  -- Using CLMs to pull trace and multiplication through Bochner integrals.
  suffices h_eq : (I_op * I_op).trace =
      ∫ h : unitaryGroup (Fin d) ℂ,
        ∫ g : unitaryGroup (Fin d) ℂ,
          ((coherentStateDensityOp g n).toOp *
            (coherentStateDensityOp h n).toOp).trace
        ∂haarProbUnitary d
      ∂haarProbUnitary d by
    rw [h_eq]; exact coherent_overlap_double_integral d n
  -- Pull right integral through: Tr(I · I) = ∫_h Tr(I · ρ_h) dh
  -- CLM: X ↦ Tr(I_op * X)
  let trMulI : Op (d ^ n) →L[ℝ] ℂ :=
    (Matrix.traceLinearMap (Fin (d ^ n)) ℝ ℂ).toContinuousLinearMap.comp
      (LinearMap.mulLeft ℝ I_op).toContinuousLinearMap
  -- Then pull left integral through each inner term:
  -- Tr(I · ρ_h) = Tr((∫ ρ_g dg) · ρ_h) = ∫_g Tr(ρ_g · ρ_h) dg
  -- CLM: X ↦ Tr(X * ρ_h) for fixed h
  calc (I_op * I_op).trace
      = trMulI I_op := by simp [trMulI, Matrix.traceLinearMap_apply]
    _ = ∫ h, trMulI ((coherentStateDensityOp h n).toOp)
          ∂haarProbUnitary d :=
        (trMulI.integral_comp_comm h_int).symm
    _ = ∫ h, ∫ g, ((coherentStateDensityOp g n).toOp *
            (coherentStateDensityOp h n).toOp).trace
          ∂haarProbUnitary d
        ∂haarProbUnitary d := by
        congr 1; ext h
        -- For fixed h: trMulI(ρ_h) = Tr(I · ρ_h) = ∫ Tr(ρ_g · ρ_h) dg
        show trMulI ((coherentStateDensityOp h n).toOp) = _
        simp only [trMulI, ContinuousLinearMap.comp_apply,
          LinearMap.coe_toContinuousLinearMap', Matrix.traceLinearMap_apply,
          LinearMap.mulLeft_apply]
        -- Goal: (I_op * ρ_h).trace = ∫ (ρ_g * ρ_h).trace dg
        let trMulRh : Op (d ^ n) →L[ℝ] ℂ :=
          (Matrix.traceLinearMap (Fin (d ^ n)) ℝ ℂ).toContinuousLinearMap.comp
            (LinearMap.mulRight ℝ
              (coherentStateDensityOp h n).toOp).toContinuousLinearMap
        change trMulRh I_op = ∫ g,
          trMulRh ((coherentStateDensityOp g n).toOp)
          ∂haarProbUnitary d
        exact (trMulRh.integral_comp_comm h_int).symm

/-- **Schur's lemma for the symmetric subspace** (resolution of identity).
    ∫_{U(d)} dim(Sym^n(ℂᵈ)) · |v^g_n⟩⟨v^g_n| dg = P_sym.

    The coherent states form an overcomplete basis weighted by the
    dimension of the symmetric subspace. This follows from Schur's lemma:
    the integral commutes with all U^⊗n (by Haar invariance), so by
    irreducibility on the symmetric subspace, it must be proportional to P_sym.
    The proportionality constant is fixed by taking traces.

    **Reference**: CKMR definetti.tex lines 349-360, Harrow arXiv:1308.6595 §3. -/
theorem schur_lemma_symmetric (d n : ℕ) [NeZero d] [NeZero n] :
    ∫ g : unitaryGroup (Fin d) ℂ,
      (Nat.choose (n + d - 1) (d - 1) : ℝ) • (coherentStateDensityOp g n).toOp
      ∂(haarProbUnitary d) =
    symmetricProjector d n := by
  -- By CKMR definetti.tex line 346-351 and Harrow prop:twirl.
  -- Step 1: By Schur's lemma, ∫ |v^g⟩⟨v^g| dg = c • P_sym for some c.
  obtain ⟨c, hc⟩ := coherent_integral_proportional_irred d n
  -- Step 2: Determine c by taking traces.
  have h_trace := coherent_integral_trace d n
  have h_sym_trace := symmetricProjector_trace d n
  -- Step 3: Pull constant out, substitute, and simplify.
  rw [MeasureTheory.integral_smul, hc, smul_smul]
  rw [hc, Matrix.trace_smul, h_sym_trace] at h_trace
  conv_rhs => rw [← one_smul ℝ (symmetricProjector d n)]
  congr 1
  have h1 : (c : ℂ) * ↑((n + d - 1).choose (d - 1)) = 1 := by
    rwa [Algebra.smul_def] at h_trace
  have h_rc : c * (↑((n + d - 1).choose (d - 1)) : ℝ) = 1 := by exact_mod_cast h1
  linarith [mul_comm c (↑((n + d - 1).choose (d - 1)) : ℝ)]

/-- **Schur integral trace identity**: for Ψ in the symmetric subspace,
    ∫ dim(Sym^n) · ⟨v^g|Ψ|v^g⟩ dg = 1.

    This follows from `schur_lemma_symmetric` by sandwiching with Ψ and
    using P_sym Ψ P_sym = Ψ (since Ψ is in the symmetric subspace). -/
theorem schur_integral_trace (d n : ℕ) [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp) :
    ∫ g : unitaryGroup (Fin d) ℂ,
      (Nat.choose (n + d - 1) (d - 1) : ℝ) *
        ((coherentStateDensityOp g n).toOp * Ψ.toOp).trace.re
      ∂(haarProbUnitary d) = 1 := by
  -- Step 1: Get Schur's lemma
  have hschur := schur_lemma_symmetric d n
  -- Step 2: Multiply schur by Ψ and take trace
  -- Tr(P_sym * Ψ) = Tr(Ψ) = 1 using hsym and projector properties
  have hP := symmetricProjector_is_projector d n
  have hP_idem : symmetricProjector d n * symmetricProjector d n = symmetricProjector d n :=
    hP.1
  have hPΨ_trace : (symmetricProjector d n * Ψ.toOp).trace = Ψ.toOp.trace := by
    calc (symmetricProjector d n * Ψ.toOp).trace
        = (symmetricProjector d n * Ψ.toOp * symmetricProjector d n).trace := by
          rw [Matrix.trace_mul_comm (symmetricProjector d n * Ψ.toOp) (symmetricProjector d n)]
          rw [← Matrix.mul_assoc, hP_idem]
      _ = Ψ.toOp.trace := by rw [hsym]
  have hΨ_trace_one : Ψ.toOp.trace = 1 := by
    exact_mod_cast Ψ.trace_one
  -- Step 3: Connect scalar integral to matrix integral via entrywise Bochner
  -- ∫ dim * Tr(A(g) * Ψ).re dg = Tr((∫ dim • A(g) dg) * Ψ).re = Tr(P_sym * Ψ).re = 1
  -- Key step: interchange integral and trace (requires Bochner integrability)
  have h_interchange :
      ∫ g : unitaryGroup (Fin d) ℂ,
        (Nat.choose (n + d - 1) (d - 1) : ℝ) *
          ((coherentStateDensityOp g n).toOp * Ψ.toOp).trace.re
        ∂(haarProbUnitary d) =
      ((∫ g : unitaryGroup (Fin d) ℂ,
          (Nat.choose (n + d - 1) (d - 1) : ℝ) • (coherentStateDensityOp g n).toOp
          ∂(haarProbUnitary d)) * Ψ.toOp).trace.re := by
    -- Proof: pull constant c out of both sides, then interchange ∫ and Tr entry-by-entry.
    set c := (Nat.choose (n + d - 1) (d - 1) : ℝ) with hc_def
    set μ := haarProbUnitary d with hμ_def
    set A := fun g : unitaryGroup (Fin d) ℂ => (coherentStateDensityOp g n).toOp with hA_def
    -- Integrability helpers for entry-level interchange
    have h_entry_int : ∀ i j, MeasureTheory.Integrable (fun g => A g i j) μ :=
      fun i j => coherentStateDensityOp_entry_integrable i j
    -- Probability measure instance for integrability
    haveI : MeasureTheory.IsProbabilityMeasure μ := by
      rw [hμ_def]; exact haarProbUnitary_isProbability d
    -- Matrix-valued integrability
    have h_A_int : MeasureTheory.Integrable A μ :=
      (continuous_matrix
        (fun i j => coherentStateDensityOp_entry_continuous i j)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    -- Step 1: Pull constant c out of LHS
    rw [MeasureTheory.integral_const_mul]
    -- Step 2: Pull c out of RHS integral and through trace
    rw [MeasureTheory.integral_smul, smul_mul_assoc,
        Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    -- Now goal: c * ∫ (A g * Ψ).trace.re ∂μ = c * ((∫ A g ∂μ) * Ψ).trace.re
    congr 1
    -- Step 3: interchange ∫ and Tr(· * Ψ).re using ContinuousLinearMap.integral_comp_comm
    let L : Op (d ^ n) →L[ℝ] ℝ :=
      Complex.reCLM.comp
        ((Matrix.traceLinearMap (Fin (d ^ n)) ℝ ℂ).toContinuousLinearMap.comp
          (LinearMap.mulRight ℝ Ψ.toOp).toContinuousLinearMap)
    have hL_eq : ∀ M : Op (d ^ n), (M * Ψ.toOp).trace.re = L M := by
      intro M; simp [L, ContinuousLinearMap.comp_apply, LinearMap.mulRight_apply,
        Matrix.traceLinearMap_apply, Complex.reCLM_apply]
    simp_rw [hL_eq]
    exact L.integral_comp_comm h_A_int
  rw [h_interchange, hschur, hPΨ_trace, hΨ_trace_one]
  simp

end InfoTheory.DeFinetti.PureState
