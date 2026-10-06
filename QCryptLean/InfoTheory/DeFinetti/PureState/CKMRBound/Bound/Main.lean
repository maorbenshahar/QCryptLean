import QCryptLean.InfoTheory.DeFinetti.PureState.CKMRBound.Bound.SchurIdentities

/-!
# CKMR Trace Distance Bound — PSD decomposition, trace norm bound, main theorems

This module proves the CKMR trace distance bound for the pure-state quantum de Finetti
theorem. The key step is a PSD decomposition of ρ_k - σ_k into positive and negative
parts, each with trace bounded by 2(1 - dim_ratio). This uses three Schur lemma
identities (from the Schur-identities companion file) and the fact that
(1-P_g) · unnorm(g) · (1-P_g) is PSD.

## Main statements
- `ckmr_gamma_posSemidef`: The γ operator (1-2f)·ρ_k + f·σ_k is PSD
- `ckmr_psd_decomposition`: ρ_k - σ_k = P - Q with P, Q PSD and Tr ≤ 2(1-f)
- `ckmr_trace_distance_bound`: D(ρ_k, ∫ ρ_g^⊗k w(g) dg) ≤ 2(1 - dim_ratio)
- `pure_state_deFinetti_symmetric`: ∃ μ, ∀ k ≤ n, D(ρ_k, ∫ σ^⊗k dμ) ≤ 2dk/n

## References
- Christandl, König, Mitchison, Renner (2007) "One-and-a-Half Quantum de Finetti
  Theorems", Comm. Math. Phys. 273(2), 473-498 (Corollary II.2 / Theorem II.4)
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Symmetry MeasureTheory
open Math.HaarMeasure Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.DeFinetti.PureState

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-- Splitting a Bochner integral of a four-term combination a - b - c + d. -/
private lemma integral_four_split {α E : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f₁ f₂ f₃ f₄ : α → E}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ)
    (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ) :
    ∫ g, (f₁ g - f₂ g - f₃ g + f₄ g) ∂μ =
      ∫ g, f₁ g ∂μ - ∫ g, f₂ g ∂μ - ∫ g, f₃ g ∂μ + ∫ g, f₄ g ∂μ :=
  (integral_add ((h₁.sub h₂).sub h₃) h₄).trans
    (congr_arg₂ (· + ·)
      ((integral_sub (h₁.sub h₂) h₃).trans
        (congr_arg₂ (· - ·) (integral_sub h₁ h₂) rfl))
      rfl)

/-- The CKMR integral identity: expanding (1-P_g)·unnorm·(1-P_g) and applying
    three Schur lemma identities yields the γ operator expression.

    The three identities are:
    1. ∫ dim_{n-k} · unnorm(g) dg = ρ_k  (Schur on (n-k)-system)
    2. ∫ dim_{n-k} · P_g · unnorm(g) dg = f · ρ_k  (Schur on n-system)
    3. ∫ dim_{n-k} · P_g · unnorm(g) · P_g dg = f · σ_k  (weight factorization)

    **Reference**: CKMR definetti.tex lines 396-448. -/
lemma ckmr_gamma_identity {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (_hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    ((1 - 2 * ((Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
                Nat.choose (n + d - 1) (d - 1))) •
      (InfoTheory.DeFinetti.partialTraceToFirstK k _hk Ψ).toOp +
    ((Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
      Nat.choose (n + d - 1) (d - 1)) •
    ∫ g : unitaryGroup (Fin d) ℂ,
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
      ∂(haarProbUnitary d)) =
    ∫ g : unitaryGroup (Fin d) ℂ,
      (↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) •
      ((1 - (coherentStateDensityOp g k).toOp) *
       ckmrUnnorm Ψ k _hk g *
       (1 - (coherentStateDensityOp g k).toOp))
      ∂(haarProbUnitary d) := by
  -- Abbreviations (only scalar/matrix constants, not function-level)
  set haar := haarProbUnitary d
  set dim_nk : ℝ := ↑((n - k + d - 1).choose (d - 1))
  set f_ratio : ℝ := dim_nk / ↑((n + d - 1).choose (d - 1))
  haveI : IsProbabilityMeasure haar := haarProbUnitary_isProbability d
  -- Continuity (needed for integrability)
  have h_P_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ =>
      (coherentStateDensityOp g k).toOp) :=
    continuous_matrix (fun a b => coherentStateDensityOp_entry_continuous a b)
  have h_V_entry : ∀ (i : Fin (d ^ k * d ^ (n - k))) (a' : Fin (d ^ k)),
      Continuous (fun g : unitaryGroup (Fin d) ℂ => ckmrKetEmbed k _hk g i a') := by
    intro i a'
    simp only [ckmrKetEmbed, Matrix.of_apply]
    split_ifs
    · exact continuous_const
    · apply continuous_finsetProd; intro j _
      exact continuous_subtype_val.matrix_elem _ _
    · exact continuous_const
  have h_A_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ => ckmrUnnorm Ψ k _hk g) := by
    apply continuous_matrix; intro a b
    simp only [ckmrUnnorm, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply continuous_finsetSum; intro j _
    apply Continuous.mul
    · apply continuous_finsetSum; intro i _
      apply Continuous.mul
      · exact (h_V_entry i a).star
      · exact continuous_const
    · exact h_V_entry j b
  -- Integrability of each piece
  have h_int_1 : Integrable (fun g => dim_nk • ckmrUnnorm Ψ k _hk g) haar :=
    (continuous_const.smul h_A_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_int_2 : Integrable (fun g => dim_nk •
      ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g)) haar :=
    (continuous_const.smul (h_P_cont.mul h_A_cont)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_int_3 : Integrable (fun g => dim_nk •
      (ckmrUnnorm Ψ k _hk g * (coherentStateDensityOp g k).toOp)) haar :=
    (continuous_const.smul (h_A_cont.mul h_P_cont)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_int_4 : Integrable (fun g => dim_nk •
      ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g *
       (coherentStateDensityOp g k).toOp)) haar :=
    (continuous_const.smul ((h_P_cont.mul h_A_cont).mul h_P_cont)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- Expand integrand: dim_nk • (1-P)*A*(1-P) = dim_nk•A - dim_nk•P*A - dim_nk•A*P + dim_nk•P*A*P
  have h_expand : ∀ g : unitaryGroup (Fin d) ℂ,
      dim_nk • ((1 - (coherentStateDensityOp g k).toOp) * ckmrUnnorm Ψ k _hk g *
        (1 - (coherentStateDensityOp g k).toOp)) =
      dim_nk • ckmrUnnorm Ψ k _hk g -
      dim_nk • ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g) -
      dim_nk • (ckmrUnnorm Ψ k _hk g * (coherentStateDensityOp g k).toOp) +
      dim_nk • ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g *
        (coherentStateDensityOp g k).toOp) := by
    intro g
    have : (1 - (coherentStateDensityOp g k).toOp) * ckmrUnnorm Ψ k _hk g *
        (1 - (coherentStateDensityOp g k).toOp) =
        ckmrUnnorm Ψ k _hk g -
        (coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g -
        ckmrUnnorm Ψ k _hk g * (coherentStateDensityOp g k).toOp +
        (coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g *
          (coherentStateDensityOp g k).toOp := by
      simp only [sub_mul, one_mul, mul_sub, mul_one]; abel
    rw [this, smul_add, smul_sub, smul_sub]
  -- Split the four-term integral using helper
  simp_rw [h_expand]
  rw [integral_four_split h_int_1 h_int_2 h_int_3 h_int_4]
  -- Apply the four Schur identities
  rw [ckmr_schur_identity_1 Ψ _hsym k _hk,
      ckmr_schur_identity_2 Ψ _hsym k _hk,
      ckmr_schur_identity_2' Ψ _hsym k _hk,
      ckmr_schur_identity_3 Ψ _hsym k _hk]
  -- Final algebra: ρ - f•ρ - f•ρ + f•σ = (1-2f)•ρ + f•σ
  module

/-- The CKMR γ operator has an integral representation as a sum of PSD operators.

    γ := (1-2f)·ρ_k + f·σ_k = ∫ dim(Sym^{n-k}) · (I-P_g) · unnorm(g) · (I-P_g) dg

    where unnorm(g) = (I_k ⊗ ⟨v^g_{n-k}|) Ψ (I_k ⊗ |v^g_{n-k}⟩) is PSD (compression
    of PSD Ψ) and (I-P_g) is self-adjoint, so each integrand is PSD.

    The identity follows from three Schur lemma applications:
    - ∫ dim_nk · unnorm(g) dg = ρ_k
    - ∫ dim_nk · P_g · unnorm(g) dg = f · ρ_k
    - ∫ dim_nk · ⟨v|unnorm|v⟩ · P_g dg = f · σ_k

    **Reference**: CKMR definetti.tex lines 396-448. -/
lemma ckmr_gamma_integral_form {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (_hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    ∃ (F : unitaryGroup (Fin d) ℂ → Op (d ^ k)),
      (∀ g, (F g).PosSemidef) ∧
      MeasureTheory.Integrable F (haarProbUnitary d) ∧
      ((1 - 2 * ((Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
                  Nat.choose (n + d - 1) (d - 1))) •
        (InfoTheory.DeFinetti.partialTraceToFirstK k _hk Ψ).toOp +
      ((Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
        Nat.choose (n + d - 1) (d - 1)) •
      ∫ g : unitaryGroup (Fin d) ℂ,
        postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
        ∂(haarProbUnitary d)) =
      ∫ g : unitaryGroup (Fin d) ℂ, F g ∂(haarProbUnitary d) := by
  -- The integrand: F(g) = dim_{n-k} • (1 - P_g) * unnorm(g) * (1 - P_g)
  refine ⟨fun g => (↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) •
    ((1 - (coherentStateDensityOp g k).toOp) *
     ckmrUnnorm Ψ k _hk g *
     (1 - (coherentStateDensityOp g k).toOp)), ?_, ?_, ?_⟩
  · -- PSD: dim_{n-k} • (1-P_g) * unnorm * (1-P_g) is PSD
    intro g
    -- Step 1: unnorm(g) is PSD
    have h_unnorm := ckmrUnnorm_posSemidef Ψ k _hk g
    -- Step 2: B† * PSD * B is PSD for any B
    have h_conj := h_unnorm.conjTranspose_mul_mul_same
      (1 - (coherentStateDensityOp g k).toOp)
    -- Step 3: (1-P_g) is Hermitian, so (1-P_g)† = (1-P_g)
    have h_Pg_herm : ((coherentStateDensityOp g k).toOp).IsHermitian :=
      (posSemidefOp_implies_mathlib (coherentStateDensityOp g k).toPosSemidefOp).isHermitian
    rw [(Matrix.isHermitian_one.sub h_Pg_herm).eq] at h_conj
    -- Step 4: nonneg real smul of PSD is PSD
    exact h_conj.smul (by positivity : (0 : ℝ) ≤ ↑(Nat.choose (n - k + d - 1) (d - 1)))
  · -- Integrable: continuous on compact space → integrable w.r.t. probability measure
    haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
    apply (Continuous.integrable_of_hasCompactSupport · (HasCompactSupport.of_compactSpace _))
    apply continuous_const.smul
    -- Continuity of coherentStateDensityOp entries
    have h_Pg_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ =>
        (coherentStateDensityOp g k).toOp) :=
      continuous_matrix (fun a b => coherentStateDensityOp_entry_continuous a b)
    -- Continuity of ckmrKetEmbed entries
    have h_V_entry : ∀ (i : Fin (d ^ k * d ^ (n - k))) (a' : Fin (d ^ k)),
        Continuous (fun g : unitaryGroup (Fin d) ℂ => ckmrKetEmbed k _hk g i a') := by
      intro i a'
      simp only [ckmrKetEmbed, Matrix.of_apply]
      split_ifs
      · exact continuous_const  -- n-k=0, index match: value is 1
      · apply continuous_finsetProd; intro j _  -- n-k≠0, index match: ∏ g entries
        exact continuous_subtype_val.matrix_elem _ _
      · exact continuous_const  -- index mismatch: value is 0
    -- Continuity of ckmrUnnorm = V† * Ψ_bip * V
    have h_unnorm_cont : Continuous (fun g => ckmrUnnorm Ψ k _hk g) := by
      apply continuous_matrix; intro a b
      simp only [ckmrUnnorm, Matrix.mul_apply, Matrix.conjTranspose_apply]
      apply continuous_finsetSum; intro j _
      apply Continuous.mul
      · apply continuous_finsetSum; intro i _
        apply Continuous.mul
        · exact (h_V_entry i a).star
        · exact continuous_const
      · exact h_V_entry j b
    exact ((continuous_const.sub h_Pg_cont).mul h_unnorm_cont).mul
      (continuous_const.sub h_Pg_cont)
  · -- Integral identity: follows from the three Schur lemma applications
    exact ckmr_gamma_identity Ψ _hsym k _hk

/-- The CKMR γ operator is positive semidefinite:
    γ := (1-2f)·ρ_k + f·σ_k ≥ 0.

    This is the key content of the CKMR decomposition. The γ operator equals
    ∫ dim(Sym^{n-k}) · (I-P_g) · unnorm(g) · (I-P_g) dg, which is an integral
    of PSD operators (since unnorm(g) = (I⊗⟨v^g|)Ψ(I⊗|v^g⟩) is PSD for PSD Ψ),
    weighted by the positive scalar dim(Sym^{n-k}).

    The integral representation follows from:
    - ∫ dim_nk · unnorm(g) dg = ρ_k (Schur + symmetric containment)
    - ∫ dim_nk · P_g · unnorm(g) dg = f · ρ_k (Schur on n-system)
    - ∫ dim_nk · ⟨v|unnorm|v⟩ · P_g dg = f · σ_k (weight factorization)
    Combining: γ = ρ_k - 2f·ρ_k + f·σ_k = (1-2f)·ρ_k + f·σ_k. ✓

    **Reference**: CKMR definetti.tex lines 396-448. -/
lemma ckmr_gamma_posSemidef {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (_hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    ((1 - 2 * ((Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
                Nat.choose (n + d - 1) (d - 1))) •
      (InfoTheory.DeFinetti.partialTraceToFirstK k _hk Ψ).toOp +
    ((Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
      Nat.choose (n + d - 1) (d - 1)) •
    ∫ g : unitaryGroup (Fin d) ℂ,
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
      ∂(haarProbUnitary d)).PosSemidef := by
  obtain ⟨F, hF_psd, hF_int, hγ_eq⟩ := ckmr_gamma_integral_form Ψ _hsym k _hk
  rw [hγ_eq]
  exact bochner_integral_posSemidef F hF_int hF_psd

/-- The CKMR negative-part operator Q = (1-2f)·ρ_k + σ_k is positive semidefinite.

    Algebraically, Q = γ + (1-f)·σ_k where γ = (1-2f)·ρ_k + f·σ_k.
    Both terms are PSD: γ by `ckmr_gamma_posSemidef` (CKMR integral decomposition),
    and (1-f)·σ_k since 0 ≤ f ≤ 1 and σ_k is PSD.

    **Reference**: CKMR definetti.tex lines 385-448. -/
lemma ckmr_Q_posSemidef {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (hk : k ≤ n) :
    ((1 - 2 * ((Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
                Nat.choose (n + d - 1) (d - 1))) •
      (InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ).toOp +
    ∫ g : unitaryGroup (Fin d) ℂ,
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
      ∂(haarProbUnitary d)).PosSemidef := by
  -- σ_k is PSD: it equals (integralTensorPower k μ).toOp which is a DensityOp
  have hσ_psd : (∫ g : unitaryGroup (Fin d) ℂ,
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
      ∂haarProbUnitary d).PosSemidef := by
    rw [← integralTensorPower_coherentState_eq Ψ hsym k hk]
    exact posSemidefOp_implies_mathlib
      (InfoTheory.DeFinetti.integralTensorPower k
        (coherentState_deFinettiMeasure d Ψ hsym)).toPosSemidefOp
  -- ρ_k is PSD
  have hρ_psd := posSemidefOp_implies_mathlib
    (InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ).toPosSemidefOp
  -- Split on the sign of (1 - 2f)
  by_cases hf : (0 : ℝ) ≤ 1 - 2 * (↑((n - k + d - 1).choose (d - 1)) /
      ↑((n + d - 1).choose (d - 1)))
  · -- Case f ≤ 1/2: both summands PSD, use PosSemidef.add
    exact (hρ_psd.smul hf).add hσ_psd
  · -- Case f > 1/2: decompose Q = γ + (1-f)·σ_k, both PSD
    set f : ℝ := ↑((n - k + d - 1).choose (d - 1)) / ↑((n + d - 1).choose (d - 1))
    set ρ := (InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ).toOp
    set σ := ∫ g : unitaryGroup (Fin d) ℂ,
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
      ∂haarProbUnitary d
    -- γ = (1-2f)·ρ + f·σ is PSD by CKMR integral decomposition
    have hγ : ((1 - 2 * f) • ρ + f • σ).PosSemidef := ckmr_gamma_posSemidef Ψ hsym k hk
    -- (1-f)·σ is PSD since 0 ≤ f ≤ 1 and σ PSD
    have hf_le : f ≤ 1 := dim_ratio_le_one hk
    have h1f : ((1 - f) • σ).PosSemidef := hσ_psd.smul (by linarith)
    -- Q = γ + (1-f)·σ algebraically
    suffices heq : (1 - 2 * f) • ρ + σ = ((1 - 2 * f) • ρ + f • σ) + (1 - f) • σ by
      rw [heq]; exact hγ.add h1f
    -- σ = f·σ + (1-f)·σ
    have hσ_split : σ = f • σ + (1 - f) • σ := by
      rw [← add_smul, show f + (1 - f) = 1 from by ring, one_smul]
    conv_lhs => rw [hσ_split]
    abel

/-- CKMR PSD decomposition of ρ_k - σ_k (definetti.tex lines 390-440).

    The difference ρ_k - σ_k decomposes as P - Q where P = α + β and Q = γ + δ
    are PSD operators with traces bounded by 2(1-f). Here:
    - α = (1-f)·ρ_k (from ∫ w(g)(ξ^g_k - P_g·ξ^g_k) dg, using Schur's lemma)
    - β = (1-f)·ρ_k (adjoint of α)
    - γ = ∫ w(g)(I-P_g)·ξ^g_k·(I-P_g) dg (PSD, Tr = 1-f)
    - δ = ∫ w(g)(1-⟨v^g_k|ξ^g_k|v^g_k⟩)P_g dg (PSD, Tr = 1-f)

    **Reference**: CKMR definetti.tex lines 385-448. -/
lemma ckmr_psd_decomposition {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (hk : k ≤ n) :
    let f : ℝ := (Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
                  Nat.choose (n + d - 1) (d - 1)
    let diff := (InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ).toOp -
               ∫ g : unitaryGroup (Fin d) ℂ,
                 postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
                 ∂(haarProbUnitary d)
    ∃ (P Q : Op (d ^ k)),
      diff = P - Q ∧
      P.PosSemidef ∧ Q.PosSemidef ∧
      P.trace.re ≤ 2 * (1 - f) ∧ Q.trace.re ≤ 2 * (1 - f) := by
  -- CKMR decomposition: P = 2(1-f)·ρ_k (positive part), Q = (1-2f)·ρ_k + σ_k (negative part)
  -- Then P - Q = 2(1-f)·ρ_k - (1-2f)·ρ_k - σ_k = ρ_k - σ_k = diff  ✓
  -- Tr(P) = 2(1-f)·1 = 2(1-f)  ✓
  -- Tr(Q) = (1-2f)·1 + 1 = 2(1-f)  ✓ (using Tr(σ_k) = 1 from approx_integral_trace_re)
  set f : ℝ := (↑((n - k + d - 1).choose (d - 1))) / ↑((n + d - 1).choose (d - 1))
  set ρ_k := InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ
  set σ_k := ∫ g : unitaryGroup (Fin d) ℂ,
    postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
    ∂(haarProbUnitary d) with hσ_def
  refine ⟨(2 * (1 - f)) • ρ_k.toOp,
          (1 - 2 * f) • ρ_k.toOp + σ_k,
          ?eq, ?psd_P, ?psd_Q, ?tr_P, ?tr_Q⟩
  case eq =>
    -- diff = P - Q: (2(1-f) - (1-2f)) = 1, so P - Q = 1·ρ_k - σ_k = ρ_k - σ_k = diff
    rw [sub_add_eq_sub_sub, ← sub_smul]
    simp only [show (2 * (1 - f) - (1 - 2 * f)) = (1 : ℝ) from by ring, one_smul]
  case psd_P =>
    -- P = 2(1-f) · ρ_k is PSD since 2(1-f) ≥ 0 and ρ_k is PSD
    have hf_le : f ≤ 1 := dim_ratio_le_one hk
    exact (posSemidefOp_implies_mathlib ρ_k.toPosSemidefOp).smul (by linarith)
  case psd_Q =>
    -- Q = (1-2f)·ρ_k + σ_k is PSD (the core CKMR content)
    exact ckmr_Q_posSemidef Ψ hsym k hk
  case tr_P =>
    -- Tr(P).re = 2(1-f) · Tr(ρ_k).re = 2(1-f) · 1 = 2(1-f)
    rw [Matrix.trace_smul, ρ_k.trace_one, Complex.smul_re, Complex.one_re,
        smul_eq_mul, mul_one]
  case tr_Q =>
    -- Tr(Q).re = (1-2f) + Tr(σ_k).re = (1-2f) + 1 = 2(1-f)
    rw [Matrix.trace_add, Matrix.trace_smul, ρ_k.trace_one, Complex.add_re,
        Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one,
        approx_integral_trace_re Ψ hsym k hk]
    linarith

/-- Integrated trace norm bound (CKMR alpha/beta/gamma/delta decomposition).

    The difference ρ_k - approx has traceNormHermitian ≤ 4(1 - dim_ratio), where
    traceNormHermitian = tr|A| = Σ|eigenvalues|. (CKMR uses ‖·‖ = (1/2)tr|A| and
    proves ‖ξ-mixture‖ ≤ 2(1-r); converting: 2 × 2(1-r) = 4(1-r).)

    The proof defines S = α + β - γ (definetti.tex line 400) and δ separately,
    so ρ_k - approx = S - δ = α + β - γ - δ, then bounds each of the four
    terms by (1-r) in traceNormHermitian after integration.

    NOTE: CKMR does NOT establish per-outcome bounds. The cancellations happen
    only after integrating over g.

    **Reference**: CKMR definetti.tex lines 385-448. -/
lemma integrated_trace_norm_bound {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (hk : k ≤ n)
    (h_herm : ((InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ).toOp -
               ∫ g : unitaryGroup (Fin d) ℂ,
                 postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
                 ∂(haarProbUnitary d)).IsHermitian) :
    -- The difference between ρ_k and the integrated coherent-state approximation
    -- has trace norm at most 4(1 - dim_ratio)
    traceNormHermitian ((InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ).toOp -
               ∫ g : unitaryGroup (Fin d) ℂ,
                 postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
                 ∂(haarProbUnitary d)) h_herm ≤
        4 * (1 - (Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
                Nat.choose (n + d - 1) (d - 1)) := by
  -- Step 1: Get the CKMR PSD decomposition diff = P - Q
  set f : ℝ := (Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
                Nat.choose (n + d - 1) (d - 1)
  obtain ⟨P, Q, h_eq, hP, hQ, hP_tr, hQ_tr⟩ := ckmr_psd_decomposition Ψ hsym k hk
  -- Step 2: Apply the PSD decomposition trace norm bound
  -- traceNormHermitian (P - Q) ≤ (Tr(P) + Tr(Q)).re
  have h_bound :=
    Quantum.Metrics.traceNormHermitian_le_trace_posSemidef_sub
      _ P Q h_herm hP hQ h_eq
  -- Step 3: Bound (Tr(P) + Tr(Q)).re ≤ 4(1-f)
  calc traceNormHermitian _ h_herm
      ≤ (P.trace + Q.trace).re := h_bound
    _ = P.trace.re + Q.trace.re := Complex.add_re P.trace Q.trace
    _ ≤ 2 * (1 - f) + 2 * (1 - f) := add_le_add hP_tr hQ_tr
    _ = 4 * (1 - f) := by ring

/-- **CKMR trace distance bound** (core estimate for Theorem II.2).

    D(ρ_k, ∫ |v^g_k⟩⟨v^g_k| w(g) dg) ≤ 2(1 - dim_ratio)

    where dim_ratio = C(n-k+d-1,d-1)/C(n+d-1,d-1).

    This combines `integrated_trace_norm_bound` with the fact that the
    coherent-state mixture equals `integralTensorPower k μ` when μ is
    the POVM-weighted pushforward measure `coherentState_deFinettiMeasure`.

    **Reference**: CKMR definetti.tex lines 410-440. -/
theorem ckmr_trace_distance_bound (d n : ℕ) [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (hk : k ≤ n) :
    traceDistance (InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ).toOp
      (InfoTheory.DeFinetti.integralTensorPower k
        (coherentState_deFinettiMeasure d Ψ hsym)).toOp ≤
      2 * (1 - (Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
              Nat.choose (n + d - 1) (d - 1)) := by
  -- Step 1: Connect integralTensorPower with the POVM integral form
  have h_eq := integralTensorPower_coherentState_eq Ψ hsym k hk
  set ρ_k := InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ
  set μ := coherentState_deFinettiMeasure d Ψ hsym
  set σ := InfoTheory.DeFinetti.integralTensorPower k μ
  have h_sub_eq : ρ_k.toOp - σ.toOp = ρ_k.toOp -
      ∫ g : unitaryGroup (Fin d) ℂ,
        postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
        ∂(haarProbUnitary d) := by
    rw [sub_right_inj]; exact h_eq
  -- Step 2: Apply integrated_trace_norm_bound
  have h_herm_approx : (ρ_k.toOp - ∫ g : unitaryGroup (Fin d) ℂ,
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
      ∂(haarProbUnitary d)).IsHermitian := by
    rw [← h_sub_eq]; exact densityOp_sub_isHermitian ρ_k σ
  have h_tn_bound := integrated_trace_norm_bound Ψ hsym k hk h_herm_approx
  -- Step 3: Transport the trace norm bound to the original form
  have h_herm_orig := densityOp_sub_isHermitian ρ_k σ
  have h_tn_transport : traceNormHermitian (ρ_k.toOp - σ.toOp) h_herm_orig ≤
      4 * (1 - ↑((n - k + d - 1).choose (d - 1)) /
              ↑((n + d - 1).choose (d - 1))) := by
    have : ρ_k.toOp - σ.toOp = ρ_k.toOp -
        ∫ g : unitaryGroup (Fin d) ℂ,
          postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
          ∂(haarProbUnitary d) := h_sub_eq
    calc traceNormHermitian (ρ_k.toOp - σ.toOp) h_herm_orig
        = traceNormHermitian (ρ_k.toOp - ∫ g : unitaryGroup (Fin d) ℂ,
            postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
            ∂(haarProbUnitary d)) h_herm_approx := by
          simp only [this]
      _ ≤ 4 * (1 - ↑((n - k + d - 1).choose (d - 1)) /
              ↑((n + d - 1).choose (d - 1))) := h_tn_bound
  -- Step 4: Unfold traceDistance = (1/2) * traceNormHermitian, combine
  rw [Quantum.Metrics.traceDistance_densityOp_eq_traceNormHermitian]
  calc 1 / 2 * traceNormHermitian (ρ_k.toOp - σ.toOp) (densityOp_sub_isHermitian ρ_k σ)
      ≤ 1 / 2 * (4 * (1 - ↑((n - k + d - 1).choose (d - 1)) /
              ↑((n + d - 1).choose (d - 1)))) := by
        apply mul_le_mul_of_nonneg_left h_tn_transport (by norm_num : (0:ℝ) ≤ 1 / 2)
    _ = 2 * (1 - ↑((n - k + d - 1).choose (d - 1)) /
            ↑((n + d - 1).choose (d - 1))) := by ring

/-!
## Section 6: Main Theorem

The pure-state de Finetti theorem: for Ψ in the symmetric subspace of (ℂᵈ)^⊗n,
there exists a probability measure μ over pure states such that for all k ≤ n,
the k-copy reduced state is within 2dk/n of the de Finetti mixture.
-/

/-- **Quantum de Finetti theorem for Bose-symmetric states** (CKMR 2007, Corollary II.2).

    For any state Ψ in the symmetric subspace of (ℂᵈ)^⊗n, there exists
    a probability measure μ on DensityOp d such that for ALL k ≤ n:

      D(Tr_{k+1,...,n}[Ψ], ∫ σ^⊗k dμ(σ)) ≤ 2dk/n.

    The measure μ is constructed once from the coherent-state POVM on
    systems 1,...,n and works for all k simultaneously.

    **Proof outline** (CKMR definetti.tex lines 333-495):
    1. Construct coherent-state POVM from Schur's lemma
    2. Show post-measurement state is close to coherent (dimension ratio)
    3. Bound trace distance via `ckmr_trace_distance_bound`
    4. Simplify 2(1 - dim_ratio) ≤ 2dk/n via `dim_ratio_bound` -/
theorem pure_state_deFinetti_symmetric (d n : ℕ) [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp) :
    ∃ μ : InfoTheory.DeFinetti.DensityMeasure d,
      ∀ (k : ℕ) [NeZero k] (hk : k ≤ n),
        traceDistance (InfoTheory.DeFinetti.partialTraceToFirstK k hk Ψ).toOp
          (InfoTheory.DeFinetti.integralTensorPower k μ).toOp ≤
            2 * (d : ℝ) * k / n := by
  -- Witness: the POVM-derived measure (same for all k).
  refine ⟨coherentState_deFinettiMeasure d Ψ hsym, fun k _ hk => ?_⟩
  -- Step 1: Apply the CKMR trace distance bound
  have h1 := ckmr_trace_distance_bound d n Ψ hsym k hk
  -- Step 2: Apply the dimension ratio bound
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h2 := dim_ratio_bound d n k hd hn hk
  -- Chain: traceDistance ≤ 2*(1 - ratio) ≤ 2*dk/n
  -- h2 says 1 - dk/n ≤ ratio, equivalently 1 - ratio ≤ dk/n
  -- so 2*(1 - ratio) ≤ 2*dk/n
  calc traceDistance _ _ ≤ 2 * (1 - (↑((n - k + d - 1).choose (d - 1)) : ℝ) /
          ↑((n + d - 1).choose (d - 1))) := h1  -- h1 : traceDistance _.toOp _.toOp ≤ ...
    _ ≤ 2 * (↑d * ↑k / ↑n) := by linarith
    _ = 2 * ↑d * ↑k / ↑n := by ring

end InfoTheory.DeFinetti.PureState
