import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.LeftIsometryPenaltyEmbedding

/-!
# Isometric embedding dimension penalties

An isometric embedding compares conditional and smooth entropy against maximally mixed references.
The real logarithmic dimension penalty appears as a finite additive charge in the canonical smooth
entropy comparison.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

private lemma subDensityOp_toOp_eq_zero_of_trace_eq_zero
    {d : ℕ} (ρ : SubDensityOp d) (htrace : ρ.trace = 0) :
    ρ.toOp = 0 := by
  have hpsd : Matrix.PosSemidef ρ.toOp :=
    posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have htrace_complex : ρ.toOp.trace = 0 := by
    rw [SubDensityOp.trace_complex_eq, htrace]
    norm_num
  exact hpsd.trace_eq_zero_iff.mp htrace_complex

private lemma cqState_stateMap_toOp_eq_zero_of_weight_nonpos
    {α : Type*} [Fintype α] {d : ℕ}
    (ρ : CQState α d)
    (hweight : ¬ 0 < ∑ x : α, (ρ.stateMap x).trace) :
    ∀ x : α, (ρ.stateMap x).toOp = 0 := by
  classical
  have hsum_nonpos : (∑ x : α, (ρ.stateMap x).trace) ≤ 0 := le_of_not_gt hweight
  intro x
  have hx_nonneg : 0 ≤ (ρ.stateMap x).trace := (ρ.stateMap x).trace_nonneg
  have hx_le_sum :
      (ρ.stateMap x).trace ≤ ∑ y : α, (ρ.stateMap y).trace :=
    Finset.single_le_sum (fun y _ => (ρ.stateMap y).trace_nonneg) (Finset.mem_univ x)
  have hx_trace_zero : (ρ.stateMap x).trace = 0 :=
    le_antisymm (le_trans hx_le_sum hsum_nonpos) hx_nonneg
  exact subDensityOp_toOp_eq_zero_of_trace_eq_zero (ρ.stateMap x) hx_trace_zero

private lemma cqState_weight_pos_of_minFeasibleLambda_pos
    {α : Type*} [Fintype α] {d : ℕ}
    (ρ : CQState α d) (σ : SubDensityOp d)
    (hpos : 0 < minFeasibleLambda ρ σ) :
    0 < ∑ x : α, (ρ.stateMap x).trace := by
  by_contra hweight
  have hzero_blocks : ∀ x : α, (ρ.stateMap x).toOp = 0 :=
    cqState_stateMap_toOp_eq_zero_of_weight_nonpos ρ hweight
  have hlam_zero : minFeasibleLambda ρ σ = 0 :=
    minFeasibleLambda_eq_zero_of_stateMap_zero ρ hzero_blocks σ
  linarith

private lemma cqState_nonempty_of_weight_pos
    {α : Type*} [Fintype α] {d : ℕ}
    (ρ : CQState α d)
    (hweight : 0 < ∑ x : α, (ρ.stateMap x).trace) :
    Nonempty α := by
  classical
  by_contra hne
  have : IsEmpty α := not_nonempty_iff.mp hne
  have hsum : (∑ x : α, (ρ.stateMap x).trace) = 0 := by
    simp
  linarith

private lemma cqState_weight_eq_of_left_isometry_embed
    {α : Type*} [Fintype α] {dSrc dTgt : ℕ}
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK_iso : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ : CQState α dSrc) (ρ_embed : CQState α dTgt)
    (h_embed : ∀ x : α,
      (ρ_embed.stateMap x).toOp = K * (ρ.stateMap x).toOp * Kᴴ) :
    (∑ x : α, (ρ_embed.stateMap x).trace) =
      ∑ x : α, (ρ.stateMap x).trace := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  unfold SubDensityOp.trace
  rw [h_embed x, trace_rect_conj_of_left_isometry K hK_iso (ρ.stateMap x).toOp]

/-- The base-two logarithmic dimension penalty is nonnegative under inclusion. -/
theorem log_dim_penalty_nonneg_of_le
    {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    (hdim : d₁ ≤ d₂) :
    0 ≤ Real.log (d₂ : ℝ) / Real.log 2 -
      Real.log (d₁ : ℝ) / Real.log 2 := by
  have hd₁_pos : 0 < (d₁ : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d₁)
  have hdim_real : (d₁ : ℝ) ≤ (d₂ : ℝ) := by
    exact_mod_cast hdim
  have hlog_dim_le :
      Real.log (d₁ : ℝ) ≤ Real.log (d₂ : ℝ) :=
    Real.log_le_log hd₁_pos hdim_real
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← sub_div]
  exact div_nonneg (sub_nonneg.mpr hlog_dim_le) hlog2_pos.le

/-- Candidate-level real min-entropy comparison for a source CQ candidate and
its `K = I_E ⊗ V` embedded ambient candidate: given the feasibility-scaling
hypothesis relating the two minimal feasible `λ`'s, the source conditional
min-entropy is bounded by the ambient one plus the dimension penalty
`log₂ dR₂ - log₂ dR₁`. -/
theorem conditionalMinEntropyReal_maxMixed_left_isometry_embed_le_add_dimPenalty
    (Xcl : Type) [Fintype Xcl]
    {dE dR₁ dR₂ : ℕ} [NeZero dE] [NeZero dR₁] [NeZero dR₂]
    (hdim : dR₁ ≤ dR₂)
    (ρ : CQState Xcl (dE * dR₁))
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_embed : CQState Xcl (dE * dR₂))
    (h_embed : ∀ x : Xcl,
      (ρ_embed.stateMap x).toOp =
        kronIdLeftIso (dH := dE) V *
          (ρ.stateMap x).toOp *
          (kronIdLeftIso (dH := dE) V)ᴴ)
    (hscale : ∀ {t : ℝ},
      isFeasible ρ
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))) t →
        isFeasible ρ_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂)))
          (((dR₂ : ℝ) / (dR₁ : ℝ)) * t)) :
    conditionalMinEntropyReal ρ
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))) ≤
      conditionalMinEntropyReal ρ_embed
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))) +
        (Real.log (dR₂ : ℝ) / Real.log 2 -
          Real.log (dR₁ : ℝ) / Real.log 2) := by
  classical
  let σ₁ : SubDensityOp (dE * dR₁) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))
  let σ₂ : SubDensityOp (dE * dR₂) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))
  let lam1 : ℝ := minFeasibleLambda ρ σ₁
  let lam2 : ℝ := minFeasibleLambda ρ_embed σ₂
  let c : ℝ := (dR₂ : ℝ) / (dR₁ : ℝ)
  have hdR₁_pos : 0 < (dR₁ : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dR₁)
  have hdR₂_pos : 0 < (dR₂ : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dR₂)
  have hdR₁_ne : (dR₁ : ℝ) ≠ 0 := ne_of_gt hdR₁_pos
  have hdR₂_ne : (dR₂ : ℝ) ≠ 0 := ne_of_gt hdR₂_pos
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (Nat.cast_nonneg dR₂) (Nat.cast_nonneg dR₁)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos hdR₂_pos hdR₁_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hσ₁_pd : σ₁.toOp.PosDef := by
    simpa [σ₁] using
      maxMixed_toSubDensityOp_posDef
        (dE := dE * dR₁)
  have hσ₂_pd : σ₂.toOp.PosDef := by
    simpa [σ₂] using
      maxMixed_toSubDensityOp_posDef
        (dE := dE * dR₂)
  have hfeas₁ : hasFeasibleLambda ρ σ₁ :=
    InfoTheory.SmoothMinEntropy.hasFeasibleLambda_of_posDef ρ σ₁ hσ₁_pd
  have hfeas₂ : hasFeasibleLambda ρ_embed σ₂ :=
    InfoTheory.SmoothMinEntropy.hasFeasibleLambda_of_posDef ρ_embed σ₂ hσ₂_pd
  have hlam_le : lam2 ≤ c * lam1 := by
    simpa [lam1, lam2, σ₁, σ₂, c] using
      InfoTheory.SmoothMinEntropy.minFeasibleLambda_le_mul_of_isFeasible_scaling
        ρ σ₁ ρ_embed σ₂ hc_nonneg hfeas₁
        (fun {t} ht => hscale (by simpa [σ₁] using ht))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hlam1_pos : 0 < lam1
  · have hweight₁ : 0 < ∑ x : Xcl, (ρ.stateMap x).trace :=
      cqState_weight_pos_of_minFeasibleLambda_pos ρ σ₁ hlam1_pos
    have : Nonempty Xcl := cqState_nonempty_of_weight_pos ρ hweight₁
    let K := kronIdLeftIso (dH := dE) V
    have hK_iso :
        Kᴴ * K = (1 : Matrix (Fin (dE * dR₁)) (Fin (dE * dR₁)) ℂ) := by
      simpa [K] using kronIdLeftIso_left_iso (dH := dE) V hV_iso
    have hweight_eq :
        (∑ x : Xcl, (ρ_embed.stateMap x).trace) =
          ∑ x : Xcl, (ρ.stateMap x).trace := by
      exact cqState_weight_eq_of_left_isometry_embed K hK_iso ρ ρ_embed
        (by intro x; simpa [K] using h_embed x)
    have hweight₂ : 0 < ∑ x : Xcl, (ρ_embed.stateMap x).trace := by
      rwa [hweight_eq]
    have hlam2_pos : 0 < lam2 := by
      simpa [lam2, σ₂] using
        InfoTheory.SmoothMinEntropy.minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos
          ρ_embed σ₂ hweight₂ hfeas₂
    have hlam1_ne : lam1 ≠ 0 := ne_of_gt hlam1_pos
    have hlog_le : Real.log lam2 ≤ Real.log (c * lam1) :=
      Real.log_le_log hlam2_pos hlam_le
    have hlog_mul :
        Real.log (c * lam1) = Real.log c + Real.log lam1 := by
      rw [Real.log_mul hc_ne hlam1_ne]
    have hlog_c :
        Real.log c = Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ) := by
      dsimp [c]
      rw [Real.log_div hdR₂_ne hdR₁_ne]
    have hlog_bound :
        Real.log lam2 ≤
          (Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ)) + Real.log lam1 := by
      simpa [hlog_mul, hlog_c, add_comm, add_left_comm, add_assoc] using hlog_le
    unfold conditionalMinEntropyReal
    change
      -Real.log lam1 / Real.log 2 ≤
        -Real.log lam2 / Real.log 2 +
          (Real.log (dR₂ : ℝ) / Real.log 2 -
            Real.log (dR₁ : ℝ) / Real.log 2)
    have hnum :
        -Real.log lam1 ≤
          -Real.log lam2 + (Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ)) := by
      linarith
    have hdiv :
        -Real.log lam1 / Real.log 2 ≤
          (-Real.log lam2 +
              (Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ))) / Real.log 2 :=
      div_le_div_of_nonneg_right hnum hlog2_pos.le
    have harith :
        (-Real.log lam2 +
            (Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ))) / Real.log 2 =
          -Real.log lam2 / Real.log 2 +
            (Real.log (dR₂ : ℝ) / Real.log 2 -
              Real.log (dR₁ : ℝ) / Real.log 2) := by
      ring
    simpa [harith] using hdiv
  · have hlam1_zero : lam1 = 0 := by
      exact le_antisymm (le_of_not_gt hlam1_pos) (by
        simpa [lam1, σ₁] using
          InfoTheory.SmoothMinEntropy.minFeasibleLambda_nonneg ρ σ₁)
    have hlam2_zero : lam2 = 0 := by
      have hlam2_nonneg : 0 ≤ lam2 := by
        simpa [lam2, σ₂] using
          InfoTheory.SmoothMinEntropy.minFeasibleLambda_nonneg ρ_embed σ₂
      have hlam2_le_zero : lam2 ≤ 0 := by
        simpa [hlam1_zero] using hlam_le
      exact le_antisymm hlam2_le_zero hlam2_nonneg
    have hpenalty_nonneg :
        0 ≤ Real.log (dR₂ : ℝ) / Real.log 2 -
          Real.log (dR₁ : ℝ) / Real.log 2 :=
      log_dim_penalty_nonneg_of_le hdim
    unfold conditionalMinEntropyReal
    change
      -Real.log lam1 / Real.log 2 ≤
        -Real.log lam2 / Real.log 2 +
          (Real.log (dR₂ : ℝ) / Real.log 2 -
            Real.log (dR₁ : ℝ) / Real.log 2)
    rw [hlam1_zero, hlam2_zero, Real.log_zero, neg_zero, zero_div]
    simpa using hpenalty_nonneg

/-- **Bare-register conditional min-entropy dimension penalty.**

The `dE = 1` (no ancilla factor) specialization of
`conditionalMinEntropyReal_maxMixed_left_isometry_embed_le_add_dimPenalty`, stated over the bare
registers `dR₁`/`dR₂` and a bare left isometry `V` (rather than `kronIdLeftIso (dH := dE) V` over
`dE * dR`).  This is the form consumers carrying a single quantum register (no separate Eve-ancilla
tensor factor) need; the proof is identical to the bipartite lemma with `K := V`, `hK_iso :=
hV_iso`. -/
theorem conditionalMinEntropyReal_maxMixed_left_isometry_embed_le_add_dimPenalty_bare
    (Xcl : Type) [Fintype Xcl]
    {dR₁ dR₂ : ℕ} [NeZero dR₁] [NeZero dR₂]
    (hdim : dR₁ ≤ dR₂)
    (ρ : CQState Xcl dR₁)
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_embed : CQState Xcl dR₂)
    (h_embed : ∀ x : Xcl,
      (ρ_embed.stateMap x).toOp = V * (ρ.stateMap x).toOp * Vᴴ)
    (hscale : ∀ {t : ℝ},
      isFeasible ρ
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) t →
        isFeasible ρ_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂))
          (((dR₂ : ℝ) / (dR₁ : ℝ)) * t)) :
    conditionalMinEntropyReal ρ
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) ≤
      conditionalMinEntropyReal ρ_embed
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) +
        (Real.log (dR₂ : ℝ) / Real.log 2 -
          Real.log (dR₁ : ℝ) / Real.log 2) := by
  classical
  let σ₁ : SubDensityOp dR₁ :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)
  let σ₂ : SubDensityOp dR₂ :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)
  let lam1 : ℝ := minFeasibleLambda ρ σ₁
  let lam2 : ℝ := minFeasibleLambda ρ_embed σ₂
  let c : ℝ := (dR₂ : ℝ) / (dR₁ : ℝ)
  have hdR₁_pos : 0 < (dR₁ : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dR₁)
  have hdR₂_pos : 0 < (dR₂ : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dR₂)
  have hdR₁_ne : (dR₁ : ℝ) ≠ 0 := ne_of_gt hdR₁_pos
  have hdR₂_ne : (dR₂ : ℝ) ≠ 0 := ne_of_gt hdR₂_pos
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (Nat.cast_nonneg dR₂) (Nat.cast_nonneg dR₁)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos hdR₂_pos hdR₁_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hσ₁_pd : σ₁.toOp.PosDef := by
    simpa [σ₁] using maxMixed_toSubDensityOp_posDef (dE := dR₁)
  have hσ₂_pd : σ₂.toOp.PosDef := by
    simpa [σ₂] using maxMixed_toSubDensityOp_posDef (dE := dR₂)
  have hfeas₁ : hasFeasibleLambda ρ σ₁ :=
    InfoTheory.SmoothMinEntropy.hasFeasibleLambda_of_posDef ρ σ₁ hσ₁_pd
  have hfeas₂ : hasFeasibleLambda ρ_embed σ₂ :=
    InfoTheory.SmoothMinEntropy.hasFeasibleLambda_of_posDef ρ_embed σ₂ hσ₂_pd
  have hlam_le : lam2 ≤ c * lam1 := by
    simpa [lam1, lam2, σ₁, σ₂, c] using
      InfoTheory.SmoothMinEntropy.minFeasibleLambda_le_mul_of_isFeasible_scaling
        ρ σ₁ ρ_embed σ₂ hc_nonneg hfeas₁
        (fun {t} ht => hscale (by simpa [σ₁] using ht))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hlam1_pos : 0 < lam1
  · have hweight₁ : 0 < ∑ x : Xcl, (ρ.stateMap x).trace :=
      cqState_weight_pos_of_minFeasibleLambda_pos ρ σ₁ hlam1_pos
    have : Nonempty Xcl := cqState_nonempty_of_weight_pos ρ hweight₁
    have hweight_eq :
        (∑ x : Xcl, (ρ_embed.stateMap x).trace) =
          ∑ x : Xcl, (ρ.stateMap x).trace :=
      cqState_weight_eq_of_left_isometry_embed V hV_iso ρ ρ_embed h_embed
    have hweight₂ : 0 < ∑ x : Xcl, (ρ_embed.stateMap x).trace := by
      rwa [hweight_eq]
    have hlam2_pos : 0 < lam2 := by
      simpa [lam2, σ₂] using
        InfoTheory.SmoothMinEntropy.minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos
          ρ_embed σ₂ hweight₂ hfeas₂
    have hlam1_ne : lam1 ≠ 0 := ne_of_gt hlam1_pos
    have hlog_le : Real.log lam2 ≤ Real.log (c * lam1) :=
      Real.log_le_log hlam2_pos hlam_le
    have hlog_mul :
        Real.log (c * lam1) = Real.log c + Real.log lam1 := by
      rw [Real.log_mul hc_ne hlam1_ne]
    have hlog_c :
        Real.log c = Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ) := by
      dsimp [c]
      rw [Real.log_div hdR₂_ne hdR₁_ne]
    have hlog_bound :
        Real.log lam2 ≤
          (Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ)) + Real.log lam1 := by
      simpa [hlog_mul, hlog_c, add_comm, add_left_comm, add_assoc] using hlog_le
    unfold conditionalMinEntropyReal
    change
      -Real.log lam1 / Real.log 2 ≤
        -Real.log lam2 / Real.log 2 +
          (Real.log (dR₂ : ℝ) / Real.log 2 -
            Real.log (dR₁ : ℝ) / Real.log 2)
    have hnum :
        -Real.log lam1 ≤
          -Real.log lam2 + (Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ)) := by
      linarith
    have hdiv :
        -Real.log lam1 / Real.log 2 ≤
          (-Real.log lam2 +
              (Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ))) / Real.log 2 :=
      div_le_div_of_nonneg_right hnum hlog2_pos.le
    have harith :
        (-Real.log lam2 +
            (Real.log (dR₂ : ℝ) - Real.log (dR₁ : ℝ))) / Real.log 2 =
          -Real.log lam2 / Real.log 2 +
            (Real.log (dR₂ : ℝ) / Real.log 2 -
              Real.log (dR₁ : ℝ) / Real.log 2) := by
      ring
    simpa [harith] using hdiv
  · have hlam1_zero : lam1 = 0 := by
      exact le_antisymm (le_of_not_gt hlam1_pos) (by
        simpa [lam1, σ₁] using
          InfoTheory.SmoothMinEntropy.minFeasibleLambda_nonneg ρ σ₁)
    have hlam2_zero : lam2 = 0 := by
      have hlam2_nonneg : 0 ≤ lam2 := by
        simpa [lam2, σ₂] using
          InfoTheory.SmoothMinEntropy.minFeasibleLambda_nonneg ρ_embed σ₂
      have hlam2_le_zero : lam2 ≤ 0 := by
        simpa [hlam1_zero] using hlam_le
      exact le_antisymm hlam2_le_zero hlam2_nonneg
    have hpenalty_nonneg :
        0 ≤ Real.log (dR₂ : ℝ) / Real.log 2 -
          Real.log (dR₁ : ℝ) / Real.log 2 :=
      log_dim_penalty_nonneg_of_le hdim
    unfold conditionalMinEntropyReal
    change
      -Real.log lam1 / Real.log 2 ≤
        -Real.log lam2 / Real.log 2 +
          (Real.log (dR₂ : ℝ) / Real.log 2 -
            Real.log (dR₁ : ℝ) / Real.log 2)
    rw [hlam1_zero, hlam2_zero, Real.log_zero, neg_zero, zero_div]
    simpa using hpenalty_nonneg

/-- **ε = 0 collapse of the metric dimension-penalty lemma.**

The per-component instantiation: when the Bell CQ state is at purified distance `0` from the EXACT
left-isometry image of the collective state (the single accepted IID component is exactly
the embedded collective product block, Frobenius diff `0`), the bound is a *plain*
`conditionalMinEntropyReal` (no smoothing).

Proof: `purifiedDistance_eq_zero_iff` ⟹ `toJointDensity` equality ⟹
`conditionalMinEntropyReal_congr_toJointDensity` lets us replace `ρ_bell` by the image, then apply
the
EXACT `ε = 0` penalty (the embed identity is `rfl`).

References: as for `conditionalMinEntropy_maxMixed_traceDist_dimPenalty_embed`. -/
theorem conditionalMinEntropyReal_maxMixed_exactEmbed_dimPenalty_of_purifiedDistance_zero
    (Xcl : Type) [Fintype Xcl] [DecidableEq Xcl] [Nonempty Xcl]
    {dR₁ dR₂ : ℕ} [NeZero dR₁] [NeZero dR₂]
    (hdim : dR₁ ≤ dR₂)
    (ρ_coll : CQState Xcl dR₁)
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_bell : CQState Xcl dR₂)
    (hMetric0 :
      CQState.purifiedDistance ρ_bell (cqStateLeftIsometryEmbed V hV_iso ρ_coll) = 0)
    (hscale : ∀ {t : ℝ},
      isFeasible ρ_coll
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) t →
        isFeasible (cqStateLeftIsometryEmbed V hV_iso ρ_coll)
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂))
          (((dR₂ : ℝ) / (dR₁ : ℝ)) * t)) :
    conditionalMinEntropyReal ρ_coll
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) -
      (Real.log (dR₂ : ℝ) / Real.log 2 - Real.log (dR₁ : ℝ) / Real.log 2) ≤
    conditionalMinEntropyReal ρ_bell
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) := by
  set ρ_embed : CQState Xcl dR₂ := cqStateLeftIsometryEmbed V hV_iso ρ_coll with hρ_embed
  -- The ε = 0 ball forces equal joint densities, hence equal conditional min-entropies.
  have hjoint : ρ_bell.toJointDensity = ρ_embed.toJointDensity :=
    (purifiedDistance_eq_zero_iff _ _).mp hMetric0
  have hcongr :
      conditionalMinEntropyReal ρ_bell
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) =
        conditionalMinEntropyReal ρ_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) :=
    conditionalMinEntropyReal_congr_toJointDensity _ hjoint
  -- EXACT ε = 0 penalty on the image.
  have hPen :
      conditionalMinEntropyReal ρ_coll
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) ≤
        conditionalMinEntropyReal ρ_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) +
          (Real.log (dR₂ : ℝ) / Real.log 2 -
            Real.log (dR₁ : ℝ) / Real.log 2) :=
    conditionalMinEntropyReal_maxMixed_left_isometry_embed_le_add_dimPenalty_bare
      Xcl (dR₁ := dR₁) (dR₂ := dR₂) hdim ρ_coll V hV_iso ρ_embed
      (fun _ => rfl) (fun {t} ht => hscale ht)
  rw [hcongr]
  linarith

/-- Embedding source ball witnesses into an ambient maximally mixed reference costs the
logarithm of the register-dimension ratio in extended smooth entropy. -/
theorem smoothMinEntropy_embedded_maxMixed_le_ambient_maxMixed_add_dimPenalty
    (Xcl : Type) [Fintype Xcl] [DecidableEq Xcl] [Nonempty Xcl]
    {dE dR₁ dR₂ : ℕ} [NeZero dE] [NeZero dR₁] [NeZero dR₂]
    (hdim : dR₁ ≤ dR₂) (ε : ℝ) (ρ : CQState Xcl (dE * dR₁))
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_embed : CQState Xcl (dE * dR₂))
    (h_embed : ∀ x : Xcl, (ρ_embed.stateMap x).toOp =
      kronIdLeftIso (dH := dE) V * (ρ.stateMap x).toOp * (kronIdLeftIso (dH := dE) V)ᴴ) :
    smoothMinEntropy ε ρ
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))) ≤
      smoothMinEntropy ε ρ_embed
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))) +
        ENNReal.ofReal (Real.log (dR₂ : ℝ) / Real.log 2 -
          Real.log (dR₁ : ℝ) / Real.log 2) := by
  have : NeZero (dE * dR₁) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have : NeZero (dE * dR₂) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  let K := kronIdLeftIso (dH := dE) V
  have hK : Kᴴ * K = 1 := kronIdLeftIso_left_iso (dH := dE) V hV_iso
  apply smoothMinEntropy_le_add_of_transport
  intro τ hd
  refine ⟨cqStateLeftIsometryEmbed K hK τ, ?_, fun k hk => ?_⟩
  · exact cqState_purifiedDistance_left_isometry_embed_le Xcl ε K hK
      ρ τ ρ_embed (cqStateLeftIsometryEmbed K hK τ) h_embed (fun _ => rfl) hd
  · have h₁ : (0 : ℝ) < dR₁ := Nat.cast_pos.mpr (NeZero.pos dR₁)
    have h₂ : (0 : ℝ) < dR₂ := Nat.cast_pos.mpr (NeZero.pos dR₂)
    have hpow := two_rpow_neg_sub_log k (div_pos h₂ h₁)
    rw [Real.log_div h₂.ne' h₁.ne', sub_div] at hpow
    rw [hpow]
    exact isFeasible_maxMixed_left_isometry_embed_of_isFeasible Xcl hdim τ V hV_iso
      (cqStateLeftIsometryEmbed K hK τ) (fun _ => rfl) hk

/-- A nearby isometric image gives an extended smooth entropy floor with the logarithmic
dimension penalty; the image's feasible coefficients follow from the isometry itself. -/
theorem conditionalMinEntropy_maxMixed_traceDist_dimPenalty_embed
    (Xcl : Type) [Fintype Xcl] [DecidableEq Xcl] [Nonempty Xcl]
    {dR₁ dR₂ : ℕ} [NeZero dR₁] [NeZero dR₂]
    (ε : ℝ) (ρ_coll : CQState Xcl dR₁)
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_bell : CQState Xcl dR₂)
    (hMetric : CQState.purifiedDistance ρ_bell (cqStateLeftIsometryEmbed V hV_iso ρ_coll) ≤ ε) :
    conditionalMinEntropy ρ_coll (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) ≤
      smoothMinEntropy ε ρ_bell (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) +
        ENNReal.ofReal (Real.log (dR₂ : ℝ) / Real.log 2 -
          Real.log (dR₁ : ℝ) / Real.log 2) := by
  have hpen : conditionalMinEntropy ρ_coll
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) ≤
      conditionalMinEntropy (cqStateLeftIsometryEmbed V hV_iso ρ_coll)
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) +
        ENNReal.ofReal (Real.log (dR₂ : ℝ) / Real.log 2 -
          Real.log (dR₁ : ℝ) / Real.log 2) := by
    apply conditionalMinEntropy_le_add_of_isFeasible_imp
    intro k hk
    have h₁ : (0 : ℝ) < dR₁ := Nat.cast_pos.mpr (NeZero.pos dR₁)
    have h₂ : (0 : ℝ) < dR₂ := Nat.cast_pos.mpr (NeZero.pos dR₂)
    have hpow := two_rpow_neg_sub_log k (div_pos h₂ h₁)
    rw [Real.log_div h₂.ne' h₁.ne', sub_div] at hpow
    rw [hpow]
    exact isFeasible_maxMixed_left_isometry_embed_bare_of_isFeasible ρ_coll V hV_iso
      (cqStateLeftIsometryEmbed V hV_iso ρ_coll) (fun _ => rfl) hk
  exact hpen.trans (add_le_add
    (conditionalMinEntropy_le_smoothMinEntropy ρ_bell _ _ hMetric) le_rfl)


/-- Embedding a source smoothing candidate transfers its signed entropy to the ambient maximally
mixed reference with the logarithmic dimension cost. -/
theorem smoothedSetReal_maxMixed_left_isometry_embed_candidate_transfer
    (Xcl : Type) [Fintype Xcl] [DecidableEq Xcl] [Nonempty Xcl]
    {dE dR₁ dR₂ : ℕ} [NeZero dE] [NeZero dR₁] [NeZero dR₂]
    (hdim : dR₁ ≤ dR₂)
    (ε : ℝ)
    (ρ : CQState Xcl (dE * dR₁))
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_embed : CQState Xcl (dE * dR₂))
    (h_embed : ∀ x : Xcl,
      (ρ_embed.stateMap x).toOp =
        kronIdLeftIso (dH := dE) V *
          (ρ.stateMap x).toOp *
          (kronIdLeftIso (dH := dE) V)ᴴ)
    (hbdd_ambient :
      BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ_embed
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))))))
    {h : ℝ}
    (hh : isInSmoothedSetReal ε ρ
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))) h) :
    h ≤ smoothMinEntropyReal ε ρ_embed
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))) +
        (Real.log (dR₂ : ℝ) / Real.log 2 -
          Real.log (dR₁ : ℝ) / Real.log 2) := by
  rcases hh with ⟨ρ_tilde, hh_eq, hdist_src⟩
  let K := kronIdLeftIso (dH := dE) V
  have hK_iso :
      Kᴴ * K = (1 : Matrix (Fin (dE * dR₁)) (Fin (dE * dR₁)) ℂ) := by
    simpa [K] using kronIdLeftIso_left_iso (dH := dE) V hV_iso
  let ρ_tilde_embed : CQState Xcl (dE * dR₂) :=
    cqStateLeftIsometryEmbed K hK_iso ρ_tilde
  have hdist :
      CQState.purifiedDistance ρ_embed ρ_tilde_embed ≤ ε :=
    cqState_purifiedDistance_left_isometry_embed_le
      Xcl ε K hK_iso ρ ρ_tilde ρ_embed ρ_tilde_embed
      (by intro x; simpa [K] using h_embed x)
      (by intro x; rfl)
      hdist_src
  have hscale : ∀ {t : ℝ},
      isFeasible ρ_tilde
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))) t →
        isFeasible ρ_tilde_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂)))
          (((dR₂ : ℝ) / (dR₁ : ℝ)) * t) := by
    intro t ht
    exact isFeasible_maxMixed_left_isometry_embed_of_isFeasible
      Xcl (dE := dE) (dR₁ := dR₁) (dR₂ := dR₂)
      hdim ρ_tilde V hV_iso ρ_tilde_embed
      (by intro x; rfl)
      ht
  have hH :
      conditionalMinEntropyReal ρ_tilde
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))) ≤
        conditionalMinEntropyReal ρ_tilde_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))) +
          (Real.log (dR₂ : ℝ) / Real.log 2 -
            Real.log (dR₁ : ℝ) / Real.log 2) :=
    conditionalMinEntropyReal_maxMixed_left_isometry_embed_le_add_dimPenalty
      Xcl (dE := dE) (dR₁ := dR₁) (dR₂ := dR₂)
      hdim ρ_tilde V hV_iso ρ_tilde_embed
      (by intro x; rfl)
      hscale
  have hamb :
      conditionalMinEntropyReal ρ_tilde_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))) ≤
        smoothMinEntropyReal ε ρ_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))) := by
    unfold smoothMinEntropyReal
    exact le_csSup hbdd_ambient ⟨ρ_tilde_embed, rfl, hdist⟩
  rw [hh_eq]
  linarith

/-- If the source signed smoothing set is unbounded above, so is the isometrically embedded set
against its maximally mixed reference. -/
theorem smoothedSetReal_maxMixed_left_isometry_embed_not_bddAbove
    (Xcl : Type) [Fintype Xcl] [DecidableEq Xcl] [Nonempty Xcl]
    {dE dR₁ dR₂ : ℕ} [NeZero dE] [NeZero dR₁] [NeZero dR₂]
    (hdim : dR₁ ≤ dR₂)
    (ε : ℝ)
    (ρ : CQState Xcl (dE * dR₁))
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_embed : CQState Xcl (dE * dR₂))
    (h_embed : ∀ x : Xcl,
      (ρ_embed.stateMap x).toOp =
        kronIdLeftIso (dH := dE) V *
          (ρ.stateMap x).toOp *
          (kronIdLeftIso (dH := dE) V)ᴴ)
    (hnot_source :
      ¬ BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁)))))) :
    ¬ BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ_embed
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))))) := by
  intro hbdd_ambient
  apply hnot_source
  refine ⟨smoothMinEntropyReal ε ρ_embed
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))) +
      (Real.log (dR₂ : ℝ) / Real.log 2 -
        Real.log (dR₁ : ℝ) / Real.log 2), ?_⟩
  intro h hh
  exact smoothedSetReal_maxMixed_left_isometry_embed_candidate_transfer
    Xcl (dE := dE) (dR₁ := dR₁) (dR₂ := dR₂)
    hdim ε ρ V hV_iso ρ_embed h_embed hbdd_ambient hh

/-- At a negative smoothing radius, the signed candidate set is empty. -/
theorem smoothedSetReal_eq_empty_of_neg
    {Xcl : Type*} [Fintype Xcl] [DecidableEq Xcl] [Nonempty Xcl]
    {d : ℕ} [NeZero d]
    {ε : ℝ} (ρ : CQState Xcl d) (σ : SubDensityOp d)
    (hε : ε < 0) :
    Set.ofPred (isInSmoothedSetReal ε ρ σ) = ∅ := by
  have : NeZero (Fintype.card Xcl) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (d * Fintype.card Xcl) :=
    ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne _)⟩
  ext h
  constructor
  · intro hh
    rcases hh with ⟨ρ_tilde, _hh_eq, hdist⟩
    have hdist_nonneg : 0 ≤ CQState.purifiedDistance ρ ρ_tilde := by
      unfold CQState.purifiedDistance
      exact purifiedDistance_nonneg ρ.toJointDensity ρ_tilde.toJointDensity
    linarith
  · intro hh
    cases hh

/-- Unboundedness of the ambient signed smoothing set implies unboundedness of the source set
under an isometric embedding. -/
theorem smoothedSetReal_maxMixed_left_isometry_embed_not_bddAbove_source_of_ambient
    (Xcl : Type) [Fintype Xcl] [DecidableEq Xcl] [Nonempty Xcl]
    {dE dR₁ dR₂ : ℕ} [NeZero dE] [NeZero dR₁] [NeZero dR₂]
    (_hdim : dR₁ ≤ dR₂)
    (ε : ℝ)
    (ρ : CQState Xcl (dE * dR₁))
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_embed : CQState Xcl (dE * dR₂))
    (h_embed : ∀ x : Xcl,
      (ρ_embed.stateMap x).toOp =
        kronIdLeftIso (dH := dE) V *
          (ρ.stateMap x).toOp *
          (kronIdLeftIso (dH := dE) V)ᴴ)
    (hnot_ambient :
      ¬ BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ_embed
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂)))))) :
    ¬ BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))))) := by
  have hε_nonneg : 0 ≤ ε := by
    by_contra hε_nonneg
    have hε_neg : ε < 0 := lt_of_not_ge hε_nonneg
    apply hnot_ambient
    rw [smoothedSetReal_eq_empty_of_neg ρ_embed
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))) hε_neg]
    exact bddAbove_empty
  let K := kronIdLeftIso (dH := dE) V
  have hK_iso :
      Kᴴ * K = (1 : Matrix (Fin (dE * dR₁)) (Fin (dE * dR₁)) ℂ) := by
    simpa [K] using kronIdLeftIso_left_iso (dH := dE) V hV_iso
  have hweight :
      (∑ x : Xcl, (ρ_embed.stateMap x).trace) =
        ∑ x : Xcl, (ρ.stateMap x).trace := by
    exact cqState_weight_eq_of_left_isometry_embed K hK_iso ρ ρ_embed
      (by intro x; simpa [K] using h_embed x)
  exact
    InfoTheory.SmoothMinEntropy.smoothedSetReal_maxMixed_not_bddAbove_of_weight_eq
      (ρn := ρ_embed) (ρm := ρ) ε hε_nonneg hweight hnot_ambient

/-- Embedding into a larger maximally mixed reference bounds the source signed smooth entropy by
the ambient value plus `log dR₂ / log 2 - log dR₁ / log 2`. -/
theorem smoothMinEntropyReal_embedded_maxMixed_le_ambient_maxMixed_add_dimPenalty
    (Xcl : Type) [Fintype Xcl] [DecidableEq Xcl] [Nonempty Xcl]
    {dE : ℕ} [NeZero dE]
    {dR₁ dR₂ : ℕ} [NeZero dR₁] [NeZero dR₂]
    (hdim : dR₁ ≤ dR₂)
    (ε : ℝ)
    (ρ : CQState Xcl (dE * dR₁))
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_embed : CQState Xcl (dE * dR₂))
    (h_embed : ∀ x : Xcl,
      (ρ_embed.stateMap x).toOp =
        kronIdLeftIso (dH := dE) V *
          (ρ.stateMap x).toOp *
          (kronIdLeftIso (dH := dE) V)ᴴ) :
    smoothMinEntropyReal ε ρ
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))) ≤
      smoothMinEntropyReal ε ρ_embed
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))) +
        (Real.log (dR₂ : ℝ) / Real.log 2 - Real.log (dR₁ : ℝ) / Real.log 2) := by
  classical
  let σ₁ : SubDensityOp (dE * dR₁) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₁))
  let σ₂ : SubDensityOp (dE * dR₂) :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed (dE * dR₂))
  let penalty : ℝ :=
    Real.log (dR₂ : ℝ) / Real.log 2 - Real.log (dR₁ : ℝ) / Real.log 2
  change smoothMinEntropyReal ε ρ σ₁ ≤ smoothMinEntropyReal ε ρ_embed σ₂ + penalty
  have hpen_nonneg : 0 ≤ penalty := by
    dsimp [penalty]
    exact log_dim_penalty_nonneg_of_le hdim
  by_cases hε_nonneg : 0 ≤ ε
  · by_cases hbdd_source : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ σ₁))
    · by_cases hbdd_ambient : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ_embed σ₂))
      · change sSup (Set.ofPred (isInSmoothedSetReal ε ρ σ₁)) ≤
          smoothMinEntropyReal ε ρ_embed σ₂ + penalty
        apply csSup_le
        · exact ⟨conditionalMinEntropyReal ρ σ₁, ρ, rfl, by
            rw [CQState.purifiedDistance_self_zero]
            exact hε_nonneg⟩
        · intro h hh
          exact smoothedSetReal_maxMixed_left_isometry_embed_candidate_transfer
            Xcl (dE := dE) (dR₁ := dR₁) (dR₂ := dR₂)
            hdim ε ρ V hV_iso ρ_embed h_embed
            (by simpa [σ₂] using hbdd_ambient)
            (by simpa [σ₁] using hh)
      · have hnot_source :
            ¬ BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ σ₁)) := by
          simpa [σ₁, σ₂] using
            smoothedSetReal_maxMixed_left_isometry_embed_not_bddAbove_source_of_ambient
              Xcl (dE := dE) (dR₁ := dR₁) (dR₂ := dR₂)
              hdim ε ρ V hV_iso ρ_embed h_embed
              (by simpa [σ₂] using hbdd_ambient)
        exact (hnot_source hbdd_source).elim
    · have hnot_ambient :
          ¬ BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ_embed σ₂)) := by
        simpa [σ₁, σ₂] using
          smoothedSetReal_maxMixed_left_isometry_embed_not_bddAbove
            Xcl (dE := dE) (dR₁ := dR₁) (dR₂ := dR₂)
            hdim ε ρ V hV_iso ρ_embed h_embed
            (by simpa [σ₁] using hbdd_source)
      change sSup (Set.ofPred (isInSmoothedSetReal ε ρ σ₁)) ≤
        sSup (Set.ofPred (isInSmoothedSetReal ε ρ_embed σ₂)) + penalty
      rw [show sSup (Set.ofPred (isInSmoothedSetReal ε ρ σ₁)) =
            sSup (∅ : Set ℝ) from csSup_of_not_bddAbove hbdd_source,
          show sSup (Set.ofPred (isInSmoothedSetReal ε ρ_embed σ₂)) =
            sSup (∅ : Set ℝ) from csSup_of_not_bddAbove hnot_ambient]
      have hsSup_empty : sSup (∅ : Set ℝ) = 0 := by simp
      simpa [hsSup_empty] using hpen_nonneg
  · have hε_neg : ε < 0 := lt_of_not_ge hε_nonneg
    change sSup (Set.ofPred (isInSmoothedSetReal ε ρ σ₁)) ≤
      sSup (Set.ofPred (isInSmoothedSetReal ε ρ_embed σ₂)) + penalty
    have hsource_empty : Set.ofPred (isInSmoothedSetReal ε ρ σ₁) = ∅ :=
      smoothedSetReal_eq_empty_of_neg ρ σ₁ hε_neg
    have hambient_empty : Set.ofPred (isInSmoothedSetReal ε ρ_embed σ₂) = ∅ :=
      smoothedSetReal_eq_empty_of_neg ρ_embed σ₂ hε_neg
    rw [hsource_empty, hambient_empty]
    have hsSup_empty : sSup (∅ : Set ℝ) = 0 := by simp
    simpa [hsSup_empty] using hpen_nonneg

/-- An isometrically embedded state within the target ball transfers its signed conditional
entropy with dimension cost `log dR₂ / log 2 - log dR₁ / log 2`. -/
theorem conditionalMinEntropyReal_maxMixed_traceDist_dimPenalty_embed
    (Xcl : Type) [Fintype Xcl] [DecidableEq Xcl] [Nonempty Xcl]
    {dR₁ dR₂ : ℕ} [NeZero dR₁] [NeZero dR₂]
    (hdim : dR₁ ≤ dR₂)
    (ε : ℝ)
    (ρ_coll : CQState Xcl dR₁)
    (V : Matrix (Fin dR₂) (Fin dR₁) ℂ)
    (hV_iso : Vᴴ * V = (1 : Matrix (Fin dR₁) (Fin dR₁) ℂ))
    (ρ_bell : CQState Xcl dR₂)
    (hMetric :
      CQState.purifiedDistance ρ_bell (cqStateLeftIsometryEmbed V hV_iso ρ_coll) ≤ ε)
    (hbdd :
      BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ_bell
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)))))
    (hscale : ∀ {t : ℝ},
      isFeasible ρ_coll
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) t →
        isFeasible (cqStateLeftIsometryEmbed V hV_iso ρ_coll)
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂))
          (((dR₂ : ℝ) / (dR₁ : ℝ)) * t)) :
    conditionalMinEntropyReal ρ_coll
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) -
      (Real.log (dR₂ : ℝ) / Real.log 2 - Real.log (dR₁ : ℝ) / Real.log 2) ≤
    smoothMinEntropyReal ε ρ_bell
      (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) := by
  set ρ_embed : CQState Xcl dR₂ := cqStateLeftIsometryEmbed V hV_iso ρ_coll with hρ_embed
  have hPen :
      conditionalMinEntropyReal ρ_coll
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₁)) ≤
        conditionalMinEntropyReal ρ_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) +
          (Real.log (dR₂ : ℝ) / Real.log 2 -
            Real.log (dR₁ : ℝ) / Real.log 2) :=
    conditionalMinEntropyReal_maxMixed_left_isometry_embed_le_add_dimPenalty_bare
      Xcl (dR₁ := dR₁) (dR₂ := dR₂) hdim ρ_coll V hV_iso ρ_embed
      (fun _ => rfl) (fun {t} ht => hscale ht)
  have hmem :
      conditionalMinEntropyReal ρ_embed
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) ≤
        smoothMinEntropyReal ε ρ_bell
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dR₂)) := by
    unfold smoothMinEntropyReal
    exact le_csSup hbdd ⟨ρ_embed, rfl, hMetric⟩
  linarith

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
