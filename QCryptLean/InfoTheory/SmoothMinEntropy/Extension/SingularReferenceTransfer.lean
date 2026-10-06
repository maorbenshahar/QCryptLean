import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.FinitePostFilterFloor

/-!
# Entropy under reference domination

Löwner domination transfers feasible coefficients to a dominating reference. Positive smooth
entropy floors supply feasible ball witnesses even when the source reference is singular.
Nonpositive floors follow from nonnegativity; real logarithmic penalties are converted only after
signed arithmetic.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Feasibility under a positive rescaling of the reference -/

/-- Feasibility survives a positive rescaling of the reference: if `ρ_x ≼ t·σ` for some `t`, then
`ρ_x ≼ (t/c)·(c·σ)`.  The scalar-level content is `isFeasible_smul_sigma_iff`. -/
lemma hasFeasibleLambda_smul_sigma {X : Type*} [Fintype X] {d : ℕ}
    (ρ : CQState X d) (σ : SubDensityOp d) {c : ℝ} (hc : 0 < c) (hc_le : c ≤ 1)
    (h : hasFeasibleLambda ρ σ) : hasFeasibleLambda ρ (σ.smul c hc.le hc_le) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨c⁻¹ * t, ?_⟩
  rw [isFeasible_smul_sigma_iff ρ σ hc hc_le]
  have hct : c * (c⁻¹ * t) = t := by field_simp
  rw [hct]
  exact ht

/-! ## The floor transfer at a positive floor -/

/-! ## The boundary of the `c = 1` form -/

/-- **A trace-one sub-density operator is Löwner-dominated only by itself.**

If `σ ≼ σ'` in the Löwner order and `tr σ = 1`, then `σ' = σ`: the difference `σ' − σ` is positive
semidefinite with trace `tr σ' − 1 ≤ 0`, hence with trace `0`, hence zero.

This is the trace-slack accounting behind the block-reference inflation trap: a reference family
whose weights already sum to `1` has no room to be enlarged. -/
theorem SubDensityOp.eq_of_opLe_of_trace_eq_one {d : ℕ} (σ σ' : SubDensityOp d)
    (hdom : opLe σ.toOp σ'.toOp) (htr : σ.trace = 1) : σ' = σ := by
  have hσ_herm : σ.toOp.IsHermitian := σ.isHermitian
  have hσ'_herm : σ'.toOp.IsHermitian := σ'.isHermitian
  have hpsd : Matrix.PosSemidef (σ'.toOp - σ.toOp) :=
    Quantum.Operators.opLe.posSemidef_sub hσ_herm hσ'_herm hdom
  have htrace_re : (σ'.toOp - σ.toOp).trace.re = σ'.trace - 1 := by
    rw [Matrix.trace_sub, Complex.sub_re]
    change σ'.trace - σ.trace = σ'.trace - 1
    rw [htr]
  have hσ'_le : σ'.trace ≤ 1 := σ'.trace_le_one
  have hle : (σ'.toOp - σ.toOp).trace.re ≤ 0 := by
    rw [htrace_re]; linarith
  have hge : 0 ≤ (σ'.toOp - σ.toOp).trace.re := hpsd.trace_nonneg.1
  have hzero_re : (σ'.toOp - σ.toOp).trace.re = 0 := le_antisymm hle hge
  have hzero : (σ'.toOp - σ.toOp).trace = 0 :=
    Complex.ext hzero_re (by simpa using (hpsd.trace_nonneg.2).symm)
  have hsub : σ'.toOp - σ.toOp = 0 := hpsd.trace_eq_zero_iff.mp hzero
  exact SubDensityOp.ext (by linear_combination (norm := module) hsub)

/-- **At trace one, a positive definite dominating reference forces the reference itself to be
positive definite.**

Contrapositive: a **singular** sub-density reference of trace exactly `1` — which is what a
block-diagonal announced reference whose block weights sum to `1` is — is dominated by no positive
definite sub-density operator at all.  The `c = 1` transfer
`smoothMinEntropy_antitone_sigma` therefore has no instance there, and moving a floor
off such a reference costs `log₂(1/c) > 0` through the `c < 1` form. -/
theorem SubDensityOp.posDef_of_opLe_of_trace_eq_one {d : ℕ} (σ σ' : SubDensityOp d)
    (hdom : opLe σ.toOp σ'.toOp) (htr : σ.trace = 1) (hσ'_pd : σ'.toOp.PosDef) :
    σ.toOp.PosDef := by
  have := SubDensityOp.eq_of_opLe_of_trace_eq_one σ σ' hdom htr
  rwa [this] at hσ'_pd

/-- Reference domination transfers extended smooth entropy with the positive part of its
signed logarithmic cost, including singular references. -/
theorem smoothMinEntropy_ge_of_smul_opLe
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {d : ℕ} [NeZero d]
    (ε : ℝ) (ρ : CQState X d) (σ σ' : SubDensityOp d)
    (c : ℝ) (hc : 0 < c) (hdom : opLe ((c : ℂ) • σ.toOp) σ'.toOp) :
    smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε ρ σ' + ENNReal.ofReal (-Real.log c / Real.log 2) := by
  apply smoothMinEntropy_le_add_of_transport
  intro τ hd
  refine ⟨τ, hd, fun k hk => ?_⟩
  have hpow : (2 : ℝ) ^ (-(k - -Real.log c / Real.log 2)) = c⁻¹ * 2 ^ (-k) := by
    simpa only [Real.log_inv, neg_div] using two_rpow_neg_sub_log k (inv_pos.mpr hc)
  rw [hpow]
  refine ⟨mul_nonneg (inv_nonneg.mpr hc.le) hk.1, fun x => ?_⟩
  have hscaled := opLe_smul_nonneg (mul_nonneg (inv_nonneg.mpr hc.le) hk.1) hdom
  have heq : Complex.ofReal (c⁻¹ * (2 : ℝ) ^ (-k)) • ((c : ℂ) • σ.toOp) =
      Complex.ofReal ((2 : ℝ) ^ (-k)) • σ.toOp := by
    rw [smul_smul, ← Complex.ofReal_mul]
    congr 2
    field_simp
  rw [heq] at hscaled
  exact opLe_trans (hk.2 x) hscaled

/-- A clipped smooth floor survives reference domination at a nonpositive logarithmic shift.
The condition `c ≤ 1` ensures that a clipped zero floor cannot create a positive target floor. -/
theorem smoothMinEntropy_ge_of_smul_opLe_of_floor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {d : ℕ} [NeZero d]
    (ε : ℝ) (ρ : CQState X d) (σ σ' : SubDensityOp d)
    (c : ℝ) (hc : 0 < c) (hc_le : c ≤ 1)
    (hdom : opLe ((c : ℂ) • σ.toOp) σ'.toOp)
    (k : ℝ) (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    ENNReal.ofReal (k + Real.log c / Real.log 2) ≤ smoothMinEntropy ε ρ σ' := by
  have hp : 0 ≤ -Real.log c / Real.log 2 :=
    div_nonneg (neg_nonneg.mpr (Real.log_nonpos hc.le hc_le))
      (Real.log_pos one_lt_two).le
  have h := hk.trans (smoothMinEntropy_ge_of_smul_opLe ε ρ σ σ' c hc hdom)
  have hsub := tsub_le_iff_right.mpr h
  rw [← ENNReal.ofReal_sub k hp] at hsub
  simpa only [neg_div, sub_neg_eq_add] using hsub

/-- Increasing a reference in operator order increases extended smooth min-entropy. -/
theorem smoothMinEntropy_antitone_sigma
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {d : ℕ} [NeZero d]
    (ε : ℝ) (ρ : CQState X d) (σ σ' : SubDensityOp d)
    (hdom : opLe σ.toOp σ'.toOp) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy ε ρ σ' := by
  apply smoothMinEntropy_le_of_transport
  exact fun τ hd => ⟨τ, hd, fun _ ht => isFeasible_of_opLe τ σ' σ hdom ht⟩


/-- Domination of `c` times the source reference transfers a positive input floor `k` to the
signed target floor `k + log c / log 2`. -/
theorem smoothMinEntropyReal_ge_of_smul_opLe_of_pos_floor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {d : ℕ} [NeZero d]
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (ρ : CQState X d) (σ σ' : SubDensityOp d)
    (c : ℝ) (hc : 0 < c) (hc_le : c ≤ 1)
    (hdom : ∀ v : Fin d → ℂ,
      (quadraticForm ((c : ℂ) • σ.toOp) v).re ≤ (quadraticForm σ'.toOp v).re)
    (hσ'_pd : σ'.toOp.PosDef)
    (hweight : 2 * ε < ∑ x : X, (ρ.stateMap x).trace)
    (k : ℝ) (hk_pos : 0 < k)
    (hk : k ≤ smoothMinEntropyReal ε ρ σ) :
    k + Real.log c / Real.log 2 ≤ smoothMinEntropyReal ε ρ σ' := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogc_nonpos : Real.log c / Real.log 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hc.le hc_le) hlog2.le
  set η : ℝ := (∑ x : X, (ρ.stateMap x).trace) - 2 * ε with hηdef
  have hη_pos : 0 < η := by rw [hηdef]; linarith
  have hρ_lower : η + 2 * ε ≤ ∑ x : X, (ρ.stateMap x).trace := by rw [hηdef]; linarith
  have hbdd' : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ σ')) :=
    (fun ε η hη ρ hρ σ =>
      smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη ρ σ
        (fun _ hd => CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ hd))
      ε η hη_pos ρ hρ_lower σ'
  have hdom' : ∀ v : Fin d → ℂ,
      (quadraticForm (σ.smul c hc.le hc_le).toOp v).re ≤ (quadraticForm σ'.toOp v).re := by
    intro v
    have hsmul_toOp : (σ.smul c hc.le hc_le).toOp = (c : ℂ) • σ.toOp := rfl
    rw [hsmul_toOp]; exact hdom v
  refine le_of_forall_pos_le_add (fun ν hν => ?_)
  set ν' : ℝ := min ν (k / 2) with hν'def
  have hν'_pos : 0 < ν' := lt_min hν (by linarith)
  have hν'_le : ν' ≤ ν := min_le_left _ _
  have hν'_half : ν' ≤ k / 2 := min_le_right _ _
  have hlevel_pos : 0 < k - ν' := by linarith
  have hlt : k - ν' < smoothMinEntropyReal ε ρ σ := by linarith
  obtain ⟨ρt, hdist, hfloor⟩ := smoothMinEntropyReal_exists_approx ε hε_nn ρ σ (k - ν') hlt
  have hfeasσ : hasFeasibleLambda ρt σ := by
    by_contra hno
    have hzero := minFeasibleLambda_eq_zero_of_not_hasFeasibleLambda ρt σ hno
    have hpos := lt_of_lt_of_le hlevel_pos hfloor
    simp [conditionalMinEntropyReal, hzero] at hpos
  have hfeas_scaled : hasFeasibleLambda ρt (σ.smul c hc.le hc_le) :=
    hasFeasibleLambda_smul_sigma ρt σ hc hc_le hfeasσ
  have hweight_witness : η ≤ ∑ x : X, (ρt.stateMap x).trace :=
    CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ_lower hdist
  have hpos' : 0 < minFeasibleLambda ρt σ' :=
    minFeasibleLambda_pos_of_posDef_of_weight_pos ρt σ' hσ'_pd
      (lt_of_lt_of_le hη_pos hweight_witness)
  have hscaled : k - ν' + Real.log c / Real.log 2 ≤
      conditionalMinEntropyReal ρt (σ.smul c hc.le hc_le) :=
    le_trans (by linarith) (conditionalMinEntropyReal_smul_sigma_ge ρt σ hc hc_le)
  have htransfer : k - ν' + Real.log c / Real.log 2 ≤ conditionalMinEntropyReal ρt σ' :=
    le_trans hscaled
      (conditionalMinEntropyReal_antitone_sigma ρt σ' (σ.smul c hc.le hc_le) hdom'
        hfeas_scaled hpos')
  have hfinal : k - ν' + Real.log c / Real.log 2 ≤ smoothMinEntropyReal ε ρ σ' :=
    smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove ε ρ σ' (k - ν' + Real.log c / Real.log 2) ρt
      hbdd' hdist htransfer
  linarith

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
