import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.ProductReference
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.CQExtensionFiber
import QCryptLean.Quantum.Channels.CPTP.CKRBound.SupportPreservation
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Order
import QCryptLean.Quantum.Symmetry.SymmetricSubspace

/-!
# Conditional entropy extension rules

Operator domination and supported extension witnesses transfer feasible coefficients to enlarged
conditioning registers. Signed real conditional entropy statements retain logarithmic penalties
before clipping. Canonical smooth transport and extension results are supplied by the imported
entropy modules.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexOrder MatrixOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- A feasible-scalar transfer controls the product-reference SDP optimum.

The hypothesis hFeasibleTransfer requires that every scalar feasible for the
Eve-only approximant at `maxMixed_E` transfers to a feasible scalar for the
specified τ-side approximant at `maxMixed_E ⊗ σR`, at the cost of the factor
`polyDim`. With the blockwise marginal identity, the minimal feasible λ at the
product reference is positive when the Eve-side weight is positive and is bounded
by `polyDim · minFeasibleLambda ρEtilde maxMixed_E`. -/
theorem minFeasibleLambda_product_ref_control_of_feasible_transfer
    {X : Type*} [Fintype X] [Nonempty X]
    {dR dE : ℕ} [NeZero dE]
    (σR : DensityOp dR)
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hERtilde_marginal : ∀ x : X,
      partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hFeasibleTransfer :
      ∀ {t : ℝ},
        isFeasible ρEtilde
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t →
          isFeasible ρERtilde
            (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR))
            ((polyDim : ℝ) * t)) :
    (0 < ∑ x : X, (ρEtilde.stateMap x).trace →
      0 < minFeasibleLambda ρERtilde
        (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR))) ∧
    minFeasibleLambda ρERtilde
        (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR)) ≤
      (polyDim : ℝ) *
        minFeasibleLambda ρEtilde
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  let σE : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  let σER : SubDensityOp (dE * dR) :=
    DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR)
  have hweight_eq :
      (∑ x : X, (ρERtilde.stateMap x).trace) =
        ∑ x : X, (ρEtilde.stateMap x).trace := by
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [← hERtilde_marginal x, trace_partialTraceB]
  have hfeasE : hasFeasibleLambda ρEtilde σE := by
    simpa [σE] using hasFeasibleLambda_maxMixed ρEtilde
  have hfeasER : hasFeasibleLambda ρERtilde σER := by
    obtain ⟨t, ht⟩ := hfeasE
    exact ⟨(polyDim : ℝ) * t, by simpa [σE, σER] using hFeasibleTransfer ht⟩
  constructor
  · intro hweightE
    have hweightER : 0 < ∑ x : X, (ρERtilde.stateMap x).trace := by
      simpa [hweight_eq] using hweightE
    simpa [σER] using
      minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρERtilde σER
        hweightER hfeasER
  · have hpoly_nonneg : (0 : ℝ) ≤ (polyDim : ℝ) := by
      exact_mod_cast h_polyDim_pos.le
    simpa [σE, σER] using
      minFeasibleLambda_le_mul_of_isFeasible_scaling
        ρEtilde σE ρERtilde σER hpoly_nonneg hfeasE
        (fun {t} ht => by simpa [σE, σER] using hFeasibleTransfer ht)

/-- Converts product-reference min-feasible-λ control into the additive
`log polyDim / log 2` penalty on the conditional min-entropy. The argument is
real-valued logarithm algebra together with the zero-weight sentinel (both optima
vanish when the Eve-side weight is nonpositive). -/
theorem conditionalMinEntropyReal_extension_at_product_ref_ge_of_minFeasibleLambda_control
    {X : Type*} [Fintype X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE]
    (σR : DensityOp dR)
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hERtilde_marginal : ∀ x : X,
      partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hposER :
      0 < ∑ x : X, (ρEtilde.stateMap x).trace →
        0 < minFeasibleLambda ρERtilde
          (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR)))
    (hlam :
      minFeasibleLambda ρERtilde
          (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR)) ≤
        (polyDim : ℝ) *
          minFeasibleLambda ρEtilde
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))) :
    conditionalMinEntropyReal ρEtilde
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
        Real.log (polyDim : ℝ) / Real.log 2 ≤
      conditionalMinEntropyReal ρERtilde
        (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR)) := by
  set M_E : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE) with hM_E
  set σER : SubDensityOp (dE * dR) :=
    DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR) with hσER
  set lamE : ℝ := minFeasibleLambda ρEtilde M_E with hlamE_def
  set lamER : ℝ := minFeasibleLambda ρERtilde σER with hlamER_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpoly_pos : (0 : ℝ) < (polyDim : ℝ) := by exact_mod_cast h_polyDim_pos
  have hpoly_ne : (polyDim : ℝ) ≠ 0 := hpoly_pos.ne'
  have hpoly_ge_one : (1 : ℝ) ≤ (polyDim : ℝ) := by exact_mod_cast h_polyDim_pos
  have hweight_eq :
      (∑ x : X, (ρERtilde.stateMap x).trace) =
        ∑ x : X, (ρEtilde.stateMap x).trace := by
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [← hERtilde_marginal x, trace_partialTraceB]
  by_cases hweightE : 0 < ∑ x : X, (ρEtilde.stateMap x).trace
  · have hfeasE : hasFeasibleLambda ρEtilde M_E := by
      simpa [hM_E] using hasFeasibleLambda_maxMixed ρEtilde
    have hlamE_pos : 0 < lamE := by
      simpa [hlamE_def] using
        minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρEtilde M_E
          hweightE hfeasE
    have hlamER_pos : 0 < lamER := by
      simpa [hlamER_def, hσER] using hposER hweightE
    have hlog_le :
        Real.log lamER ≤ Real.log ((polyDim : ℝ) * lamE) := by
      exact Real.log_le_log hlamER_pos (by simpa [hlamER_def, hlamE_def, hM_E, hσER] using hlam)
    have hlog_mul :
        Real.log ((polyDim : ℝ) * lamE) =
          Real.log (polyDim : ℝ) + Real.log lamE := by
      rw [Real.log_mul hpoly_ne (ne_of_gt hlamE_pos)]
    have hlog_bound :
        Real.log lamER ≤ Real.log (polyDim : ℝ) + Real.log lamE := by
      simpa [hlog_mul] using hlog_le
    unfold conditionalMinEntropyReal
    change
      -Real.log lamE / Real.log 2 - Real.log (polyDim : ℝ) / Real.log 2 ≤
        -Real.log lamER / Real.log 2
    rw [← sub_div]
    have hnum : -Real.log lamE - Real.log (polyDim : ℝ) ≤ -Real.log lamER := by
      linarith
    exact div_le_div_of_nonneg_right hnum hlog2_pos.le
  · have hE_zero : ∀ x : X, (ρEtilde.stateMap x).toOp = 0 :=
      CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρEtilde hweightE
    have hweightER : ¬ 0 < ∑ x : X, (ρERtilde.stateMap x).trace := by
      intro h
      exact hweightE (by rwa [hweight_eq] at h)
    have hER_zero : ∀ x : X, (ρERtilde.stateMap x).toOp = 0 :=
      CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρERtilde hweightER
    have hlamE_zero : lamE = 0 :=
      minFeasibleLambda_eq_zero_of_stateMap_zero ρEtilde hE_zero M_E
    have hlamER_zero : lamER = 0 :=
      minFeasibleLambda_eq_zero_of_stateMap_zero ρERtilde hER_zero σER
    unfold conditionalMinEntropyReal
    rw [← hlamE_def, ← hlamER_def, hlamE_zero, hlamER_zero, Real.log_zero,
      neg_zero, zero_div, zero_sub]
    have hpenalty_nonneg : 0 ≤ Real.log (polyDim : ℝ) / Real.log 2 :=
      div_nonneg (Real.log_nonneg hpoly_ge_one) hlog2_pos.le
    linarith

/-- From a feasible-scalar transfer `t ↦ polyDim · t` to the product reference
`maxMixed_E ⊗ σR` together with the blockwise marginal identity, the τ-side
conditional min-entropy at `maxMixed_E ⊗ σR` is at least the Eve-only conditional
min-entropy at `maxMixed_E` minus `log polyDim / log 2`. -/
theorem conditionalMinEntropyReal_extension_at_product_ref_ge_of_feasible_transfer
    {X : Type*} [Fintype X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE]
    (σR : DensityOp dR)
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hERtilde_marginal : ∀ x : X,
      partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hFeasibleTransfer :
      ∀ {t : ℝ},
        isFeasible ρEtilde
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t →
          isFeasible ρERtilde
            (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR))
            ((polyDim : ℝ) * t)) :
    conditionalMinEntropyReal ρEtilde
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
        Real.log (polyDim : ℝ) / Real.log 2 ≤
      conditionalMinEntropyReal ρERtilde
        (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR)) := by
  have hcontrol :=
    minFeasibleLambda_product_ref_control_of_feasible_transfer
      (σR := σR) (ρEtilde := ρEtilde) (ρERtilde := ρERtilde)
      polyDim h_polyDim_pos hERtilde_marginal hFeasibleTransfer
  exact
    conditionalMinEntropyReal_extension_at_product_ref_ge_of_minFeasibleLambda_control
      (σR := σR) (ρEtilde := ρEtilde) (ρERtilde := ρERtilde)
      polyDim h_polyDim_pos hERtilde_marginal hcontrol.1 hcontrol.2

/-- From a feasible-scalar transfer `t ↦ polyDim · t` (every scalar feasible for the
Eve-only SDP at `maxMixed_E` yields one feasible for `ρERtilde` at `σER`) and the
blockwise marginal identity, the minimal feasible λ at `σER` is positive whenever
the Eve-side weight is positive and is bounded by
`polyDim · minFeasibleLambda ρEtilde maxMixed_E`. The reference `σER` is arbitrary:
the product structure `maxMixed_E ⊗ σR` is never used, so the correlated CKR
calibration reference `σ_corr` is admissible. -/
theorem minFeasibleLambda_correlated_ref_control_of_feasible_transfer
    {X : Type*} [Fintype X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hERtilde_marginal : ∀ x : X,
      partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hFeasibleTransfer :
      ∀ {t : ℝ},
        isFeasible ρEtilde
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t →
          isFeasible ρERtilde σER ((polyDim : ℝ) * t)) :
    (0 < ∑ x : X, (ρEtilde.stateMap x).trace →
      0 < minFeasibleLambda ρERtilde σER) ∧
    minFeasibleLambda ρERtilde σER ≤
      (polyDim : ℝ) *
        minFeasibleLambda ρEtilde
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) := by
  let σE : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  have hweight_eq :
      (∑ x : X, (ρERtilde.stateMap x).trace) =
        ∑ x : X, (ρEtilde.stateMap x).trace := by
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [← hERtilde_marginal x, trace_partialTraceB]
  have hfeasE : hasFeasibleLambda ρEtilde σE := by
    simpa [σE] using hasFeasibleLambda_maxMixed ρEtilde
  have hfeasER : hasFeasibleLambda ρERtilde σER := by
    obtain ⟨t, ht⟩ := hfeasE
    exact ⟨(polyDim : ℝ) * t, by simpa [σE] using hFeasibleTransfer ht⟩
  constructor
  · intro hweightE
    have hweightER : 0 < ∑ x : X, (ρERtilde.stateMap x).trace := by
      simpa [hweight_eq] using hweightE
    exact
      minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρERtilde σER
        hweightER hfeasER
  · have hpoly_nonneg : (0 : ℝ) ≤ (polyDim : ℝ) := by
      exact_mod_cast h_polyDim_pos.le
    simpa [σE] using
      minFeasibleLambda_le_mul_of_isFeasible_scaling
        ρEtilde σE ρERtilde σER hpoly_nonneg hfeasE
        (fun {t} ht => by simpa [σE] using hFeasibleTransfer ht)

/-- Converts min-feasible-λ control at an arbitrary extension-side reference `σER`
into the additive entropy bound
`conditionalMinEntropyReal ρERtilde σER ≥ conditionalMinEntropyReal ρEtilde maxMixed_E − log₂
polyDim`.
The argument is real-logarithm algebra plus the zero-weight sentinel (both optima
vanish when the Eve-side weight is nonpositive); the product structure of `σER`
is not used. -/
theorem conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_minFeasibleLambda_control
    {X : Type*} [Fintype X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hERtilde_marginal : ∀ x : X,
      partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hposER :
      0 < ∑ x : X, (ρEtilde.stateMap x).trace →
        0 < minFeasibleLambda ρERtilde σER)
    (hlam :
      minFeasibleLambda ρERtilde σER ≤
        (polyDim : ℝ) *
          minFeasibleLambda ρEtilde
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))) :
    conditionalMinEntropyReal ρEtilde
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
        Real.log (polyDim : ℝ) / Real.log 2 ≤
      conditionalMinEntropyReal ρERtilde σER := by
  set M_E : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE) with hM_E
  set lamE : ℝ := minFeasibleLambda ρEtilde M_E with hlamE_def
  set lamER : ℝ := minFeasibleLambda ρERtilde σER with hlamER_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpoly_pos : (0 : ℝ) < (polyDim : ℝ) := by exact_mod_cast h_polyDim_pos
  have hpoly_ne : (polyDim : ℝ) ≠ 0 := hpoly_pos.ne'
  have hpoly_ge_one : (1 : ℝ) ≤ (polyDim : ℝ) := by exact_mod_cast h_polyDim_pos
  have hweight_eq :
      (∑ x : X, (ρERtilde.stateMap x).trace) =
        ∑ x : X, (ρEtilde.stateMap x).trace := by
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [← hERtilde_marginal x, trace_partialTraceB]
  by_cases hweightE : 0 < ∑ x : X, (ρEtilde.stateMap x).trace
  · have hfeasE : hasFeasibleLambda ρEtilde M_E := by
      simpa [hM_E] using hasFeasibleLambda_maxMixed ρEtilde
    have hlamE_pos : 0 < lamE := by
      simpa [hlamE_def] using
        minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρEtilde M_E
          hweightE hfeasE
    have hlamER_pos : 0 < lamER := by
      simpa [hlamER_def] using hposER hweightE
    have hlog_le :
        Real.log lamER ≤ Real.log ((polyDim : ℝ) * lamE) :=
      Real.log_le_log hlamER_pos (by simpa [hlamER_def, hlamE_def, hM_E] using hlam)
    have hlog_mul :
        Real.log ((polyDim : ℝ) * lamE) =
          Real.log (polyDim : ℝ) + Real.log lamE := by
      rw [Real.log_mul hpoly_ne (ne_of_gt hlamE_pos)]
    have hlog_bound :
        Real.log lamER ≤ Real.log (polyDim : ℝ) + Real.log lamE := by
      simpa [hlog_mul] using hlog_le
    unfold conditionalMinEntropyReal
    change
      -Real.log lamE / Real.log 2 - Real.log (polyDim : ℝ) / Real.log 2 ≤
        -Real.log lamER / Real.log 2
    rw [← sub_div]
    have hnum : -Real.log lamE - Real.log (polyDim : ℝ) ≤ -Real.log lamER := by
      linarith
    exact div_le_div_of_nonneg_right hnum hlog2_pos.le
  · have hE_zero : ∀ x : X, (ρEtilde.stateMap x).toOp = 0 :=
      CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρEtilde hweightE
    have hweightER : ¬ 0 < ∑ x : X, (ρERtilde.stateMap x).trace := by
      intro h
      exact hweightE (by rwa [hweight_eq] at h)
    have hER_zero : ∀ x : X, (ρERtilde.stateMap x).toOp = 0 :=
      CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρERtilde hweightER
    have hlamE_zero : lamE = 0 :=
      minFeasibleLambda_eq_zero_of_stateMap_zero ρEtilde hE_zero M_E
    have hlamER_zero : lamER = 0 :=
      minFeasibleLambda_eq_zero_of_stateMap_zero ρERtilde hER_zero σER
    unfold conditionalMinEntropyReal
    rw [← hlamE_def, ← hlamER_def, hlamE_zero, hlamER_zero, Real.log_zero,
      neg_zero, zero_div, zero_sub]
    have hpenalty_nonneg : 0 ≤ Real.log (polyDim : ℝ) / Real.log 2 :=
      div_nonneg (Real.log_nonneg hpoly_ge_one) hlog2_pos.le
    linarith

/-- From a feasible-scalar transfer `t ↦ polyDim · t` to an arbitrary extension-side
reference `σER` together with the blockwise marginal identity,
`conditionalMinEntropyReal ρERtilde σER ≥ conditionalMinEntropyReal ρEtilde maxMixed_E − log₂
polyDim`.
Since the product reference `maxMixed_E ⊗ σR` does not Löwner-dominate `ρER` for
`n ≥ 2`, this is instantiated at the correlated CKR calibration reference
`σER = σ_corr` (Renner smooth-min-entropy chain rule; CKR 2009 key-shortening). -/
theorem conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_feasible_transfer
    {X : Type*} [Fintype X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hERtilde_marginal : ∀ x : X,
      partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hFeasibleTransfer :
      ∀ {t : ℝ},
        isFeasible ρEtilde
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t →
          isFeasible ρERtilde σER ((polyDim : ℝ) * t)) :
    conditionalMinEntropyReal ρEtilde
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
        Real.log (polyDim : ℝ) / Real.log 2 ≤
      conditionalMinEntropyReal ρERtilde σER := by
  have hcontrol :=
    minFeasibleLambda_correlated_ref_control_of_feasible_transfer
      (σER := σER) (ρEtilde := ρEtilde) (ρERtilde := ρERtilde)
      polyDim h_polyDim_pos hERtilde_marginal hFeasibleTransfer
  exact
    conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_minFeasibleLambda_control
      (σER := σER) (ρEtilde := ρEtilde) (ρERtilde := ρERtilde)
      polyDim h_polyDim_pos hERtilde_marginal hcontrol.1 hcontrol.2

/-- Constructs a τ-side smoothing approximant within purified distance `ε` of `ρER`
whose Eve-side block marginal matches `ρEtilde`, from the center-block data
`ρE x = Λ x σR`, `ρER x = mapTensorId (Λ x) τ`, and `σR = τ.partialTraceB`. The
center block marginal follows from tracing out the untouched reference after
`mapTensorId`. -/
theorem exists_product_ref_tau_side_approximant_of_block_marginals
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρE : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (hτ_marginal : τ.partialTraceB = σR)
    (hρE_center : ∀ x : X, (ρE.stateMap x).toOp = Λ x σR.toOp)
    (hρER_center : ∀ x : X, (ρER.stateMap x).toOp = mapTensorId (Λ x) τ.toOp)
    (ε : ℝ)
    (ρEtilde : CQState X dE)
    (hdE : CQState.purifiedDistance ρE ρEtilde ≤ ε) :
    ∃ ρERtilde : CQState X (dE * d ^ n),
      CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
      ∀ x : X,
        partialTraceB (ρERtilde.stateMap x).toOp =
          (ρEtilde.stateMap x).toOp := by
  have hτ_toOp : partialTraceB τ.toOp = σR.toOp := by
    change τ.partialTraceB.toOp = σR.toOp
    rw [hτ_marginal]
  have hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρE.stateMap x).toOp := by
    intro x
    calc
      partialTraceB (ρER.stateMap x).toOp
          = partialTraceB (mapTensorId (Λ x) τ.toOp) := by
              rw [hρER_center x]
      _ = Λ x (partialTraceB τ.toOp) := by
              rw [partialTraceB_mapTensorId]
      _ = Λ x σR.toOp := by
              rw [hτ_toOp]
      _ = (ρE.stateMap x).toOp := by
              rw [hρE_center x]
  exact
    finiteDimensional_CQ_extension_fiber_of_block_marginals
      (d := d ^ n) (ρE := ρE) (ρER := ρER) hblocks ε ρEtilde hdE

/-- An Eve-side scalar `t` together with a proof that it is feasible for the
Eve-only SDP at `maxMixed_E`. -/
structure EveFeasibleScalar
    {X : Type*} [Fintype X]
    {dE : ℕ} [NeZero dE]
    (ρEtilde : CQState X dE) where
  /-- The Eve-side feasible scalar. -/
  t : ℝ
  /-- Feasibility of `t` for the Eve-only max-mixed reference. -/
  feasible : isFeasible ρEtilde
    (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) t

/-! ## Correlated-reference scalar-construction frontier

The product-reference frontier (`ProductRefExtensionLiftAtScalar`,
`ProductRefExtensionLiftExists`) keys `feasible_at_scalar` to the product reference
`maxMixed_E ⊗ σR`, against which the per-block operator domination
`ρERtilde.block ⪯ (polyDim · t) · (maxMixed_E ⊗ σR)` is **false** at the live
CKR parameters: the untouched de Finetti marginal `σR` has `λ_min(σR) ≤ d^{-2n}`,
so a single spike fiber `(ρEtilde.block) ⊗ |r_min⟩⟨r_min|` satisfying the block
marginal constraint violates the bound (`1 ≤ polyDim · λ_min(σR)`).  The honest
reference for the operator domination is a **correlated**, attack-aware reference
`σER` (the regularized joint `E ⊗ R` marginal of the attacked symmetric state),
which Löwner-dominates each block at scale `polyDim` because it is built from the
attack image.  The structures below carry the same selected smoothed extension and
block-marginal data, but key `feasible_at_scalar` to an arbitrary extension-side
reference `σER`, so the operator domination is taken where it is true.

The entropy transfer they feed
(`conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_feasible_transfer`,
proved above) is reference-agnostic: it conditions the τ-side conditional min-entropy
on the **same** `σER`, so re-keying the feasibility to the correlated reference
re-keys the conclusion to it as well — there is no bridge between the two references
(none exists at cost `≤ log polyDim`), the entire chain runs at the correlated
reference. -/

/-- Per-scalar τ-side construction data at the **correlated** reference `σER`, for a
fixed feasible Eve-side scalar `ctx`.

Records the selected τ-side extension, its smooth-radius bound, its Eve-side block
marginal, and explicit feasibility at the scalar `polyDim · ctx.t` against the
arbitrary correlated reference `σER`.  Unlike `ProductRefExtensionLiftAtScalar`,
the reference is not a product `maxMixed_E ⊗ σR`, and the semantically-passive
paired-source `postselection_compat` field is dropped (it had no proof-body
consumer). -/
structure CorrelatedRefExtensionLiftAtScalar
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero (dE * dR)]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * dR))
    (polyDim : ℕ)
    (ε : ℝ)
    (ctx : EveFeasibleScalar ρEtilde) where
  /-- The τ-side smoothed extension selected for this scalar context. -/
  rhoERtilde : CQState X (dE * dR)
  /-- The selected extension remains in the requested smooth ball. -/
  distance_le : CQState.purifiedDistance ρER rhoERtilde ≤ ε
  /-- The selected extension has the requested Eve-side block marginal. -/
  block_marginal_eq : ∀ x : X,
    partialTraceB (rhoERtilde.stateMap x).toOp =
      (ρEtilde.stateMap x).toOp
  /-- Correlated-reference feasibility for the selected scalar context. -/
  feasible_at_scalar :
    isFeasible rhoERtilde σER ((polyDim : ℝ) * ctx.t)

/-- Holds when every feasible Eve-side scalar context admits τ-side construction
data (`CorrelatedRefExtensionLiftAtScalar`) at the correlated reference `σER`, with
explicit correlated-reference feasibility at the scaled scalar. -/
def CorrelatedRefExtensionLiftExists
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero (dE * dR)]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * dR))
    (polyDim : ℕ)
    (ε : ℝ) : Prop :=
  ∀ ctx : EveFeasibleScalar ρEtilde,
    Nonempty (CorrelatedRefExtensionLiftAtScalar
      (σER := σER) (ρEtilde := ρEtilde) (ρER := ρER)
      (polyDim := polyDim) (ε := ε) ctx)

/-- Blockwise correlated-reference feasibility of the selected extension at the
scalar `polyDim · ctx.t`, obtained from the scalar-construction data. -/
theorem isFeasible_correlatedRef_of_extensionLiftAtScalar
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero (dE * dR)]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * dR))
    (polyDim : ℕ)
    (ε : ℝ)
    (ctx : EveFeasibleScalar ρEtilde)
    (data :
      CorrelatedRefExtensionLiftAtScalar
        (σER := σER) (ρEtilde := ρEtilde) (ρER := ρER)
        (polyDim := polyDim) (ε := ε) ctx) :
    isFeasible data.rhoERtilde σER ((polyDim : ℝ) * ctx.t) :=
  data.feasible_at_scalar

/-- **Correlated-reference analogue of `isFeasible_productRef_of_blockDomination`.**
A per-block Löwner domination of each `rhoERtilde` block by the scaled correlated
reference `(polyDim · ctx.t) · σER` yields SDP feasibility at that scalar. This is
the operator-order → SDP-feasibility step of the CKR `lem:extractpart`
smooth-min-entropy chain rule, taken at the attack-aware correlated reference `σER`
(where the operator domination is true; the product reference `maxMixed_E ⊗ σR` is
ruled out at `n ≥ 2` by the eigenvalue-floor obstruction). -/
theorem isFeasible_correlatedRef_of_blockDomination
    {X : Type*} [Fintype X]
    {dE dR : ℕ} [NeZero dE] [NeZero (dE * dR)]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ)
    (ctx : EveFeasibleScalar ρEtilde)
    (hblock_domination : ∀ x : X,
      opLe (ρERtilde.stateMap x).toOp
        ((Complex.ofReal ((polyDim : ℝ) * ctx.t)) • σER.toOp)) :
    isFeasible ρERtilde σER ((polyDim : ℝ) * ctx.t) :=
  ⟨mul_nonneg (Nat.cast_nonneg polyDim) ctx.feasible.1, hblock_domination⟩

/-- **General correlated-reference scalar-construction frontier from a smoothed
operator domination** (the CKR `lem:extractpart` smooth-min-entropy chain-rule
frontier, stated generally).

Builds `CorrelatedRefExtensionLiftExists` — the operator-order smooth-min-entropy
chain-rule frontier — from a single per-scalar **smoothed operator-domination**
ingredient hsmoothedDomination: for every feasible Eve-side scalar `ctx`, a τ-side
smoothed extension `rhoERtilde` in the `ε`-ball of `ρER`, with the requested Eve-side
block marginal `ρEtilde`, whose blocks are Löwner-dominated by `(polyDim · ctx.t) · σER`.

The packaging is reference-agnostic and TRUE for any `σER`: the genuine CKR
`lem:extractpart` content is entirely in hsmoothedDomination (the operator
domination of the *smoothed* extension within the `ε`-ball). Per the eigenvalue-floor
obstruction (`PairedLowner.lean`), hsmoothedDomination is satisfiable only at an
attack-aware correlated `σER`, never at the product reference, and only for a smoothed
`rhoERtilde` (the unsmoothed center fails it); the caller supplies it coupled to the
attack structure. The smoothing witness itself (existence, `ε`-ball membership, and the
Eve-side block marginal) is constructible from the center-block data via the
finite-dimensional extension-fiber theorem
`exists_product_ref_tau_side_approximant_of_block_marginals`, so only the operator
domination of that witness is genuine content. This lemma carries no `sorry`. -/
theorem correlatedRefExtensionLiftExists_of_smoothedDomination
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero (dE * dR)]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * dR))
    (ε : ℝ)
    (polyDim : ℕ)
    -- The smoothed operator domination: for every feasible Eve-side scalar context,
    -- a τ-side smoothed extension in the `ε`-ball of `ρER` with the `ρEtilde`-block
    -- marginal whose blocks are dominated by `(polyDim · ctx.t) · σER`. This is the
    -- CKR `lem:extractpart` operator-order content (smoothed, attack-aware `σER`).
    (hsmoothedDomination : ∀ ctx : EveFeasibleScalar ρEtilde,
      ∃ ρERtilde : CQState X (dE * dR),
        CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
        (∀ x : X,
          partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp) ∧
        (∀ x : X,
          opLe (ρERtilde.stateMap x).toOp
            ((Complex.ofReal ((polyDim : ℝ) * ctx.t)) • σER.toOp))) :
    CorrelatedRefExtensionLiftExists
      (σER := σER) (ρEtilde := ρEtilde) (ρER := ρER)
      (polyDim := polyDim) (ε := ε) := by
  intro ctx
  obtain ⟨ρERtilde, hdist, hmarginal, hdom⟩ := hsmoothedDomination ctx
  exact ⟨{
    rhoERtilde := ρERtilde
    distance_le := hdist
    block_marginal_eq := hmarginal
    feasible_at_scalar :=
      isFeasible_correlatedRef_of_blockDomination
        (σER := σER) (ρEtilde := ρEtilde) (ρERtilde := ρERtilde)
        (polyDim := polyDim) ctx hdom
  }⟩

/-- **Correlated-reference smooth-min-entropy dimension penalty from a
scalar-construction frontier.**

From the correlated-reference scalar-construction frontier
(`CorrelatedRefExtensionLiftExists` for the chosen `ρEtilde`) and `0 < polyDim`,
selects the τ-side approximant `ρERtilde` (in the `ε`-ball of `ρER`, with the
requested Eve-side block marginal and correlated-reference feasibility at the scaled
Eve-side optimum) and applies the reference-agnostic correlated-reference entropy
transfer: the τ-side conditional min-entropy at `σER` is at least the Eve-only
conditional min-entropy at `maxMixed_E` minus `log polyDim / log 2`.

The feasibility at the Eve-side optimal scalar is upgraded to a `t`-parametrized
feasible transfer (`isFeasible_mul_minFeasibleLambda_mono`), and the entropy
comparison is `conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_feasible_transfer`. -/
theorem exists_correlatedRef_entropyRealTransfer_of_extensionLiftExists
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero (dE * dR)]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (ε : ℝ)
    (hFrontier : CorrelatedRefExtensionLiftExists
      (σER := σER) (ρEtilde := ρEtilde) (ρER := ρER)
      (polyDim := polyDim) (ε := ε)) :
    ∃ ρERtilde : CQState X (dE * dR),
      CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
      conditionalMinEntropyReal ρEtilde
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
          Real.log (polyDim : ℝ) / Real.log 2 ≤
        conditionalMinEntropyReal ρERtilde σER := by
  let M_E : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  let ctx : EveFeasibleScalar ρEtilde := {
    t := minFeasibleLambda ρEtilde M_E
    feasible := by
      simpa [M_E] using
        isFeasible_minFeasibleLambda_of_posDef ρEtilde M_E
          (by simpa [M_E] using (maxMixed_toSubDensityOp_posDef : M_E.toOp.PosDef))
  }
  obtain ⟨data⟩ := hFrontier ctx
  refine ⟨data.rhoERtilde, data.distance_le, ?_⟩
  -- Feasibility at the Eve-side optimum `polyDim · minFeasibleLambda ρEtilde M_E`.
  have hmin : isFeasible data.rhoERtilde σER
      ((polyDim : ℝ) * minFeasibleLambda ρEtilde M_E) := by
    simpa [ctx, M_E] using data.feasible_at_scalar
  -- Upgrade to the `t`-parametrized feasible transfer.
  have hFeasibleTransfer :
      ∀ {t : ℝ},
        isFeasible ρEtilde M_E t →
          isFeasible data.rhoERtilde σER ((polyDim : ℝ) * t) := by
    intro t ht
    exact
      isFeasible_mul_minFeasibleLambda_mono
        ρEtilde M_E data.rhoERtilde σER
        (Nat.cast_nonneg polyDim) hmin ht
  exact
    conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_feasible_transfer
      (σER := σER) (ρEtilde := ρEtilde) (ρERtilde := data.rhoERtilde)
      polyDim h_polyDim_pos data.block_marginal_eq
      (fun {t} ht => by simpa [M_E] using hFeasibleTransfer (by simpa [M_E] using ht))

/-- Paired-support data certifying that a selected τ-side extension satisfies the
CKR trace-norm postselection bound.

The source operators live before applying the block channels `Λ x`. The structure
is indexed by the reference `σR`, which must be the untouched `τ`-marginal
`τ.partialTraceA` (recorded by `reference_marginal`). -/
structure ProductRefPostselectionCompatibility
    {X : Type*} [Fintype X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (polyDim : ℕ) where
  /-- The reference `σR` is the untouched `τ` marginal `τ.partialTraceA`. -/
  reference_marginal : τ.partialTraceA = σR
  /-- Per-block paired source operator before applying `Λ x ⊗ id`. -/
  source : X → Op (d ^ n * d ^ n)
  /-- The source operators are positive, hence substate candidates. -/
  source_pos : ∀ x : X, (source x).PosSemidef
  /-- Each source operator has trace at most one. -/
  source_trace_le_one : ∀ x : X, (source x).trace.re ≤ 1
  /-- Each source operator is supported on the paired symmetric subspace. -/
  source_support : ∀ x : X,
    InfoTheory.DeFinetti.symmetricProjectorPaired d n * source x *
        InfoTheory.DeFinetti.symmetricProjectorPaired d n = source x
  /-- CKR paired marginal domination for each source block. -/
  source_marginal_domination : ∀ x : X,
    opLe (partialTraceB (source x))
      ((Complex.ofReal (polyDim : ℝ)) • σR.toOp)
  /-- Applying the block channel to the source realizes the selected extension. -/
  realizes_extension : ∀ x : X,
    (ρERtilde.stateMap x).toOp = mapTensorId (Λ x) (source x)
  /-- The source marginal realizes the selected Eve-side smoothed block. -/
  realizes_eve_marginal : ∀ x : X,
    Λ x (partialTraceB (source x)) = (ρEtilde.stateMap x).toOp
  /-- The CKR postselection trace-norm bound is available for each source block. -/
  postselection_bound : ∀ x : X, ∀ {dimOut : ℕ} [NeZero dimOut],
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut) →
      Quantum.Metrics.traceNorm (mapTensorId Δ (source x)) ≤
        (polyDim : ℝ) *
          Quantum.Metrics.traceNorm (mapTensorId Δ τ.toOp)

/-- Per-scalar τ-side construction data for a fixed feasible Eve-side scalar `ctx`.

Records the selected τ-side extension, its smooth-radius bound, its Eve-side block
marginal, the paired-source postselection compatibility data, and explicit
product-reference feasibility at the scalar `polyDim · ctx.t`. -/
structure ProductRefExtensionLiftAtScalar
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (polyDim : ℕ)
    (ε : ℝ)
    (ctx : EveFeasibleScalar ρEtilde) where
  /-- The τ-side smoothed extension selected for this scalar context. -/
  rhoERtilde : CQState X (dE * d ^ n)
  /-- The selected extension remains in the requested smooth ball. -/
  distance_le : CQState.purifiedDistance ρER rhoERtilde ≤ ε
  /-- The selected extension has the requested Eve-side block marginal. -/
  block_marginal_eq : ∀ x : X,
    partialTraceB (rhoERtilde.stateMap x).toOp =
      (ρEtilde.stateMap x).toOp
  /-- Paired-source and postselection data for the selected extension. -/
  postselection_compat :
    ProductRefPostselectionCompatibility
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde)
      (ρERtilde := rhoERtilde) (Λ := Λ) (polyDim := polyDim)
  /-- Product-reference feasibility for the selected scalar context. -/
  feasible_at_scalar :
    isFeasible rhoERtilde
      (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR))
      ((polyDim : ℝ) * ctx.t)

/-- Holds when every feasible Eve-side scalar context admits τ-side construction
data (`ProductRefExtensionLiftAtScalar`) at the product reference, with
paired source operators realizing the smoothed Eve blocks through `Λ` and explicit
product-reference feasibility. -/
def ProductRefExtensionLiftExists
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (polyDim : ℕ)
    (ε : ℝ) : Prop :=
  ∀ ctx : EveFeasibleScalar ρEtilde,
    Nonempty (ProductRefExtensionLiftAtScalar
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) (ε := ε) ctx)

/-- Scalar construction data supplied by the paired-source-lift frontier. -/
theorem nonempty_productRefExtensionLiftAtScalar_of_liftExists
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (polyDim : ℕ)
    (ε : ℝ)
    (hFrontier : ProductRefExtensionLiftExists
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) (ε := ε))
    (ctx : EveFeasibleScalar ρEtilde) :
    Nonempty (ProductRefExtensionLiftAtScalar
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) (ε := ε) ctx) := by
  exact hFrontier ctx

/-- Blockwise Löwner domination of each `ρERtilde` block by the scaled product
reference yields SDP feasibility at that scalar. -/
theorem isFeasible_productRef_of_blockDomination
    {X : Type*} [Fintype X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * d ^ n))
    (polyDim : ℕ)
    (ctx : EveFeasibleScalar ρEtilde)
    (hblock_domination : ∀ x : X,
      opLe (ρERtilde.stateMap x).toOp
        ((Complex.ofReal ((polyDim : ℝ) * ctx.t)) •
          (DensityOp.toSubDensityOp
            (DensityOp.tensor (DensityOp.maxMixed dE) σR)).toOp)) :
    isFeasible ρERtilde
      (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR))
      ((polyDim : ℝ) * ctx.t) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg polyDim) ctx.feasible.1, ?_⟩
  intro x
  exact hblock_domination x

/-- A τ-side approximant within purified distance `ε` of `ρER`, together with the
conditional-min-entropy comparison at the product reference `maxMixed_E ⊗ σR`. -/
structure ProductRefEntropyRealTransferWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (polyDim : ℕ)
    (ε : ℝ) where
  /-- The tau-side smoothed extension selected by the trace-norm Route-C leaf. -/
  rhoERtilde : CQState X (dE * d ^ n)
  /-- The selected extension remains in the requested smooth ball. -/
  distance_le : CQState.purifiedDistance ρER rhoERtilde ≤ ε
  /-- Direct entropy transfer at the product reference. -/
  entropy_transfer :
    conditionalMinEntropyReal ρEtilde
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
        Real.log (polyDim : ℝ) / Real.log 2 ≤
      conditionalMinEntropyReal rhoERtilde
        (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR))

/-- Asserts the existence of a `ProductRefEntropyRealTransferWitness`. -/
def ProductRefEntropyRealTransferWitnessExists
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (polyDim : ℕ)
    (ε : ℝ) : Prop :=
  Nonempty (ProductRefEntropyRealTransferWitness
    (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
    (polyDim := polyDim) (ε := ε))

/-- A τ-side smoothing approximant: the selected extension, its purified-distance
bound from `ρER`, and its Eve-side block marginal. -/
structure ProductRefTauSideSmoothingWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (ε : ℝ) where
  /-- The tau-side smoothed extension selected by the fiber theorem. -/
  rhoERtilde : CQState X (dE * d ^ n)
  /-- The selected extension remains in the requested smooth ball. -/
  distance_le : CQState.purifiedDistance ρER rhoERtilde ≤ ε
  /-- The selected extension has the requested Eve-side block marginal. -/
  block_marginal_eq : ∀ x : X,
    partialTraceB (rhoERtilde.stateMap x).toOp =
      (ρEtilde.stateMap x).toOp

/-- Constructs a `ProductRefTauSideSmoothingWitness` from the center-block
data and an Eve-side smoothing approximant. -/
theorem nonempty_productRefTauSideSmoothingWitness_of_blockMarginals
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρE : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (hτ_marginal : τ.partialTraceB = σR)
    (hρE_center : ∀ x : X, (ρE.stateMap x).toOp = Λ x σR.toOp)
    (hρER_center : ∀ x : X, (ρER.stateMap x).toOp = mapTensorId (Λ x) τ.toOp)
    (ε : ℝ)
    (ρEtilde : CQState X dE)
    (hdE : CQState.purifiedDistance ρE ρEtilde ≤ ε) :
    Nonempty (ProductRefTauSideSmoothingWitness
      (ρEtilde := ρEtilde) (ρER := ρER) (ε := ε)) := by
  obtain ⟨ρERtilde, hdist, hmarginal⟩ :=
    exists_product_ref_tau_side_approximant_of_block_marginals
      (τ := τ) (σR := σR) (ρE := ρE) (ρER := ρER) (Λ := Λ)
      hτ_marginal hρE_center hρER_center ε ρEtilde hdE
  exact ⟨{
    rhoERtilde := ρERtilde
    distance_le := hdist
    block_marginal_eq := hmarginal
  }⟩

/-- A τ-side smoothing approximant equipped with its purified-distance bound, its
Eve-side block marginal, the paired-source postselection compatibility data, and
product-reference feasibility at the Eve-side optimal scalar
`polyDim · minFeasibleLambda ρEtilde maxMixed_E`. -/
structure ProductRefSupportedPostselectionSmoothingWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (polyDim : ℕ)
    (ε : ℝ) where
  /-- The tau-side smoothed extension selected by the supported argument. -/
  rhoERtilde : CQState X (dE * d ^ n)
  /-- The selected extension remains in the requested smooth ball. -/
  distance_le : CQState.purifiedDistance ρER rhoERtilde ≤ ε
  /-- The selected extension has the requested Eve-side block marginal. -/
  block_marginal_eq : ∀ x : X,
    partialTraceB (rhoERtilde.stateMap x).toOp =
      (ρEtilde.stateMap x).toOp
  /-- Paired-source and postselection data realizing the selected extension. -/
  postselection_compat :
    ProductRefPostselectionCompatibility
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde)
      (ρERtilde := rhoERtilde) (Λ := Λ) (polyDim := polyDim)
  /-- Order-duality feasibility at the Eve-side optimal scalar. -/
  feasible_at_min :
    isFeasible rhoERtilde
      (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR))
      ((polyDim : ℝ) *
        minFeasibleLambda ρEtilde
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)))

/-- The conditional-min-entropy comparison at the product reference for a
`ProductRefSupportedPostselectionSmoothingWitness`. -/
theorem conditionalMinEntropyReal_productRef_ge_of_supportedPostselectionWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (ε : ℝ)
    (smooth : ProductRefSupportedPostselectionSmoothingWitness
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) (ε := ε)) :
    conditionalMinEntropyReal ρEtilde
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
        Real.log (polyDim : ℝ) / Real.log 2 ≤
      conditionalMinEntropyReal smooth.rhoERtilde
        (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR)) := by
  let M_E : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  let σER : SubDensityOp (dE * d ^ n) :=
    DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR)
  have hmin :
      isFeasible smooth.rhoERtilde σER
        ((polyDim : ℝ) * minFeasibleLambda ρEtilde M_E) := by
    simpa [M_E, σER] using smooth.feasible_at_min
  have htransfer :
      ∀ {t : ℝ},
        isFeasible ρEtilde M_E t →
          isFeasible smooth.rhoERtilde σER ((polyDim : ℝ) * t) := by
    intro t ht
    exact
      isFeasible_mul_minFeasibleLambda_mono
        ρEtilde M_E smooth.rhoERtilde σER
        (Nat.cast_nonneg polyDim) hmin ht
  exact
    conditionalMinEntropyReal_extension_at_product_ref_ge_of_feasible_transfer
      (σR := σR) (ρEtilde := ρEtilde) (ρERtilde := smooth.rhoERtilde)
      polyDim h_polyDim_pos smooth.block_marginal_eq
      (by
        intro t ht
        simpa [M_E, σER] using htransfer (t := t) (by simpa [M_E] using ht))

/-- Produces a `ProductRefEntropyRealTransferWitnessExists` from a
`ProductRefSupportedPostselectionSmoothingWitness`. -/
theorem productRefEntropyRealTransferWitnessExists_of_supportedPostselectionWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (ε : ℝ)
    (smooth : ProductRefSupportedPostselectionSmoothingWitness
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) (ε := ε)) :
    ProductRefEntropyRealTransferWitnessExists
      (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (polyDim := polyDim) (ε := ε) := by
  refine ⟨{
    rhoERtilde := smooth.rhoERtilde
    distance_le := smooth.distance_le
    entropy_transfer := ?_
  }⟩
  exact
    conditionalMinEntropyReal_productRef_ge_of_supportedPostselectionWitness
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) h_polyDim_pos (ε := ε) smooth

/-- Extracts the blockwise Löwner domination of the selected extension at index
`x` from the product-reference feasibility datum of the scalar-construction data. -/
theorem opLe_smul_productRef_of_extensionLiftAtScalar
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (_hΛ_cp : ∀ x : X, IsCompletelyPositive (Λ x))
    (polyDim : ℕ) (_h_polyDim_pos : 0 < polyDim)
    (_hPostselection :
      ∀ {dimOut : ℕ} [NeZero dimOut],
        (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut) → (ρ' : Op (d ^ n * d ^ n)) →
        ρ'.PosSemidef → ρ'.trace.re ≤ 1 →
        InfoTheory.DeFinetti.symmetricProjectorPaired d n * ρ' *
            InfoTheory.DeFinetti.symmetricProjectorPaired d n = ρ' →
        Quantum.Metrics.traceNorm (mapTensorId Δ ρ') ≤
          (polyDim : ℝ) *
            Quantum.Metrics.traceNorm (mapTensorId Δ τ.toOp))
    (ε : ℝ)
    (ctx : EveFeasibleScalar ρEtilde)
    (data :
      ProductRefExtensionLiftAtScalar
        (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
        (Λ := Λ) (polyDim := polyDim) (ε := ε) ctx)
    (x : X) :
    opLe (data.rhoERtilde.stateMap x).toOp
      ((Complex.ofReal ((polyDim : ℝ) * ctx.t)) •
        (DensityOp.toSubDensityOp
          (DensityOp.tensor (DensityOp.maxMixed dE) σR)).toOp) := by
  exact data.feasible_at_scalar.2 x

/-- Product-reference feasibility of the selected extension at the scalar
`polyDim · ctx.t`, obtained from the scalar-construction data. -/
theorem isFeasible_productRef_of_extensionLiftAtScalar
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (hΛ_cp : ∀ x : X, IsCompletelyPositive (Λ x))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hPostselection :
      ∀ {dimOut : ℕ} [NeZero dimOut],
        (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut) → (ρ' : Op (d ^ n * d ^ n)) →
        ρ'.PosSemidef → ρ'.trace.re ≤ 1 →
        InfoTheory.DeFinetti.symmetricProjectorPaired d n * ρ' *
            InfoTheory.DeFinetti.symmetricProjectorPaired d n = ρ' →
        Quantum.Metrics.traceNorm (mapTensorId Δ ρ') ≤
          (polyDim : ℝ) *
            Quantum.Metrics.traceNorm (mapTensorId Δ τ.toOp))
    (ε : ℝ)
    (ctx : EveFeasibleScalar ρEtilde)
    (data :
      ProductRefExtensionLiftAtScalar
        (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
        (Λ := Λ) (polyDim := polyDim) (ε := ε) ctx) :
    isFeasible data.rhoERtilde
      (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR))
      ((polyDim : ℝ) * ctx.t) := by
  exact
    isFeasible_productRef_of_blockDomination
      (σR := σR) (ρEtilde := ρEtilde) (ρERtilde := data.rhoERtilde)
      (polyDim := polyDim) (ctx := ctx)
      (fun x =>
        opLe_smul_productRef_of_extensionLiftAtScalar
          (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
          (Λ := Λ) hΛ_cp (polyDim := polyDim) h_polyDim_pos
          hPostselection (ε := ε) ctx data x)

/-- Produces a `ProductRefEntropyRealTransferWitnessExists` from a
scalar-construction frontier for the chosen `ρEtilde`, the CKR trace-norm
postselection bound, and the paired-symmetric support data for `τ`. -/
theorem productRefEntropyRealTransferWitnessExists_of_extensionLiftExists
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρE : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (hΛ_cp : ∀ x : X, IsCompletelyPositive (Λ x))
    (hτ_marginal : τ.partialTraceB = σR)
    (hτ_reference_marginal : τ.partialTraceA = σR)
    (hτ_paired : InfoTheory.DeFinetti.IsPairedPermInvariant τ)
    (hτ_support :
      InfoTheory.DeFinetti.symmetricProjectorPaired d n * τ.toOp *
          InfoTheory.DeFinetti.symmetricProjectorPaired d n = τ.toOp)
    (hρE_center : ∀ x : X, (ρE.stateMap x).toOp = Λ x σR.toOp)
    (hρER_center : ∀ x : X, (ρER.stateMap x).toOp = mapTensorId (Λ x) τ.toOp)
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hPostselection :
      ∀ {dimOut : ℕ} [NeZero dimOut],
        (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut) → (ρ' : Op (d ^ n * d ^ n)) →
        ρ'.PosSemidef → ρ'.trace.re ≤ 1 →
        InfoTheory.DeFinetti.symmetricProjectorPaired d n * ρ' *
            InfoTheory.DeFinetti.symmetricProjectorPaired d n = ρ' →
        Quantum.Metrics.traceNorm (mapTensorId Δ ρ') ≤
          (polyDim : ℝ) *
            Quantum.Metrics.traceNorm (mapTensorId Δ τ.toOp))
    (ε : ℝ)
    (ρEtilde : CQState X dE)
    (hdE : CQState.purifiedDistance ρE ρEtilde ≤ ε)
    (hFrontier : ProductRefExtensionLiftExists
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) (ε := ε)) :
    ProductRefEntropyRealTransferWitnessExists
      (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (polyDim := polyDim) (ε := ε) := by
  have _ : τ.partialTraceB = σR := hτ_marginal
  have _ : τ.partialTraceA = σR := hτ_reference_marginal
  have _ : InfoTheory.DeFinetti.IsPairedPermInvariant τ := hτ_paired
  have _ :
      InfoTheory.DeFinetti.symmetricProjectorPaired d n * τ.toOp *
          InfoTheory.DeFinetti.symmetricProjectorPaired d n = τ.toOp :=
    hτ_support
  have _ : ∀ x : X, (ρE.stateMap x).toOp = Λ x σR.toOp := hρE_center
  have _ : ∀ x : X, (ρER.stateMap x).toOp = mapTensorId (Λ x) τ.toOp :=
    hρER_center
  have _ : CQState.purifiedDistance ρE ρEtilde ≤ ε := hdE
  let M_E : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE)
  let ctx : EveFeasibleScalar ρEtilde := {
    t := minFeasibleLambda ρEtilde M_E
    feasible := by
      simpa [M_E] using
        isFeasible_minFeasibleLambda_of_posDef ρEtilde M_E
          (by simpa [M_E] using (maxMixed_toSubDensityOp_posDef : M_E.toOp.PosDef))
  }
  obtain ⟨data⟩ :=
    nonempty_productRefExtensionLiftAtScalar_of_liftExists
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) (ε := ε) hFrontier ctx
  let smooth : ProductRefSupportedPostselectionSmoothingWitness
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) (ε := ε) := {
    rhoERtilde := data.rhoERtilde
    distance_le := data.distance_le
    block_marginal_eq := data.block_marginal_eq
    postselection_compat := data.postselection_compat
    feasible_at_min := by
      simpa [ctx, M_E] using
        isFeasible_productRef_of_extensionLiftAtScalar
          (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
          (Λ := Λ) hΛ_cp (polyDim := polyDim) h_polyDim_pos
          hPostselection (ε := ε) ctx data
  }
  exact
    productRefEntropyRealTransferWitnessExists_of_supportedPostselectionWitness
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) h_polyDim_pos (ε := ε) smooth

/-- Paired-CKR smooth-min-entropy chain rule at the product reference.

Let `τ : DensityOp (dⁿ · dⁿ)` be a paired-permutation-invariant purification with
`E`-side family `Λ x : Op dⁿ → Op dE` of completely positive maps, producing the
Eve-only center blocks `ρE x = Λ x σR` and the τ-side center extension blocks
`ρER x = mapTensorId (Λ x) τ`, where `σR = τ.partialTraceB` and also
`σR = τ.partialTraceA` for the untouched product-reference factor. Given paired
symmetric support for `τ`, an Eve-side smoothing approximant `ρEtilde` in the
`ε`-ball of `ρE`, the CKR trace-norm postselection bound hPostselection (any `Δ`
applied to a paired-symmetric subnormalized state has trace norm at most `polyDim`
times its value on `τ`), and a scalar-construction frontier for the chosen
`ρEtilde`, there exists a τ-side approximant extension in the `ε`-ball of `ρER`
whose conditional min-entropy at the product reference `maxMixed_E ⊗ σR` is at
least the Eve-only approximant conditional min-entropy at `maxMixed_E` minus the
additive penalty `log polyDim / log 2`.

The content beyond the trivial register factor `(dⁿ)²` is the CKR improvement to
the symmetric-subspace dimension `polyDim` at the marginal reference `σR` rather
than max-mixed.

References: Renner, smooth-min-entropy chain rule (arXiv:quant-ph/0512258,
`lem:Halphachainsmooth`); Christandl–König–Renner key-shortening
(arXiv:0809.3019, `thm:main`). -/
theorem conditionalMinEntropyReal_extension_at_product_ref_ge_of_traceNorm_postselection
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {d n dE : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero dE]
    [NeZero (dE * d ^ n)]
    (τ : DensityOp (d ^ n * d ^ n))
    (σR : DensityOp (d ^ n))
    (ρE : CQState X dE)
    (ρER : CQState X (dE * d ^ n))
    (Λ : X → Op (d ^ n) →ₗ[ℂ] Op dE)
    (hΛ_cp : ∀ x : X, IsCompletelyPositive (Λ x))
    (hτ_marginal : τ.partialTraceB = σR)
    (hτ_reference_marginal : τ.partialTraceA = σR)
    (hτ_paired : InfoTheory.DeFinetti.IsPairedPermInvariant τ)
    (hτ_support :
      InfoTheory.DeFinetti.symmetricProjectorPaired d n * τ.toOp *
          InfoTheory.DeFinetti.symmetricProjectorPaired d n = τ.toOp)
    (hρE_center : ∀ x : X, (ρE.stateMap x).toOp = Λ x σR.toOp)
    (hρER_center : ∀ x : X, (ρER.stateMap x).toOp = mapTensorId (Λ x) τ.toOp)
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hPostselection :
      ∀ {dimOut : ℕ} [NeZero dimOut],
        (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut) → (ρ' : Op (d ^ n * d ^ n)) →
        ρ'.PosSemidef → ρ'.trace.re ≤ 1 →
        InfoTheory.DeFinetti.symmetricProjectorPaired d n * ρ' *
            InfoTheory.DeFinetti.symmetricProjectorPaired d n = ρ' →
        Quantum.Metrics.traceNorm (mapTensorId Δ ρ') ≤
          (polyDim : ℝ) *
            Quantum.Metrics.traceNorm (mapTensorId Δ τ.toOp))
    (ε : ℝ)
    (ρEtilde : CQState X dE)
    (hdE : CQState.purifiedDistance ρE ρEtilde ≤ ε)
    (hFrontier : ProductRefExtensionLiftExists
      (τ := τ) (σR := σR) (ρEtilde := ρEtilde) (ρER := ρER)
      (Λ := Λ) (polyDim := polyDim) (ε := ε)) :
    ∃ ρERtilde : CQState X (dE * d ^ n),
      CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
      conditionalMinEntropyReal ρEtilde
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
          Real.log (polyDim : ℝ) / Real.log 2 ≤
        conditionalMinEntropyReal ρERtilde
          (DensityOp.toSubDensityOp (DensityOp.tensor (DensityOp.maxMixed dE) σR)) := by
  obtain ⟨witness⟩ :=
    productRefEntropyRealTransferWitnessExists_of_extensionLiftExists
      (τ := τ) (σR := σR) (ρE := ρE) (ρER := ρER) (Λ := Λ)
      hΛ_cp hτ_marginal hτ_reference_marginal hτ_paired hτ_support
      hρE_center hρER_center
      polyDim h_polyDim_pos hPostselection ε ρEtilde hdE hFrontier
  exact ⟨witness.rhoERtilde, witness.distance_le, witness.entropy_transfer⟩

/-! ## Extension at an arbitrary reference

A caller-supplied positive-definite Eve reference avoids a maximally mixed reference penalty.
Feasible coefficients and signed conditional entropy transfer to the extended register with
logarithmic cost `log₂ polyDim`. The canonical smooth comparison follows by transporting ball
witnesses through `smoothMinEntropy_le_add_of_transport`.
-/

/-- A general Eve-side feasible scalar at an arbitrary reference `σE`.  The eveDim-free
analogue of `EveFeasibleScalar`, which pins the reference to `maxMixed dE`. -/
structure FeasibleScalarAt
    {X : Type*} [Fintype X]
    {dE : ℕ} [NeZero dE]
    (ρEtilde : CQState X dE)
    (σE : SubDensityOp dE) where
  /-- The Eve-side feasible scalar. -/
  t : ℝ
  /-- Feasibility of `t` for the chosen reference `σE`. -/
  feasible : isFeasible ρEtilde σE t

/-- Min-feasible-λ control at an arbitrary extension-side reference `σER` from a feasible
transfer keyed to an arbitrary positive-definite Eve-side reference `σE` (NOT `maxMixed`).
The eveDim-free analogue of `minFeasibleLambda_correlated_ref_control_of_feasible_transfer`. -/
theorem minFeasibleLambda_correlated_ref_control_of_feasible_transfer_atRef
    {X : Type*} [Fintype X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE]
    (σE : SubDensityOp dE) (hσE_pd : σE.toOp.PosDef)
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hERtilde_marginal : ∀ x : X,
      partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hFeasibleTransfer :
      ∀ {t : ℝ},
        isFeasible ρEtilde σE t →
          isFeasible ρERtilde σER ((polyDim : ℝ) * t)) :
    (0 < ∑ x : X, (ρEtilde.stateMap x).trace →
      0 < minFeasibleLambda ρERtilde σER) ∧
    minFeasibleLambda ρERtilde σER ≤
      (polyDim : ℝ) * minFeasibleLambda ρEtilde σE := by
  have hweight_eq :
      (∑ x : X, (ρERtilde.stateMap x).trace) =
        ∑ x : X, (ρEtilde.stateMap x).trace := by
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [← hERtilde_marginal x, trace_partialTraceB]
  have hfeasE : hasFeasibleLambda ρEtilde σE := hasFeasibleLambda_of_posDef ρEtilde σE hσE_pd
  have hfeasER : hasFeasibleLambda ρERtilde σER := by
    obtain ⟨t, ht⟩ := hfeasE
    exact ⟨(polyDim : ℝ) * t, hFeasibleTransfer ht⟩
  constructor
  · intro hweightE
    have hweightER : 0 < ∑ x : X, (ρERtilde.stateMap x).trace := by
      simpa [hweight_eq] using hweightE
    exact
      minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρERtilde σER
        hweightER hfeasER
  · have hpoly_nonneg : (0 : ℝ) ≤ (polyDim : ℝ) := by
      exact_mod_cast h_polyDim_pos.le
    exact
      minFeasibleLambda_le_mul_of_isFeasible_scaling
        ρEtilde σE ρERtilde σER hpoly_nonneg hfeasE
        (fun {t} ht => hFeasibleTransfer ht)

/-- Converts min-feasible-λ control at `σER` into the additive entropy bound keyed to an
arbitrary positive-definite Eve-side reference `σE` (NOT `maxMixed`).  The eveDim-free
analogue of `conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_minFeasibleLambda_control`.
-/
theorem conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_minFeasibleLambda_control_atRef
    {X : Type*} [Fintype X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE]
    (σE : SubDensityOp dE) (hσE_pd : σE.toOp.PosDef)
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hERtilde_marginal : ∀ x : X,
      partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hposER :
      0 < ∑ x : X, (ρEtilde.stateMap x).trace →
        0 < minFeasibleLambda ρERtilde σER)
    (hlam :
      minFeasibleLambda ρERtilde σER ≤
        (polyDim : ℝ) * minFeasibleLambda ρEtilde σE) :
    conditionalMinEntropyReal ρEtilde σE -
        Real.log (polyDim : ℝ) / Real.log 2 ≤
      conditionalMinEntropyReal ρERtilde σER := by
  set lamE : ℝ := minFeasibleLambda ρEtilde σE with hlamE_def
  set lamER : ℝ := minFeasibleLambda ρERtilde σER with hlamER_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpoly_pos : (0 : ℝ) < (polyDim : ℝ) := by exact_mod_cast h_polyDim_pos
  have hpoly_ne : (polyDim : ℝ) ≠ 0 := hpoly_pos.ne'
  have hpoly_ge_one : (1 : ℝ) ≤ (polyDim : ℝ) := by exact_mod_cast h_polyDim_pos
  have hweight_eq :
      (∑ x : X, (ρERtilde.stateMap x).trace) =
        ∑ x : X, (ρEtilde.stateMap x).trace := by
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [← hERtilde_marginal x, trace_partialTraceB]
  by_cases hweightE : 0 < ∑ x : X, (ρEtilde.stateMap x).trace
  · have hfeasE : hasFeasibleLambda ρEtilde σE :=
      hasFeasibleLambda_of_posDef ρEtilde σE hσE_pd
    have hlamE_pos : 0 < lamE := by
      simpa [hlamE_def] using
        minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρEtilde σE
          hweightE hfeasE
    have hlamER_pos : 0 < lamER := by
      simpa [hlamER_def] using hposER hweightE
    have hlog_le :
        Real.log lamER ≤ Real.log ((polyDim : ℝ) * lamE) :=
      Real.log_le_log hlamER_pos (by simpa [hlamER_def, hlamE_def] using hlam)
    have hlog_mul :
        Real.log ((polyDim : ℝ) * lamE) =
          Real.log (polyDim : ℝ) + Real.log lamE := by
      rw [Real.log_mul hpoly_ne (ne_of_gt hlamE_pos)]
    have hlog_bound :
        Real.log lamER ≤ Real.log (polyDim : ℝ) + Real.log lamE := by
      simpa [hlog_mul] using hlog_le
    unfold conditionalMinEntropyReal
    change
      -Real.log lamE / Real.log 2 - Real.log (polyDim : ℝ) / Real.log 2 ≤
        -Real.log lamER / Real.log 2
    rw [← sub_div]
    have hnum : -Real.log lamE - Real.log (polyDim : ℝ) ≤ -Real.log lamER := by
      linarith
    exact div_le_div_of_nonneg_right hnum hlog2_pos.le
  · have hE_zero : ∀ x : X, (ρEtilde.stateMap x).toOp = 0 :=
      CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρEtilde hweightE
    have hweightER : ¬ 0 < ∑ x : X, (ρERtilde.stateMap x).trace := by
      intro h
      exact hweightE (by rwa [hweight_eq] at h)
    have hER_zero : ∀ x : X, (ρERtilde.stateMap x).toOp = 0 :=
      CQState.stateMap_toOp_eq_zero_of_weight_nonpos ρERtilde hweightER
    have hlamE_zero : lamE = 0 :=
      minFeasibleLambda_eq_zero_of_stateMap_zero ρEtilde hE_zero σE
    have hlamER_zero : lamER = 0 :=
      minFeasibleLambda_eq_zero_of_stateMap_zero ρERtilde hER_zero σER
    unfold conditionalMinEntropyReal
    rw [← hlamE_def, ← hlamER_def, hlamE_zero, hlamER_zero, Real.log_zero,
      neg_zero, zero_div, zero_sub]
    have hpenalty_nonneg : 0 ≤ Real.log (polyDim : ℝ) / Real.log 2 :=
      div_nonneg (Real.log_nonneg hpoly_ge_one) hlog2_pos.le
    linarith

/-- The eveDim-free entropy transfer keyed to an arbitrary positive-definite Eve-side
reference `σE`: from a feasible-scalar transfer `t ↦ polyDim · t` and the blockwise
marginal identity,
`conditionalMinEntropyReal ρERtilde σER ≥ conditionalMinEntropyReal ρEtilde σE − log₂ polyDim`.
This is `conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_feasible_transfer` with
the Eve-side reference moved off `maxMixed` (and hence eveDim-free for the optimal `σE`). -/
theorem conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_feasible_transfer_atRef
    {X : Type*} [Fintype X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE]
    (σE : SubDensityOp dE) (hσE_pd : σE.toOp.PosDef)
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρERtilde : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (hERtilde_marginal : ∀ x : X,
      partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hFeasibleTransfer :
      ∀ {t : ℝ},
        isFeasible ρEtilde σE t →
          isFeasible ρERtilde σER ((polyDim : ℝ) * t)) :
    conditionalMinEntropyReal ρEtilde σE -
        Real.log (polyDim : ℝ) / Real.log 2 ≤
      conditionalMinEntropyReal ρERtilde σER := by
  have hcontrol :=
    minFeasibleLambda_correlated_ref_control_of_feasible_transfer_atRef
      (σE := σE) hσE_pd (σER := σER) (ρEtilde := ρEtilde) (ρERtilde := ρERtilde)
      polyDim h_polyDim_pos hERtilde_marginal hFeasibleTransfer
  exact
    conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_minFeasibleLambda_control_atRef
      (σE := σE) hσE_pd (σER := σER) (ρEtilde := ρEtilde) (ρERtilde := ρERtilde)
      polyDim h_polyDim_pos hERtilde_marginal hcontrol.1 hcontrol.2

/-- **Unsmoothed correlated-reference entropy transfer at an arbitrary positive-definite
Eve-side reference `σE`** (eveDim-free analogue of
`exists_correlatedRef_entropyRealTransfer_of_extensionLiftExists`).

From the per-scalar smoothed operator domination hsmoothedDomination keyed to the
`σE`-feasible scalar, selects the τ-side approximant and applies the eveDim-free transfer:
the τ-side conditional min-entropy at `σER` is at least
`conditionalMinEntropyReal ρEtilde σE − log polyDim / log 2`. -/
theorem exists_correlatedRef_entropyRealTransfer_of_extensionLiftExists_atRef
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero (dE * dR)]
    (σE : SubDensityOp dE) (hσE_pd : σE.toOp.PosDef)
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (ε : ℝ)
    (hsmoothedDomination : ∀ ctx : FeasibleScalarAt ρEtilde σE,
      ∃ ρERtilde : CQState X (dE * dR),
        CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
        (∀ x : X,
          partialTraceB (ρERtilde.stateMap x).toOp = (ρEtilde.stateMap x).toOp) ∧
        (∀ x : X,
          opLe (ρERtilde.stateMap x).toOp
            ((Complex.ofReal ((polyDim : ℝ) * ctx.t)) • σER.toOp))) :
    ∃ ρERtilde : CQState X (dE * dR),
      CQState.purifiedDistance ρER ρERtilde ≤ ε ∧
      conditionalMinEntropyReal ρEtilde σE -
          Real.log (polyDim : ℝ) / Real.log 2 ≤
        conditionalMinEntropyReal ρERtilde σER := by
  let ctx : FeasibleScalarAt ρEtilde σE := {
    t := minFeasibleLambda ρEtilde σE
    feasible := isFeasible_minFeasibleLambda_of_posDef ρEtilde σE hσE_pd
  }
  obtain ⟨ρERtilde, hdist, hmarginal, hdom⟩ := hsmoothedDomination ctx
  refine ⟨ρERtilde, hdist, ?_⟩
  have hmin : isFeasible ρERtilde σER
      ((polyDim : ℝ) * minFeasibleLambda ρEtilde σE) := by
    refine ⟨mul_nonneg (Nat.cast_nonneg polyDim) (minFeasibleLambda_nonneg ρEtilde σE),
      fun x => ?_⟩
    exact hdom x
  have hFeasibleTransfer :
      ∀ {t : ℝ}, isFeasible ρEtilde σE t →
          isFeasible ρERtilde σER ((polyDim : ℝ) * t) := by
    intro t ht
    exact
      isFeasible_mul_minFeasibleLambda_mono
        ρEtilde σE ρERtilde σER (Nat.cast_nonneg polyDim) hmin ht
  exact
    conditionalMinEntropyReal_extension_at_correlated_ref_ge_of_feasible_transfer_atRef
      (σE := σE) hσE_pd (σER := σER) (ρEtilde := ρEtilde) (ρERtilde := ρERtilde)
      polyDim h_polyDim_pos hmarginal (fun {t} ht => hFeasibleTransfer ht)


/-- A lift of every smoothed domination witness transfers signed smooth min-entropy to the
correlated reference with loss `log polyDim / log 2`. -/
theorem smoothMinEntropyReal_extension_at_correlated_ref_ge_of_smoothedDomination
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero (dE * dR)]
    (σER : SubDensityOp (dE * dR))
    (ρEtilde : CQState X dE)
    (ρER : CQState X (dE * dR))
    (polyDim : ℕ) (h_polyDim_pos : 0 < polyDim)
    (ε : ℝ)
    (hblocks : ∀ x : X,
      partialTraceB (ρER.stateMap x).toOp = (ρEtilde.stateMap x).toOp)
    (hsmoothedDomination : ∀ ρ' : CQState X dE,
      CQState.purifiedDistance ρEtilde ρ' ≤ ε →
      ∀ ctx' : EveFeasibleScalar ρ',
        ∃ ρ'ER : CQState X (dE * dR),
          CQState.purifiedDistance ρER ρ'ER ≤ ε ∧
          (∀ x : X,
            partialTraceB (ρ'ER.stateMap x).toOp = (ρ'.stateMap x).toOp) ∧
          (∀ x : X,
            opLe (ρ'ER.stateMap x).toOp
              ((Complex.ofReal ((polyDim : ℝ) * ctx'.t)) • σER.toOp))) :
    smoothMinEntropyReal ε ρEtilde
        (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)) -
        Real.log (polyDim : ℝ) / Real.log 2 ≤
      smoothMinEntropyReal ε ρER σER := by
  classical
  set M_E : SubDensityOp dE :=
    DensityOp.toSubDensityOp (DensityOp.maxMixed dE) with hM_E
  set penalty : ℝ := Real.log (polyDim : ℝ) / Real.log 2 with hpenalty
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpolyDim_ge1 : (1 : ℝ) ≤ (polyDim : ℝ) := by exact_mod_cast h_polyDim_pos
  have hpenalty_nn : 0 ≤ penalty := by
    rw [hpenalty]; exact div_nonneg (Real.log_nonneg hpolyDim_ge1) hlog2.le
  set A := setOf (isInSmoothedSetReal ε ρEtilde M_E) with hA
  set B := setOf (isInSmoothedSetReal ε ρER σER) with hB
  change sSup A - penalty ≤ sSup B
  have hweight_eq :
      (∑ x : X, (ρER.stateMap x).trace) =
        ∑ x : X, (ρEtilde.stateMap x).trace := by
    apply Finset.sum_congr rfl
    intro x _
    unfold SubDensityOp.trace
    rw [← hblocks x, trace_partialTraceB]
  by_cases hε_nn : 0 ≤ ε
  · -- Nonnegative radius: forward map A → B, then csSup transfer.
    have hA_ne : A.Nonempty := smoothedSetReal_nonempty hε_nn ρEtilde M_E
    have h_AB : ∀ a ∈ A, ∃ b ∈ B, a - penalty ≤ b := by
      rintro a ⟨ρ', rfl, hd⟩
      have hd' : CQState.purifiedDistance ρEtilde ρ' ≤ ε := hd
      have hFrontier :
          CorrelatedRefExtensionLiftExists
            (σER := σER) (ρEtilde := ρ') (ρER := ρER)
            (polyDim := polyDim) (ε := ε) :=
        correlatedRefExtensionLiftExists_of_smoothedDomination
          (σER := σER) (ρEtilde := ρ') (ρER := ρER) (ε := ε) (polyDim := polyDim)
          (fun ctx' => hsmoothedDomination ρ' hd' ctx')
      obtain ⟨ρ'ER, hdER, htransfer⟩ :=
        exists_correlatedRef_entropyRealTransfer_of_extensionLiftExists
          (σER := σER) (ρEtilde := ρ') (ρER := ρER)
          (polyDim := polyDim) h_polyDim_pos (ε := ε) hFrontier
      refine ⟨conditionalMinEntropyReal ρ'ER σER, ⟨ρ'ER, rfl, hdER⟩, ?_⟩
      simpa [hM_E, hpenalty] using htransfer
    by_cases hBddB : BddAbove B
    · -- B bounded above: csSup transfer directly.
      exact csSup_sub_le_csSup_of_forall_exists_sub_le A B penalty hA_ne hBddB h_AB
    · -- B not bounded above: `sSup B = 0`; show `sSup A - penalty ≤ 0`.
      rw [Real.sSup_of_not_bddAbove hBddB]
      have hweightER_le : (∑ x : X, (ρER.stateMap x).trace) ≤ ε ^ 2 := by
        by_contra hgt
        push_neg at hgt
        apply hBddB
        set wER : ℝ := ∑ x : X, (ρER.stateMap x).trace with hwER_def
        have hwER_le_one : wER ≤ 1 := by simpa [hwER_def] using ρER.weight_le_one
        set η : ℝ := purifiedDistanceWeightFloor ε wER with hη_def
        have hη_pos : 0 < η := by
          simpa [hη_def] using
            purifiedDistanceWeightFloor_pos hε_nn hwER_le_one (by simpa [hwER_def] using hgt)
        have hfloor : ∀ ρ' : CQState X (dE * dR),
            CQState.purifiedDistance ρER ρ' ≤ ε →
              η ≤ ∑ x : X, (ρ'.stateMap x).trace := by
          intro ρ' hd
          simpa [hη_def] using
            CQState.sum_stateMap_trace_ge_purifiedDistanceWeightFloor
              (ρ := ρER) (ρ' := ρ') hε_nn (by simpa [hwER_def] using hgt) hd
        exact
          smoothMinEntropyReal_bddAbove_of_candidate_weight_floor
            ε η hη_pos ρER σER hfloor
      have hweightE_le : (∑ x : X, (ρEtilde.stateMap x).trace) ≤ ε ^ 2 := by
        rw [← hweight_eq]; exact hweightER_le
      have hε_pos : 0 < ε := by
        rcases lt_or_eq_of_le hε_nn with h | h
        · exact h
        · exfalso
          apply hBddB
          refine ⟨conditionalMinEntropyReal ρER σER, ?_⟩
          rintro v ⟨ρt, rfl, hdt⟩
          have hdt0 : purifiedDistance ρER.toJointDensity ρt.toJointDensity ≤ 0 := by
            have : CQState.purifiedDistance ρER ρt ≤ 0 := h ▸ hdt
            exact this
          have hnn := purifiedDistance_nonneg ρER.toJointDensity ρt.toJointDensity
          have hzero : purifiedDistance ρER.toJointDensity ρt.toJointDensity = 0 :=
            le_antisymm hdt0 hnn
          have hjoint_eq : ρER.toJointDensity = ρt.toJointDensity :=
            (purifiedDistance_eq_zero_iff _ _).mp hzero
          exact ge_of_eq (conditionalMinEntropyReal_congr_toJointDensity σER hjoint_eq)
      have hA_unbdd :
          ¬ BddAbove (setOf (isInSmoothedSetReal ε ρEtilde
            (DensityOp.toSubDensityOp (DensityOp.maxMixed dE)))) :=
        smoothedSetReal_not_bddAbove_of_weight_le_eps_sq_of_posDef ρEtilde
          (DensityOp.toSubDensityOp (DensityOp.maxMixed dE))
          maxMixed_toSubDensityOp_posDef ε hε_pos hweightE_le
      have hA_unbdd' : ¬ BddAbove A := by rw [hA, hM_E]; exact hA_unbdd
      rw [Real.sSup_of_not_bddAbove hA_unbdd']
      linarith [hpenalty_nn]
  · -- Negative radius: both balls empty, `sSup A = sSup B = 0`, penalty nonnegative.
    have hε_lt : ε < 0 := lt_of_not_ge hε_nn
    have hA_empty : A = ∅ := by
      rw [hA]; ext v; constructor
      · rintro ⟨ρt, _, hd⟩
        have hnn : 0 ≤ CQState.purifiedDistance ρEtilde ρt := by
          unfold CQState.purifiedDistance
          exact purifiedDistance_nonneg ρEtilde.toJointDensity ρt.toJointDensity
        linarith
      · intro hv; cases hv
    have hB_empty : B = ∅ := by
      rw [hB]; ext v; constructor
      · rintro ⟨ρt, _, hd⟩
        have hnn : 0 ≤ CQState.purifiedDistance ρER ρt := by
          unfold CQState.purifiedDistance
          exact purifiedDistance_nonneg ρER.toJointDensity ρt.toJointDensity
        linarith
      · intro hv; cases hv
    rw [hA_empty, hB_empty, Real.sSup_empty]
    linarith [hpenalty_nn]

/-- A marginal signed floor transfers to a supported extension with loss at most `2 * log g /
log 2` when the extension dimension is at most `g`. -/
theorem smoothMinEntropyReal_correlatedRef_ge_floor_of_supportedExtension
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dV : ℕ} [NeZero dE] [NeZero dV]
    (σE : SubDensityOp dE)
    (ρEtilde : CQState X dE)
    (ρEV : CQState X (dE * dV))
    (g : ℕ) (hg_pos : 0 < g) (hdV : dV ≤ g)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (floor : ℝ)
    (hFloor : floor ≤ smoothMinEntropyReal ε ρEtilde σE)
    (hblocks : ∀ x : X,
      partialTraceB (ρEV.stateMap x).toOp = (ρEtilde.stateMap x).toOp) :
    floor - (2 : ℝ) * Real.log (g : ℝ) / Real.log 2 ≤
      smoothMinEntropyReal ε ρEV (σE.tensorMaxMixed dV) := by
  have hpen := smoothMinEntropyReal_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius
    ρEV ρEtilde σE hblocks ε hε_nn
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdV_pos : 0 < (dV : ℝ) := Nat.cast_pos.mpr (NeZero.pos dV)
  have hg_pos' : 0 < (g : ℝ) := Nat.cast_pos.mpr hg_pos
  have hcast : (dV : ℝ) ≤ (g : ℝ) := Nat.cast_le.mpr hdV
  have hlog_le : Real.log (dV : ℝ) ≤ Real.log (g : ℝ) := Real.log_le_log hdV_pos hcast
  have hmono : (2 : ℝ) * Real.log (dV : ℝ) / Real.log 2 ≤
      (2 : ℝ) * Real.log (g : ℝ) / Real.log 2 := by gcongr
  linarith [hpen, hmono, hFloor]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
