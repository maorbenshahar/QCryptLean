import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.InfoTheory.Measurement.POVM
import QCryptLean.InfoTheory.DistanceBounds.FuchsVanDeGraaf.FuchsCaves

/-!
# Fuchs–van de Graaf lower bound `1 − F ≤ D`

This file develops the lower Fuchs–van de Graaf inequality for normalized mixed
states (Nielsen–Chuang Thm 9.3.1, Watrous Thm 3.33, Tomamichel §3.2–3.3):

  `1 − F(ρ, σ) ≤ D(ρ, σ)`,

complementing the proved upper bound `D ≤ √(1 − F²)`.

## Structure

The proof factors through Fuchs's theorem (`F(ρ,σ) = inf over measurements of the
classical fidelity of the outcome distributions`).  Concretely we use the
achievability half — there is a measurement whose classical (Bhattacharyya)
fidelity equals the quantum fidelity — together with two fully proved facts:

* `classicalFidelity_lower` — the classical Fuchs–van de Graaf bound on probability
  vectors `1 − ∑ᵢ √(pᵢ qᵢ) ≤ ½ ∑ᵢ |pᵢ − qᵢ|`;
* `povm_statisticalDistance_le_traceNormHermitian` — measurement contraction of the
  trace norm: `∑ᵢ |Tr(Mᵢ Δ).re| ≤ ‖Δ‖₁` for a POVM `{Mᵢ}` and a Hermitian
  trace-zero `Δ` (the data-processing inequality for the measurement channel).

## Main statements

* `classicalFidelity_lower`
* `effect_trace_re_abs_le_half_traceNormHermitian_of_trace_zero`
* `povm_statisticalDistance_le_traceNormHermitian`
* `fidelity_eq_classicalFidelity_measurement` (Fuchs achievability — proved by dispatch to
  the Fuchs–Caves construction in `FuchsCaves.lean`; the positive-definite cases are proved
  there, the both-singular case reduces to
  `fidelity_eq_classicalFidelity_measurement_of_bothSingular`)
* `one_sub_fidelity_le_traceDistance` (proved from the above)
-/

open Matrix Quantum.Operators
open scoped ComplexOrder

noncomputable section

namespace Quantum.Metrics

/-!
## Classical Fuchs–van de Graaf

For finite probability vectors `p q`, the Bhattacharyya overlap `∑ √(pᵢ qᵢ)` and
the total variation distance `½ ∑ |pᵢ − qᵢ|` satisfy
`1 − ∑ √(pᵢ qᵢ) ≤ ½ ∑ |pᵢ − qᵢ|`.
-/

/-- **Classical Fuchs–van de Graaf lower bound.**

For finite probability vectors `p q` (nonnegative, summing to one),
`1 − ∑ᵢ √(pᵢ qᵢ) ≤ ½ ∑ᵢ |pᵢ − qᵢ|`. Proved via `min(pᵢ,qᵢ) ≤ √(pᵢ qᵢ)`
(AM–GM) and `½ ∑ |pᵢ − qᵢ| = 1 − ∑ min(pᵢ, qᵢ)`. -/
theorem classicalFidelity_lower {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    1 - classicalFidelity p q ≤ (1 / 2) * ∑ i, |p i - q i| := by
  unfold classicalFidelity
  have hmin : ∀ i, min (p i) (q i) ≤ Real.sqrt (p i * q i) := by
    intro i
    rcases le_total (p i) (q i) with h | h
    · rw [min_eq_left h]
      calc p i = Real.sqrt (p i * p i) := by rw [Real.sqrt_mul_self (hp i)]
        _ ≤ Real.sqrt (p i * q i) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h (hp i))
    · rw [min_eq_right h]
      calc q i = Real.sqrt (q i * q i) := by rw [Real.sqrt_mul_self (hq i)]
        _ ≤ Real.sqrt (p i * q i) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h (hq i))
  have habs : ∀ i, |p i - q i| = p i + q i - 2 * min (p i) (q i) := by
    intro i
    rcases le_total (p i) (q i) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  have hsum_abs : ∑ i, |p i - q i| = 2 - 2 * ∑ i, min (p i) (q i) := by
    simp_rw [habs]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hps, hqs, ← Finset.mul_sum]
    ring
  have hmin_sum : ∑ i, min (p i) (q i) ≤ ∑ i, Real.sqrt (p i * q i) :=
    Finset.sum_le_sum (fun i _ => hmin i)
  rw [hsum_abs]; linarith

/-!
## Effect / measurement contraction of the trace norm
-/

/-- The diagonal entries of an effect `0 ≤ E ≤ I` lie in `[0, 1]`. -/
lemma effect_diag_re_bounds {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ)
    (hE_psd : E.PosSemidef) (hE_le : (1 - E).PosSemidef) (i : Fin n) :
    0 ≤ (E i i).re ∧ (E i i).re ≤ 1 := by
  have h0 : (0 : ℝ) ≤ (E i i).re := by
    have := hE_psd.diag_nonneg (i := i); rw [Complex.le_def] at this; exact this.1
  have h1 : (0 : ℝ) ≤ ((1 - E) i i).re := by
    have := hE_le.diag_nonneg (i := i); rw [Complex.le_def] at this; exact this.1
  rw [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at h1
  exact ⟨h0, by linarith⟩

/-- **Sharp effect bound for trace-zero `A`:** for an effect `0 ≤ E ≤ I` and a
Hermitian matrix `A` with `Tr A = 0`, `|Tr(E A).re| ≤ ½ ‖A‖₁`.

In the eigenbasis of `A`, `Tr(E A).re = ∑ᵢ (Qᵢᵢ).re λᵢ` with `0 ≤ (Qᵢᵢ).re ≤ 1`,
so the value is squeezed between `∑ min(0, λᵢ)` and `∑ max(0, λᵢ)`, each equal to
`±½ ∑ |λᵢ|` by the trace-zero eigenvalue balance. -/
theorem effect_trace_re_abs_le_half_traceNormHermitian_of_trace_zero {n : ℕ} [NeZero n]
    (E : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hE_psd : E.PosSemidef) (hE_le : (1 - E).PosSemidef)
    (hA_herm : A.IsHermitian) (hA_tr : A.trace = 0) :
    |(E * A).trace.re| ≤ (1 / 2) * traceNormHermitian A hA_herm := by
  let U := hA_herm.eigenvectorUnitary.val
  let ev := hA_herm.eigenvalues
  let D := Matrix.diagonal (fun i => (ev i : ℂ))
  have hU_l : U† * U = 1 := by
    have := hA_herm.eigenvectorUnitary.2
    simp only [mem_unitaryGroup_iff'] at this; exact this
  have h_spec : A = U * D * U† := by
    have := hA_herm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h_trace_eq : (E * A).trace = ((U† * E * U) * D).trace := by
    calc (E * A).trace
        = (E * (U * D * U†)).trace := by rw [h_spec]
      _ = (E * U * D * U†).trace := by simp only [Matrix.mul_assoc]
      _ = (U† * (E * U * D)).trace := by rw [Matrix.trace_mul_comm]
      _ = ((U† * E * U) * D).trace := by simp only [Matrix.mul_assoc]
  let Q := U† * E * U
  have hQ_psd : Q.PosSemidef := by
    have : Q = (U†) * E * (U†)† := by simp only [Q, Matrix.conjTranspose_conjTranspose]
    rw [this]; exact hE_psd.mul_mul_conjTranspose_same _
  have hQ_le : (1 - Q).PosSemidef := by
    have h1Q : (1 : Matrix (Fin n) (Fin n) ℂ) - Q = (U†) * (1 - E) * (U†)† := by
      rw [Matrix.conjTranspose_conjTranspose]
      calc (1 : Matrix (Fin n) (Fin n) ℂ) - Q
          = U† * U - U† * E * U := by rw [hU_l]
        _ = U† * (1 - E) * U := by rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [h1Q]; exact hE_le.mul_mul_conjTranspose_same _
  have h_trace_sum : (Q * D).trace = ∑ i, Q i i * (ev i : ℂ) := by
    simp [D, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal]
  rw [h_trace_eq, show (U† * E * U) = Q from rfl, h_trace_sum, Complex.re_sum]
  have h_re_terms : ∀ i, (Q i i * (ev i : ℂ)).re = (Q i i).re * ev i := by
    intro i; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp_rw [h_re_terms]
  have hQdiag := fun i => effect_diag_re_bounds Q hQ_psd hQ_le i
  have hupper : ∑ i, (Q i i).re * ev i ≤ ∑ i, max 0 (ev i) := by
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨hq0, hq1⟩ := hQdiag i
    rcases le_total 0 (ev i) with hev | hev
    · calc (Q i i).re * ev i ≤ 1 * ev i := mul_le_mul_of_nonneg_right hq1 hev
        _ = ev i := one_mul _
        _ = max 0 (ev i) := (max_eq_right hev).symm
    · calc (Q i i).re * ev i ≤ 0 := mul_nonpos_iff.mpr (Or.inl ⟨hq0, hev⟩)
        _ = max 0 (ev i) := (max_eq_left hev).symm
  have hlower : ∑ i, (- max 0 (- ev i)) ≤ ∑ i, (Q i i).re * ev i := by
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨hq0, hq1⟩ := hQdiag i
    rcases le_total 0 (ev i) with hev | hev
    · calc - max 0 (- ev i) = 0 := by rw [max_eq_left (by linarith), neg_zero]
        _ ≤ (Q i i).re * ev i := mul_nonneg hq0 hev
    · calc - max 0 (- ev i) = ev i := by rw [max_eq_right (by linarith)]; ring
        _ = 1 * ev i := (one_mul _).symm
        _ ≤ (Q i i).re * ev i := mul_le_mul_of_nonpos_right hq1 hev
  have heq := trace_zero_eigenvalue_bound A hA_herm hA_tr
  have hhalf : ∑ i, max 0 (ev i) = (1 / 2) * ∑ i, |hA_herm.eigenvalues i| := by
    rw [heq]; ring
  have hbal : ∑ i, max 0 (-ev i) = ∑ i, max 0 (ev i) := by
    have h_abs_split : ∀ x : ℝ, |x| = max 0 x + max 0 (-x) := by
      intro x
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx, max_eq_right hx, max_eq_left (by linarith), add_zero]
      · rw [abs_of_nonpos hx, max_eq_left hx, zero_add, max_eq_right (by linarith)]
    have hsum_split : ∑ i, |ev i| = ∑ i, max 0 (ev i) + ∑ i, max 0 (-ev i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => h_abs_split (ev i))
    have hev_eq : ∑ i, |hA_herm.eigenvalues i| = ∑ i, |ev i| := rfl
    rw [hev_eq] at heq
    linarith [hsum_split, heq]
  have hhalf2 : ∑ i, (- max 0 (- ev i)) = -((1 / 2) * ∑ i, |hA_herm.eigenvalues i|) := by
    rw [Finset.sum_neg_distrib, hbal, hhalf]
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · calc -((1 / 2) * traceNormHermitian A hA_herm)
        = ∑ i, (- max 0 (- ev i)) := by unfold traceNormHermitian; rw [hhalf2]
      _ ≤ ∑ i, (Q i i).re * ev i := hlower
  · calc ∑ i, (Q i i).re * ev i ≤ ∑ i, max 0 (ev i) := hupper
      _ = (1 / 2) * traceNormHermitian A hA_herm := by unfold traceNormHermitian; rw [hhalf]

/-- **Measurement contraction of the trace norm** (data-processing inequality for
the measurement channel).

For a POVM `{Mᵢ}` and a Hermitian trace-zero `A`,
`∑ᵢ |Tr(Mᵢ A).re| ≤ ‖A‖₁`. The positive- and negative-outcome subsets assemble into
two complementary effects `P` and `I − P`; the sharp effect bound applied to each gives
two contributions of `≤ ½‖A‖₁`. -/
theorem povm_statisticalDistance_le_traceNormHermitian {n k : ℕ} [NeZero n]
    (M : InfoTheory.Measurement.POVM n k) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA_herm : A.IsHermitian) (hA_tr : A.trace = 0) :
    ∑ i, |((M.elements i) * A).trace.re| ≤ traceNormHermitian A hA_herm := by
  classical
  set S : Finset (Fin k) := Finset.univ.filter (fun i => 0 ≤ ((M.elements i) * A).trace.re)
    with hS
  set P : Matrix (Fin n) (Fin n) ℂ := ∑ i ∈ S, M.elements i with hP
  set Sc : Finset (Fin k) :=
    Finset.univ.filter (fun i => ¬ 0 ≤ ((M.elements i) * A).trace.re) with hSc
  have hPc : (1 : Matrix (Fin n) (Fin n) ℂ) - P = ∑ i ∈ Sc, M.elements i := by
    have hsum : ∑ i ∈ S, M.elements i + ∑ i ∈ Sc, M.elements i = 1 := by
      rw [hS, hSc, Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => 0 ≤ ((M.elements i) * A).trace.re), M.complete]
    rw [hP, ← hsum]; abel
  have hP_psd : P.PosSemidef := by
    rw [hP]
    exact Matrix.posSemidef_sum S
      (fun i _ => InfoTheory.Measurement.povm_element_is_mathlib_psd M i)
  have hPc_psd : (1 - P).PosSemidef := by
    rw [hPc]
    exact Matrix.posSemidef_sum Sc
      (fun i _ => InfoTheory.Measurement.povm_element_is_mathlib_psd M i)
  have hsplit : ∑ i, |((M.elements i) * A).trace.re|
      = ∑ i ∈ S, ((M.elements i) * A).trace.re
        + ∑ i ∈ Sc, (-((M.elements i) * A).trace.re) := by
    rw [hS, hSc, ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => 0 ≤ ((M.elements i) * A).trace.re)]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_filter] at hi
      rw [abs_of_nonneg hi.2]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_filter] at hi
      rw [abs_of_neg (by push Not at hi; exact hi.2)]
  have hPsum : ∑ i ∈ S, ((M.elements i) * A).trace.re = (P * A).trace.re := by
    rw [hP, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  have hPcsum : ∑ i ∈ Sc, (-((M.elements i) * A).trace.re) = -((1 - P) * A).trace.re := by
    rw [hPc, Finset.sum_neg_distrib, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  have h1P_eff : (1 - (1 - P)).PosSemidef := by
    rw [sub_sub_cancel]; exact hP_psd
  have hboundP := effect_trace_re_abs_le_half_traceNormHermitian_of_trace_zero
    P A hP_psd hPc_psd hA_herm hA_tr
  have hboundPc := effect_trace_re_abs_le_half_traceNormHermitian_of_trace_zero
    (1 - P) A hPc_psd h1P_eff hA_herm hA_tr
  rw [hsplit, hPsum, hPcsum]
  have h1 : (P * A).trace.re ≤ |(P * A).trace.re| := le_abs_self _
  have h2 : -((1 - P) * A).trace.re ≤ |((1 - P) * A).trace.re| := neg_le_abs _
  linarith [hboundP, hboundPc, h1, h2]

/-!
## Fuchs achievability and the lower Fuchs–van de Graaf inequality
-/

/-- **Fuchs's measurement-achievability theorem** (Fuchs–Caves; Nielsen–Chuang Thm 9.3.1
discussion, Watrous Thm 3.33).

For normalized density operators `ρ σ` there is a POVM whose classical (Bhattacharyya)
fidelity of the outcome distributions equals the quantum Uhlmann fidelity:
`F(ρ, σ) = ∑ᵢ √(Tr(Mᵢ ρ).re · Tr(Mᵢ σ).re)`. The optimal measurement is the
projective measurement in the eigenbasis of `σ^{-1/2}(σ^{1/2} ρ σ^{1/2})^{1/2} σ^{-1/2}`.

The proof dispatches on which state is positive definite, using the inverse-based
Fuchs–Caves construction (`fidelity_eq_classicalFidelity_measurement_of_posDef` and its
role-swapped companion), falling back to the support-restricted construction
(`fidelity_eq_classicalFidelity_measurement_of_bothSingular`) when both states are
singular. -/
theorem fidelity_eq_classicalFidelity_measurement {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    ∃ (k : ℕ) (M : InfoTheory.Measurement.POVM n k),
      DensityOp.fidelity ρ σ
        = classicalFidelity (fun i => (M.elements i * ρ.toOp).trace.re)
            (fun i => (M.elements i * σ.toOp).trace.re) := by
  by_cases hσ : σ.toOp.PosDef
  · exact fidelity_eq_classicalFidelity_measurement_of_posDef ρ σ hσ
  · by_cases hρ : ρ.toOp.PosDef
    · exact fidelity_eq_classicalFidelity_measurement_of_posDef_left ρ σ hρ
    · exact fidelity_eq_classicalFidelity_measurement_of_bothSingular ρ σ

/-- **Lower Fuchs–van de Graaf inequality** for normalized mixed states
(Nielsen–Chuang Thm 9.3.1, Watrous Thm 3.33): `1 − F(ρ, σ) ≤ D(ρ, σ)`.

Proved from Fuchs achievability (`fidelity_eq_classicalFidelity_measurement`), the
classical bound (`classicalFidelity_lower`), and the measurement contraction
(`povm_statisticalDistance_le_traceNormHermitian`). -/
theorem one_sub_fidelity_le_traceDistance {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    1 - DensityOp.fidelity ρ σ ≤ DensityOp.traceDistance ρ σ := by
  obtain ⟨k, M, hF⟩ := fidelity_eq_classicalFidelity_measurement ρ σ
  set p : Fin k → ℝ := fun i => (M.elements i * ρ.toOp).trace.re with hp_def
  set q : Fin k → ℝ := fun i => (M.elements i * σ.toOp).trace.re with hq_def
  have hp_nonneg : ∀ i, 0 ≤ p i := fun i => M.prob_nonneg ρ i
  have hq_nonneg : ∀ i, 0 ≤ q i := fun i => M.prob_nonneg σ i
  have hp_sum : ∑ i, p i = 1 := M.prob_sum ρ
  have hq_sum : ∑ i, q i = 1 := M.prob_sum σ
  -- classical FvdG on the outcome distributions
  have hcl : 1 - classicalFidelity p q ≤ (1 / 2) * ∑ i, |p i - q i| :=
    classicalFidelity_lower p q hp_nonneg hq_nonneg hp_sum hq_sum
  -- the difference operator is Hermitian and trace-zero
  set Δ : Matrix (Fin n) (Fin n) ℂ := ρ.toOp - σ.toOp with hΔ
  have hΔ_herm : Δ.IsHermitian := densityOp_sub_isHermitian ρ σ
  have hΔ_tr : Δ.trace = 0 := by
    rw [hΔ, Matrix.trace_sub, ρ.trace_one, σ.trace_one, sub_self]
  -- the statistical distance of the outcomes equals ½ ∑ |p−q| with the Mᵢ
  have hpq_eq : ∀ i, p i - q i = (M.elements i * Δ).trace.re := by
    intro i
    rw [hp_def, hq_def, hΔ, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have hstat : (1 / 2) * ∑ i, |p i - q i| ≤ (1 / 2) * traceNormHermitian Δ hΔ_herm := by
    have hcontract := povm_statisticalDistance_le_traceNormHermitian M Δ hΔ_herm hΔ_tr
    have hrw : ∑ i, |p i - q i| = ∑ i, |((M.elements i) * Δ).trace.re| :=
      Finset.sum_congr rfl (fun i _ => by rw [hpq_eq i])
    rw [hrw]; linarith
  -- trace distance equals ½ ‖Δ‖₁ (Hermitian)
  have hD : DensityOp.traceDistance ρ σ = (1 / 2) * traceNormHermitian Δ hΔ_herm :=
    DensityOp.traceDistance_eq_traceNormHermitian ρ σ
  rw [hF, hD]
  linarith [hcl, hstat]

end Quantum.Metrics

end -- noncomputable section
