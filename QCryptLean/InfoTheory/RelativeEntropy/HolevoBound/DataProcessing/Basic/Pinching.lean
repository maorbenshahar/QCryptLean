import QCryptLean.InfoTheory.RelativeEntropy.Variational.Singular

/-!
# Pinching Data Processing — support cutoffs and diagonal KL monotonicity

This file proves the standard-basis pinching form of data processing for quantum
relative entropy. After a cutoff estimate for exponentially suppressed support
leakage, it derives both the kernel-based and basis-support formulations of the
pinching inequality.

## Main statements
- `exists_mul_exp_neg_le`: exponential cutoff bound `B * exp(-C) ≤ ε`
- `data_processing_pinching`: pinching DPI from kernel containment
- `InfoTheory.RelativeEntropy.data_processing_pinching`: compatibility wrapper for
`data_processing_pinching`
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-- For any real `B` and positive `ε`, there exists `C` such that `B * exp(-C) ≤ ε`. -/
lemma exists_mul_exp_neg_le {B ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, B * Real.exp (-C) ≤ ε := by
  by_cases hB_nn : 0 ≤ B
  · by_cases hB : B = 0
    · exact ⟨0, by simp [hB, le_of_lt hε]⟩
    · have hB_pos : 0 < B := lt_of_le_of_ne hB_nn (Ne.symm hB)
      refine ⟨Real.log B - Real.log ε + 1, ?_⟩
      have hexp : Real.exp (-(Real.log B - Real.log ε + 1)) = ε / B * Real.exp (-1) := by
        rw [show -(Real.log B - Real.log ε + 1) = -Real.log B + Real.log ε + (-1) by ring]
        rw [Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hB_pos,
            Real.exp_log hε]
        ring
      rw [hexp]
      have hexp_le : Real.exp (-1 : ℝ) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by norm_num)
      calc B * (ε / B * Real.exp (-1))
          = ε * Real.exp (-1) := by field_simp
        _ ≤ ε * 1 := by apply mul_le_mul_of_nonneg_left hexp_le (le_of_lt hε)
        _ = ε := by ring
  · refine ⟨0, ?_⟩
    have hB_lt : B < 0 := lt_of_not_ge hB_nn
    simp
    linarith

/-- Under basis-support containment, a positive diagonal entry of `ρ` forces the
corresponding diagonal entry of `σ` to be positive. -/
lemma densityOp_diag_re_pos_of_basis_support {N : ℕ}
    (ρ σ : DensityOp N)
    {j : Fin N}
    (h_basis_support_j : (σ.toOp j j).re = 0 → (ρ.toOp j j).re = 0)
    (hρjj : 0 < (ρ.toOp j j).re) :
    0 < (σ.toOp j j).re := by
  have hσjj_nonneg :
      0 ≤ (σ.toOp j j).re :=
    Quantum.Operators.psd_diag_re_nonneg σ.toOp (posSemidefOp_implies_mathlib σ.toPosSemidefOp) j
  refine lt_of_le_of_ne hσjj_nonneg ?_
  intro hσjj
  exact hρjj.ne' (h_basis_support_j hσjj.symm)

/-- **Data processing for pinching (diagonal extraction) channel** under kernel
containment.

    If `ker σ ⊆ ker ρ`, then the induced classical KL divergence of the
    standard-basis diagonals is bounded by the quantum relative entropy. -/
lemma data_processing_pinching {N : ℕ} [NeZero N]
    (ρ σ : DensityOp N)
    (h_ker : ∀ v : Fin N → ℂ,
      σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    (∑ j : Fin N,
      if (ρ.toOp j j).re = 0 then 0
      else (ρ.toOp j j).re *
        Real.log ((ρ.toOp j j).re / (σ.toOp j j).re)) ≤
    relativeEntropyReal ρ σ := by
  set d : Fin N → ℝ := fun j => (ρ.toOp j j).re with d_def
  set m : Fin N → ℝ := fun j => (σ.toOp j j).re with m_def
  have hσ_psd : σ.toOp.PosSemidef := posSemidefOp_implies_mathlib σ.toPosSemidefOp
  have hd_nn : ∀ j, 0 ≤ d j := fun j =>
    Quantum.Operators.psd_diag_re_nonneg ρ.toOp (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) j
  have hm_nn : ∀ j, 0 ≤ m j := fun j =>
    Quantum.Operators.psd_diag_re_nonneg σ.toOp hσ_psd j
  have hd_sum : ∑ j, d j = 1 :=
    densityOp_diag_re_sum_one ρ.toOp
      ρ.toPosSemidefOp.toHermitianOp.isHermitian ρ.trace_one
  have h_basis_support : ∀ j, (σ.toOp j j).re = 0 → (ρ.toOp j j).re = 0 := by
    intro j hσjj
    exact diag_zero_of_ker_sub σ.toOp ρ.toOp hσ_psd h_ker (j := j) hσjj
  have hd_pos_imp_m_pos : ∀ j, 0 < d j → 0 < m j := by
    intro j hdj
    simpa [d_def, m_def] using
      (densityOp_diag_re_pos_of_basis_support
        (ρ := ρ) (σ := σ) (j := j) (h_basis_support j)
        (by simpa [d_def] using hdj))
  set KL := ∑ j : Fin N, if d j = 0 then 0
    else d j * Real.log (d j / m j)
  apply le_of_forall_pos_le_add
  intro ε hε
  set B := ∑ j ∈ Finset.univ.filter (fun j => d j = 0), m j with B_def
  have hB_nn : 0 ≤ B := Finset.sum_nonneg (fun j _ => hm_nn j)
  obtain ⟨C, hBC⟩ := exists_mul_exp_neg_le hε
  set hC : Fin N → ℝ := fun j => if d j = 0 then -C else Real.log (d j / m j)
  have gibbs : (∑ j, (ρ.toOp j j).re * hC j) -
      Real.log (∑ j, (σ.toOp j j).re * Real.exp (hC j)) ≤
      relativeEntropyReal ρ σ := by
    simpa [hC, d_def, m_def] using
      InfoTheory.RelativeEntropy.gibbs_variational_diagonal_bound_of_ker_sub ρ σ hC h_ker
  have sum_d_hC : (∑ j, d j * hC j) = KL := by
    congr 1
    ext j
    simp only [hC]
    by_cases hj : d j = 0
    · simp [hj]
    · simp [hj]
  have sum_m_exp : (∑ j, m j * Real.exp (hC j)) = 1 + B * Real.exp (-C) := by
    have hterm : ∀ j, m j * Real.exp (hC j) =
        if d j = 0 then m j * Real.exp (-C) else d j := by
      intro j
      by_cases hj : d j = 0
      · simp [hC, hj]
      · simp only [hC, hj, ite_false]
        have hdj : 0 < d j := lt_of_le_of_ne (hd_nn j) (Ne.symm hj)
        have hmj : 0 < m j := hd_pos_imp_m_pos j hdj
        rw [Real.exp_log (div_pos hdj hmj)]
        field_simp
    simp_rw [hterm]
    rw [Finset.sum_ite]
    have h_filt_zero : (∑ j ∈ Finset.univ.filter (fun j => d j = 0),
        m j * Real.exp (-C)) = B * Real.exp (-C) := by
      rw [B_def, Finset.sum_mul]
    have h_filt_nonzero : (∑ j ∈ Finset.univ.filter (fun j => ¬d j = 0), d j) = 1 := by
      have h_split := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j => d j = 0) d
      have h_zero_part : ∑ j ∈ Finset.univ.filter (fun j => d j = 0), d j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact (Finset.mem_filter.mp hj).2
      linarith [hd_sum]
    rw [h_filt_zero, h_filt_nonzero]
    ring
  rw [sum_d_hC, sum_m_exp] at gibbs
  suffices hlog : Real.log (1 + B * Real.exp (-C)) ≤ ε by linarith
  have hBexp_nn : 0 ≤ B * Real.exp (-C) :=
    mul_nonneg hB_nn (le_of_lt (Real.exp_pos _))
  calc Real.log (1 + B * Real.exp (-C))
      ≤ B * Real.exp (-C) := by
        have : Real.log (1 + B * Real.exp (-C)) ≤
          (1 + B * Real.exp (-C)) - 1 := Real.log_le_sub_one_of_pos (by linarith)
        linarith
    _ ≤ ε := hBC

end InfoTheory.RelativeEntropy

end
