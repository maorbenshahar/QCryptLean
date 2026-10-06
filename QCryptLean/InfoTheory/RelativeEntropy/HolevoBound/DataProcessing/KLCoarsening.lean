import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.Basic.Basic
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.Basic.Pinching
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.IsometricInvariance

/-!
# KL Coarsening and Generalized Klein

KL divergence coarsening (log-sum inequality for groups), kernel containment from
eigenvalue support, basis-independent support containment, and the generalized Klein
inequality (diagonal KL ≤ quantum relative entropy in any unitary basis).

## Main statements
- `classicalKLDiv_eq_neg_entropy_sub_log_weight_sum`:
  algebraic KL expansion under support nonvanishing
- `ker_sigma_sub_ker_rho_of_eigenvalue_support`:
  compatibility wrapper for the forward direction of `eigenvalue_support_iff_ker_sub`
- `eigenvalue_support_isometryEmbed`:
  support condition transfers under isometric embedding
- `kl_group_le_sum`: per-group log-sum inequality
- `kl_divergence_coarsening`:
  unnormalized KL coarsening inequality for grouped nonnegative weights
- `support_containment_any_basis`: supp(ρ) ⊆ supp(σ) in any basis
- `generalized_klein_diagonal_bound`:
  diagonal KL bound under an explicit kernel-containment hypothesis
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-- Algebraic decomposition of the project's totalized real-log KL expression.

    For nonnegative `d` and any `m` that does not vanish on the support of `d`, the sum
    `∑ j, if d j = 0 then 0 else d j * log (d j / m j)` splits as
    negative Shannon entropy minus `∑ j, d j * log (m j)`.

    This does not assert that `d` and `m` are normalized probability
    distributions; it is the finite-support algebraic identity used later in the
    coarsening argument. -/
lemma classicalKLDiv_eq_neg_entropy_sub_log_weight_sum {N : ℕ}
    (d m : Fin N → ℝ)
    (hd_nonneg : ∀ j, 0 ≤ d j)
    (h_support : ∀ j, d j ≠ 0 → m j ≠ 0) :
    (∑ j, if d j = 0 then 0 else d j * Real.log (d j / m j)) =
    -shannonEntropy d -
      ∑ j, d j * Real.log (m j) := by
  -- Split log(d/m) = log d - log m term by term
  have hterm : ∀ j, (if d j = 0 then 0
      else d j * Real.log (d j / m j)) =
      (if d j = 0 then 0 else d j * Real.log (d j)) -
        d j * Real.log (m j) := by
    intro j
    by_cases hd : d j = 0
    · simp [hd]
    · simp only [hd, ite_false]
      have hm : m j ≠ 0 := h_support j hd
      have hd_pos : 0 < d j :=
        lt_of_le_of_ne (hd_nonneg j) (Ne.symm hd)
      rw [Real.log_div (ne_of_gt hd_pos) hm]
      ring
  simp_rw [hterm, Finset.sum_sub_distrib]
  -- Match the entropy part: Σ (if d=0 then 0 else d*log d) = -shannonEntropy d
  unfold shannonEntropy entropyTerm
  congr 1
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext j
  by_cases hd : d j = 0 <;> simp [hd, neg_mul]

/-- Compatibility wrapper for the forward direction of `eigenvalue_support_iff_ker_sub`.
    If diag(VρV†)ₖₖ = 0 wherever eigenvalue μₖ = 0, then
    σv = 0 → ρv = 0. -/
lemma ker_sigma_sub_ker_rho_of_eigenvalue_support {N : ℕ} [NeZero N]
    (ρ σ : DensityOp N)
    (h_support :
      ∀ j, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j = 0 →
      diagonalOfRhoInSigmaBasis ρ σ j = 0) :
    ∀ v : Fin N → ℂ,
      σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0 := by
  simpa using (eigenvalue_support_iff_ker_sub ρ σ).mp h_support

/-- Transfer of eigenvalue support condition under isometric embedding. -/
lemma eigenvalue_support_isometryEmbed {n N : ℕ} [NeZero n] [NeZero N]
    (W : Matrix (Fin N) (Fin n) ℂ) (hWU' : W.conjTranspose * W = 1)
    (ρ σ : DensityOp n)
    (h : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
      diagonalOfRhoInSigmaBasis ρ σ i = 0) :
    ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf
        (DensityOp.isometryEmbed W hWU' σ) i = 0 →
      diagonalOfRhoInSigmaBasis
        (DensityOp.isometryEmbed W hWU' ρ)
        (DensityOp.isometryEmbed W hWU' σ) i = 0 := by
  set ρ' := DensityOp.isometryEmbed W hWU' ρ
  set σ' := DensityOp.isometryEmbed W hWU' σ
  have hW_inj : Function.Injective W.mulVec :=
    mulVec_injective_of_conjTranspose_mul_eq_one W hWU'
  have h_ker' : ∀ v, σ'.toOp.mulVec v = 0 →
      ρ'.toOp.mulVec v = 0 :=
    ker_mulVec_zero_conj σ.toOp ρ.toOp W hW_inj
      (ker_sigma_sub_ker_rho_of_eigenvalue_support ρ σ h)
  exact (eigenvalue_support_iff_ker_sub ρ' σ').mpr h_ker'

/-- Generalized Klein inequality after an isometric embedding.

    For an isometry `W`, the KL divergence of the standard diagonals of `WρW†`
    and `WσW†` is bounded by `relativeEntropyReal ρ σ`, provided
    `ker σ ⊆ ker ρ`. The support hypothesis is essential for this finite-valued
    formulation. -/
lemma generalized_klein_diagonal_bound {n N : ℕ} [NeZero n] [NeZero N]
    (W : Matrix (Fin N) (Fin n) ℂ)
    (hWU' : W.conjTranspose * W = 1)
    (ρ σ : DensityOp n)
    (h_ker : ∀ v : Fin n → ℂ,
      σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    (∑ j : Fin N,
      if ((W * ρ.toOp * W.conjTranspose) j j).re = 0 then 0
      else ((W * ρ.toOp * W.conjTranspose) j j).re *
        Real.log (((W * ρ.toOp * W.conjTranspose) j j).re /
                  ((W * σ.toOp * W.conjTranspose) j j).re)) ≤
    relativeEntropyReal ρ σ := by
  set ρ' := DensityOp.isometryEmbed W hWU' ρ
  set σ' := DensityOp.isometryEmbed W hWU' σ
  have hW_inj : Function.Injective W.mulVec :=
    mulVec_injective_of_conjTranspose_mul_eq_one W hWU'
  have h_ker' : ∀ v : Fin N → ℂ, σ'.toOp.mulVec v = 0 → ρ'.toOp.mulVec v = 0 :=
    ker_mulVec_zero_conj σ.toOp ρ.toOp W hW_inj h_ker
  rw [← relativeEntropyReal_isometry_invariance W hWU' ρ σ]
  simpa [ρ', σ'] using InfoTheory.RelativeEntropy.data_processing_pinching ρ' σ' h_ker'

/-- On a finite set where `p` is nonnegative, the totalized KL sum only depends on
the indices where `p` is strictly positive. -/
lemma sum_kl_div_eq_sum_filter_pos {ι : Type*}
    (s : Finset ι) (p q : ι → ℝ)
    (hp_nonneg : ∀ j ∈ s, 0 ≤ p j) :
    ∑ j ∈ s, (if p j = 0 then 0 else p j * Real.log (p j / q j)) =
      ∑ j ∈ s.filter (fun j => 0 < p j), p j * Real.log (p j / q j) := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun j => 0 < p j)]
  have h_zero :
      ∑ j ∈ s.filter (fun j => ¬0 < p j),
        (if p j = 0 then (0 : ℝ) else p j * Real.log (p j / q j)) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      simp [le_antisymm (not_lt.mp (Finset.mem_filter.mp hj).2)
        (hp_nonneg j (Finset.mem_of_mem_filter j hj))]
  rw [h_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp [ne_of_gt (Finset.mem_filter.mp hj).2]

/-- Per-group log-sum inequality (unnormalized).
    For nonneg p, q with support condition, the coarsened KL term is
    ≤ the fine KL sum.
    This is the log-sum inequality: Σ aᵢ log(aᵢ/bᵢ) ≥ A log(A/B). -/
lemma kl_group_le_sum {ι : Type*}
    (s : Finset ι) (p q : ι → ℝ)
    (hp_nonneg : ∀ j ∈ s, 0 ≤ p j) (hq_nonneg : ∀ j ∈ s, 0 ≤ q j)
    (h_support : ∀ j ∈ s, q j = 0 → p j = 0) :
    let ps := ∑ j ∈ s, p j
    let qs := ∑ j ∈ s, q j
    (if ps = 0 then 0 else ps * Real.log (ps / qs)) ≤
    ∑ j ∈ s, if p j = 0 then 0 else p j * Real.log (p j / q j) := by
  classical
  set S := s.filter (fun j => 0 < p j)
  set ps := ∑ j ∈ s, p j
  set qs := ∑ j ∈ s, q j
  have hp_zero_outside : ∀ j ∈ s, j ∉ S → p j = 0 := by
    intro j hj hjS
    have : ¬(0 < p j) := fun h => hjS (Finset.mem_filter.mpr ⟨hj, h⟩)
    linarith [hp_nonneg j hj]
  by_cases hps : ps = 0
  · -- ps = 0: all p j = 0, both sides are 0
    simp only [hps, ite_true]
    have hp_all_zero : ∀ j ∈ s, p j = 0 := fun j hj =>
      le_antisymm
        (by linarith [Finset.single_le_sum (fun i hi => hp_nonneg i hi) hj])
        (hp_nonneg j hj)
    apply Finset.sum_nonneg; intro j hj; simp [hp_all_zero j hj]
  · -- ps > 0: use Jensen's inequality
    simp only [hps, ite_false]
    have hps_pos : 0 < ps := lt_of_le_of_ne
      (Finset.sum_nonneg (fun j hj => hp_nonneg j hj)) (Ne.symm hps)
    have hS_nonempty : S.Nonempty := by
      by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
      exact hps (Finset.sum_eq_zero fun j hj =>
        hp_zero_outside j hj (h ▸ Finset.notMem_empty _))
    -- Fine sum reduces to sum over S = {j ∈ s | p j > 0}
    rw [sum_kl_div_eq_sum_filter_pos s p q hp_nonneg]
    have hps_eq : ps = ∑ j ∈ S, p j :=
      (Finset.sum_subset (Finset.filter_subset _ _)
        (fun j hj hjS => hp_zero_outside j hj hjS)).symm
    have hpj_pos : ∀ j ∈ S, 0 < p j :=
      fun j hj => (Finset.mem_filter.mp hj).2
    have hqj_pos : ∀ j ∈ S, 0 < q j := by
      intro j hj; have hjs := (Finset.mem_filter.mp hj).1
      by_contra h; push Not at h
      linarith [h_support j hjs (le_antisymm h (hq_nonneg j hjs)),
                hpj_pos j hj]
    set qs' := ∑ j ∈ S, q j
    have hqs'_pos : 0 < qs' := Finset.sum_pos'
      (fun j hj => le_of_lt (hqj_pos j hj))
      (by obtain ⟨j, hj⟩ := hS_nonempty; exact ⟨j, hj, hqj_pos j hj⟩)
    have hqs'_le : qs' ≤ qs :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun j hj _ => hq_nonneg j hj)
    have hqs_pos : 0 < qs := lt_of_lt_of_le hqs'_pos hqs'_le
    -- Apply Jensen for concave log with weights p j / ps, points q j / p j
    have hconcave : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
      strictConcaveOn_log_Ioi.concaveOn
    have h_wt_sum : ∑ j ∈ S, p j / ps = 1 := by
      rw [← Finset.sum_div, ← hps_eq]
      exact div_self (ne_of_gt hps_pos)
    have hJ := hconcave.le_map_sum
      (fun j hj => div_nonneg (le_of_lt (hpj_pos j hj))
        (le_of_lt hps_pos))
      h_wt_sum
      (fun j hj => Set.mem_Ioi.mpr
        (div_pos (hqj_pos j hj) (hpj_pos j hj)))
    -- Simplify average: Σ (p j / ps) • (q j / p j) = qs' / ps
    have h_avg : ∑ j ∈ S, (p j / ps) • (q j / p j) = qs' / ps := by
      simp only [smul_eq_mul]
      rw [Finset.sum_congr rfl (fun j hj =>
        show p j / ps * (q j / p j) = q j / ps from by
          rw [div_mul_div_comm, mul_comm ps (p j),
              mul_div_mul_left _ _ (ne_of_gt (hpj_pos j hj))])]
      rw [← Finset.sum_div]
    rw [h_avg] at hJ
    -- Suffices: Σ pj log(qj/pj) ≤ ps log(qs/ps), then negate
    suffices h : ∑ j ∈ S, p j * Real.log (q j / p j) ≤
        ps * Real.log (qs / ps) by
      have h_neg : ∀ j ∈ S,
          p j * Real.log (p j / q j) =
          -(p j * Real.log (q j / p j)) := by
        intro j hj
        rw [Real.log_div (ne_of_gt (hpj_pos j hj))
              (ne_of_gt (hqj_pos j hj)),
            Real.log_div (ne_of_gt (hqj_pos j hj))
              (ne_of_gt (hpj_pos j hj))]; ring
      rw [Finset.sum_congr rfl h_neg,
          show ps * Real.log (ps / qs) =
            -(ps * Real.log (qs / ps)) from by
            rw [Real.log_div (ne_of_gt hps_pos) (ne_of_gt hqs_pos),
                Real.log_div (ne_of_gt hqs_pos) (ne_of_gt hps_pos)]
            ring]
      linarith [Finset.sum_neg_distrib
        (f := fun j => p j * Real.log (q j / p j)) (s := S)]
    -- From Jensen: (1/ps) Σ pj log(qj/pj) ≤ log(qs'/ps) ≤ log(qs/ps)
    have hJ_scaled :
        (1/ps) * ∑ j ∈ S, p j * Real.log (q j / p j) ≤
        Real.log (qs / ps) := by
      have h1 : (1/ps) * ∑ j ∈ S, p j * Real.log (q j / p j) =
          ∑ j ∈ S, (p j / ps) • Real.log (q j / p j) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro j _; simp [smul_eq_mul]; ring
      rw [h1]
      exact le_trans hJ (Real.log_le_log (div_pos hqs'_pos hps_pos)
        (div_le_div_of_nonneg_right hqs'_le (le_of_lt hps_pos)))
    -- Multiply by ps to get the result
    calc ∑ j ∈ S, p j * Real.log (q j / p j)
        = ps * ((1/ps) * ∑ j ∈ S, p j * Real.log (q j / p j)) := by
          rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hps_pos),
              one_mul]
      _ ≤ ps * Real.log (qs / ps) :=
          mul_le_mul_of_nonneg_left hJ_scaled (le_of_lt hps_pos)

/-- Unnormalized KL coarsening inequality (log-sum inequality for groups).

    Grouping nonnegative weights by `g : Fin N → Fin m` can only decrease the
    totalized real-log KL expression. No normalization assumptions are used. -/
lemma kl_divergence_coarsening {N m : ℕ}
    (p q : Fin N → ℝ)
    (hp_nonneg : ∀ j, 0 ≤ p j)
    (hq_nonneg : ∀ j, 0 ≤ q j)
    (g : Fin N → Fin m)
    (h_support : ∀ j, q j = 0 → p j = 0) :
    (∑ y : Fin m,
      let py := ∑ j ∈ Finset.univ.filter (g · = y), p j
      let qy := ∑ j ∈ Finset.univ.filter (g · = y), q j
      if py = 0 then 0 else py * Real.log (py / qy)) ≤
    (∑ j : Fin N,
      if p j = 0 then 0 else p j * Real.log (p j / q j)) := by
  rw [show ∑ j, (if p j = 0 then 0 else p j * Real.log (p j / q j)) =
      ∑ y, ∑ j ∈ Finset.univ.filter (fun j => g j = y),
        (if p j = 0 then 0 else p j * Real.log (p j / q j)) from
    (Finset.sum_fiberwise Finset.univ g _).symm]
  apply Finset.sum_le_sum; intro y _
  exact kl_group_le_sum (Finset.univ.filter (fun j => g j = y)) p q
    (fun j _ => hp_nonneg j) (fun j _ => hq_nonneg j)
    (fun j _ => h_support j)

/-- Support containment is basis-independent.

    If supp(ρ) ⊆ supp(σ) (eigenvalue condition), then for any injective `W.mulVec`,
    (W*σ*W†)_{jj} = 0 implies (W*ρ*W†)_{jj} = 0.

    This uses the PSD structure: ⟨e_j|σ|e_j⟩ = 0 iff σ|e_j⟩ = 0 for
    PSD σ, and supp(ρ) ⊆ supp(σ) means ker(σ) ⊆ ker(ρ). -/
lemma support_containment_any_basis {n m : ℕ} [NeZero n]
    (W : Matrix (Fin m) (Fin n) ℂ)
    (hW_inj : Function.Injective W.mulVec)
    (ρ σ : DensityOp n)
    (h_support : ∀ j, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j = 0 →
      diagonalOfRhoInSigmaBasis ρ σ j = 0) :
    ∀ j, ((W * σ.toOp * W.conjTranspose) j j).re = 0 →
      ((W * ρ.toOp * W.conjTranspose) j j).re = 0 := by
  intro j hj
  have h_ker := ker_sigma_sub_ker_rho_of_eigenvalue_support ρ σ h_support
  have hWσW_psd : (W * σ.toOp * W†).PosSemidef :=
    by
      simpa [Matrix.conjTranspose_conjTranspose] using
        Matrix.PosSemidef.conjTranspose_mul_mul_same
          (posSemidefOp_implies_mathlib σ.toPosSemidefOp) W.conjTranspose
  have h_ker_conj :
      ∀ v, (W * σ.toOp * W.conjTranspose).mulVec v = 0 →
        (W * ρ.toOp * W.conjTranspose).mulVec v = 0 :=
    ker_mulVec_zero_conj σ.toOp ρ.toOp W hW_inj h_ker
  exact diag_zero_of_ker_sub
    (W * σ.toOp * W.conjTranspose)
    (W * ρ.toOp * W.conjTranspose)
    hWσW_psd h_ker_conj (j := j) hj

end InfoTheory.RelativeEntropy

end
