import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSmooth

/-!
# Rank-sensitive IID entropy floors

Rank-sensitive classical IID estimates supply extended smooth entropy floors for normalized tensor
powers. The entropy rate and finite-size penalty are computed in bits before conversion to
`ENNReal`.
-/

open Quantum.Operators
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Renner's general `δ` under an explicit classical-rank cap, at the quantum-marginal
reference.**

`δ_iidAEP_general ρ σ n_copies ε ≤ 2·log₂(r + 3)·noiseFactor n_copies ε`
whenever `ρ.classicalRank ≤ r` and `σ.toOp = ρ.quantumMarginalOp`.

The two inputs are the two terms of Renner's log-argument: `rank(ρ_A) ≤ r` by hypothesis, and
`tr(ρ_{AB}²(id ⊗ σ_B⁻¹)) ≤ 1` by `CQState.sum_trace_sq_mul_rpowNegOne_re_le_one`, which needs the
reference to be the quantum marginal.  Together the argument `rank + tr + 2` is at most `r + 3`.

Compare `logb_rank_plus_two_le_two_mul_logb_rank_plus_four`, which instead widens to
`2·log₂ rank + 4`; that bound discards the cap and is weaker as soon as `r + 3 < 4·r`, i.e. for
every `r ≥ 2`. -/
lemma δ_iidAEP_general_le_rankBound
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (hσ_eq : σ.toOp = ρ.quantumMarginalOp)
    (n_copies : ℕ) (ε : ℝ) (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    δ_iidAEP_general ρ σ n_copies ε ≤
      2 * Real.logb 2 ((r : ℝ) + 3) * noiseFactor n_copies ε := by
  have h_rank1 : 1 ≤ ρ.classicalRank :=
    InfoTheory.SmoothMinEntropy.CQState.classicalRank_filter_pos ρ hρ_norm
  have h_tr_le : ρ.tracedSquareTimesInvFactor σ ≤ 1 :=
    InfoTheory.SmoothMinEntropy.CQState.sum_trace_sq_mul_rpowNegOne_re_le_one ρ hρ_norm σ hσ_eq
  have h_tr_nn : 0 ≤ ρ.tracedSquareTimesInvFactor σ :=
    InfoTheory.SmoothMinEntropy.CQState.sum_trace_sq_mul_rpowNegOne_re_nonneg ρ hρ_norm σ hσ_eq
  have h_rank1R : (1 : ℝ) ≤ (ρ.classicalRank : ℝ) := by exact_mod_cast h_rank1
  have h_rankR : (ρ.classicalRank : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrank
  have hpos : (0 : ℝ) < (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2 := by linarith
  have hle : (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2 ≤ (r : ℝ) + 3 := by
    linarith
  have hlog :
      Real.logb 2 ((ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2) ≤
        Real.logb 2 ((r : ℝ) + 3) :=
    Real.logb_le_logb_of_le (by norm_num) hpos hle
  have hnf : 0 ≤ noiseFactor n_copies ε := Real.sqrt_nonneg _
  unfold δ_iidAEP_general
  exact mul_le_mul_of_nonneg_right (by linarith) hnf

/-- The extended classical AEP rate with the completed rank-capped correction. -/
theorem iidAEPClassical_bit_normalized_rankBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (n_copies : ℕ) [NeZero n_copies]
    (ε : ℝ) (hε : 0 < ε)
    (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    ENNReal.ofReal
      (((vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)) / Real.log 2)
        - 2 * Real.logb 2 ((r : ℝ) + 3) * noiseFactor n_copies ε) ≤
      iidAEPSmoothRate ρ (ρ.quantumMarginalDensityOp hρ_norm) n_copies ε := by
  let ρ_B := ρ.quantumMarginalDensityOp hρ_norm
  have hδ := δ_iidAEP_general_le_rankBound ρ hρ_norm ρ_B rfl n_copies ε r hrank
  have hAEP := iidAEPBitEntropyFloor_le_smoothRate_aep ρ hρ_norm ρ_B n_copies ε
    hε (hasFeasibleLambda_quantumMarginalDensityOp ρ hρ_norm)
  refine (ENNReal.ofReal_le_ofReal ?_).trans hAEP
  unfold iidAEPBitEntropyFloor iidAEPBitEntropyContribution
  rw [InfoTheory.RelativeEntropy.relativeEntropyReal_self]
  simp only [sub_zero]
  exact sub_le_sub_left hδ _

/-- The rank-capped i.i.d. AEP lower bound for extended smooth entropy of the full block. -/
theorem iid_smoothHmin_lower_bound_bit_normalized_rankBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (n_copies : ℕ) [NeZero n_copies]
    (ε : ℝ) (hε : 0 < ε)
    (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    ENNReal.ofReal ((n_copies : ℝ) *
      (((vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)) / Real.log 2)
        - 2 * Real.logb 2 ((r : ℝ) + 3) * noiseFactor n_copies ε)) ≤
      smoothMinEntropy ε (CQState.tensorPower ρ n_copies)
        (SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hρ_norm)) n_copies) := by
  exact (ofReal_le_iidAEPSmoothRate_iff
    ρ (ρ.quantumMarginalDensityOp hρ_norm) n_copies ε _).mp
      (iidAEPClassical_bit_normalized_rankBound ρ hρ_norm n_copies ε hε r hrank)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
