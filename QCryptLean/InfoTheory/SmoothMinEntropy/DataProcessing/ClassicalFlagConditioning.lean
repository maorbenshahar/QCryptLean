import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth

/-!
# Conditioning on a classical flag

Operator inequalities yield signed conditional min-entropy comparisons. A lift of each purified-
distance ball witness gives the corresponding canonical smooth entropy comparison.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **PSD sub-branch supply.**  For a classically-labelled flag mixture `Σ_t p_t · blk t` with
nonnegative weights `p ≥ 0` and PSD blocks `blk t`, the accept-mass partial sum over any accept set
`acc` is Löwner below the full sum:

  `Σ_{t ∈ acc} p_t · blk t  ≼  Σ_t p_t · blk t`.

The difference is the reject mass `Σ_{t ∉ acc} p_t · blk t`, a sum of nonnegatively-scaled PSD
blocks and hence PSD. Taking `blk t = (ρ^t.stateMap x).toOp` (the `x`-block of the `t`-th branch)
supplies the operator hypothesis of `conditionalMinEntropyReal_opInequality_conditioning_ge`. -/
theorem accept_PSD_subbranch_of_classicalFlag {n : ℕ} {T : Type*} [Fintype T]
    (p : T → ℝ) (hp : ∀ t, 0 ≤ p t)
    (blk : T → Op n) (hblk : ∀ t, (blk t).PosSemidef)
    (acc : Finset T) :
    opLe (∑ t ∈ acc, Complex.ofReal (p t) • blk t)
         (∑ t : T, Complex.ofReal (p t) • blk t) := by
  classical
  apply opLe_of_posSemidef_sub
  have hsub :
      (∑ t : T, Complex.ofReal (p t) • blk t) - (∑ t ∈ acc, Complex.ofReal (p t) • blk t)
        = ∑ t ∈ (Finset.univ \ acc), Complex.ofReal (p t) • blk t := by
    have h := Finset.sum_sdiff (f := fun t => Complex.ofReal (p t) • blk t)
      (Finset.subset_univ acc)
    rw [← h]; abel
  rw [hsub]
  apply Matrix.posSemidef_sum
  intro t _
  refine (hblk t).smul ?_
  rw [Complex.le_def]
  exact ⟨by simpa using hp t, by simp⟩

/-- **Operator-core accept conditioning chain rule (non-smooth).**  If the accept-conditioned CQ
state `ρ_acc` scaled by the accept probability `p_acc` is blockwise Löwner below the full post-test
CQ state `ρ_full` (`p_acc · ρ_acc(x) ≼ ρ_full(x)` for every key value `x`), then the real-valued
conditional min-entropies satisfy the **linear** deduction

  `H_min_ℝ(K|E)_{ρ_full|σ} + log₂ p_acc ≤ H_min_ℝ(K|E)_{ρ_acc|σ}`.

Proof: one Löwner-scaling step on the min-entropy SDP. From a feasible `λ` for `(ρ_full, σ)`
(`λ · σ ≽ ρ_full(x)`) and the domination `p_acc · ρ_acc(x) ≼ ρ_full(x)`, the scalar `λ / p_acc` is
feasible for `(ρ_acc, σ)`, so `minFeasibleLambda ρ_acc σ ≤ minFeasibleLambda ρ_full σ / p_acc` and
the `−log₂` conversion gives the additive `log₂ p_acc` (nonpositive for a probability `p_acc ≤ 1`).

The side condition `0 < minFeasibleLambda ρ_acc σ` encodes finiteness of the accept-conditioned
min-entropy (the real-valued variant uses Mathlib's `Real.log 0 = 0` sentinel at the boundary), and
`hfeas` (nonempty feasible set for the full state) lets the defining infimum be attained. The bound
is unconditional in how `E` correlates with the flag through the shared source. -/
theorem conditionalMinEntropyReal_opInequality_conditioning_ge
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ_full ρ_acc : CQState X n) (σ : SubDensityOp n) {p_acc : ℝ}
    (hp_pos : 0 < p_acc)
    (hdom : ∀ x : X,
      opLe (Complex.ofReal p_acc • (ρ_acc.stateMap x).toOp) (ρ_full.stateMap x).toOp)
    (hfeas : hasFeasibleLambda ρ_full σ)
    (hpos_acc : 0 < minFeasibleLambda ρ_acc σ) :
    conditionalMinEntropyReal ρ_full σ + Real.log p_acc / Real.log 2
      ≤ conditionalMinEntropyReal ρ_acc σ := by
  set lamF := minFeasibleLambda ρ_full σ with hlamF
  set lamA := minFeasibleLambda ρ_acc σ with hlamA
  have hlamF_nn : 0 ≤ lamF := minFeasibleLambda_nonneg ρ_full σ
  have hfeasF : isFeasible ρ_full σ lamF :=
    isFeasible_minFeasibleLambda_of_hasFeasibleLambda ρ_full σ hfeas
  -- `lamF / p_acc` is feasible for `ρ_acc`.
  have hfeasA : isFeasible ρ_acc σ (lamF / p_acc) := by
    refine ⟨div_nonneg hlamF_nn hp_pos.le, fun x => ?_⟩
    have h1 : opLe (Complex.ofReal p_acc • (ρ_acc.stateMap x).toOp)
                   (Complex.ofReal lamF • σ.toOp) :=
      opLe_trans (hdom x) (hfeasF.2 x)
    have h2 := opLe_smul_nonneg (t := 1 / p_acc) (by positivity) h1
    have hL : Complex.ofReal (1 / p_acc) • (Complex.ofReal p_acc • (ρ_acc.stateMap x).toOp)
            = (ρ_acc.stateMap x).toOp := by
      rw [smul_smul, ← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (ne_of_gt hp_pos),
        Complex.ofReal_one, one_smul]
    have hR : Complex.ofReal (1 / p_acc) • (Complex.ofReal lamF • σ.toOp)
            = Complex.ofReal (lamF / p_acc) • σ.toOp := by
      rw [smul_smul, ← Complex.ofReal_mul, one_div, inv_mul_eq_div]
    rw [hL, hR] at h2
    exact h2
  have hlamA_le : lamA ≤ lamF / p_acc := minFeasibleLambda_le_of_isFeasible ρ_acc σ hfeasA
  have hlamF_pos : 0 < lamF := by
    have h0 : 0 < lamF / p_acc := lt_of_lt_of_le hpos_acc hlamA_le
    have hmul := mul_pos h0 hp_pos
    rwa [div_mul_cancel₀ lamF (ne_of_gt hp_pos)] at hmul
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hkey : Real.log lamA ≤ Real.log lamF - Real.log p_acc := by
    calc Real.log lamA
        ≤ Real.log (lamF / p_acc) := Real.log_le_log hpos_acc hlamA_le
      _ = Real.log lamF - Real.log p_acc := Real.log_div (ne_of_gt hlamF_pos) (ne_of_gt hp_pos)
  have heqF : conditionalMinEntropyReal ρ_full σ = -Real.log lamF / Real.log 2 := by
    rw [hlamF]; rfl
  have heqA : conditionalMinEntropyReal ρ_acc σ = -Real.log lamA / Real.log 2 := by
    rw [hlamA]; rfl
  rw [heqF, heqA, ← add_div]
  rw [div_le_div_iff_of_pos_right hlog2]
  linarith [hkey]

/-- A classical accept-flag ball lift transfers extended smooth entropy with the positive
part of the logarithmic conditioning penalty. -/
theorem smoothMinEntropy_classicalFlag_conditioning_ge_of_ballLift
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (ρ_full ρ_acc : CQState X n) (σ : SubDensityOp n)
    {p_acc : ℝ} (hp_pos : 0 < p_acc)
    (hlift : ∀ ρ' : CQState X n, CQState.purifiedDistance ρ_full ρ' ≤ ε →
      ∃ ρ'_acc : CQState X n, CQState.purifiedDistance ρ_acc ρ'_acc ≤ ε ∧
        ∀ x : X, opLe (Complex.ofReal p_acc • (ρ'_acc.stateMap x).toOp)
          (ρ'.stateMap x).toOp) :
    smoothMinEntropy ε ρ_full σ ≤
      smoothMinEntropy ε ρ_acc σ + ENNReal.ofReal (-Real.log p_acc / Real.log 2) := by
  apply smoothMinEntropy_le_add_of_transport
  intro ρ' hd
  obtain ⟨ρ'_acc, hd', hdom⟩ := hlift ρ' hd
  refine ⟨ρ'_acc, hd', fun k hk => ?_⟩
  have hpow : (2 : ℝ) ^ (-(k - -Real.log p_acc / Real.log 2)) =
      p_acc⁻¹ * 2 ^ (-k) := by
    simpa only [Real.log_inv, neg_div] using two_rpow_neg_sub_log k (inv_pos.mpr hp_pos)
  rw [hpow]
  refine ⟨mul_nonneg (inv_nonneg.mpr hp_pos.le) hk.1, fun x => ?_⟩
  have hscaled := opLe_smul_nonneg (inv_nonneg.mpr hp_pos.le)
    (opLe_trans (hdom x) (hk.2 x))
  simpa only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hp_pos.ne',
    Complex.ofReal_one, one_smul] using hscaled


/-- A classical-flag ball lift increases signed smooth min-entropy by `log p_acc / log 2`. The
positive scalar `p_acc` may exceed one. -/
theorem smoothMinEntropyReal_classicalFlag_conditioning_ge_of_ballLift
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε : 0 ≤ ε) (ρ_full ρ_acc : CQState X n) (σ : SubDensityOp n)
    {p_acc : ℝ} (hp_pos : 0 < p_acc)
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ_acc σ)))
    (hlift : ∀ ρ' : CQState X n, CQState.purifiedDistance ρ_full ρ' ≤ ε →
      ∃ ρ'_acc : CQState X n, CQState.purifiedDistance ρ_acc ρ'_acc ≤ ε ∧
        (∀ x : X,
          opLe (Complex.ofReal p_acc • (ρ'_acc.stateMap x).toOp) (ρ'.stateMap x).toOp) ∧
        hasFeasibleLambda ρ' σ ∧ 0 < minFeasibleLambda ρ'_acc σ) :
    smoothMinEntropyReal ε ρ_full σ + Real.log p_acc / Real.log 2
      ≤ smoothMinEntropyReal ε ρ_acc σ := by
  unfold smoothMinEntropyReal
  have hcomp := csSup_sub_le_csSup_of_forall_exists_sub_le
    (Set.ofPred (isInSmoothedSetReal ε ρ_full σ)) (Set.ofPred (isInSmoothedSetReal ε ρ_acc σ))
    (-(Real.log p_acc / Real.log 2))
    (smoothedSetReal_nonempty hε ρ_full σ) hbdd
    (by
      intro a ha
      obtain ⟨ρ', rfl, hd⟩ := ha
      obtain ⟨ρ'_acc, hdist, hop, hfeas', hpos'⟩ := hlift ρ' hd
      refine ⟨conditionalMinEntropyReal ρ'_acc σ, ⟨ρ'_acc, rfl, hdist⟩, ?_⟩
      have hdecl1 :=
        conditionalMinEntropyReal_opInequality_conditioning_ge ρ' ρ'_acc σ hp_pos hop hfeas' hpos'
      linarith [hdecl1])
  linarith [hcomp]

end InfoTheory.SmoothMinEntropy

end
