import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SuperpositionDephasing.FeasibilityTransfer
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SuperpositionDephasing.PurifiedDistance

/-!
# Classical reduction for superpositions

Feasible-coefficient estimates for dephased mixtures give an extended smooth entropy floor for
superpositions. Real cardinality and entropy penalties are combined before conversion to a
nonnegative floor.
-/

open Real Math.ClassicalEntropy
open Quantum.Operators
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open InfoTheory.SmoothMinEntropy

/-- The dephased mixture is normalized (total trace `1`) when the weights sum to
    `1` and each component is normalized: `tr ρ̃_{ABS} = ∑_{s∈S} weight s · 1 = 1`. -/
lemma dephasedMixtureCQ_sum_stateMap_trace_eq_one
    {X : Type*} [Fintype X] {n : ℕ}
    (S : Finset ℕ) (comp : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (hweight_le_one : ∀ s ∈ S, weight s ≤ 1)
    (hweight_sum : ∑ s ∈ S, weight s ≤ 1)
    (hweight_sum_eq : ∑ s ∈ S, weight s = 1)
    (hcomp_norm : ∀ s ∈ S, ∑ x : X, ((comp s).stateMap x).trace = 1) :
    ∑ p : X × {s // s ∈ S},
        ((dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum).stateMap
          p).trace = 1 := by
  classical
  rw [← CQState.toJointDensity_trace_eq_sum,
    dephasedMixtureCQ_toJointDensity_trace S comp weight hweight_nonneg hweight_le_one
      hweight_sum]
  rw [← hweight_sum_eq]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [CQState.toJointDensity_trace_eq_sum, hcomp_norm s hs, mul_one]

/-- The infimum of completed component floors bounds the extended entropy of the dephased
mixture at any radius. Nonnegative weights with sum at most one are sufficient. Positive
approximating floors give common feasible coefficients and force a nonnegative radius;
nonpositive floors are clipped to zero. -/
theorem smoothHmin_classicalCond_reduction
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (S : Finset ℕ) (hS_nonempty : S.Nonempty)
    (comp : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (hweight_sum : ∑ s ∈ S, weight s ≤ 1)
    (σ_dephased : SubDensityOp n) (σ_cond : ℕ → SubDensityOp n)
    (hσ_dephased_pin : σ_dephased.toOp =
      ∑ s ∈ S, (weight s : ℂ) • (σ_cond s).toOp)
    (ε : ℝ) (componentLower : ℕ → ℝ)
    (hComponentLower : ∀ s ∈ S,
      ENNReal.ofReal (componentLower s) ≤ smoothMinEntropy ε (comp s) (σ_cond s)) :
    letI : Nonempty {s // s ∈ S} := ⟨⟨hS_nonempty.choose, hS_nonempty.choose_spec⟩⟩
    ENNReal.ofReal (S.inf' hS_nonempty componentLower) ≤
      smoothMinEntropy ε
        (dephasedMixtureCQ S comp weight hweight_nonneg
          (fun _ hs => (Finset.single_le_sum hweight_nonneg hs).trans hweight_sum)
          hweight_sum)
        σ_dephased := by
  classical
  have hweight_le_one : ∀ s ∈ S, weight s ≤ 1 :=
    fun _ hs => (Finset.single_le_sum hweight_nonneg hs).trans hweight_sum
  letI : Nonempty {s // s ∈ S} := ⟨⟨hS_nonempty.choose, hS_nonempty.choose_spec⟩⟩
  let mix := dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum
  let H := smoothMinEntropy ε mix σ_dephased
  let F := S.inf' hS_nonempty componentLower
  change ENNReal.ofReal F ≤ H
  by_contra h
  have hlt : H < ENNReal.ofReal F := lt_of_not_ge h
  have hfinite : H ≠ ⊤ := hlt.ne_top
  have hreal : H.toReal < F := ENNReal.toReal_lt_of_lt_ofReal hlt
  let k := (H.toReal + F) / 2
  have hk0 : 0 < k := by dsimp [k]; linarith [ENNReal.toReal_nonneg (a := H)]
  have hkF : k < F := by dsimp [k]; linarith
  have hHk : H < ENNReal.ofReal k := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr
    dsimp [k]
    linarith
  have hex : ∀ s, ∃ τ : CQState X n, s ∈ S →
      CQState.purifiedDistance (comp s) τ ≤ ε ∧
        isFeasible τ (σ_cond s) (2 ^ (-k)) := by
    intro s
    by_cases hs : s ∈ S
    · have hk_component : k < componentLower s :=
        hkF.trans_le (Finset.inf'_le _ hs)
      have hlevel : ENNReal.ofReal k < smoothMinEntropy ε (comp s) (σ_cond s) :=
        (ENNReal.ofReal_lt_ofReal_iff (hk0.trans hk_component)).mpr hk_component |>.trans_le
          (hComponentLower s hs)
      obtain ⟨τ, hd, _, hτ⟩ := smoothMinEntropy_exists_approx
        (comp s) (σ_cond s) (ENNReal.ofReal k) hlevel
      exact ⟨τ, fun _ => ⟨hd,
        isFeasible_of_ofReal_le_conditionalMinEntropy τ (σ_cond s) hk0 hτ.le⟩⟩
    · exact ⟨comp s, fun hs' => (hs hs').elim⟩
  choose comp' hcomp' using hex
  obtain ⟨s, hs⟩ := hS_nonempty.exists_mem
  have hε : 0 ≤ ε :=
    (purifiedDistance_nonneg (comp s).toJointDensity (comp' s).toJointDensity).trans
      (hcomp' s hs).1
  let mix' := dephasedMixtureCQ S comp' weight hweight_nonneg hweight_le_one hweight_sum
  have hpd : CQState.purifiedDistance mix mix' ≤ ε :=
    CQState.purifiedDistance_dephasedMixtureCQ_le S hS_nonempty comp comp' weight
      hweight_nonneg hweight_le_one hweight_sum ε hε (fun s hs => (hcomp' s hs).1)
  have hfeas : isFeasible mix' σ_dephased (2 ^ (-k)) :=
    isFeasible_dephasedMixtureCQ_of_components S comp' weight hweight_nonneg
      hweight_le_one hweight_sum σ_dephased σ_cond hσ_dephased_pin
      (Real.rpow_nonneg (by norm_num) _) (fun s hs => (hcomp' s hs).2)
  exact (not_le_of_gt hHk)
    (smoothMinEntropy_ge_of_isFeasible mix mix' σ_dephased k hpd hfeas)


/-- A dephased mixture inherits the infimum of the signed smooth component floors against their
corresponding references. -/
theorem smoothHminReal_classicalCond_reduction
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (S : Finset ℕ) (hS_nonempty : S.Nonempty)
    (comp : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (hweight_le_one : ∀ s ∈ S, weight s ≤ 1)
    (hweight_sum : ∑ s ∈ S, weight s ≤ 1)
    (hweight_sum_eq : ∑ s ∈ S, weight s = 1)
    (hcomp_norm : ∀ s ∈ S, ∑ x : X, ((comp s).stateMap x).trace = 1)
    (σ_dephased : SubDensityOp n)
    (σ_cond : ℕ → SubDensityOp n)
    (hσ_dephased_pin : σ_dephased.toOp =
      ∑ s ∈ S, (weight s : ℂ) • (σ_cond s).toOp)
    (ε : ℝ) (hε : 0 ≤ ε) (hε_lt_one : ε < 1)
    (hcomp_ball_feas : ∀ s ∈ S, ∀ ρ' : CQState X n,
      CQState.purifiedDistance (comp s) ρ' ≤ ε → hasFeasibleLambda ρ' (σ_cond s))
    (componentLower : ℕ → ℝ)
    (hComponentLower : ∀ s ∈ S,
      componentLower s ≤ smoothMinEntropyReal ε (comp s) (σ_cond s)) :
    letI : Nonempty {s // s ∈ S} := ⟨⟨hS_nonempty.choose, hS_nonempty.choose_spec⟩⟩
    S.inf' hS_nonempty componentLower ≤
      smoothMinEntropyReal ε
        (dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum)
        σ_dephased := by
  classical
  letI : Nonempty {s // s ∈ S} := ⟨⟨hS_nonempty.choose, hS_nonempty.choose_spec⟩⟩
  set mix := dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum with hmix
  have hmix_norm : ∑ p : X × {s // s ∈ S}, (mix.stateMap p).trace = 1 := by
    rw [hmix]
    exact dephasedMixtureCQ_sum_stateMap_trace_eq_one S comp weight hweight_nonneg
      hweight_le_one hweight_sum hweight_sum_eq hcomp_norm
  have hbdd : BddAbove (setOf (isInSmoothedSetReal ε mix σ_dephased)) :=
    smoothMinEntropyReal_bddAbove ε hε_lt_one mix hmix_norm σ_dephased
  refine le_of_forall_pos_le_add (fun ν hν => ?_)
  set k : ℝ := S.inf' hS_nonempty componentLower - ν with hk
  have hex : ∀ s, ∃ ρ' : CQState X n, s ∈ S →
      (CQState.purifiedDistance (comp s) ρ' ≤ ε ∧
        componentLower s - ν ≤ conditionalMinEntropyReal ρ' (σ_cond s)) := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨ρ', hd, he⟩ := smoothMinEntropyReal_exists_approx ε hε (comp s) (σ_cond s)
        (componentLower s - ν) (by linarith [hComponentLower s hs])
      exact ⟨ρ', fun _ => ⟨hd, he⟩⟩
    · exact ⟨comp s, fun h => absurd h hs⟩
  choose comp' hcomp' using hex
  set mix' := dephasedMixtureCQ S comp' weight hweight_nonneg hweight_le_one hweight_sum
    with hmix'
  have hpd_mix : CQState.purifiedDistance mix mix' ≤ ε := by
    rw [hmix, hmix']
    exact CQState.purifiedDistance_dephasedMixtureCQ_le S hS_nonempty comp comp' weight
      hweight_nonneg hweight_le_one hweight_sum ε hε (fun s hs => (hcomp' s hs).1)
  have hcomp_ge : ∀ s ∈ S, k ≤ conditionalMinEntropyReal (comp' s) (σ_cond s) := by
    intro s hs
    have hinf : S.inf' hS_nonempty componentLower ≤ componentLower s :=
      Finset.inf'_le _ hs
    have := (hcomp' s hs).2
    rw [hk]; linarith
  have hcomp_feas : ∀ s ∈ S, hasFeasibleLambda (comp' s) (σ_cond s) := fun s hs =>
    hcomp_ball_feas s hs (comp' s) (hcomp' s hs).1
  have hmix'_weight_pos : 0 < ∑ p : X × {s // s ∈ S}, (mix'.stateMap p).trace := by
    have hε_sq_lt_one : ε ^ 2 < 1 := by nlinarith [hε, hε_lt_one]
    have hge : 1 - ε ^ 2 ≤ ∑ p : X × {s // s ∈ S}, (mix'.stateMap p).trace :=
      CQState.sum_stateMap_trace_ge_of_purifiedDistance hε hmix_norm hpd_mix
    linarith
  have hmix'_feas : hasFeasibleLambda mix' σ_dephased := by
    refine ⟨2 ^ (-k), ?_⟩
    refine isFeasible_dephasedMixtureCQ_of_components S comp' weight hweight_nonneg
      hweight_le_one hweight_sum σ_dephased σ_cond hσ_dephased_pin
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) (fun s hs => ?_)
    have hfeas_attain :=
      isFeasible_minFeasibleLambda_of_hasFeasibleLambda (comp' s) (σ_cond s)
        (hcomp_feas s hs)
    exact isFeasible_mono_t hfeas_attain
      (minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le (comp' s) (σ_cond s) k
          (hcomp_ge s hs))
  have hpos : 0 < minFeasibleLambda mix' σ_dephased :=
    minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos mix' σ_dephased
      hmix'_weight_pos hmix'_feas
  have hk_le_mix : k ≤ conditionalMinEntropyReal mix' σ_dephased := by
    rw [hmix']
    exact conditionalMinEntropyReal_dephasedMixtureCQ_ge_of_components S comp' weight
      hweight_nonneg hweight_le_one hweight_sum σ_dephased σ_cond hσ_dephased_pin k
      hcomp_feas hcomp_ge (by rw [← hmix']; exact hpos)
  have hmain : k ≤ smoothMinEntropyReal ε mix σ_dephased :=
    smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove ε mix σ_dephased k mix' hbdd hpd_mix
      hk_le_mix
  rw [hk] at hmain
  linarith

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
