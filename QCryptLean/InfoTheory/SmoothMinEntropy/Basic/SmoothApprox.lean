import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth


/-!
# Signed smooth min-entropy approximation

Real entropy floors from nearby states and trace-gap bounds.
-/

open Quantum.Operators MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy


/-- A nearby state gives its signed conditional entropy floor to a normalized center at radius
less than one. -/
theorem smoothMinEntropyReal_ge_of_hmin_approx
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε_lt_one : ε < 1)
    (ρ : CQState X n)
    (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : SubDensityOp n)
    (k : ℝ)
    (ρ' : CQState X n)
    (hd : CQState.purifiedDistance ρ ρ' ≤ ε)
    (hk : k ≤ conditionalMinEntropyReal ρ' σ) :
    k ≤ smoothMinEntropyReal ε ρ σ := by
  unfold smoothMinEntropyReal
  apply le_trans hk
  apply le_csSup_of_le (smoothMinEntropyReal_bddAbove ε hε_lt_one ρ hρ_norm σ)
  · exact ⟨ρ', rfl, hd⟩
  · exact le_refl _

/-- A good branch within distance `sqrt (2 * ε)` gives its signed entropy floor to the
normalized center at that radius. -/
theorem smoothMinEntropyReal_ge_of_goodBranch_approx
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (_hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (ρ : CQState X n)
    (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : SubDensityOp n)
    (k : ℝ)
    (ρ_good : CQState X n)
    (hd : CQState.purifiedDistance ρ ρ_good ≤ Real.sqrt (2 * ε))
    (hk : k ≤ conditionalMinEntropyReal ρ_good σ) :
    k ≤ smoothMinEntropyReal (Real.sqrt (2 * ε)) ρ σ := by
  exact smoothMinEntropyReal_ge_of_hmin_approx
    (Real.sqrt (2 * ε))
    (by rw [Real.sqrt_lt' zero_lt_one]; nlinarith)
    ρ hρ_norm σ k ρ_good hd hk

/-- A dominated good branch with trace deficit at most `ε` gives its signed floor to the
normalized center at radius `sqrt (2 * ε)`. -/
theorem smoothMinEntropyReal_ge_of_goodBranch_traceDeficit
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt_half : ε < 1 / 2)
    (ρ_mix : CQState X n)
    (hρ_norm : ∑ x : X, (ρ_mix.stateMap x).trace = 1)
    (σ_ref : SubDensityOp n)
    (k : ℝ)
    (ρ_good : CQState X n)
    (hρ_good_le_mix :
      ∀ x : X, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp)
    (htrace_deficit :
      1 - (∑ x : X, (ρ_good.stateMap x).trace) ≤ ε)
    (hk : k ≤ conditionalMinEntropyReal ρ_good σ_ref) :
    k ≤ smoothMinEntropyReal (Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  exact smoothMinEntropyReal_ge_of_goodBranch_approx
    ε hε_nonneg hε_lt_half ρ_mix hρ_norm σ_ref k ρ_good
    (CQState.purifiedDistance_le_sqrt_two_mul_epsilon_of_forall_stateMap_opLe
      ρ_mix ρ_good hρ_norm hε_nonneg hρ_good_le_mix htrace_deficit)
    hk

/-- A dominated good branch with trace gap at most `ε` gives its signed floor to a subnormalized
center at radius `sqrt (2 * ε)`. -/
theorem smoothMinEntropyReal_ge_of_goodBranch_traceGap
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (ρ_mix : CQState X n)
    (h_subNorm : 2 * Real.sqrt (2 * ε) < ∑ x : X, (ρ_mix.stateMap x).trace)
    (σ_ref : SubDensityOp n)
    (k : ℝ)
    (ρ_good : CQState X n)
    (hρ_good_le_mix :
      ∀ x : X, opLe (ρ_good.stateMap x).toOp (ρ_mix.stateMap x).toOp)
    (htrace_gap :
      (∑ x : X, (ρ_mix.stateMap x).trace) -
          (∑ x : X, (ρ_good.stateMap x).trace) ≤ ε)
    (hk : k ≤ conditionalMinEntropyReal ρ_good σ_ref) :
    k ≤ smoothMinEntropyReal (Real.sqrt (2 * ε)) ρ_mix σ_ref := by
  let η : ℝ := (∑ x : X, (ρ_mix.stateMap x).trace) - 2 * Real.sqrt (2 * ε)
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hρ_lower :
      η + 2 * Real.sqrt (2 * ε) ≤ ∑ x : X, (ρ_mix.stateMap x).trace := by
    dsimp [η]
    linarith
  have hbdd : BddAbove
      (setOf (isInSmoothedSetReal (Real.sqrt (2 * ε)) ρ_mix σ_ref)) :=
    (fun ε η hη ρ hρ σ =>
      smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη ρ σ
        (fun _ hd => CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ hd))
      (Real.sqrt (2 * ε)) η hη_pos ρ_mix hρ_lower σ_ref
  exact smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove
    (Real.sqrt (2 * ε)) ρ_mix σ_ref k ρ_good hbdd
    (CQState.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_forall_stateMap_opLe
      ρ_mix ρ_good hε_nonneg hρ_good_le_mix htrace_gap)
    hk

/-- Moving the center by distance at most `d` preserves signed smooth min-entropy after
enlarging the radius from `ε` to `ε + d` below one. -/
theorem smoothMinEntropyReal_triangle_of_purifiedDistance
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε d : ℝ) (hε : 0 ≤ ε)
    (ρA ρB : CQState X n) (σ : SubDensityOp n)
    (hρA_norm : ∑ x : X, (ρA.stateMap x).trace = 1)
    (hsum_lt_one : ε + d < 1)
    (hdist : CQState.purifiedDistance ρA ρB ≤ d) :
    smoothMinEntropyReal ε ρB σ ≤ smoothMinEntropyReal (ε + d) ρA σ := by
  unfold smoothMinEntropyReal
  refine csSup_le_csSup
    (smoothMinEntropyReal_bddAbove (ε + d) hsum_lt_one ρA hρA_norm σ)
    (smoothedSetReal_nonempty hε ρB σ) ?_
  rintro v ⟨rho2, rfl, hd2⟩
  refine ⟨rho2, rfl, ?_⟩
  calc CQState.purifiedDistance ρA rho2
      ≤ CQState.purifiedDistance ρA ρB + CQState.purifiedDistance ρB rho2 :=
        CQState.purifiedDistance_triangle ρA ρB rho2
    _ ≤ d + ε := add_le_add hdist hd2
    _ = ε + d := by ring

end InfoTheory.SmoothMinEntropy

end
