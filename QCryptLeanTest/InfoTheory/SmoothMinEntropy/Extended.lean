import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.ClassicalFlagConditioning
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.WeightedSubMixtureFloor
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.OfBlocks

/-!
# Extended smooth min-entropy boundary regressions

Explicit zero, threshold, singular-reference and negative-entropy examples for the
positive-part extension of Tomamichel 2016, Definitions 6.2 and 6.4–6.5.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace QCryptLeanTest.SmoothMinEntropy

open InfoTheory.SmoothMinEntropy

/-- A diagonal two-dimensional subnormalized state (Tomamichel 2016, §2.3.2). -/
private def diagonalState (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    SubDensityOp 2 :=
  SubDensityOp.ofPosSemidef
    (Matrix.PosSemidef.diagonal (d := ![(a : ℂ), (b : ℂ)]) (by
      intro i
      fin_cases i
      · change (0 : ℂ) ≤ (a : ℂ)
        exact_mod_cast ha
      · change (0 : ℂ) ≤ (b : ℂ)
        exact_mod_cast hb))
    (by simpa [Matrix.trace, Fin.sum_univ_two] using hab)

/-- A single classical outcome carrying a subnormalized state
(Tomamichel 2016, §2.4.4). -/
private def oneOutcome {n : ℕ} (σ : SubDensityOp n) : CQState Unit n where
  stateMap _ := σ
  weight_le_one := by
    simp only [Fintype.sum_unique]
    exact σ.trace_le_one

/-- The diagonal state's weight is the sum of its entries (Tomamichel 2016, §2.3.2). -/
private lemma diagonalState_trace (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) : (diagonalState a b ha hb hab).trace = a + b := by
  simp [SubDensityOp.trace, diagonalState, Matrix.trace, Fin.sum_univ_two]

/-- Zero has infinite fixed and smoothed entropy even against the zero reference
(Tomamichel 2016, Definition 6.2, extended to zero). -/
theorem zero_state_entropy :
    conditionalMinEntropy (zeroCQ (X := Unit) (n := 2)) 0 = ⊤ ∧
      smoothMinEntropy 0 (zeroCQ (X := Unit) (n := 2)) 0 = ⊤ ∧
      smoothMinEntropyOpt 0 (zeroCQ (X := Unit) (n := 2)) = ⊤ := by
  refine ⟨conditionalMinEntropy_zeroCQ _, by simp, ?_⟩
  apply smoothMinEntropyOpt_eq_top_of_weight_le_eps_sq (by norm_num)
  have hzero : (0 : SubDensityOp 2).trace = 0 := by
    change (0 : Op 2).trace.re = 0
    simp
  simp [zeroCQ, hzero]

/-- Every real floor is witnessed by zero without a positive-weight assumption
(Tomamichel 2016, Definitions 6.2 and 6.5). -/
theorem zero_state_all_floors (k : ℝ) (σ : SubDensityOp 2) :
    ENNReal.ofReal k ≤ smoothMinEntropy 0 (zeroCQ (X := Unit)) σ := by
  apply smoothMinEntropy_ge_of_isFeasible _ zeroCQ σ k
  · rw [CQState.purifiedDistance_self_zero]
  · exact isFeasible_zeroCQ σ (Real.rpow_nonneg (by norm_num) _)

/-- Equality at the radius threshold includes zero and gives infinite entropy
(Tomamichel 2016, Definition 6.4, extended to its boundary). -/
theorem exact_weight_threshold :
    smoothMinEntropy (1 / 2)
      (oneOutcome (diagonalState (1 / 4) 0 (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)) = ⊤ := by
  apply smoothMinEntropy_eq_top_of_weight_le_eps_sq (by norm_num)
  norm_num [oneOutcome, diagonalState_trace]

/-- A radius below the same threshold has finite entropy, even at a singular reference
(Tomamichel 2016, Definitions 6.4–6.5). -/
theorem below_weight_threshold :
    smoothMinEntropy (1 / 4)
      (oneOutcome (diagonalState (1 / 4) 0 (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)) ≠ ⊤ := by
  apply smoothMinEntropy_ne_top_of_eps_sq_lt_weight (by norm_num)
  norm_num [oneOutcome, diagonalState_trace]

/-- A normalized rank-one reference cannot dominate a state with mass in its kernel
(Tomamichel 2016, Definition 6.2, support convention). -/
theorem singular_reference_infeasible :
    ¬ hasFeasibleLambda
      (oneOutcome (diagonalState (1 / 2) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)) := by
  rintro ⟨t, ht⟩
  have h := opLe_re_diag_le (ht.2 ()) (1 : Fin 2)
  norm_num [oneOutcome, diagonalState, Matrix.smul_apply] at h

/-- Infeasible singular-reference witnesses have zero positive-part entropy
(Tomamichel 2016, Definition 6.2). -/
theorem singular_reference_entropy_zero :
    conditionalMinEntropy
      (oneOutcome (diagonalState (1 / 2) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)) = 0 :=
  conditionalMinEntropy_eq_zero_of_not_hasFeasibleLambda _ _ singular_reference_infeasible

/-- An infeasible witness lies inside a radius strictly below the zero-state threshold:
`diag(1/2,1/2)` is at distance at most `sqrt(1/2)` from `diag(1,0)`.
This is the support issue in Tomamichel 2016, Definitions 6.2 and 6.4. -/
theorem singular_reference_witness_in_ball :
    CQState.purifiedDistance
      (oneOutcome (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)))
      (oneOutcome (diagonalState (1 / 2) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num))) ≤ Real.sqrt (1 / 2) := by
  let ρ := oneOutcome (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num))
  let τ := oneOutcome (diagonalState (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num))
  have hdom : opLe ρ.toJointDensity.toOp ((2 : ℂ) • τ.toJointDensity.toOp) := by
    apply CQState.toJointDensity_opLe_of_forall ρ τ (by norm_num : (0 : ℝ) ≤ 2)
    intro x
    apply opLe_of_posSemidef_sub
    have hmat : ((2 : ℝ) : ℂ) • (τ.stateMap x).toOp - (ρ.stateMap x).toOp =
        Matrix.diagonal ![(0 : ℂ), 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [ρ, τ, oneOutcome, diagonalState]
    rw [hmat]
    exact Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)
  have htr : ρ.toJointDensity.trace = 1 := by
    rw [CQState.toJointDensity_trace_eq_sum]
    norm_num [ρ, oneOutcome, diagonalState_trace]
  have hF := Quantum.Metrics.trace_div_sqrt_le_fidelity_of_opLe
    ρ.toJointDensity.toPosSemidefOp τ.toJointDensity.toPosSemidefOp (by norm_num) hdom
  change ρ.toJointDensity.trace / Real.sqrt 2 ≤ _ at hF
  rw [htr] at hF
  have hFsq := mul_self_le_mul_self (by positivity : 0 ≤ 1 / Real.sqrt 2) hF
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hinv : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, hsqrt]
    norm_num
  rw [hinv] at hFsq
  change CQState.purifiedDistance ρ τ ≤ _
  unfold CQState.purifiedDistance InfoTheory.SmoothMinEntropy.purifiedDistance
  apply Real.sqrt_le_sqrt
  rw [fidelityGen_eq_fidelity_of_trace_one _ _ htr]
  nlinarith

/-- The singular reference does not make this smoothing supremum spuriously infinite
(Tomamichel 2016, Definitions 6.4–6.5). -/
theorem singular_reference_smooth_finite :
    smoothMinEntropy (Real.sqrt (1 / 2))
      (oneOutcome (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)) ≠ ⊤ := by
  apply smoothMinEntropy_ne_top_of_eps_sq_lt_weight (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num [oneOutcome, diagonalState_trace]

/-- A unit-weight state against one quarter of itself has optimum four
(Tomamichel 2016, Definition 6.2). -/
private lemma negative_entropy_optimum :
    minFeasibleLambda
      (oneOutcome (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState (1 / 4) 0 (by norm_num) (by norm_num) (by norm_num)) = 4 := by
  let ρ := oneOutcome (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num))
  let σ := diagonalState (1 / 4) 0 (by norm_num) (by norm_num) (by norm_num)
  have h4 : isFeasible ρ σ 4 := by
    refine ⟨by norm_num, fun x => ?_⟩
    have hmat : ((4 : ℝ) : ℂ) • σ.toOp = (ρ.stateMap x).toOp := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [ρ, σ, oneOutcome, diagonalState]
    rw [hmat]
    exact opLe_refl _
  apply le_antisymm (minFeasibleLambda_le_of_isFeasible ρ σ h4)
  apply le_csInf ⟨4, h4⟩
  intro t ht
  have h := opLe_re_diag_le (ht.2 ()) (0 : Fin 2)
  norm_num [ρ, σ, oneOutcome, diagonalState, Matrix.smul_apply] at h
  linarith

/-- Negative fixed-reference entropy is clipped: the real value is `−2`, the extended
value and its zero-radius smoothing are zero, and coefficient one is infeasible.
This checks the sign restriction in Tomamichel 2016, Definition 6.2. -/
theorem negative_fixed_reference_entropy :
    let ρ := oneOutcome (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num))
    let σ := diagonalState (1 / 4) 0 (by norm_num) (by norm_num) (by norm_num)
    conditionalMinEntropyReal ρ σ = -2 ∧ conditionalMinEntropy ρ σ = 0 ∧
      smoothMinEntropy 0 ρ σ = 0 ∧ ¬ isFeasible ρ σ 1 := by
  dsimp only
  have hreal : conditionalMinEntropyReal
      (oneOutcome (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState (1 / 4) 0 (by norm_num) (by norm_num) (by norm_num)) = -2 := by
    rw [conditionalMinEntropyReal, negative_entropy_optimum,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
    norm_num
  refine ⟨hreal, ?_, ?_, ?_⟩
  · rw [conditionalMinEntropy, negative_entropy_optimum, ite_eq_left (by norm_num), hreal]
    norm_num
  · rw [smoothMinEntropy_zero_eq, conditionalMinEntropy, negative_entropy_optimum,
      ite_eq_left (by norm_num), hreal]
    norm_num
  · intro h
    have hd := opLe_re_diag_le (h.2 ()) (0 : Fin 2)
    norm_num [oneOutcome, diagonalState, Matrix.smul_apply] at hd

/-- Signed real component floors supply the weighted theorem's feasibility witnesses. -/
example {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (hσ : σ.toOp.PosDef) (k : ℝ) (kz : Z → ℝ)
    (hfloor : ∀ z, kz z < smoothMinEntropyReal ε (comp z) σ)
    (hk : ∑ z, p z * (2 : ℝ) ^ (-(kz z)) ≤ (2 : ℝ) ^ (-k)) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
  apply smoothMinEntropy_subMixture_ge_weighted
    ε hε p hp_nonneg hp_sum_le comp ρ hmix σ k kz _ hk
  intro z
  obtain ⟨τ, hd, hτ⟩ := smoothMinEntropyReal_exists_approx ε hε (comp z) σ (kz z) (hfloor z)
  exact ⟨τ, hd, Real.rpow_nonneg (by norm_num) _,
    stateMap_opLe_pow_neg_of_conditionalMinEntropyReal_le τ σ hσ hτ⟩

/-- Positive extended component floors supply exact witnesses, including equality at the floor. -/
example {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (hσ : σ.toOp.PosDef) (k : ℝ) (kz : Z → ℝ)
    (hkz : ∀ z, 0 < kz z)
    (hfloor : ∀ z, ENNReal.ofReal (kz z) ≤ smoothMinEntropy ε (comp z) σ)
    (hk : ∑ z, p z * (2 : ℝ) ^ (-(kz z)) ≤ (2 : ℝ) ^ (-k)) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
  exact smoothMinEntropy_subMixture_ge_weighted ε hε p hp_nonneg hp_sum_le
    comp ρ hmix σ k kz
    (fun z => smoothMinEntropy_exists_approx_le ε hε (comp z) σ hσ (kz z) (hkz z)
      (hfloor z)) hk

/-- Strict extended floors supply certificates even for singular references. -/
example {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum_le : ∑ z, p z ≤ 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ) (kz : Z → ℝ)
    (hfloor : ∀ z, ENNReal.ofReal (kz z) < smoothMinEntropy ε (comp z) σ)
    (hk : ∑ z, p z * (2 : ℝ) ^ (-(kz z)) ≤ (2 : ℝ) ^ (-k)) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
  apply smoothMinEntropy_subMixture_ge_weighted
    ε hε p hp_nonneg hp_sum_le comp ρ hmix σ k kz _ hk
  intro z
  obtain ⟨τ, hd, _, hτ⟩ :=
    smoothMinEntropy_exists_approx (comp z) σ (ENNReal.ofReal (kz z)) (hfloor z)
  exact ⟨τ, hd, isFeasible_of_ofReal_lt_conditionalMinEntropy τ σ hτ⟩

/-- A scalar subnormalized state. -/
private def scalarState (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : SubDensityOp 1 :=
  SubDensityOp.ofPosSemidef
    (Matrix.PosSemidef.diagonal (d := fun _ : Fin 1 => (a : ℂ)) (by
      intro i
      change (0 : ℂ) ≤ (a : ℂ)
      exact_mod_cast ha))
    (by simpa [Matrix.trace] using ha1)

/-- The scalar optimum is the ratio of the state and reference weights. -/
private lemma scalar_optimum (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) :
    minFeasibleLambda (oneOutcome (scalarState a ha ha1)) (scalarState b hb.le hb1) =
      a / b := by
  let ρ := oneOutcome (scalarState a ha ha1)
  let σ := scalarState b hb.le hb1
  have hfeas : isFeasible ρ σ (a / b) := by
    refine ⟨div_nonneg ha hb.le, fun x => ?_⟩
    have hmat : ((a / b : ℝ) : ℂ) • σ.toOp = (ρ.stateMap x).toOp := by
      ext i j
      fin_cases i
      fin_cases j
      simp [ρ, σ, oneOutcome, scalarState, hb.ne']
    rw [hmat]
    exact opLe_refl _
  apply le_antisymm (minFeasibleLambda_le_of_isFeasible ρ σ hfeas)
  apply le_csInf ⟨a / b, hfeas⟩
  intro t ht
  apply (div_le_iff₀ hb).mpr
  simpa [ρ, σ, oneOutcome, scalarState, Matrix.smul_apply] using
    opLe_re_diag_le (ht.2 ()) (0 : Fin 1)

/-- A component floor of `−3` at weight `1/16` certifies the positive mixture floor `1`.
The component has entropy `−2`, its clipped floor premise fails, and the mixture has entropy `2`. -/
theorem weighted_negative_component_positive_output :
    let comp := oneOutcome (scalarState 1 (by norm_num) (by norm_num))
    let σ := scalarState (1 / 4) (by norm_num) (by norm_num)
    let ρ := oneOutcome (scalarState (1 / 16) (by norm_num) (by norm_num))
    (-3 : ℝ) < smoothMinEntropyReal 0 comp σ ∧
      ¬ ENNReal.ofReal (-3) < smoothMinEntropy 0 comp σ ∧
      smoothMinEntropy 0 ρ σ = 2 ∧
      ENNReal.ofReal 1 ≤ smoothMinEntropy 0 ρ σ := by
  dsimp only
  let comp := oneOutcome (scalarState 1 (by norm_num) (by norm_num))
  let σ := scalarState (1 / 4) (by norm_num) (by norm_num)
  let ρ := oneOutcome (scalarState (1 / 16) (by norm_num) (by norm_num))
  change (-3 : ℝ) < smoothMinEntropyReal 0 comp σ ∧
    ¬ ENNReal.ofReal (-3) < smoothMinEntropy 0 comp σ ∧
    smoothMinEntropy 0 ρ σ = 2 ∧ ENNReal.ofReal 1 ≤ smoothMinEntropy 0 ρ σ
  have hc : minFeasibleLambda comp σ = 4 := by
    convert scalar_optimum 1 (1 / 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) using 1
    norm_num
  have hρ : minFeasibleLambda ρ σ = 1 / 4 := by
    convert scalar_optimum (1 / 16) (1 / 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) using 1
    norm_num
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hc_real : conditionalMinEntropyReal comp σ = -2 := by
    rw [conditionalMinEntropyReal, hc, hlog]
    field_simp
  have hρ_real : conditionalMinEntropyReal ρ σ = 2 := by
    rw [conditionalMinEntropyReal, hρ, Real.log_div (by norm_num) (by norm_num),
      Real.log_one, hlog]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [smoothMinEntropyReal_zero_eq, hc_real]
    norm_num
  · rw [smoothMinEntropy_zero_eq, conditionalMinEntropy, hc,
      ite_eq_left (by norm_num), hc_real]
    norm_num [ENNReal.ofReal_of_nonpos]
  · rw [smoothMinEntropy_zero_eq, conditionalMinEntropy, hρ,
      ite_eq_left (by norm_num), hρ_real]
    norm_num
  · refine smoothMinEntropy_subMixture_ge_weighted 0 (by norm_num)
      (fun _ : Unit => 1 / 16) (by intro z; norm_num) (by norm_num)
      (fun _ => comp) ρ ?_ σ 1 (fun _ => -3) ?_ ?_
    · intro x
      ext i j
      fin_cases i
      fin_cases j
      norm_num [comp, ρ, oneOutcome, scalarState]
    · intro z
      refine ⟨comp, ?_, ?_⟩
      · rw [CQState.purifiedDistance_self_zero]
      · norm_num [Real.rpow_natCast]
        refine ⟨by norm_num, fun x => ?_⟩
        apply opLe_of_posSemidef_sub
        have hmat : ((8 : ℝ) : ℂ) • σ.toOp - (comp.stateMap x).toOp = 1 := by
          ext i j
          fin_cases i
          fin_cases j
          norm_num [comp, σ, oneOutcome, scalarState]
        rw [hmat]
        exact Matrix.PosSemidef.one
    · norm_num [Real.rpow_natCast, Real.rpow_neg_one]


/-- The signed weighted theorem retains a negative mixture floor: a component of entropy `-2`
at weight `1/2` gives a mixture of entropy `-1` and the usable signed floor `-2`. -/
theorem weighted_negative_output :
    let σ := scalarState (1 / 4) (by norm_num) (by norm_num)
    let ρ := oneOutcome (scalarState (1 / 2) (by norm_num) (by norm_num))
    smoothMinEntropyReal 0 ρ σ = -1 ∧ (-2 : ℝ) ≤ smoothMinEntropyReal 0 ρ σ := by
  dsimp only
  let comp := oneOutcome (scalarState 1 (by norm_num) (by norm_num))
  let σ := scalarState (1 / 4) (by norm_num) (by norm_num)
  let ρ := oneOutcome (scalarState (1 / 2) (by norm_num) (by norm_num))
  change smoothMinEntropyReal 0 ρ σ = -1 ∧ (-2 : ℝ) ≤ smoothMinEntropyReal 0 ρ σ
  have hσ : σ.toOp.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    norm_num
  have hc : minFeasibleLambda comp σ = 4 := by
    convert scalar_optimum 1 (1 / 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) using 1
    norm_num
  have hρ : minFeasibleLambda ρ σ = 2 := by
    convert scalar_optimum (1 / 2) (1 / 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) using 1
    norm_num
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hc_real : conditionalMinEntropyReal comp σ = -2 := by
    rw [conditionalMinEntropyReal, hc, hlog]
    field_simp
  constructor
  · rw [smoothMinEntropyReal_zero_eq, conditionalMinEntropyReal, hρ]
    field_simp
  · refine smoothMinEntropyReal_subMixture_ge_weighted 0 (by norm_num)
      (fun _ : Unit => 1 / 2) (by intro z; norm_num) (by norm_num)
      (fun _ => comp) ρ ?_ σ hσ ?_ ?_ (-2) (fun _ => -3) ?_ ?_
    · intro x
      ext i j
      fin_cases i
      fin_cases j
      norm_num [comp, ρ, oneOutcome, scalarState]
    · norm_num [ρ, oneOutcome, scalarState, SubDensityOp.trace, Matrix.trace]
    · apply smoothMinEntropyReal_bddAbove_of_eps_sq_lt_weight 0 (by norm_num)
      norm_num [ρ, oneOutcome, scalarState, SubDensityOp.trace, Matrix.trace]
    · intro z
      rw [smoothMinEntropyReal_zero_eq, hc_real]
      norm_num
    · norm_num [Real.rpow_natCast]

/-- A flag factor of four preserves the signed gain of two bits: at radius zero the scalar
states `1/2` and `1/8` have entropies one and three relative to the unit reference. -/
theorem classical_flag_positive_gain :
    let ρfull := oneOutcome (scalarState (1 / 2) (by norm_num) (by norm_num))
    let ρacc := oneOutcome (scalarState (1 / 8) (by norm_num) (by norm_num))
    let σ := scalarState 1 (by norm_num) (by norm_num)
    smoothMinEntropyReal 0 ρfull σ = 1 ∧ smoothMinEntropyReal 0 ρacc σ = 3 ∧
      smoothMinEntropyReal 0 ρfull σ + 2 ≤ smoothMinEntropyReal 0 ρacc σ := by
  dsimp only
  let ρfull := oneOutcome (scalarState (1 / 2) (by norm_num) (by norm_num))
  let ρacc := oneOutcome (scalarState (1 / 8) (by norm_num) (by norm_num))
  let σ := scalarState 1 (by norm_num) (by norm_num)
  change smoothMinEntropyReal 0 ρfull σ = 1 ∧ smoothMinEntropyReal 0 ρacc σ = 3 ∧
    smoothMinEntropyReal 0 ρfull σ + 2 ≤ smoothMinEntropyReal 0 ρacc σ
  have hσ : σ.toOp.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    norm_num
  have hfull : minFeasibleLambda ρfull σ = 1 / 2 := by
    convert scalar_optimum (1 / 2) 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) using 1
    norm_num
  have hacc : minFeasibleLambda ρacc σ = 1 / 8 := by
    convert scalar_optimum (1 / 8) 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) using 1
    norm_num
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [smoothMinEntropyReal_zero_eq, conditionalMinEntropyReal, hfull,
      Real.log_div (by norm_num) (by norm_num), Real.log_one]
    field_simp
    ring
  · rw [smoothMinEntropyReal_zero_eq, conditionalMinEntropyReal, hacc,
      Real.log_div (by norm_num) (by norm_num), Real.log_one, hlog8]
    field_simp
    ring
  · have hgain := smoothMinEntropyReal_classicalFlag_conditioning_ge_of_ballLift
      0 (by norm_num) ρfull ρacc σ (p_acc := 4) (by norm_num)
      (smoothMinEntropyReal_bddAbove_of_eps_sq_lt_weight 0 (by norm_num) ρacc σ
        (by norm_num [ρacc, oneOutcome, scalarState, SubDensityOp.trace, Matrix.trace]))
      (by
        intro τ hd
        have hzero : purifiedDistance ρfull.toJointDensity τ.toJointDensity = 0 :=
          le_antisymm hd (purifiedDistance_nonneg _ _)
        have hstates := CQState.toJointDensity_injective
          ((purifiedDistance_eq_zero_iff _ _).mp hzero)
        refine ⟨ρacc, ?_, ?_, hasFeasibleLambda_of_posDef τ σ hσ, ?_⟩
        · rw [CQState.purifiedDistance_self_zero]
        · intro x
          have hmat : (4 : ℂ) • (ρacc.stateMap x).toOp = (ρfull.stateMap x).toOp := by
            ext i j
            fin_cases i
            fin_cases j
            norm_num [ρfull, ρacc, oneOutcome, scalarState]
          change opLe ((4 : ℂ) • (ρacc.stateMap x).toOp) (τ.stateMap x).toOp
          rw [← hstates, hmat]
          exact opLe_refl _
        · rw [hacc]
          norm_num)
    have hlog4 : Real.log (4 : ℝ) / Real.log 2 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      field_simp
      ring
    rwa [hlog4] at hgain

end QCryptLeanTest.SmoothMinEntropy

end -- noncomputable section
