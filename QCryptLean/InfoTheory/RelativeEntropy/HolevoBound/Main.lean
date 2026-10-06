import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.Concavity
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.NaimarkDilation

/-!
# Holevo Bound — accessible information bound, entropy upper bound, Eve's information

The Holevo bound theorem: for any POVM measurement on an ensemble of quantum states,
the classical mutual information I(X:Y) is bounded by the Holevo χ quantity, which is
itself bounded by the entropy of the average state S(ρ_avg).

## Main statements
- `holevo_bound`: I(X:Y) ≤ χ
- `holevoChi_le_entropy`: χ ≤ S(ρ_avg)
- `eve_info_bounded_by_entropy`: I_Eve ≤ S(ρ)
- `vonNeumannEntropy_concave_unitary_average`: S(ρ) ≤ S(Σ wᵢ UᵢρUᵢ†)
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

/-- Express classical mutual information as weighted sum of KL divergences.

    I(X:Y) = Σᵢ pᵢ D_KL(p(·|X=i) || p(·))

    where p(·|X=i) is the measurement distribution for state i,
    and p(·) is the marginal (measurement on average state).

    This is a classical information-theoretic identity that holds because:
    I(X:Y) = D_KL(p(X,Y) || p(X)p(Y))
           = Σₓ,ᵧ p(x,y) log(p(y|x)/p(y))
           = Σₓ pₓ Σᵧ p(y|x) log(p(y|x)/p(y))
           = Σₓ pₓ D_KL(p(·|x) || p(·)) -/
lemma mutualInfo_eq_weighted_kl {n : ℕ} [NeZero n] {k m : ℕ} [NeZero k] [NeZero m]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    (M : InfoTheory.Measurement.POVM n m) :
    InfoTheory.Measurement.mutualInfo probs states M =
    ∑ i, probs i * measurementKLDivReal M (states i)
      (InfoTheory.Measurement.DensityOp.fromEnsemble
        probs states hprobs_nonneg hprobs_sum) := by
  -- Bridge: marginalProbY y = M.prob ρ_avg y
  let ρ_avg := InfoTheory.Measurement.DensityOp.fromEnsemble
    probs states hprobs_nonneg hprobs_sum
  have h_marginal : ∀ y,
      InfoTheory.Measurement.marginalProbY probs states M y =
      M.prob ρ_avg y :=
    InfoTheory.Measurement.marginalProbY_eq_average_measurement
      probs states hprobs_nonneg hprobs_sum M
  -- Step 1: I(X:Y) = D_KL(p(x,y) ‖ p(x)⊗p(y)) in flat form
  have h_kl := InfoTheory.Measurement.mutual_info_eq_kl_divergence
    probs states M hprobs_nonneg hprobs_sum
  unfold InfoTheory.Measurement.mutualInfo; rw [h_kl]
  -- Step 2: Convert flat-indexed sum to double-indexed sum
  rw [show ∑ i, (if InfoTheory.Measurement.flatJoint probs states M i = 0 then 0
        else InfoTheory.Measurement.flatJoint probs states M i *
        Real.log (InfoTheory.Measurement.flatJoint probs states M i /
                  InfoTheory.Measurement.flatProduct probs states M i)) =
      ∑ x, ∑ y, (if InfoTheory.Measurement.jointProb probs states M x y = 0 then 0
        else InfoTheory.Measurement.jointProb probs states M x y *
        Real.log (InfoTheory.Measurement.jointProb probs states M x y /
                  (probs x * InfoTheory.Measurement.marginalProbY probs states M y))) from by
    rw [← InfoTheory.Measurement.flat_sum_eq_double_sum]; rfl]
  -- Step 3: Simplify term by term using jointProb = probs · M.prob
  --         and marginalProbY = M.prob ρ_avg
  apply Finset.sum_congr rfl; intro x _
  by_cases hpx : probs x = 0
  · -- probs(x) = 0: jointProb = 0, both sides vanish
    have hjoint_zero : ∀ y, InfoTheory.Measurement.jointProb probs states M x y = 0 :=
      fun y => by simp [InfoTheory.Measurement.jointProb, hpx]
    have h_each_zero : ∀ y ∈ Finset.univ,
        (if InfoTheory.Measurement.jointProb probs states M x y = 0 then (0 : ℝ)
         else InfoTheory.Measurement.jointProb probs states M x y *
           Real.log (InfoTheory.Measurement.jointProb probs states M x y /
                     (probs x * InfoTheory.Measurement.marginalProbY probs states M y))) = 0 :=
      fun y _ => by simp [hjoint_zero y]
    rw [Finset.sum_eq_zero h_each_zero, hpx, zero_mul]
  · -- probs(x) > 0: cancel probs(x) in log argument, factor out
    have hpx_pos : 0 < probs x := lt_of_le_of_ne (hprobs_nonneg x) (Ne.symm hpx)
    -- Transform each summand
    have h_term : ∀ y,
        (if InfoTheory.Measurement.jointProb probs states M x y = 0 then (0 : ℝ)
         else InfoTheory.Measurement.jointProb probs states M x y *
           Real.log (InfoTheory.Measurement.jointProb probs states M x y /
                     (probs x * InfoTheory.Measurement.marginalProbY probs states M y))) =
        probs x * (if M.prob (states x) y = 0 then 0
                   else M.prob (states x) y *
                     Real.log (M.prob (states x) y / M.prob ρ_avg y)) := by
      intro y
      by_cases hqy : M.prob (states x) y = 0
      · have : InfoTheory.Measurement.jointProb probs states M x y = 0 := by
          simp [InfoTheory.Measurement.jointProb, hqy]
        simp [this, hqy]
      · have hjoint_ne : InfoTheory.Measurement.jointProb probs states M x y ≠ 0 := by
          simp only [InfoTheory.Measurement.jointProb]; exact mul_ne_zero hpx hqy
        simp only [hjoint_ne, hqy, ↓reduceIte]
        rw [show InfoTheory.Measurement.jointProb probs states M x y =
              probs x * M.prob (states x) y from rfl,
            h_marginal y, mul_div_mul_left _ _ (ne_of_gt hpx_pos)]
        ring
    simp_rw [h_term, ← Finset.mul_sum]; congr 1

/-- Support containment for ensemble: if pᵢ > 0 and σ = Σⱼ pⱼ ρⱼ,
    then supp(ρᵢ) ⊆ supp(σ) in σ's eigenbasis.

    When eigenvalue of σ is 0, σ has zero weight in that direction.
    Since σ = Σⱼ pⱼ ρⱼ with pⱼ ≥ 0 and ρⱼ positive semidefinite,
    each pⱼ ⟨v|ρⱼ|v⟩ must be 0, so ⟨v|ρᵢ|v⟩ = 0 when pᵢ > 0. -/
lemma ensemble_support_containment {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    (i : Fin k) (hpi : 0 < probs i) :
    let σ := InfoTheory.Measurement.DensityOp.fromEnsemble
      probs states hprobs_nonneg hprobs_sum
    ∀ j, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j = 0 →
      diagonalOfRhoInSigmaBasis (states i) σ j = 0 := by
  intro σ j hj
  -- Step 1: By linearity, Σ pₖ * d(states k, σ, j) = d(σ, σ, j)
  have h_lin := diagonalOfRhoInSigmaBasis_linear
    probs states hprobs_nonneg hprobs_sum σ j
  -- Step 2: d(σ, σ, j) = eigenvaluesOf σ j = 0
  have h_self : diagonalOfRhoInSigmaBasis σ σ j = 0 := by
    rw [diagonalOfRhoInSigmaBasis_self σ j, hj]
  -- Step 3: Sum of nonneg terms = 0, so each term is 0
  have h_sum_zero : ∑ l, probs l *
      diagonalOfRhoInSigmaBasis (states l) σ j = 0 := by
    rw [h_lin, h_self]
  have h_nonneg : ∀ l, 0 ≤ probs l *
      diagonalOfRhoInSigmaBasis (states l) σ j :=
    fun l => mul_nonneg (hprobs_nonneg l)
      (diagonalOfRhoInSigmaBasis_nonneg (states l) σ j)
  have h_each_zero := Finset.sum_eq_zero_iff_of_nonneg
    (fun l _ => h_nonneg l) |>.mp h_sum_zero i (Finset.mem_univ i)
  -- Step 4: pᵢ * d(states i, σ, j) = 0 with pᵢ > 0
  exact (mul_eq_zero.mp h_each_zero).resolve_left (ne_of_gt hpi)

/-- **Holevo Bound via Data Processing**: I(X:Y) ≤ χ.

    This is the central result connecting classical and quantum information.

    **Proof structure**:
    1. χ = Σᵢ pᵢ S(ρᵢ || ρ_avg)           [by concavity_identity]
    2. I(X:Y) = Σᵢ pᵢ D_KL(prob(ρᵢ)||prob(ρ_avg))  [classical identity]
    3. D_KL(prob(ρᵢ)||prob(ρ_avg)) ≤ S(ρᵢ || ρ_avg)  [measurement_monotonicity]
    4. Therefore I(X:Y) ≤ χ -/
theorem holevo_bound_via_data_processing {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    {m : ℕ} [NeZero m] (M : InfoTheory.Measurement.POVM n m) :
    InfoTheory.Measurement.mutualInfo probs states M ≤
    InfoTheory.Measurement.holevoChi probs states hprobs_nonneg hprobs_sum := by
  -- Step 1: Use concavity identity
  have h_chi := concavity_identity probs states hprobs_nonneg hprobs_sum
  let ρ_avg := InfoTheory.Measurement.DensityOp.fromEnsemble probs states hprobs_nonneg hprobs_sum
  -- Step 2: Express mutual info as weighted KL sum
  have h_mi := mutualInfo_eq_weighted_kl probs states hprobs_nonneg hprobs_sum M
  -- Step 3: Apply measurement monotonicity to each term (only when probs i > 0)
  have h_mono : ∀ i, 0 < probs i →
      measurementKLDivReal M (states i) ρ_avg ≤ relativeEntropyReal (states i) ρ_avg :=
    fun i hpi => measurement_monotonicity_with_support M (states i) ρ_avg
      (ensemble_support_containment probs states hprobs_nonneg hprobs_sum i hpi)
  -- Step 4: Combine via weighted sum inequality
  rw [h_mi]
  unfold InfoTheory.Measurement.holevoChi
  rw [h_chi]
  apply Finset.sum_le_sum
  intro i _
  by_cases hpi : probs i = 0
  · simp [hpi]
  · have hpi_pos : 0 < probs i := lt_of_le_of_ne (hprobs_nonneg i) (Ne.symm hpi)
    apply mul_le_mul_of_nonneg_left (h_mono i hpi_pos) (hprobs_nonneg i)

/-!
### Concavity under unitary averaging

Combines unitary invariance of entropy with general concavity
(via Klein's inequality) to show S(ρ) ≤ S(Σ wᵢ Uᵢ ρ Uᵢ†).
-/

/-- Two density operators with the same matrix have the same entropy. -/
lemma vonNeumannEntropy_toOp_eq {n : ℕ} [NeZero n]
    (ρ σ : Quantum.Operators.DensityOp n) (h : ρ.toOp = σ.toOp) :
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ =
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy σ := by
  have h_spec_σ := InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec σ
  have h_spec_ρ : InfoTheory.VonNeumannEntropy.IsEigenvalueSpectrum ρ
      (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ) := by
    obtain ⟨h1, h2, h3, U, hUU, hUU', hspec⟩ := h_spec_σ
    exact ⟨h1, h2, h3, U, hUU, hUU', by rw [h]; exact hspec⟩
  unfold InfoTheory.VonNeumannEntropy.vonNeumannEntropy
  exact InfoTheory.VonNeumannEntropy.eigenvalueSpectrum_entropy_eq ρ
    (InfoTheory.VonNeumannEntropy.eigenvaluesOf ρ)
    (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ)
    (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec ρ) h_spec_ρ

/-- Concavity of von Neumann entropy under unitary averaging.

    S(ρ) ≤ S(Σᵢ wᵢ Uᵢ ρ Uᵢ†) when wᵢ ≥ 0 and Σ wᵢ = 1.

    Combines unitary invariance S(UρU†) = S(ρ) with concavity of S. -/
theorem vonNeumannEntropy_concave_unitary_average {n : ℕ} [NeZero n]
    {k : ℕ} (ρ : Quantum.Operators.DensityOp n)
    (weights : Fin k → ℝ) (unitaries : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hw_nonneg : ∀ i, 0 ≤ weights i)
    (hw_sum : ∑ i, weights i = 1)
    (hU_unitary : ∀ i, (unitaries i) * (unitaries i).conjTranspose = 1)
    (ρ_mix : Quantum.Operators.DensityOp n)
    (hρ_mix : ρ_mix.toOp =
      ∑ i, weights i • ((unitaries i) * ρ.toOp *
        (unitaries i).conjTranspose)) :
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ ≤
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ_mix := by
  -- Handle k = 0: hw_sum gives 0 = 1, contradiction
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hw_sum; norm_num at hw_sum
  · haveI : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk⟩
    -- Construct UnitaryOp for each unitary matrix
    have hU_left : ∀ i, (unitaries i).conjTranspose *
        (unitaries i) = 1 :=
      fun i => mul_eq_one_comm.mpr (hU_unitary i)
    let U_op : Fin k → Quantum.Operators.UnitaryOp n := fun i =>
      ⟨unitaries i, hU_left i, hU_unitary i⟩
    let states : Fin k → Quantum.Operators.DensityOp n := fun i =>
      (U_op i).evolve ρ
    -- S(U_i ρ U_i†) = S(ρ) by unitary invariance
    have h_inv : ∀ i,
        InfoTheory.VonNeumannEntropy.vonNeumannEntropy (states i) =
        InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ :=
      fun i =>
        InfoTheory.VonNeumannEntropy.vonNeumannEntropy_unitary_evolve
          (U_op i) ρ
    -- Bridge: ρ_mix and fromEnsemble have the same toOp
    set ρ_ens := InfoTheory.Measurement.DensityOp.fromEnsemble
      weights states hw_nonneg hw_sum with hρ_ens_def
    have h_toOp : ρ_mix.toOp = ρ_ens.toOp := by
      rw [hρ_mix, hρ_ens_def]
      simp only [InfoTheory.Measurement.DensityOp.fromEnsemble,
        InfoTheory.Measurement.ensembleAverage]; congr 1
    -- Apply concavity from this file
    have h_concave :=
      vonNeumannEntropy_concave weights states hw_nonneg hw_sum
    calc InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ
        = ∑ i, weights i * InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ := by
            rw [← Finset.sum_mul, hw_sum, one_mul]
      _ = ∑ i, weights i *
            InfoTheory.VonNeumannEntropy.vonNeumannEntropy (states i) := by
            congr 1; ext i; rw [h_inv i]
      _ ≤ InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ_ens := h_concave
      _ = InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ_mix :=
            (vonNeumannEntropy_toOp_eq ρ_mix ρ_ens h_toOp).symm

end InfoTheory.RelativeEntropy

/-!
## Holevo Bound (Public API)

The Holevo bound and related theorems are placed here (rather than in Measurement.lean)
because the proof requires `InfoTheory.RelativeEntropy.holevo_bound_via_data_processing`, and
RelativeEntropy imports Measurement (not vice versa).
-/

namespace InfoTheory.Measurement

open InfoTheory.RelativeEntropy

/-- Holevo χ is bounded by the entropy of the average state.

    χ = S(ρ_avg) - Σᵢ pᵢS(ρᵢ) ≤ S(ρ_avg)

    This follows because Σᵢ pᵢS(ρᵢ) ≥ 0 (weighted sum of non-negative entropies). -/
theorem holevoChi_le_entropy {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1) :
    holevoChi probs states hprobs_nonneg hprobs_sum ≤
      InfoTheory.VonNeumannEntropy.vonNeumannEntropy
        (DensityOp.fromEnsemble probs states hprobs_nonneg hprobs_sum) := by
  unfold holevoChi
  have h_sum_nonneg : 0 ≤ ∑ i, probs i *
      InfoTheory.VonNeumannEntropy.vonNeumannEntropy (states i) := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hprobs_nonneg i)
    exact InfoTheory.VonNeumannEntropy.vonNeumannEntropy_nonneg (states i)
  linarith

/-- Holevo bound: accessible information ≤ χ.

    For any measurement performed on the ensemble, the mutual information
    between the classical input X and measurement outcome Y is bounded by χ. -/
theorem holevo_bound {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    {m : ℕ} (M : POVM n m) :
    mutualInfo probs states M ≤ holevoChi probs states hprobs_nonneg hprobs_sum := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- m = 0: no measurement outcomes, mutualInfo = 0
    subst hm
    unfold mutualInfo outputEntropy conditionalEntropy
    simp only [Math.ClassicalEntropy.shannonEntropy, marginalProbY, condProbYGivenX,
               Finset.univ_eq_empty, Finset.sum_empty, mul_zero, Finset.sum_const_zero, sub_self]
    exact holevoChi_nonneg probs states hprobs_nonneg hprobs_sum
  · -- m > 0: use data processing inequality
    have : NeZero m := ⟨Nat.ne_of_gt hm⟩
    exact holevo_bound_via_data_processing probs states hprobs_nonneg hprobs_sum M

/-- Eve's information about key is bounded by entropy of her state. -/
theorem eve_info_bounded_by_entropy {n : ℕ} [NeZero n]
    (ρ_eve : DensityOp n) {m : ℕ} (M : POVM n m)
    {k : ℕ} [NeZero k] (key_probs : Fin k → ℝ) (key_states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ key_probs i) (hprobs_sum : ∑ i, key_probs i = 1)
    (h_eve_is_avg :
      ρ_eve = DensityOp.fromEnsemble key_probs key_states hprobs_nonneg hprobs_sum) :
    mutualInfo key_probs key_states M ≤ InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ_eve := by
  calc mutualInfo key_probs key_states M
      ≤ holevoChi key_probs key_states hprobs_nonneg hprobs_sum :=
        holevo_bound key_probs key_states hprobs_nonneg hprobs_sum M
    _ ≤ InfoTheory.VonNeumannEntropy.vonNeumannEntropy
        (DensityOp.fromEnsemble key_probs key_states hprobs_nonneg hprobs_sum) :=
        holevoChi_le_entropy key_probs key_states hprobs_nonneg hprobs_sum
    _ = InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ_eve := by rw [← h_eve_is_avg]

end InfoTheory.Measurement

end
