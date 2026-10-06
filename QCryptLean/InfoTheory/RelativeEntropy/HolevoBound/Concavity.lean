import QCryptLean.InfoTheory.RelativeEntropy.Basic

/-!
# Entropy Concavity — concavity identity, Klein inequality for mixtures

Concavity of von Neumann entropy via the concavity identity and Klein's inequality.
The identity S(ρ) - Σᵢ pᵢS(ρᵢ) = Σᵢ pᵢ S(ρᵢ‖ρ) combined with non-negativity of
relative entropy yields S(Σᵢ pᵢρᵢ) ≥ Σᵢ pᵢS(ρᵢ).

## Main statements
- `concavity_identity`: S(ρ) - Σᵢ pᵢS(ρᵢ) = Σᵢ pᵢ D(ρᵢ‖ρ) (ℝ version)
- `vonNeumannEntropy_concave`: Σᵢ pᵢS(ρᵢ) ≤ S(Σᵢ pᵢρᵢ)
- `holevoChi_nonneg`: χ ≥ 0
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-- Linearity of diagonal extraction: the diagonal of a convex combination equals
    the convex combination of diagonals. -/
lemma diagonalOfRhoInSigmaBasis_linear {n : ℕ} {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    (σ : DensityOp n) (j : Fin n) :
    ∑ i, probs i * diagonalOfRhoInSigmaBasis (states i) σ j =
    diagonalOfRhoInSigmaBasis
      (InfoTheory.Measurement.DensityOp.fromEnsemble
        probs states hprobs_nonneg hprobs_sum) σ j := by
  unfold diagonalOfRhoInSigmaBasis
  -- Goal: Σᵢ pᵢ * ((V * ρᵢ * V†) j j).re = ((V * (Σᵢ pᵢρᵢ) * V†) j j).re
  set V := eigenbasisOf σ with hV
  -- The ensemble operator is Σᵢ pᵢρᵢ
  have h_ensemble :
      (InfoTheory.Measurement.DensityOp.fromEnsemble probs states hprobs_nonneg hprobs_sum).toOp =
      ∑ i, (probs i : ℂ) • (states i).toOp := rfl
  rw [h_ensemble]
  -- V * (Σᵢ pᵢρᵢ) * V† = Σᵢ pᵢ * (V * ρᵢ * V†)
  have h_mul_sum : V * (∑ i, (probs i : ℂ) • (states i).toOp) * V† =
      ∑ i, (probs i : ℂ) • (V * (states i).toOp * V†) := by
    rw [Matrix.mul_sum, Finset.sum_mul]
    congr 1
    ext i
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h_mul_sum]
  -- ((Σᵢ pᵢ • Mᵢ) j j).re = (Σᵢ (pᵢ • Mᵢ j j)).re = Σᵢ (pᵢ * Mᵢ j j).re = Σᵢ pᵢ * (Mᵢ j j).re
  -- First, (Σᵢ pᵢ • Mᵢ) j j = Σᵢ (pᵢ • Mᵢ) j j (using Matrix.sum_apply)
  have h_sum_entry : (∑ i, (probs i : ℂ) • (V * (states i).toOp * V†)) j j =
      ∑ i, ((probs i : ℂ) • (V * (states i).toOp * V†)) j j := by
    rw [Matrix.sum_apply]
  rw [h_sum_entry]
  -- (pᵢ • M) j j = pᵢ * M j j
  have h_smul_entry : ∀ i, ((probs i : ℂ) • (V * (states i).toOp * V†)) j j =
      (probs i : ℂ) * (V * (states i).toOp * V†) j j := by
    intro i; rfl
  simp_rw [h_smul_entry]
  -- Take real part of sum
  rw [Complex.re_sum]
  congr 1
  funext i
  -- (pᵢ * z).re = pᵢ * z.re for real pᵢ
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]


/-- Weighted sum of traceProductLogSigma equals negative entropy of the mixture.
    This is the key algebraic identity linking trace and entropy. -/
private lemma sum_probs_traceProductLogSigma {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    (ρ : DensityOp n)
    (hρ : ρ = InfoTheory.Measurement.DensityOp.fromEnsemble probs states hprobs_nonneg hprobs_sum) :
    -(∑ i, probs i * traceProductLogSigma (states i) ρ) = vonNeumannEntropy ρ := by
  subst hρ
  unfold traceProductLogSigma
  -- Swap the order of summation
  set ρ' := InfoTheory.Measurement.DensityOp.fromEnsemble
    probs states hprobs_nonneg hprobs_sum with hρ'
  -- First, distribute the outer multiplication: pᵢ * Σⱼ aᵢⱼ = Σⱼ pᵢ * aᵢⱼ
  have h_distrib : ∑ i, probs i * ∑ j, diagonalOfRhoInSigmaBasis (states i) ρ' j *
      Real.log (eigenvaluesOf ρ' j) =
    ∑ i, ∑ j, probs i * (diagonalOfRhoInSigmaBasis (states i) ρ' j *
      Real.log (eigenvaluesOf ρ' j)) := by
    congr 1
    ext i
    rw [Finset.mul_sum]
  rw [h_distrib]
  -- Now swap the order of summation
  rw [Finset.sum_comm]
  -- Simplify the RHS
  have h_rhs : ∑ j, ∑ i, probs i * (diagonalOfRhoInSigmaBasis (states i) ρ' j *
      Real.log (eigenvaluesOf ρ' j)) =
    ∑ j, Real.log (eigenvaluesOf ρ' j) * ∑ i, probs i *
      diagonalOfRhoInSigmaBasis (states i) ρ' j := by
    congr 1
    ext j
    -- Factor out log(λⱼ) from the sum
    have h_factor : ∑ i, probs i * (diagonalOfRhoInSigmaBasis (states i) ρ' j *
        Real.log (eigenvaluesOf ρ' j)) =
        (∑ i, probs i * diagonalOfRhoInSigmaBasis (states i) ρ' j) *
          Real.log (eigenvaluesOf ρ' j) := by
      rw [Finset.sum_mul]
      congr 1
      ext i
      ring
    rw [h_factor]
    ring
  rw [h_rhs]
  -- Apply linearity of diagonal extraction
  have h_linear : ∀ j, ∑ i, probs i * diagonalOfRhoInSigmaBasis (states i) ρ' j =
      diagonalOfRhoInSigmaBasis ρ' ρ' j :=
    fun j => diagonalOfRhoInSigmaBasis_linear probs states hprobs_nonneg hprobs_sum ρ' j
  simp_rw [h_linear]
  -- Apply self-diagonal identity
  have h_self : ∀ j, diagonalOfRhoInSigmaBasis ρ' ρ' j = eigenvaluesOf ρ' j :=
    fun j => diagonalOfRhoInSigmaBasis_self ρ' j
  simp_rw [h_self]
  -- Now we have Σⱼ log(λⱼ) * λⱼ, and need to show -this = vonNeumannEntropy ρ'
  unfold vonNeumannEntropy Math.ClassicalEntropy.shannonEntropy
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext j
  -- Need: entropyTerm (eigenvaluesOf ρ' j) = -(Real.log (eigenvaluesOf ρ' j) * eigenvaluesOf ρ' j)
  by_cases hj : eigenvaluesOf ρ' j = 0
  · simp only [hj, mul_zero, neg_zero]
    unfold Math.ClassicalEntropy.entropyTerm
    simp only [↓reduceIte]
  · unfold Math.ClassicalEntropy.entropyTerm
    simp only [hj, ↓reduceIte]
    ring

/-- The concavity identity: S(ρ) - Σᵢ pᵢS(ρᵢ) = Σᵢ pᵢ S(ρᵢ || ρ) -/
theorem concavity_identity {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1) :
    let ρ := InfoTheory.Measurement.DensityOp.fromEnsemble probs states
              hprobs_nonneg hprobs_sum
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ -
      ∑ i, probs i * InfoTheory.VonNeumannEntropy.vonNeumannEntropy (states i) =
      ∑ i, probs i * relativeEntropyReal (states i) ρ := by
  intro ρ
  -- Expand relativeEntropyReal on RHS
  unfold relativeEntropyReal
  -- RHS = Σᵢ pᵢ * (-S(ρᵢ) - Tr(ρᵢ log ρ))
  --     = -Σᵢ pᵢ * S(ρᵢ) - Σᵢ pᵢ * Tr(ρᵢ log ρ)
  have h_rhs :
      ∑ i, probs i * (-vonNeumannEntropy (states i) - traceProductLogSigma (states i) ρ) =
      -∑ i, probs i * vonNeumannEntropy (states i) -
       ∑ i, probs i * traceProductLogSigma (states i) ρ := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    congr 1
    ext i
    ring
  rw [h_rhs]
  -- The key identity: -Σᵢ pᵢ * Tr(ρᵢ log ρ) = S(ρ)
  have h_key := sum_probs_traceProductLogSigma probs states hprobs_nonneg hprobs_sum ρ rfl
  linarith

/-- Support condition for mixtures: if diagonal entry of ρᵢ in ρ's basis is positive
    and probability pᵢ is positive, then the corresponding eigenvalue of ρ is positive.

    This is the key lemma that allows using log_sum_inequality for mixture components. -/
private lemma mixture_support_condition {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    (j : Fin n) (i : Fin k)
    (hpi : 0 < probs i)
    (hdiag_pos : 0 < diagonalOfRhoInSigmaBasis (states i)
      (InfoTheory.Measurement.DensityOp.fromEnsemble
        probs states hprobs_nonneg hprobs_sum) j) :
    0 < InfoTheory.VonNeumannEntropy.eigenvaluesOf
      (InfoTheory.Measurement.DensityOp.fromEnsemble
        probs states hprobs_nonneg hprobs_sum) j := by
  set ρ := InfoTheory.Measurement.DensityOp.fromEnsemble
    probs states hprobs_nonneg hprobs_sum with hρ
  -- Use linearity and self-diagonal identity
  have h_self := diagonalOfRhoInSigmaBasis_self ρ j
  have h_linear := diagonalOfRhoInSigmaBasis_linear probs states hprobs_nonneg hprobs_sum ρ j
  -- eigenvaluesOf ρ j = diag(ρ, ρ)_j = Σ_l p_l * diag(ρ_l, ρ)_j
  rw [← h_self, ← h_linear]
  -- The sum contains a positive term: p_i * diag(ρ_i, ρ)_j > 0
  have h_pos_term : 0 < probs i * diagonalOfRhoInSigmaBasis (states i) ρ j :=
    mul_pos hpi hdiag_pos
  -- All terms are non-negative
  have h_nonneg : ∀ l ∈ Finset.univ, 0 ≤ probs l * diagonalOfRhoInSigmaBasis (states l) ρ j := by
    intro l _
    exact mul_nonneg (hprobs_nonneg l) (diagonalOfRhoInSigmaBasis_nonneg (states l) ρ j)
  -- Sum of non-negative terms with at least one positive term is positive
  exact Finset.sum_pos' h_nonneg ⟨i, Finset.mem_univ i, h_pos_term⟩

/-- Classical relative entropy is non-negative for mixture components.
    Uses the weaker support condition that follows from the mixture structure. -/
private theorem classicalRelEntropy_nonneg_mixture {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    (i : Fin k) (hpi : 0 < probs i) :
    let ρ := InfoTheory.Measurement.DensityOp.fromEnsemble probs states hprobs_nonneg hprobs_sum
    0 ≤ classicalRelEntropy (states i) ρ := by
  intro ρ
  unfold classicalRelEntropy
  apply Math.ClassicalEntropy.log_sum_inequality
  · exact diagonalOfRhoInSigmaBasis_nonneg (states i) ρ
  · intro j
    have h := InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec ρ
    exact h.1 j
  · exact diagonalOfRhoInSigmaBasis_sum (states i) ρ
  · have h := InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec ρ
    exact h.2.1
  · intro j hdiag_pos
    exact mixture_support_condition probs states hprobs_nonneg hprobs_sum j i hpi hdiag_pos

/-- Classical relative entropy equals -H(diag) - Tr(ρ log σ) for mixture components.
    Uses the weaker support condition. -/
private theorem classicalRelEntropy_eq_mixture {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    (i : Fin k) (hpi : 0 < probs i) :
    let ρ := InfoTheory.Measurement.DensityOp.fromEnsemble
      probs states hprobs_nonneg hprobs_sum
    classicalRelEntropy (states i) ρ =
      -diagonalEntropy (states i) ρ -
        traceProductLogSigma (states i) ρ := by
  intro ρ
  unfold classicalRelEntropy diagonalEntropy
    Math.ClassicalEntropy.shannonEntropy
    Math.ClassicalEntropy.entropyTerm
  unfold traceProductLogSigma
  simp only
  -- Support condition for this mixture component
  have h_support : ∀ j, diagonalOfRhoInSigmaBasis (states i) ρ j > 0 →
      InfoTheory.VonNeumannEntropy.eigenvaluesOf ρ j > 0 := by
    intro j hdiag
    exact mixture_support_condition probs states hprobs_nonneg hprobs_sum j i hpi hdiag
  have h_split : ∑ j, (if diagonalOfRhoInSigmaBasis (states i) ρ j = 0 then 0
      else diagonalOfRhoInSigmaBasis (states i) ρ j *
        Real.log (diagonalOfRhoInSigmaBasis (states i) ρ j /
          InfoTheory.VonNeumannEntropy.eigenvaluesOf ρ j)) =
    (∑ j, (if diagonalOfRhoInSigmaBasis (states i) ρ j = 0 then 0
        else diagonalOfRhoInSigmaBasis (states i) ρ j *
          Real.log (diagonalOfRhoInSigmaBasis (states i) ρ j))) -
    ∑ j, diagonalOfRhoInSigmaBasis (states i) ρ j *
      Real.log (InfoTheory.VonNeumannEntropy.eigenvaluesOf ρ j) := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext j
    by_cases hrj : diagonalOfRhoInSigmaBasis (states i) ρ j = 0
    · simp [hrj]
    · simp only [hrj, ↓reduceIte]
      have hdiag_pos : diagonalOfRhoInSigmaBasis (states i) ρ j > 0 :=
        lt_of_le_of_ne
          (diagonalOfRhoInSigmaBasis_nonneg (states i) ρ j) (Ne.symm hrj)
      have hμj : InfoTheory.VonNeumannEntropy.eigenvaluesOf ρ j ≠ 0 :=
        ne_of_gt (h_support j hdiag_pos)
      rw [Real.log_div hrj hμj]
      ring
  rw [h_split]
  have h_neg : (-∑ l, (if diagonalOfRhoInSigmaBasis (states i) ρ l = 0 then 0
        else -diagonalOfRhoInSigmaBasis (states i) ρ l *
          Real.log (diagonalOfRhoInSigmaBasis (states i) ρ l))) =
      ∑ l, (if diagonalOfRhoInSigmaBasis (states i) ρ l = 0 then 0
        else diagonalOfRhoInSigmaBasis (states i) ρ l *
          Real.log (diagonalOfRhoInSigmaBasis (states i) ρ l)) := by
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext l
    by_cases h : diagonalOfRhoInSigmaBasis (states i) ρ l = 0 <;> simp [h]
  rw [h_neg]

/-- Klein's inequality for mixture components: S(ρᵢ || ρ) ≥ 0 when ρ = Σⱼ pⱼρⱼ and pᵢ > 0.

    This variant doesn't require all eigenvalues of ρ to be positive, only the
    support condition that follows from the mixture structure. -/
theorem klein_inequality_mixture {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    (i : Fin k) (hpi : 0 < probs i) :
    let ρ := InfoTheory.Measurement.DensityOp.fromEnsemble probs states hprobs_nonneg hprobs_sum
    0 ≤ relativeEntropyReal (states i) ρ := by
  intro ρ
  have h_classical_eq :=
    classicalRelEntropy_eq_mixture probs states hprobs_nonneg hprobs_sum i hpi
  have h_classical_nonneg :=
    classicalRelEntropy_nonneg_mixture probs states hprobs_nonneg hprobs_sum i hpi
  have h_entropy_ineq := vonNeumannEntropy_le_diagonalEntropy (states i) ρ
  -- Chain of inequalities: relativeEntropyReal ≥ classicalRelEntropy ≥ 0
  calc relativeEntropyReal (states i) ρ
      = -InfoTheory.VonNeumannEntropy.vonNeumannEntropy (states i) -
          traceProductLogSigma (states i) ρ := rfl
    _ ≥ -diagonalEntropy (states i) ρ - traceProductLogSigma (states i) ρ := by linarith
    _ = classicalRelEntropy (states i) ρ := h_classical_eq.symm
    _ ≥ 0 := h_classical_nonneg

/-- Von Neumann entropy is concave: Σᵢ pᵢS(ρᵢ) ≤ S(Σᵢ pᵢρᵢ)

    **Proof**: Uses Klein's inequality (relative entropy non-negativity) and concavity identity.
    1. By concavity_identity: S(ρ) - Σᵢ pᵢS(ρᵢ) = Σᵢ pᵢ S(ρᵢ || ρ)
    2. By klein_inequality_mixture: S(ρᵢ || ρ) ≥ 0 for each i with pᵢ > 0
    3. Therefore: S(ρ) - Σᵢ pᵢS(ρᵢ) = Σᵢ pᵢ [non-negative] ≥ 0
    4. Rearranging: Σᵢ pᵢS(ρᵢ) ≤ S(ρ) -/
theorem vonNeumannEntropy_concave {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1) :
    ∑ i, probs i * InfoTheory.VonNeumannEntropy.vonNeumannEntropy (states i) ≤
      InfoTheory.VonNeumannEntropy.vonNeumannEntropy
        (InfoTheory.Measurement.DensityOp.fromEnsemble
          probs states hprobs_nonneg hprobs_sum) := by
  -- Use concavity_identity
  have h_identity :=
    concavity_identity probs states hprobs_nonneg hprobs_sum
  set ρ := InfoTheory.Measurement.DensityOp.fromEnsemble
    probs states hprobs_nonneg hprobs_sum with hρ
  -- From identity: S(ρ) - Σᵢ pᵢS(ρᵢ) = Σᵢ pᵢ S(ρᵢ || ρ)
  -- Need: Σᵢ pᵢ D(ρᵢ || ρ) ≥ 0
  have h_sum_nonneg : 0 ≤ ∑ i, probs i * relativeEntropyReal (states i) ρ := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hpi : probs i = 0
    · simp [hpi]
    · -- probs i > 0
      have hpi_pos : 0 < probs i := lt_of_le_of_ne (hprobs_nonneg i) (Ne.symm hpi)
      apply mul_nonneg (hprobs_nonneg i)
      exact klein_inequality_mixture probs states hprobs_nonneg hprobs_sum i hpi_pos
  linarith

/-- Holevo χ is non-negative.

    **Proof**: Direct consequence of concavity of von Neumann entropy.
    χ = S(Σᵢ pᵢρᵢ) - Σᵢ pᵢS(ρᵢ)
    By vonNeumannEntropy_concave: Σᵢ pᵢS(ρᵢ) ≤ S(Σᵢ pᵢρᵢ)
    Therefore χ ≥ 0. -/
theorem holevoChi_nonneg {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1) :
    0 ≤ InfoTheory.Measurement.holevoChi probs states hprobs_nonneg hprobs_sum := by
  unfold InfoTheory.Measurement.holevoChi
  have h := vonNeumannEntropy_concave probs states hprobs_nonneg hprobs_sum
  linarith

end InfoTheory.RelativeEntropy

end
