import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.InfoTheory.DistanceBounds.Basic
import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.Channels.CPTP.Basic

/-!
# POVMs — measurement probabilities, mutual information, discrimination bounds

Positive Operator-Valued Measures (POVMs), ensemble averages, classical information
quantities derived from quantum measurements, and measurement discrimination limits.

## Main definitions
- `POVM`: Positive Operator-Valued Measure (elements sum to identity, each PSD)
- `POVM.prob`: Measurement outcome probability Tr(Mᵢ ρ)
- `ensembleAverage`: Average state ∑ pᵢ ρᵢ
- `DensityOp.fromEnsemble`: Density operator from a convex combination
- `holevoChi`: Holevo χ quantity S(ρ_avg) - ∑ pᵢ S(ρᵢ)
- `mutualInfo`: Classical mutual information I(X:Y)

## Main statements
- `conditioning_reduces_entropy`: H(Y|X) ≤ H(Y)
- `mutualInfo_nonneg`: I(X:Y) ≥ 0
- `perfect_measurement_implies_eigenvalue_one`: deterministic outcome implies eigenvector
- `no_perfect_discrimination`: non-orthogonal states cannot be perfectly distinguished
-/

open Quantum.Operators Quantum.TensorProducts
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.Measurement

/-!
## POVMs

A POVM (Positive Operator-Valued Measure) represents a quantum measurement.
-/

/-- A POVM is a collection of positive operators that sum to identity -/
structure POVM (n : ℕ) (k : ℕ) where
  /-- The POVM elements -/
  elements : Fin k → Op n
  /-- Each element is Hermitian -/
  hermitian : ∀ i, (elements i).IsHermitian
  /-- Each element is positive semidefinite: ⟨x|Mᵢ|x⟩ ≥ 0 for all x -/
  positive : ∀ i x, 0 ≤ (quadraticForm (elements i) x).re
  /-- Elements sum to identity -/
  complete : ∑ i, elements i = 1

/-- Probability of outcome i when measuring state ρ with POVM M -/
def POVM.prob {n k : ℕ} (M : POVM n k) (ρ : DensityOp n) (i : Fin k) : ℝ :=
  ((M.elements i * ρ.toOp).trace).re

/-- POVM elements are Hermitian (directly from the structure field). -/
private theorem povm_element_hermitian {n k : ℕ} (M : POVM n k) (i : Fin k) :
    (M.elements i).IsHermitian :=
  M.hermitian i

/-- For a POVM element, the quadratic form is purely real (im = 0).

    This follows directly from the POVM element being Hermitian. -/
lemma povm_quadraticForm_real {n k : ℕ} (M : POVM n k) (i : Fin k) (x : Fin n → ℂ) :
    (quadraticForm (M.elements i) x).im = 0 := by
  -- Use the fact that M is Hermitian
  have hM := povm_element_hermitian M i
  -- Apply the general result for Hermitian matrices
  have h := quadraticForm_hermitian_conj_eq_self (M.elements i) hM x
  rw [Complex.ext_iff] at h
  simp only [Complex.conj_re, Complex.conj_im] at h
  linarith [h.2]

/-- Helper: Convert POVM element to Mathlib's PosSemidef format -/
lemma povm_element_is_mathlib_psd {n k : ℕ} (M : POVM n k) (i : Fin k) :
    Matrix.PosSemidef (M.elements i) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · -- Hermiticity
    exact povm_element_hermitian M i
  · -- Positive semidefiniteness
    intro x
    have h := M.positive i x
    unfold quadraticForm at h
    simp only [star]
    have h_im := povm_quadraticForm_real M i x
    unfold quadraticForm at h_im
    rw [Complex.nonneg_iff]
    exact ⟨h, h_im.symm⟩

/-- POVM probabilities are non-negative.

    **Proof strategy**: Tr(Mᵢρ) ≥ 0 since both Mᵢ and ρ are positive semidefinite.
    For PSD matrices, the trace of their product is always non-negative. -/
theorem POVM.prob_nonneg {n k : ℕ} (M : POVM n k) (ρ : DensityOp n) (i : Fin k) :
    0 ≤ M.prob ρ i := by
  unfold POVM.prob
  -- Convert both to Mathlib's PosSemidef format
  have hM_psd := povm_element_is_mathlib_psd M i
  have hρ_psd := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  -- Apply the general result for product of PSD matrices
  exact Quantum.Operators.trace_mul_psd_nonneg (M.elements i) ρ.toOp hM_psd hρ_psd

/-- POVM probabilities sum to 1.

    **Proof strategy**: Σᵢ Tr(Mᵢρ) = Tr((Σᵢ Mᵢ)ρ) = Tr(Iρ) = Tr(ρ) = 1.
    Uses linearity of trace and POVM completeness ΣᵢMᵢ = I. -/
theorem POVM.prob_sum {n k : ℕ} (M : POVM n k) (ρ : DensityOp n) :
    ∑ i, M.prob ρ i = 1 := by
  unfold POVM.prob
  rw [← Complex.re_sum]
  conv_lhs => arg 1; rw [← Matrix.trace_sum]
  have hsum : (∑ i, M.elements i * ρ.toOp) = (∑ i, M.elements i) * ρ.toOp := by
    rw [Finset.sum_mul]
  rw [hsum, M.complete, one_mul, ρ.trace_one]
  simp

/-!
## Ensemble Average and Holevo Quantity
-/

/-- Average state of an ensemble: ρ_avg = Σᵢ pᵢρᵢ -/
def ensembleAverage {n : ℕ} {k : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n) : Op n :=
  ∑ i, (probs i : ℂ) • (states i).toOp


/-- The ensemble average is a valid density operator when probabilities form a distribution.

    **Properties**:
    - Hermitian: (Σᵢ pᵢρᵢ)† = Σᵢ pᵢρᵢ†  = Σᵢ pᵢρᵢ (since each ρᵢ is Hermitian)
    - Positive semidefinite: Σᵢ pᵢρᵢ is PSD (convex combination of PSD matrices with pᵢ ≥ 0)
    - Trace 1: Tr(Σᵢ pᵢρᵢ) = Σᵢ pᵢ Tr(ρᵢ) = Σᵢ pᵢ · 1 = 1 -/
def DensityOp.fromEnsemble {n : ℕ} {k : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1) :
    DensityOp n :=
  ⟨⟨⟨ensembleAverage probs states, by
    -- Hermiticity: (Σᵢ pᵢρᵢ)† = Σᵢ pᵢρᵢ
    unfold ensembleAverage Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    congr 1
    ext i
    rw [Matrix.conjTranspose_smul]
    -- pᵢ is real, so star pᵢ = pᵢ, and ρᵢ is Hermitian
    rw [(states i).toPosSemidefOp.toHermitianOp.isHermitian]
    simp only [Complex.star_def, Complex.conj_ofReal]
  ⟩, by
    -- Positive semidefiniteness: Σᵢ pᵢ · ⟨x|ρᵢ|x⟩ where each ⟨x|ρᵢ|x⟩ ≥ 0 and pᵢ ≥ 0
    intro x
    unfold ensembleAverage quadraticForm
    simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul]
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro i _
    -- (↑(probs i) • z).re = probs i * z.re for z : ℂ (since probs i is real)
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
               zero_mul, sub_zero]
    apply mul_nonneg
    · exact hprobs_nonneg i
    · exact (states i).toPosSemidefOp.pos_semidef x
  ⟩, by
    -- Trace = 1
    unfold ensembleAverage
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, smul_eq_mul]
    -- Σᵢ pᵢ · Tr(ρᵢ) = Σᵢ pᵢ · 1 = 1
    have h : ∀ i, (probs i : ℂ) * (states i).toOp.trace = (probs i : ℂ) := by
      intro i
      rw [(states i).trace_one, mul_one]
    simp_rw [h]
    rw [← Complex.ofReal_sum, hprobs_sum, Complex.ofReal_one]
  ⟩

/-- Joint probability p(x,y) = p(x) · Tr(Mᵧρₓ) for measurement outcome y given state x -/
def jointProb {n : ℕ} {k m : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) (x : Fin k) (y : Fin m) : ℝ :=
  probs x * M.prob (states x) y

/-- Marginal probability p(y) = Σₓ p(x,y) = Σₓ p(x)Tr(Mᵧρₓ) -/
def marginalProbY {n : ℕ} {k m : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) (y : Fin m) : ℝ :=
  ∑ x, jointProb probs states M x y

/-- Conditional probability p(y|x) = Tr(Mᵧρₓ) -/
def condProbYGivenX {n : ℕ} {k m : ℕ} (states : Fin k → DensityOp n)
    (M : POVM n m) (x : Fin k) (y : Fin m) : ℝ :=
  M.prob (states x) y

/-- Entropy of output distribution H(Y) = -Σᵧ p(y) log p(y) -/
def outputEntropy {n : ℕ} {k m : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) : ℝ :=
  Math.ClassicalEntropy.shannonEntropy (marginalProbY probs states M)

/-- Conditional entropy H(Y|X) = Σₓ p(x) H(Y|X=x) -/
def conditionalEntropy {n : ℕ} {k m : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) : ℝ :=
  ∑ x, probs x * Math.ClassicalEntropy.shannonEntropy (condProbYGivenX states M x)

/-- Classical mutual information: I(X:Y) = H(Y) - H(Y|X)

    This is the Shannon mutual information between the classical input X
    and classical measurement outcome Y. -/
def mutualInfo {n : ℕ} {k : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    {m : ℕ} (M : POVM n m) : ℝ :=
  outputEntropy probs states M - conditionalEntropy probs states M

/-- Helper: Joint probabilities are non-negative. -/
lemma jointProb_nonneg {n : ℕ} {k m : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) (hprobs_nonneg : ∀ i, 0 ≤ probs i) (x : Fin k) (y : Fin m) :
    0 ≤ jointProb probs states M x y := by
  unfold jointProb
  apply mul_nonneg (hprobs_nonneg x) (M.prob_nonneg (states x) y)

/-- Helper: Marginal probabilities are non-negative. -/
lemma marginalProbY_nonneg {n : ℕ} {k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) (hprobs_nonneg : ∀ i, 0 ≤ probs i) (y : Fin m) :
    0 ≤ marginalProbY probs states M y := by
  unfold marginalProbY
  apply Finset.sum_nonneg
  intro x _
  exact jointProb_nonneg probs states M hprobs_nonneg x y

/-- Helper: Marginal probabilities sum to 1. -/
lemma marginalProbY_sum {n : ℕ} {k m : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) (hprobs_sum : ∑ i, probs i = 1) :
    ∑ y, marginalProbY probs states M y = 1 := by
  unfold marginalProbY jointProb
  rw [Finset.sum_comm]
  have h : ∀ x, ∑ y, M.prob (states x) y = 1 := fun x => M.prob_sum (states x)
  calc ∑ x, ∑ y, probs x * M.prob (states x) y
      = ∑ x, probs x * (∑ y, M.prob (states x) y) := by
        congr 1; ext x; rw [← Finset.mul_sum]
    _ = ∑ x, probs x * 1 := by simp_rw [h]
    _ = ∑ x, probs x := by simp only [mul_one]
    _ = 1 := hprobs_sum

/-- Helper: Conditional probabilities sum to 1 for each x. -/
lemma condProbYGivenX_sum {n : ℕ} {k m : ℕ} (states : Fin k → DensityOp n)
    (M : POVM n m) (x : Fin k) :
    ∑ y, condProbYGivenX states M x y = 1 := by
  unfold condProbYGivenX
  exact M.prob_sum (states x)

/-- Helper: Conditional probabilities are non-negative. -/
lemma condProbYGivenX_nonneg {n : ℕ} {k m : ℕ} (states : Fin k → DensityOp n)
    (M : POVM n m) (x : Fin k) (y : Fin m) :
    0 ≤ condProbYGivenX states M x y := by
  unfold condProbYGivenX
  exact M.prob_nonneg (states x) y

/-- **Key Lemma**: Marginal probability equals measurement on average state.

    marginalProbY probs states M y = M.prob ρ_avg y

    where ρ_avg = Σᵢ pᵢρᵢ is the average state.

    **Proof**: By linearity of trace:
    marginalProbY(y) = Σₓ pₓ · Tr(Mᵧρₓ)
                     = Tr(Mᵧ · Σₓ pₓρₓ)     [linearity of trace]
                     = Tr(Mᵧ · ρ_avg)
                     = M.prob(ρ_avg, y)

    This is crucial for the Holevo bound: it identifies the output entropy H(Y)
    with the measurement entropy of the average state. -/
lemma marginalProbY_eq_average_measurement {n k m : ℕ} [NeZero n]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1)
    (M : POVM n m) (y : Fin m) :
    marginalProbY probs states M y =
    M.prob (DensityOp.fromEnsemble probs states hprobs_nonneg hprobs_sum) y := by
  unfold marginalProbY jointProb POVM.prob
  -- LHS: Σₓ probs x * Tr(Mᵧ ρₓ).re
  -- RHS: Tr(Mᵧ ρ_avg).re where ρ_avg = Σₓ probs x • ρₓ
  -- Use linearity of trace and matrix multiplication
  simp only [DensityOp.fromEnsemble, ensembleAverage]
  -- Tr(M * Σₓ pₓ • ρₓ) = Σₓ pₓ * Tr(M * ρₓ)
  have h_linear : ((M.elements y) * (∑ x, (probs x : ℂ) • (states x).toOp)).trace =
      ∑ x, (probs x : ℂ) * ((M.elements y) * (states x).toOp).trace := by
    rw [Matrix.mul_sum]
    rw [Matrix.trace_sum]
    congr 1
    ext x
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [h_linear]
  -- Convert to real
  rw [Complex.re_sum]
  congr 1
  ext x
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

-- Helper definitions for the proof of conditioning_reduces_entropy
-- These flatten the joint and product distributions to single-index form
-- for application of log_sum_inequality

/-- Flattened joint distribution p(x,y) over Fin(k*m) -/
def flatJoint {n k m : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) : Fin (k * m) → ℝ := fun i =>
  jointProb probs states M i.divNat i.modNat

/-- Flattened product of marginals p(x)p(y) over Fin(k*m) -/
def flatProduct {n k m : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) : Fin (k * m) → ℝ := fun i =>
  probs i.divNat * marginalProbY probs states M i.modNat

private lemma flatJoint_sum_eq_one {n k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_sum : ∑ i, probs i = 1) :
    ∑ i, flatJoint probs states M i = 1 := by
  unfold flatJoint
  have h1 : ∑ i : Fin (k * m), jointProb probs states M i.divNat i.modNat
          = ∑ p : Fin k × Fin m, jointProb probs states M p.1 p.2 := by
    have hequiv : ∀ i : Fin (k * m),
        jointProb probs states M i.divNat i.modNat =
        jointProb probs states M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := by
      intro i; rfl
    conv_lhs => arg 2; ext i; rw [hequiv i]
    rw [← Equiv.sum_comp finProdFinEquiv.symm]
  rw [h1, Fintype.sum_prod_type]
  unfold jointProb
  have h2 : ∀ x : Fin k, ∑ y : Fin m, probs x * M.prob (states x) y = probs x := by
    intro x; rw [← Finset.mul_sum, M.prob_sum, mul_one]
  simp_rw [h2]; exact hprobs_sum

private lemma flatProduct_sum_eq_one {n k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_sum : ∑ i, probs i = 1) :
    ∑ i, flatProduct probs states M i = 1 := by
  unfold flatProduct
  have h1 : ∑ i : Fin (k * m), probs i.divNat * marginalProbY probs states M i.modNat
          = ∑ p : Fin k × Fin m, probs p.1 * marginalProbY probs states M p.2 := by
    have hequiv : ∀ i : Fin (k * m),
        probs i.divNat * marginalProbY probs states M i.modNat =
        probs (finProdFinEquiv.symm i).1 * marginalProbY probs states M (finProdFinEquiv.symm i).2
        := by intro i; rfl
    conv_lhs => arg 2; ext i; rw [hequiv i]
    rw [← Equiv.sum_comp finProdFinEquiv.symm]
  rw [h1, Fintype.sum_prod_type]
  have hprod : ∀ x : Fin k, ∑ y : Fin m, probs x * marginalProbY probs states M y
             = probs x * ∑ y : Fin m, marginalProbY probs states M y := by
    intro x; symm; exact Finset.mul_sum _ _ _
  simp_rw [hprod]
  have hmarg_sum : ∑ y : Fin m, marginalProbY probs states M y = 1 := by
    unfold marginalProbY jointProb
    rw [Finset.sum_comm]
    have h3 : ∀ x : Fin k, ∑ y : Fin m, probs x * M.prob (states x) y = probs x := by
      intro x; rw [← Finset.mul_sum, M.prob_sum, mul_one]
    simp_rw [h3]; exact hprobs_sum
  simp_rw [hmarg_sum, mul_one]; exact hprobs_sum

private lemma flatJoint_nonneg {n k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (i : Fin (k * m)) :
    0 ≤ flatJoint probs states M i := by
  unfold flatJoint jointProb
  apply mul_nonneg (hprobs_nonneg _) (M.prob_nonneg _ _)

private lemma flatProduct_nonneg {n k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (i : Fin (k * m)) :
    0 ≤ flatProduct probs states M i := by
  unfold flatProduct marginalProbY
  apply mul_nonneg (hprobs_nonneg _)
  apply Finset.sum_nonneg; intro x _
  unfold jointProb; apply mul_nonneg (hprobs_nonneg _) (M.prob_nonneg _ _)

private lemma flat_support_condition {n k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (i : Fin (k * m)) :
    flatJoint probs states M i > 0 → flatProduct probs states M i > 0 := by
  unfold flatJoint flatProduct jointProb marginalProbY
  intro hpos
  have hp_pos : probs i.divNat > 0 := by
    by_contra h; push Not at h
    have h' : probs i.divNat = 0 := le_antisymm h (hprobs_nonneg _)
    simp only [h', zero_mul] at hpos
    exact absurd hpos (lt_irrefl 0)
  apply mul_pos hp_pos
  apply Finset.sum_pos' (fun x _ => by
    unfold jointProb at *; apply mul_nonneg (hprobs_nonneg _) (M.prob_nonneg _ _))
  refine ⟨i.divNat, Finset.mem_univ _, hpos⟩

/-- The algebraic identity expressing mutual information as KL divergence.

    I(X:Y) = H(Y) - H(Y|X) = D_KL(p(x,y) || p(x)⊗p(y))

    **Full derivation**:
    H(Y|X) = ∑_x p(x) H(Y|X=x) = -∑_x ∑_y p(x,y) log p(y|x)
           = -∑_x ∑_y p(x,y) log(p(x,y)/p(x))
           = -∑_x ∑_y p(x,y) log p(x,y) + ∑_x ∑_y p(x,y) log p(x)
           = -∑_x ∑_y p(x,y) log p(x,y) + ∑_x p(x) log p(x)

    H(Y) = -∑_y p(y) log p(y) = -∑_x ∑_y p(x,y) log p(y)  (since p(y) = ∑_x p(x,y))

    I(X:Y) = H(Y) - H(Y|X)
           = -∑_x ∑_y p(x,y) log p(y) + ∑_x ∑_y p(x,y) log p(x,y) - ∑_x p(x) log p(x)
           = ∑_x ∑_y p(x,y) [log p(x,y) - log p(y)] - ∑_x (∑_y p(x,y)) log p(x)
           = ∑_x ∑_y p(x,y) [log p(x,y) - log p(y) - log p(x)]
           = ∑_x ∑_y p(x,y) log(p(x,y) / (p(x) * p(y)))

    The formal proof involves careful handling of zero cases and sum manipulations. -/
-- Helper: finProdFinEquiv properties for index manipulation
lemma finProdFinEquiv_divNat {k m : ℕ} [NeZero m] (x : Fin k) (y : Fin m) :
    (finProdFinEquiv (x, y)).divNat = x := by
  have hm : 0 < m := NeZero.pos m
  ext
  simp only [finProdFinEquiv, Fin.divNat, Equiv.coe_fn_mk, Fin.val_mk]
  rw [Nat.add_mul_div_left y.val x.val hm]
  have hdiv : y.val / m = 0 := by rw [Nat.div_eq_zero_iff]; right; exact y.isLt
  simp [hdiv]

lemma finProdFinEquiv_modNat {k m : ℕ} [NeZero m] (x : Fin k) (y : Fin m) :
    (finProdFinEquiv (x, y)).modNat = y := by
  have hm : 0 < m := NeZero.pos m
  ext
  simp only [finProdFinEquiv, Fin.modNat, Equiv.coe_fn_mk, Fin.val_mk]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt y.isLt

-- Helper: flat sum equals double sum
lemma flat_sum_eq_double_sum {k m : ℕ} [NeZero k] [NeZero m]
    (f : Fin k → Fin m → ℝ) :
    ∑ i : Fin (k * m), f i.divNat i.modNat = ∑ x : Fin k, ∑ y : Fin m, f x y := by
  have h1 : ∑ i : Fin (k * m), f i.divNat i.modNat = ∑ p : Fin k × Fin m, f p.1 p.2 := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    congr 1; ext ⟨x, y⟩; rw [finProdFinEquiv_divNat, finProdFinEquiv_modNat]
  rw [h1, Fintype.sum_prod_type]

-- Helper: combining two double sums
private lemma combine_double_sums {k m : ℕ} (f g : Fin k → Fin m → ℝ) :
    -∑ x, ∑ y, f x y + ∑ x, ∑ y, g x y = ∑ x, ∑ y, (-f x y + g x y) := by
  simp only [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]

-- Helper: conditional entropy expansion
private lemma cond_entropy_expansion {k m : ℕ} (probs : Fin k → ℝ)
    (pyx : Fin k → Fin m → ℝ) :
    ∑ x, probs x * (-∑ y, pyx x y * Real.log (pyx x y)) =
    -∑ x, ∑ y, probs x * pyx x y * Real.log (pyx x y) := by
  simp only [mul_neg, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _; congr 1
  apply Finset.sum_congr rfl
  intro y _; ring

-- Helper: output entropy as double sum
private lemma output_entropy_as_double_sum {k m : ℕ} (pxy : Fin k → Fin m → ℝ)
    (py : Fin m → ℝ) (hpy : ∀ y, py y = ∑ x, pxy x y) :
    -∑ y, py y * Real.log (py y) = -∑ x, ∑ y, pxy x y * Real.log (py y) := by
  congr 1; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _; rw [hpy y, Finset.sum_mul]

lemma mutual_info_eq_kl_divergence {n k m : ℕ} [NeZero k] [NeZero m]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (_hprobs_sum : ∑ i, probs i = 1) :
    outputEntropy probs states M - conditionalEntropy probs states M =
    ∑ i, (if flatJoint probs states M i = 0 then 0
          else flatJoint probs states M i *
               Real.log (flatJoint probs states M i / flatProduct probs states M i)) := by
  -- Abbreviations for readability
  let pxy := jointProb probs states M
  let py := marginalProbY probs states M
  let pyx := condProbYGivenX states M
  -- Expand definitions
  unfold outputEntropy conditionalEntropy
  rw [Math.ClassicalEntropy.shannonEntropy_eq_neg_sum_mul_log]
  simp only [Math.ClassicalEntropy.shannonEntropy_eq_neg_sum_mul_log]
  -- Convert RHS flat sum to double sum
  have h_rhs : ∑ i, (if flatJoint probs states M i = 0 then 0
               else flatJoint probs states M i *
                    Real.log (flatJoint probs states M i / flatProduct probs states M i)) =
               ∑ x, ∑ y, (if pxy x y = 0 then 0
                          else pxy x y * Real.log (pxy x y / (probs x * py y))) := by
    rw [← flat_sum_eq_double_sum]; rfl
  rw [h_rhs]
  -- Key relations:
  -- pxy(x,y) = probs(x) * pyx(x,y)  [definition of jointProb]
  -- py(y) = Σ_x pxy(x,y)            [definition of marginalProbY]
  have hpxy_def : ∀ x y, pxy x y = probs x * pyx x y := fun _ _ => rfl
  have hpy_def : ∀ y, py y = ∑ x, pxy x y := fun _ => rfl
  -- Helper: pxy non-negative
  have hpxy_nonneg : ∀ x y, 0 ≤ pxy x y := fun x y => by
    simp only [pxy, jointProb]
    apply mul_nonneg (hprobs_nonneg x) (M.prob_nonneg _ _)
  -- Step 1: Expand conditional entropy term
  have h_cond : ∑ x, probs x * (-∑ y, pyx x y * Real.log (pyx x y)) =
                -∑ x, ∑ y, probs x * pyx x y * Real.log (pyx x y) :=
    cond_entropy_expansion probs pyx
  -- LHS = -Σ_y py*log(py) - Σ_x probs_x * (-Σ_y pyx*log(pyx))
  --     = -Σ_y py*log(py) + Σ_x Σ_y probs_x * pyx * log(pyx)
  --     = -Σ_y py*log(py) + Σ_x Σ_y pxy * log(pyx)      [using pxy = probs * pyx]
  have h_pxy_pyx : ∀ x y, probs x * pyx x y * Real.log (pyx x y) =
                          pxy x y * Real.log (pyx x y) := fun x y => by
    change probs x * condProbYGivenX states M x y * Real.log (condProbYGivenX states M x y) =
           jointProb probs states M x y * Real.log (condProbYGivenX states M x y)
    unfold jointProb condProbYGivenX; ring
  simp_rw [h_pxy_pyx] at h_cond
  -- Simplify LHS using h_cond
  calc -∑ i, py i * Real.log (py i) -
         ∑ x, probs x * -∑ i, pyx x i * Real.log (pyx x i)
      = -∑ i, py i * Real.log (py i) + ∑ x, ∑ y, pxy x y * Real.log (pyx x y) := by
          simp only [sub_eq_add_neg]
          congr 1
          rw [h_cond]
          simp only [neg_neg]
    _ = -∑ x, ∑ y, pxy x y * Real.log (py y) + ∑ x, ∑ y, pxy x y * Real.log (pyx x y) := by
          rw [output_entropy_as_double_sum pxy py hpy_def]
    _ = ∑ x, ∑ y, (-pxy x y * Real.log (py y) + pxy x y * Real.log (pyx x y)) := by
          rw [combine_double_sums]
          apply Finset.sum_congr rfl; intro x _
          apply Finset.sum_congr rfl; intro y _
          ring
    _ = ∑ x, ∑ y, (if pxy x y = 0 then 0
                   else pxy x y * Real.log (pxy x y / (probs x * py y))) := by
          apply Finset.sum_congr rfl; intro x _
          apply Finset.sum_congr rfl; intro y _
          by_cases hpxy0 : pxy x y = 0
          · simp [hpxy0]
          · simp only [hpxy0, ↓reduceIte]
            -- When pxy > 0, probs > 0 (since pxy = probs * pyx and pyx >= 0)
            have hprobs_pos : probs x > 0 := by
              by_contra h; push Not at h
              have h' := le_antisymm h (hprobs_nonneg x)
              rw [hpxy_def x y, h', zero_mul] at hpxy0
              exact hpxy0 rfl
            have hpyx_eq : pyx x y = pxy x y / probs x := by
              rw [hpxy_def x y]; field_simp
            -- py > 0 since it contains pxy > 0
            have hpxy_pos : 0 < pxy x y := lt_of_le_of_ne (hpxy_nonneg x y) (Ne.symm hpxy0)
            have hpy_pos : py y > 0 := by
              rw [hpy_def y]
              apply Finset.sum_pos'
              · intro z _; exact hpxy_nonneg z y
              · exact ⟨x, Finset.mem_univ x, hpxy_pos⟩
            -- Algebra: -pxy*log(py) + pxy*log(pyx) = pxy*log(pxy/(probs*py))
            rw [hpyx_eq]
            rw [Real.log_div (ne_of_gt hpxy_pos) (ne_of_gt hprobs_pos)]
            rw [Real.log_div (ne_of_gt hpxy_pos) (ne_of_gt (mul_pos hprobs_pos hpy_pos))]
            rw [Real.log_mul (ne_of_gt hprobs_pos) (ne_of_gt hpy_pos)]
            ring

theorem conditioning_reduces_entropy {n : ℕ} {k m : ℕ}
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n) (M : POVM n m)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1) :
    conditionalEntropy probs states M ≤ outputEntropy probs states M := by
  -- Handle edge cases
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- k = 0: both entropies are 0
    subst hk
    unfold conditionalEntropy outputEntropy Math.ClassicalEntropy.shannonEntropy marginalProbY
        jointProb
    simp only [Finset.sum_empty, Finset.univ_eq_empty]
    simp only [Math.ClassicalEntropy.entropyTerm_zero, Finset.sum_const_zero, le_refl]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- m = 0: both entropies are 0
    subst hm
    unfold conditionalEntropy outputEntropy Math.ClassicalEntropy.shannonEntropy condProbYGivenX
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, mul_zero, le_refl]
  -- Now k > 0 and m > 0
  have hkne : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hmne : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hkmne : NeZero (k * m) := ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne m)⟩
  -- Show I(X:Y) = H(Y) - H(Y|X) ≥ 0
  suffices h : 0 ≤ outputEntropy probs states M - conditionalEntropy probs states M by
    linarith
  -- Use the algebraic identity to express as KL divergence
  rw [mutual_info_eq_kl_divergence probs states M hprobs_nonneg hprobs_sum]
  -- Apply log_sum_inequality (Gibbs inequality)
  exact Math.ClassicalEntropy.log_sum_inequality
    (flatJoint probs states M)
    (flatProduct probs states M)
    (flatJoint_nonneg probs states M hprobs_nonneg)
    (flatProduct_nonneg probs states M hprobs_nonneg)
    (flatJoint_sum_eq_one probs states M hprobs_sum)
    (flatProduct_sum_eq_one probs states M hprobs_sum)
    (flat_support_condition probs states M hprobs_nonneg)

/-- Mutual information is non-negative: I(X:Y) ≥ 0.

    **Proof strategy**: H(Y) ≥ H(Y|X) because conditioning cannot increase entropy
    (by concavity / Jensen). Formally:
    I(X:Y) = H(Y) - H(Y|X) = Σₓ,ᵧ p(x,y) log(p(x,y)/(p(x)p(y))) ≥ 0
    by log-sum inequality / Gibbs inequality. -/
theorem mutualInfo_nonneg {n : ℕ} {k m : ℕ} (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (M : POVM n m) (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1) :
    0 ≤ mutualInfo probs states M := by
  unfold mutualInfo
  -- I(X:Y) = H(Y) - H(Y|X) ≥ 0 iff H(Y) ≥ H(Y|X)
  -- This follows from the conditioning_reduces_entropy theorem
  linarith [conditioning_reduces_entropy probs states M hprobs_nonneg hprobs_sum]

/-- Holevo χ quantity for an ensemble of quantum states:
    χ = S(Σᵢ pᵢρᵢ) - Σᵢ pᵢS(ρᵢ)

    This measures the "quantum information" in the ensemble - the difference
    between the entropy of the average state and the average entropy of states. -/
def holevoChi {n : ℕ} [NeZero n] {k : ℕ} [NeZero k]
    (probs : Fin k → ℝ) (states : Fin k → DensityOp n)
    (hprobs_nonneg : ∀ i, 0 ≤ probs i) (hprobs_sum : ∑ i, probs i = 1) : ℝ :=
  let ρ_avg := DensityOp.fromEnsemble probs states hprobs_nonneg hprobs_sum
  InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ_avg -
    ∑ i, probs i * InfoTheory.VonNeumannEntropy.vonNeumannEntropy (states i)

/-!
## State Discrimination Impossibility

Non-orthogonal quantum states cannot be perfectly distinguished by any measurement.
This is a fundamental result underlying quantum cryptography security.
-/

/-- Helper lemma: Perfect measurement on a pure state implies eigenvalue 1.

    If Tr(M |ψ⟩⟨ψ|) = ⟨ψ|M|ψ⟩ = 1 for normalized |ψ⟩ and M ≤ I (M is a POVM element),
    then M|ψ⟩ = |ψ⟩.

    **Proof sketch**:
    - M ≤ I means I - M ≥ 0, so ⟨ψ|(I - M)|ψ⟩ ≥ 0
    - ⟨ψ|(I - M)|ψ⟩ = ⟨ψ|ψ⟩ - ⟨ψ|M|ψ⟩ = 1 - 1 = 0
    - For PSD operator A, ⟨ψ|A|ψ⟩ = 0 implies A|ψ⟩ = 0 (since ⟨ψ|A|ψ⟩ = ||A^{1/2}|ψ⟩||²)
    - Therefore (I - M)|ψ⟩ = 0, which gives M|ψ⟩ = |ψ⟩

    This requires the spectral theorem and properties of positive semidefinite operators. -/
theorem perfect_measurement_implies_eigenvalue_one {n : ℕ} (M : POVM n 2) (i : Fin 2)
    (ψ : Ket n) (hψ_norm : (ψ.dag * ψ) = 1)
    (hperf : M.prob (DensityOp.fromPure ψ hψ_norm) i = 1) :
    (M.elements i).mulVec ψ.vec = ψ.vec := by
  -- Step 1: Show 1 - M.elements i is PSD (it equals the other POVM element)
  have h_sum : M.elements 0 + M.elements 1 = 1 := by
    have h := M.complete
    simp only [Fin.sum_univ_two] at h
    exact h
  -- Get PSD of the complement
  have h_comp_psd : Matrix.PosSemidef (1 - M.elements i) := by
    rcases i with ⟨iv, hiv⟩
    rcases iv with (_ | iv')
    · have hi : (⟨0, hiv⟩ : Fin 2) = (0 : Fin 2) := rfl
      simp only [hi]
      have heq : 1 - M.elements 0 = M.elements 1 := by
        calc 1 - M.elements 0 = M.elements 0 + M.elements 1 - M.elements 0 := by rw [h_sum]
          _ = M.elements 1 := by simp
      rw [heq]
      exact povm_element_is_mathlib_psd M 1
    · rcases iv' with (_ | _)
      · have hi : (⟨1, hiv⟩ : Fin 2) = (1 : Fin 2) := rfl
        simp only [hi]
        have heq : 1 - M.elements 1 = M.elements 0 := by
          calc 1 - M.elements 1 = M.elements 0 + M.elements 1 - M.elements 1 := by rw [h_sum]
            _ = M.elements 0 := by simp
        rw [heq]
        exact povm_element_is_mathlib_psd M 0
      · omega
  -- Step 2: Calculate ⟨ψ|(1 - M_i)|ψ⟩ = 1 - 1 = 0
  -- First, note that M.prob for pure state = ⟨ψ|M|ψ⟩ = quadraticForm(M, ψ).re
  -- Key identity: Tr(A |ψ⟩⟨ψ|) = Tr(|ψ⟩⟨ψ| A) = ⟨ψ|A|ψ⟩
  have h_trace_identity : ((M.elements i * (ψ * ψ.dag))).trace =
      star ψ.vec ⬝ᵥ (M.elements i).mulVec ψ.vec := by
    rw [Matrix.trace_mul_comm]
    -- ((ψ * ψ.dag) * M).trace = ⟨ψ|M|ψ⟩
    unfold Matrix.trace Matrix.diag
    simp only [Matrix.mul_apply, ket_mul_bra_apply, Ket.dag_vec]
    unfold dotProduct Matrix.mulVec
    simp only [Pi.star_apply, dotProduct]
    -- LHS: ∑ j, ∑ k, ψ j * star ψ k * M k j
    -- RHS: ∑ j, star ψ j * ∑ k, M j k * ψ k
    -- These are equal after rearranging
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    -- LHS: ψ k * star ψ j * M j k
    -- RHS: ψ k * M j k * star ψ j
    -- (starRingEnd ℂ) x = conj x = star x
    have h_star : (starRingEnd ℂ) (ψ.vec j) = star (ψ.vec j) := rfl
    rw [h_star]
    ring
  have h_prob_eq : M.prob (DensityOp.fromPure ψ hψ_norm) i =
      (star ψ.vec ⬝ᵥ (M.elements i).mulVec ψ.vec).re := by
    unfold POVM.prob DensityOp.fromPure
    simp only
    rw [h_trace_identity]
  -- Note: quadraticForm A x = star x ⬝ᵥ A.mulVec x by definition
  have h_qf_eq : quadraticForm (M.elements i) ψ.vec =
      star ψ.vec ⬝ᵥ (M.elements i).mulVec ψ.vec := by
    unfold quadraticForm; rfl
  -- So the quadratic form of M_i with ψ has real part = 1
  have h_qf_Mi : (quadraticForm (M.elements i) ψ.vec).re = 1 := by
    rw [h_qf_eq, ← h_prob_eq]; exact hperf
  -- Also compute the quadratic form of I with ψ (it's ⟨ψ|ψ⟩ = 1)
  have h_qf_I : star ψ.vec ⬝ᵥ (1 : Matrix (Fin n) (Fin n) ℂ).mulVec ψ.vec = 1 := by
    simp only [Matrix.one_mulVec]
    exact hψ_norm
  -- Now compute ⟨ψ|(1 - M_i)|ψ⟩
  have h_qf_comp : star ψ.vec ⬝ᵥ (1 - M.elements i).mulVec ψ.vec = 0 := by
    have h1 : (1 - M.elements i).mulVec ψ.vec =
              (1 : Matrix (Fin n) (Fin n) ℂ).mulVec ψ.vec - (M.elements i).mulVec ψ.vec := by
      simp only [Matrix.sub_mulVec]
    rw [h1]
    rw [dotProduct_sub]
    -- = ⟨ψ|ψ⟩ - ⟨ψ|M_i|ψ⟩ = 1 - 1 = 0 (need complex arithmetic)
    rw [h_qf_I]
    -- Need: (star ψ.vec ⬝ᵥ (M.elements i).mulVec ψ.vec) = 1
    have h_Mi_psd := povm_element_is_mathlib_psd M i
    have h_im_zero : (star ψ.vec ⬝ᵥ (M.elements i).mulVec ψ.vec).im = 0 :=
      h_Mi_psd.isHermitian.im_star_dotProduct_mulVec_self ψ.vec
    -- Note: quadraticForm A x = star x ⬝ᵥ A.mulVec x
    have h_qf_eq' : quadraticForm (M.elements i) ψ.vec =
        star ψ.vec ⬝ᵥ (M.elements i).mulVec ψ.vec := by
      unfold quadraticForm; rfl
    have h_full : star ψ.vec ⬝ᵥ (M.elements i).mulVec ψ.vec = 1 := by
      rw [Complex.ext_iff]
      constructor
      · rw [← h_qf_eq]; exact h_qf_Mi
      · simp [h_im_zero]
    rw [h_full]
    ring
  -- Step 3: Use PSD property - if ⟨ψ|A|ψ⟩ = 0 for PSD A, then A|ψ⟩ = 0
  have h_comp_zero : (1 - M.elements i).mulVec ψ.vec = 0 := by
    rw [← Matrix.PosSemidef.dotProduct_mulVec_zero_iff h_comp_psd]
    exact h_qf_comp
  -- Step 4: Hence M_i|ψ⟩ = |ψ⟩
  have h_expand : (1 - M.elements i).mulVec ψ.vec =
                  (1 : Matrix (Fin n) (Fin n) ℂ).mulVec ψ.vec - (M.elements i).mulVec ψ.vec := by
    simp only [Matrix.sub_mulVec]
  rw [h_expand] at h_comp_zero
  simp only [Matrix.one_mulVec] at h_comp_zero
  -- ψ.vec - M_i ψ.vec = 0  =>  M_i ψ.vec = ψ.vec
  have h_final := sub_eq_zero.mp h_comp_zero
  -- h_final : ψ.vec = M_i ψ.vec, need M_i ψ.vec = ψ.vec
  exact h_final.symm

/-- Non-orthogonal states cannot be perfectly distinguished by any POVM.

    **Mathematical argument**:
    If M₀, M₁ form a POVM with perfect discrimination, then:
    - Tr(M₀ |ψ⟩⟨ψ|) = 1  (ψ always triggers outcome 0)
    - Tr(M₁ |φ⟩⟨φ|) = 1  (φ always triggers outcome 1)

    From Tr(M₀ |ψ⟩⟨ψ|) = 1 and M₀ ≤ I, we get M₀|ψ⟩ = |ψ⟩.
    From Tr(M₁ |φ⟩⟨φ|) = 1 and M₁ ≤ I, we get M₁|φ⟩ = |φ⟩.

    Since M₀ + M₁ = I:
    |ψ⟩ = M₀|ψ⟩ = (I - M₁)|ψ⟩ = |ψ⟩ - M₁|ψ⟩

    This implies M₁|ψ⟩ = 0, so ⟨ψ|M₁|φ⟩ = 0.
    But Tr(M₁ |φ⟩⟨φ|) = ⟨φ|M₁|φ⟩ = 1 requires |φ⟩ to be in the range of M₁.
    The non-orthogonality ⟨ψ|φ⟩ ≠ 0 then contradicts M₁|ψ⟩ = 0.

    **Required infrastructure**: POVM eigenvalue analysis, projector properties. -/
theorem no_perfect_discrimination {n : ℕ}
    (ψ φ : Ket n)
    (hψ_norm : (ψ.dag * ψ) = 1) (hφ_norm : (φ.dag * φ) = 1)
    (hnonorth : (ψ.dag * φ) ≠ 0)
    (M : POVM n 2) :
    let ρ_ψ : DensityOp n := DensityOp.fromPure ψ hψ_norm
    let ρ_φ : DensityOp n := DensityOp.fromPure φ hφ_norm
    ¬(M.prob ρ_ψ 0 = 1 ∧ M.prob ρ_φ 1 = 1) := by
  -- Unfold the let bindings
  change ¬(M.prob (DensityOp.fromPure ψ hψ_norm) 0 = 1 ∧
           M.prob (DensityOp.fromPure φ hφ_norm) 1 = 1)
  -- Proceed by contradiction: assume perfect discrimination
  intro h
  obtain ⟨h0, h1⟩ := h
  -- From perfect discrimination, derive that M₀|ψ⟩ = |ψ⟩ and M₁|φ⟩ = |φ⟩
  have hM0_psi : (M.elements 0).mulVec ψ.vec = ψ.vec :=
    perfect_measurement_implies_eigenvalue_one M 0 ψ hψ_norm h0
  have hM1_phi : (M.elements 1).mulVec φ.vec = φ.vec :=
    perfect_measurement_implies_eigenvalue_one M 1 φ hφ_norm h1
  -- POVM completeness: M₀ + M₁ = I
  have hcomplete : M.elements 0 + M.elements 1 = 1 := by
    have h := M.complete
    -- For 2-element POVM: ∑ i, M.elements i = M.elements 0 + M.elements 1
    simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h
    simpa using h
  -- From M₀ + M₁ = I, we get M₁ = I - M₀
  have hM1_eq : M.elements 1 = 1 - M.elements 0 := by
    calc M.elements 1
        = (M.elements 0 + M.elements 1) - M.elements 0 := by simp [add_sub_cancel_left]
      _ = 1 - M.elements 0 := by rw [hcomplete]
  -- Apply M₁ to |ψ⟩: M₁|ψ⟩ = (I - M₀)|ψ⟩ = |ψ⟩ - M₀|ψ⟩ = |ψ⟩ - |ψ⟩ = 0
  have hM1_psi_zero : (M.elements 1).mulVec ψ.vec = 0 := by
    rw [hM1_eq]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, hM0_psi, sub_self]
  -- Consider ⟨ψ|M₁|φ⟩: Since M₁ is Hermitian and M₁|ψ⟩ = 0, we have ⟨ψ|M₁|φ⟩ = ⟨M₁ψ|φ⟩ = ⟨0|φ⟩ = 0
  have h_bra_M1_zero : ψ.dag * (M.elements 1) * φ = 0 := by
    -- Use Hermiticity of M₁
    have hM1_herm := povm_element_hermitian M 1
    rw [hermitian_inner_product_left (M.elements 1) hM1_herm ψ φ]
    -- Goal: innerProduct (M.elements 1).mulVec ψ.vec φ.vec = 0
    rw [hM1_psi_zero]
    -- Goal: innerProduct 0 φ.vec = 0
    unfold innerProduct
    simp only [Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero]
  -- But from M₁|φ⟩ = |φ⟩, we get ⟨ψ|M₁|φ⟩ = ⟨ψ|φ⟩
  have h_bra_M1_eq_inner : ψ.dag * (M.elements 1) * φ = ψ.dag * φ := by
    -- Since M₁|φ⟩ = |φ⟩, for any vector ψ we have ⟨ψ|M₁|φ⟩ = ⟨ψ|φ⟩
    exact operator_action_in_bra_ket (M.elements 1) ψ φ φ hM1_phi
  -- This gives ⟨ψ|φ⟩ = 0, contradicting non-orthogonality
  rw [h_bra_M1_eq_inner] at h_bra_M1_zero
  exact hnonorth h_bra_M1_zero

end InfoTheory.Measurement

end
