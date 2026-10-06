import QCryptLean.InfoTheory.VonNeumannEntropy.Defs
import QCryptLean.InfoTheory.Measurement.POVM
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Basic.ENNReal.Real

/-!
# Quantum Relative Entropy — eigenbasis extraction, Klein's inequality

Quantum relative entropy S(ρ‖σ) defined via eigenbasis diagonalization,
and Klein's inequality (non-negativity of relative entropy).

## Main definitions
- `eigenbasisOf`: Unitary diagonalizing a density operator, with `eigenbasisOf_unitary_left`,
  `eigenbasisOf_unitary_right` and `eigenbasisOf_spectral_decomp` as its three defining laws
- `diagonalInEigenbasis`: Diagonal elements of σ in ρ's eigenbasis
- `relativeEntropyReal`: Quantum relative entropy S(ρ‖σ) (ℝ-valued, proof helper)
- `relativeEntropy`: Quantum relative entropy S(ρ‖σ) (ENNReal, canonical)
- `classicalRelEntropy`: Classical relative entropy via diagonal entries

## Main statements
- `relativeEntropy_nonneg`: S(ρ‖σ) ≥ 0 — trivially true because ENNReal ≥ 0; not the
  substantive result. The substantive non-negativity is `klein_inequality_full_rank`.
- `klein_inequality_full_rank`: S(ρ‖σ) ≥ 0 (non-trivial, for full-rank σ)
- `klein_inequality`: D(ρ‖σ) = 0 ↔ ρ = σ — equality characterization
- `vonNeumannEntropy_le_diagonalEntropy`: S(ρ) ≤ H(diag)
- `classicalRelEntropy_nonneg`: D(r‖μ) ≥ 0
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-!
## Eigenbasis Extraction
-/

/-- Extract the unitary matrix from spectral decomposition of a density operator. -/
def eigenbasisOf {n : ℕ} (ρ : DensityOp n) : Op n :=
  Classical.choose (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec ρ).2.2.2

/-- The diagonal elements of σ in ρ's eigenbasis: qᵢ = ⟨φᵢ|σ|φᵢ⟩.
    These represent the "classical projection" of σ onto ρ's eigenbasis.

    This quantity computes the expectation values of σ in ρ's eigenvectors, not the
    matrix logarithm of σ. For computing Tr(ρ log σ) — which is needed for relative
    entropy — use `traceProductLogSigma` instead, which properly applies the spectral
    decomposition of σ. -/
def diagonalInEigenbasis {n : ℕ} (ρ σ : DensityOp n) : Fin n → ℝ :=
  fun i => ((eigenbasisOf ρ * σ.toOp * (eigenbasisOf ρ)†) i i).re

/-!
## Matrix Logarithm

For a positive definite Hermitian matrix σ with spectral decomposition σ = V† D V
(which is the convention used by `eigenbasisOf` from `density_has_spectrum`),
the matrix logarithm is defined as log σ = V† (log D) V where log D is the diagonal
matrix with (log D)ᵢᵢ = log(Dᵢᵢ).

The trace Tr(ρ log σ) is then computed using cyclic property:
  Tr(ρ log σ) = Tr(ρ V† (log D) V) = Tr(V ρ V† log D) = Σᵢ (V ρ V†)ᵢᵢ log(μᵢ)
where μᵢ are eigenvalues of σ.
-/

/-- The diagonal of ρ in σ's eigenbasis: (V ρ V†)ᵢᵢ where σ = V† D V.
    This is needed for computing Tr(ρ log σ). -/
def diagonalOfRhoInSigmaBasis {n : ℕ} (ρ σ : DensityOp n) : Fin n → ℝ :=
  fun i => (((eigenbasisOf σ) * ρ.toOp * (eigenbasisOf σ)†) i i).re

/-- Compute Tr(ρ log σ) using spectral decomposition of σ.

    For σ = V† D V where D = diag(μ₁, ..., μₙ) (the convention from `density_has_spectrum`):
      Tr(ρ log σ) = Tr(V ρ V† · log D) = Σᵢ (V ρ V†)ᵢᵢ · log(μᵢ)

    This is the CORRECT way to compute ⟨ρ, log σ⟩ = Tr(ρ log σ). -/
def traceProductLogSigma {n : ℕ} [NeZero n] (ρ σ : DensityOp n) : ℝ :=
  ∑ i, diagonalOfRhoInSigmaBasis ρ σ i * Real.log (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i)

/-- Conjugation by any matrix preserves positive semidefiniteness. -/
lemma posSemidef_conj_aux {n : ℕ}
    (D U : Matrix (Fin n) (Fin n) ℂ) (hD : D.PosSemidef) :
    (U * D * U†).PosSemidef := by
  -- Use the Mathlib lemma for U† * D * U by substituting U† for U
  have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hD U†
  simpa only [conjTranspose_conjTranspose] using h

/-- The diagonal elements of ρ in σ's eigenbasis are non-negative. -/
theorem diagonalOfRhoInSigmaBasis_nonneg {n : ℕ} (ρ σ : DensityOp n) :
    ∀ i, 0 ≤ diagonalOfRhoInSigmaBasis ρ σ i := by
  intro i
  unfold diagonalOfRhoInSigmaBasis
  set V := eigenbasisOf σ
  set M := V * ρ.toOp * V† with hM_def
  -- ρ is PSD
  have hρpsd : ρ.toOp.PosSemidef := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  -- V * ρ * V† is PSD via conjugation (using the helper lemma)
  have hMpsd : M.PosSemidef := posSemidef_conj_aux ρ.toOp V hρpsd
  exact psd_diag_re_nonneg M hMpsd i

/-- The diagonal elements of ρ in σ's eigenbasis sum to 1. -/
theorem diagonalOfRhoInSigmaBasis_sum {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    ∑ i, diagonalOfRhoInSigmaBasis ρ σ i = 1 := by
  unfold diagonalOfRhoInSigmaBasis
  set V := eigenbasisOf σ
  set M := V * ρ.toOp * V† with hM_def
  have hsum_eq_trace_re : ∑ i, (M i i).re = M.trace.re := by
    simpa only [trace, diag_apply] using (Complex.re_sum _ _).symm
  rw [hsum_eq_trace_re]
  -- Get unitarity from spectral decomposition
  have hV_unitary : V† * V = 1 := by
    unfold V eigenbasisOf
    exact (Classical.choose_spec
      (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec σ).2.2.2).1
  -- Trace is preserved under conjugation: Tr(V ρ V†) = Tr(V† V ρ) = Tr(ρ)
  have htrace_cycle : M.trace = ρ.toOp.trace := by
    calc M.trace = (V * ρ.toOp * V†).trace := rfl
      _ = (V† * V * ρ.toOp).trace := trace_mul_cycle V ρ.toOp V†
      _ = (1 * ρ.toOp).trace := by rw [hV_unitary]
      _ = ρ.toOp.trace := by rw [one_mul]
  rw [htrace_cycle]
  have hρtrace : ρ.toOp.trace = 1 := ρ.trace_one
  rw [hρtrace]
  simp

/-- The diagonal elements are non-negative (σ is positive semidefinite). -/
theorem diagonalInEigenbasis_nonneg {n : ℕ} (ρ σ : DensityOp n) :
    ∀ i, 0 ≤ diagonalInEigenbasis ρ σ i := by
  intro i
  unfold diagonalInEigenbasis
  -- The matrix U * σ * U† is positive semidefinite (conjugation preserves PSD)
  set U := eigenbasisOf ρ
  set M := U * σ.toOp * U† with hM_def
  -- σ is PSD
  have hσpsd : σ.toOp.PosSemidef := posSemidefOp_implies_mathlib σ.toPosSemidefOp
  -- U * σ * U† is PSD via conjugation
  have hMpsd : M.PosSemidef := posSemidef_conj_aux σ.toOp U hσpsd
  exact psd_diag_re_nonneg M hMpsd i

/-- Property of eigenbasisOf: U†U = 1 -/
lemma eigenbasisOf_unitary_left {n : ℕ} (ρ : DensityOp n) :
    (eigenbasisOf ρ)† * (eigenbasisOf ρ) = 1 := by
  unfold eigenbasisOf
  exact (Classical.choose_spec (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec ρ).2.2.2).1

/-- Property of eigenbasisOf: UU† = 1 -/
lemma eigenbasisOf_unitary_right {n : ℕ} (ρ : DensityOp n) :
    (eigenbasisOf ρ) * (eigenbasisOf ρ)† = 1 := by
  unfold eigenbasisOf
  exact (Classical.choose_spec (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec ρ).2.2.2).2.1

/-- Spectral decomposition through `eigenbasisOf`: `ρ = U† · diag (eigenvaluesOf ρ) · U` for
`U = eigenbasisOf ρ`.  This is the third component of the same spectral witness as the two
unitarity laws above. -/
lemma eigenbasisOf_spectral_decomp {n : ℕ} (ρ : DensityOp n) :
    ρ.toOp = (eigenbasisOf ρ)† *
      Matrix.diagonal (fun i => (InfoTheory.VonNeumannEntropy.eigenvaluesOf ρ i : ℂ)) *
      (eigenbasisOf ρ) := by
  unfold eigenbasisOf
  exact (Classical.choose_spec (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec ρ).2.2.2).2.2

/-- The diagonal elements sum to 1 (trace is preserved under unitary conjugation). -/
theorem diagonalInEigenbasis_sum {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    ∑ i, diagonalInEigenbasis ρ σ i = 1 := by
  unfold diagonalInEigenbasis
  set U := eigenbasisOf ρ
  set M := U * σ.toOp * U† with hM_def
  -- The sum of diagonal elements is the trace
  have hsum_eq_trace_re : ∑ i, (M i i).re = M.trace.re := by
    simpa only [trace, diag_apply] using (Complex.re_sum _ _).symm
  rw [hsum_eq_trace_re]
  -- The trace is preserved under unitary conjugation: Tr(UσU†) = Tr(σU†U) = Tr(σ)
  have htrace_cycle : M.trace = σ.toOp.trace := by
    calc M.trace = (U * σ.toOp * U†).trace := rfl
      _ = (U† * U * σ.toOp).trace := trace_mul_cycle U σ.toOp U†
      _ = (1 * σ.toOp).trace := by rw [eigenbasisOf_unitary_left]
      _ = σ.toOp.trace := by rw [one_mul]
  rw [htrace_cycle]
  -- σ has trace 1
  have hσtrace : σ.toOp.trace = 1 := σ.trace_one
  rw [hσtrace]
  simp

/-!
## Quantum Relative Entropy

Note: Classical KL divergence (`Math.ClassicalEntropy.classicalKLDiv`) and
`Math.ClassicalEntropy.log_sum_inequality`
are imported from the Math.ClassicalEntropy module.
-/

/-- Quantum relative entropy (Kullback-Leibler divergence): S(ρ||σ) = Tr(ρ log ρ - ρ log σ)

    The relative entropy measures the "distance" from σ to ρ (not symmetric).
    It quantifies how distinguishable ρ is from σ.

    **Correct formula using matrix logarithm**:
    S(ρ||σ) = Tr(ρ log ρ) - Tr(ρ log σ)
            = -S(ρ) - Tr(ρ log σ)

    where S(ρ) is the von Neumann entropy and Tr(ρ log σ) is computed via
    spectral decomposition of σ:
      Tr(ρ log σ) = Σᵢ (V ρ V†)ᵢᵢ · log(μᵢ)
    where V diagonalizes σ (so σ = V† D V) and μᵢ are eigenvalues of σ.

    **Note**: This is NOT the same as Σᵢ λᵢ log(⟨φᵢ|σ|φᵢ⟩) which incorrectly
    puts the log outside the expectation value. The correct formula requires
    computing the matrix logarithm log σ first, then taking the trace with ρ.

    Returns a finite real value; meaningful only when supp(ρ) ⊆ supp(σ). For the
    canonical definition that returns +∞ when the support condition fails,
    use `relativeEntropy`. This ℝ version is kept public for arithmetic
    convenience (subtraction, weighted sums). -/
def relativeEntropyReal {n : ℕ} [NeZero n] (ρ σ : DensityOp n) : ℝ :=
  -InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ - traceProductLogSigma ρ σ

/-!
## Klein's Inequality via Schur-Concavity

The proof of Klein's inequality reduces to showing:
1. The classical KL divergence D(r||μ) ≥ 0 where r = diag(V ρ V†) and μ = eigenvalues of σ
2. The von Neumann entropy S(ρ) ≤ H(r) (Shannon entropy of diagonals)

The second step uses Schur-concavity: eigenvalues of ρ majorize the diagonals of
V ρ V†, and Shannon entropy is Schur-concave.
-/

/-- Classical KL divergence between diagonals of ρ in σ's basis and eigenvalues of σ.

    This is D(r||μ) = Σⱼ rⱼ log(rⱼ/μⱼ) where rⱼ = (V ρ V†)ⱼⱼ and μⱼ are eigenvalues of σ. -/
def classicalRelEntropy {n : ℕ} [NeZero n] (ρ σ : DensityOp n) : ℝ :=
  let r := diagonalOfRhoInSigmaBasis ρ σ
  let μ := InfoTheory.VonNeumannEntropy.eigenvaluesOf σ
  ∑ j, (if r j = 0 then 0 else r j * Real.log (r j / μ j))

/-- Shannon entropy of the diagonal elements of ρ in σ's eigenbasis. -/
def diagonalEntropy {n : ℕ} [NeZero n] (ρ σ : DensityOp n) : ℝ :=
  Math.ClassicalEntropy.shannonEntropy (diagonalOfRhoInSigmaBasis ρ σ)

/-- The classical KL divergence is non-negative when σ has full support. -/
theorem classicalRelEntropy_nonneg {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_support : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i > 0) :
    0 ≤ classicalRelEntropy ρ σ := by
  unfold classicalRelEntropy
  apply Math.ClassicalEntropy.log_sum_inequality
  · exact diagonalOfRhoInSigmaBasis_nonneg ρ σ
  · intro i
    have h := InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec σ
    exact h.1 i
  · exact diagonalOfRhoInSigmaBasis_sum ρ σ
  · have h := InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec σ
    exact h.2.1
  · intro i _
    exact h_support i

/-- The classical relative entropy equals -H(diag) - Tr(ρ log σ). -/
theorem classicalRelEntropy_eq {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_support : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i > 0) :
    classicalRelEntropy ρ σ = -diagonalEntropy ρ σ - traceProductLogSigma ρ σ := by
  unfold classicalRelEntropy diagonalEntropy Math.ClassicalEntropy.shannonEntropy
      Math.ClassicalEntropy.entropyTerm
  unfold traceProductLogSigma
  simp only
  have h_split : ∑ j, (if diagonalOfRhoInSigmaBasis ρ σ j = 0 then 0
      else diagonalOfRhoInSigmaBasis ρ σ j *
        Real.log (diagonalOfRhoInSigmaBasis ρ σ j / InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j))
            =
    (∑ j, (if diagonalOfRhoInSigmaBasis ρ σ j = 0 then 0
        else diagonalOfRhoInSigmaBasis ρ σ j *
          Real.log (diagonalOfRhoInSigmaBasis ρ σ j))) -
    ∑ j, diagonalOfRhoInSigmaBasis ρ σ j * Real.log (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j)
        := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext j
    by_cases hrj : diagonalOfRhoInSigmaBasis ρ σ j = 0
    · simp [hrj]
    · simp only [hrj, ↓reduceIte]
      have hμj : InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j ≠ 0 := ne_of_gt (h_support j)
      rw [Real.log_div hrj hμj]
      ring
  rw [h_split]
  have h_neg : (-∑ i, (if diagonalOfRhoInSigmaBasis ρ σ i = 0 then 0
        else -diagonalOfRhoInSigmaBasis ρ σ i *
          Real.log (diagonalOfRhoInSigmaBasis ρ σ i))) =
      ∑ i, (if diagonalOfRhoInSigmaBasis ρ σ i = 0 then 0
        else diagonalOfRhoInSigmaBasis ρ σ i *
          Real.log (diagonalOfRhoInSigmaBasis ρ σ i)) := by
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext i
    by_cases h : diagonalOfRhoInSigmaBasis ρ σ i = 0 <;> simp [h]
  rw [h_neg]

/-- **Schur-concavity relation**: The diagonal elements of ρ in any basis are a
    doubly stochastic transformation of the eigenvalues.

    If V diagonalizes σ and U diagonalizes ρ (with ρ = U† Λ U), then
    setting W = V * U† (unitary), the diagonal element is:
      (V ρ V†)ᵢᵢ = Σⱼ |Wᵢⱼ|² λⱼ

    The matrix D with D_ij = |W_ij|² is doubly stochastic:
    - Row sums = 1: Σⱼ |Wᵢⱼ|² = (W W†)ᵢᵢ = 1
    - Column sums = 1: Σᵢ |Wᵢⱼ|² = (W† W)ⱼⱼ = 1

    **Proof**: Uses the spectral decomposition infrastructure available via
    `eigenbasisOf` and `eigenvaluesOf`. -/
lemma diagonalOfRhoInSigmaBasis_as_doubly_stochastic {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) : ∃ (D : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, 0 ≤ D i j) ∧
    (∀ i, ∑ j, D i j = 1) ∧
    (∀ j, ∑ i, D i j = 1) ∧
    (∀ i, diagonalOfRhoInSigmaBasis ρ σ i = ∑ j, D i j * eigenvaluesOf ρ j) := by
  -- Extract eigenbases for ρ and σ
  set V_ρ := eigenbasisOf ρ with hV_ρ_def
  set V_σ := eigenbasisOf σ with hV_σ_def
  -- Get spectral decomposition for ρ: ρ = V_ρ† * Λ_ρ * V_ρ
  have hspec_ρ := eigenvaluesOf_spec ρ
  have hV_ρ_props := Classical.choose_spec hspec_ρ.2.2.2
  have hV_ρ_adj_V_ρ : V_ρ.conjTranspose * V_ρ = 1 := hV_ρ_props.1
  have hV_ρ_V_ρ_adj : V_ρ * V_ρ.conjTranspose = 1 := hV_ρ_props.2.1
  have hρ_decomp : ρ.toOp = V_ρ.conjTranspose *
      (Matrix.diagonal (fun i => (eigenvaluesOf ρ i : ℂ))) * V_ρ := hV_ρ_props.2.2
  -- Get unitary properties for V_σ
  have hV_σ_adj_V_σ : V_σ.conjTranspose * V_σ = 1 := eigenbasisOf_unitary_left σ
  have hV_σ_V_σ_adj : V_σ * V_σ.conjTranspose = 1 := eigenbasisOf_unitary_right σ
  -- Define W = V_σ * V_ρ† (unitary transition matrix)
  set W := V_σ * V_ρ.conjTranspose with hW_def
  -- W is unitary
  have hW_adj_W : W.conjTranspose * W = 1 := by
    simp only [hW_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc V_ρ * V_σ.conjTranspose * (V_σ * V_ρ.conjTranspose)
        = V_ρ * (V_σ.conjTranspose * V_σ) * V_ρ.conjTranspose := by
            simp only [Matrix.mul_assoc]
      _ = V_ρ * 1 * V_ρ.conjTranspose := by rw [hV_σ_adj_V_σ]
      _ = V_ρ * V_ρ.conjTranspose := by simp only [Matrix.mul_one]
      _ = 1 := hV_ρ_V_ρ_adj
  have hW_W_adj : W * W.conjTranspose = 1 := by
    simp only [hW_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc V_σ * V_ρ.conjTranspose * (V_ρ * V_σ.conjTranspose)
        = V_σ * (V_ρ.conjTranspose * V_ρ) * V_σ.conjTranspose := by
            simp only [Matrix.mul_assoc]
      _ = V_σ * 1 * V_σ.conjTranspose := by rw [hV_ρ_adj_V_ρ]
      _ = V_σ * V_σ.conjTranspose := by simp only [Matrix.mul_one]
      _ = 1 := hV_σ_V_σ_adj
  -- Define D_ij = |W_ij|² (element-wise squared modulus)
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => Complex.normSq (W i j)
  use D
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- D is non-negative (normSq ≥ 0)
    intro i j
    exact Complex.normSq_nonneg (W i j)
  · -- Row sums = 1: Σⱼ |Wᵢⱼ|² = (W W†)ᵢᵢ = 1
    intro i
    have h_row : ∑ j, Complex.normSq (W i j) = ((W * W.conjTranspose) i i).re := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
          Complex.conj_im]
      ring
    rw [h_row, hW_W_adj]
    simp
  · -- Column sums = 1: Σᵢ |Wᵢⱼ|² = (W† W)ⱼⱼ = 1
    intro j
    have h_col : ∑ i, Complex.normSq (W i j) = ((W.conjTranspose * W) j j).re := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
          Complex.conj_im]
      ring
    rw [h_col, hW_adj_W]
    simp
  · -- Main identity: diagonal_i = Σⱼ D_ij * λⱼ
    intro i
    unfold diagonalOfRhoInSigmaBasis
    simp only [← hV_σ_def]
    -- V_σ * ρ * V_σ† = V_σ * (V_ρ† * Λ * V_ρ) * V_σ† = W * Λ * W†
    have h_conj : V_σ * ρ.toOp * V_σ.conjTranspose =
        W * (Matrix.diagonal (fun j => (eigenvaluesOf ρ j : ℂ))) * W.conjTranspose := by
      rw [hρ_decomp]
      simp only [hW_def, Matrix.mul_assoc, Matrix.conjTranspose_mul,
                 Matrix.conjTranspose_conjTranspose]
    rw [h_conj]
    -- Compute the diagonal entry (W * Λ * W†)ᵢᵢ = Σⱼ |Wᵢⱼ|² λⱼ
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
    -- The goal is: (∑ x, (∑ x_1, W i x_1 * (if x_1 = x then λ_x_1 else 0)) * star(W i x)).re = Σⱼ
    -- D_ij * λⱼ
    -- First simplify each inner sum (only x_1 = x contributes)
    have h_simp : ∀ x, (∑ x_1, W i x_1 * (if x_1 = x then (eigenvaluesOf ρ x_1 : ℂ) else 0)) =
        W i x * (eigenvaluesOf ρ x : ℂ) := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hyx; simp [hyx]
      · intro hx; exact (hx (Finset.mem_univ x)).elim
    -- Rewrite inner sums
    have h_sum_eq : (∑ x, (∑ x_1, W i x_1 * (if x_1 = x then (eigenvaluesOf ρ x_1 : ℂ) else 0)) *
        star (W i x)) = ∑ x, W i x * (eigenvaluesOf ρ x : ℂ) * star (W i x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [h_simp x]
    rw [h_sum_eq]
    -- Now goal is: (∑ x, W i x * λ_x * star(W i x)).re = Σⱼ D_ij * λⱼ
    -- Use: W * λ * star(W) = |W|² * λ (since λ is real)
    have h_prod : ∀ x, (W i x * (eigenvaluesOf ρ x : ℂ) * star (W i x)).re =
        Complex.normSq (W i x) * eigenvaluesOf ρ x := by
      intro x
      -- z * r * conj(z) = r * |z|² for real r
      simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
                 Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact h_prod x

/-- Shannon entropy increases under doubly stochastic transformation.

    For any probability distribution p and doubly stochastic matrix D:
      H(p) ≤ H(D·p)

    **Proof sketch**:
    1. entropyTerm = negMulLog is concave on [0, ∞)
    2. For each row i: entropyTerm((D·p)ᵢ) = entropyTerm(Σⱼ Dᵢⱼ pⱼ) ≥ Σⱼ Dᵢⱼ entropyTerm(pⱼ)
       (by Jensen's inequality since Dᵢⱼ ≥ 0 and Σⱼ Dᵢⱼ = 1)
    3. Summing over i:
       H(D·p) = Σᵢ entropyTerm((D·p)ᵢ) ≥ Σᵢ Σⱼ Dᵢⱼ entropyTerm(pⱼ)
             = Σⱼ (Σᵢ Dᵢⱼ) entropyTerm(pⱼ) = Σⱼ entropyTerm(pⱼ) = H(p) -/
lemma shannonEntropy_doubly_stochastic_ge {n : ℕ} [NeZero n]
    (p : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_row : ∀ i, ∑ j, D i j = 1)
    (hD_col : ∀ j, ∑ i, D i j = 1) :
    Math.ClassicalEntropy.shannonEntropy p ≤ Math.ClassicalEntropy.shannonEntropy (fun i => ∑ j, D i
        j * p j) := by
  -- The proof uses Jensen's inequality with concave negMulLog
  unfold Math.ClassicalEntropy.shannonEntropy
  -- Goal: Σᵢ entropyTerm(pᵢ) ≤ Σᵢ entropyTerm(Σⱼ Dᵢⱼ pⱼ)
  -- By Jensen, for each i: entropyTerm(Σⱼ Dᵢⱼ pⱼ) ≥ Σⱼ Dᵢⱼ entropyTerm(pⱼ)
  have hconcave := Real.concaveOn_negMulLog
  -- First establish bounds on transformed probabilities
  have hDp_nonneg : ∀ i, 0 ≤ ∑ j, D i j * p j := fun i => by
    apply Finset.sum_nonneg; intro j _; exact mul_nonneg (hD_nonneg i j) (hp_nonneg j)
  -- For each i, apply Jensen:
  -- entropyTerm(Σⱼ Dᵢⱼ pⱼ) ≥ Σⱼ Dᵢⱼ entropyTerm(pⱼ)  since entropyTerm = negMulLog is concave
  have hJensen_row : ∀ i,
      Math.ClassicalEntropy.entropyTerm (∑ j, D i j * p j) ≥ ∑ j, D i j *
          Math.ClassicalEntropy.entropyTerm (p j) := by
    intro i
    have hp_in_Ici : ∀ j, j ∈ Finset.univ → p j ∈ Set.Ici (0 : ℝ) := fun j _ => hp_nonneg j
    have hJensen := hconcave.le_map_sum (fun j _ => hD_nonneg i j) (hD_row i) hp_in_Ici
    simp only [smul_eq_mul] at hJensen
    -- Convert from negMulLog to entropyTerm
    have h_lhs : Math.ClassicalEntropy.entropyTerm (∑ j, D i j * p j) =
        Real.negMulLog (∑ j, D i j * p j) := by
      rw [Math.ClassicalEntropy.entropyTerm_eq_negMulLog]; exact hDp_nonneg i
    have h_rhs : ∑ j, D i j * Math.ClassicalEntropy.entropyTerm (p j) =
        ∑ j, D i j * Real.negMulLog (p j) := by
      congr 1; ext j; congr 1; rw [Math.ClassicalEntropy.entropyTerm_eq_negMulLog]; exact hp_nonneg
          j
    rw [h_lhs, h_rhs]
    exact hJensen
  -- Sum over i and exchange order of summation
  calc ∑ i, Math.ClassicalEntropy.entropyTerm (p i)
      = ∑ i, (∑ j, D j i) * Math.ClassicalEntropy.entropyTerm (p i) := by
          congr 1; ext i; rw [hD_col i, one_mul]
    _ = ∑ i, ∑ j, D j i * Math.ClassicalEntropy.entropyTerm (p i) := by
          congr 1; ext i; rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, D j i * Math.ClassicalEntropy.entropyTerm (p i) := Finset.sum_comm
    _ ≤ ∑ j, Math.ClassicalEntropy.entropyTerm (∑ i, D j i * p i) := Finset.sum_le_sum (fun j _ =>
        hJensen_row j)

theorem vonNeumannEntropy_le_diagonalEntropy {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ ≤ diagonalEntropy ρ σ := by
  -- Get the doubly stochastic matrix relating eigenvalues to diagonals
  obtain ⟨D, hD_nonneg, hD_row, hD_col, hD_eq⟩ := diagonalOfRhoInSigmaBasis_as_doubly_stochastic ρ σ
  -- Apply the Shannon entropy lemma
  have hspec := eigenvaluesOf_spec ρ
  have hp_nonneg : ∀ i, 0 ≤ eigenvaluesOf ρ i := hspec.1
  have hp_sum : ∑ i, eigenvaluesOf ρ i = 1 := hspec.2.1
  have hp_le : ∀ i, eigenvaluesOf ρ i ≤ 1 := hspec.2.2.1
  have h_diag_eq : diagonalOfRhoInSigmaBasis ρ σ = fun i => ∑ j, D i j * eigenvaluesOf ρ j :=
    funext hD_eq
  -- vonNeumannEntropy ρ = shannonEntropy (eigenvaluesOf ρ)
  -- diagonalEntropy ρ σ = shannonEntropy (diagonalOfRhoInSigmaBasis ρ σ)
  unfold vonNeumannEntropy diagonalEntropy
  rw [h_diag_eq]
  exact shannonEntropy_doubly_stochastic_ge (eigenvaluesOf ρ) D hp_nonneg
    hD_nonneg hD_row hD_col

/-- Klein's inequality (full-rank case): Relative entropy is non-negative when σ has
    full support.

    Under the hypothesis that all eigenvalues of σ are strictly positive (full rank),
    this proves `0 ≤ S(ρ||σ)`. The general support condition `supp(ρ) ⊆ supp(σ)` and
    the equality characterization `= 0 iff ρ = σ` are NOT established here.

    **Proof strategy**: We reduce to classical KL divergence non-negativity.

    1. Define the "classical" relative entropy D(r||μ) where r = diag(V ρ V†) in σ's
       eigenbasis and μ are eigenvalues of σ. This is ≥ 0 by log-sum inequality.

    2. Show that quantum relative entropy S(ρ||σ) ≥ D(r||μ) using Schur-concavity:
       S(ρ||σ) = -S(ρ) - Tr(ρ log σ)
       D(r||μ) = -H(r) - Tr(ρ log σ)
       Since S(ρ) ≤ H(r) (Schur-concavity), we have -S(ρ) ≥ -H(r), thus S(ρ||σ) ≥ D(r||μ).

    3. Combine: S(ρ||σ) ≥ D(r||μ) ≥ 0. -/
theorem klein_inequality_full_rank {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_support : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i > 0) :
    0 ≤ relativeEntropyReal ρ σ := by
  have h_classical_eq := classicalRelEntropy_eq ρ σ h_support
  have h_classical_nonneg := classicalRelEntropy_nonneg ρ σ h_support
  have h_entropy_ineq := vonNeumannEntropy_le_diagonalEntropy ρ σ
  -- Chain of inequalities: relativeEntropyReal ≥ classicalRelEntropy ≥ 0
  calc relativeEntropyReal ρ σ
      = -InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ - traceProductLogSigma ρ σ := rfl
    _ ≥ -diagonalEntropy ρ σ - traceProductLogSigma ρ σ := by linarith only [h_entropy_ineq]
    _ = classicalRelEntropy ρ σ := h_classical_eq.symm
    _ ≥ 0 := h_classical_nonneg

/-- Relative entropy in terms of entropies: S(ρ||σ) = -S(ρ) - Tr(ρ log σ)

    This is definitionally true by our definition of `relativeEntropyReal`. -/
theorem relativeEntropyReal_eq {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    relativeEntropyReal ρ σ = -InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ -
        traceProductLogSigma ρ σ := rfl

/-- Diagonal of ρ in its own eigenbasis equals the eigenvalues of ρ. -/
lemma diagonalOfRhoInSigmaBasis_self {n : ℕ} (ρ : DensityOp n)
    (j : Fin n) :
    diagonalOfRhoInSigmaBasis ρ ρ j = eigenvaluesOf ρ j := by
  unfold diagonalOfRhoInSigmaBasis
  set V := eigenbasisOf ρ
  have hV_V_adj : V * V† = 1 := eigenbasisOf_unitary_right ρ
  have hU_props :=
    Classical.choose_spec (eigenvaluesOf_spec ρ).2.2.2
  have hρ_decomp : ρ.toOp =
      V† * Matrix.diagonal (fun i => (eigenvaluesOf ρ i : ℂ)) *
        V := hU_props.2.2
  have h_VρV : V * ρ.toOp * V† =
      Matrix.diagonal (fun i => (eigenvaluesOf ρ i : ℂ)) := by
    calc V * ρ.toOp * V†
        = V * (V† * Matrix.diagonal
            (fun i => (eigenvaluesOf ρ i : ℂ)) * V) * V† := by
            rw [hρ_decomp]
      _ = (V * V†) * Matrix.diagonal
            (fun i => (eigenvaluesOf ρ i : ℂ)) * (V * V†) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * Matrix.diagonal
            (fun i => (eigenvaluesOf ρ i : ℂ)) * 1 := by
          rw [hV_V_adj]
      _ = Matrix.diagonal (fun i => (eigenvaluesOf ρ i : ℂ)) := by
          simp
  rw [h_VρV, Matrix.diagonal_apply_eq]
  simp

/-- **Self relative entropy**: D(ρ‖ρ) = 0.

    Follows from the fact that the diagonal of ρ in its own eigenbasis equals the
    eigenvalues of ρ, so traceProductLogSigma ρ ρ = -vonNeumannEntropy ρ. -/
theorem relativeEntropyReal_self {n : ℕ} [NeZero n] (ρ : DensityOp n) :
    relativeEntropyReal ρ ρ = 0 := by
  unfold relativeEntropyReal
  suffices h : traceProductLogSigma ρ ρ = -vonNeumannEntropy ρ by
    linarith only [h]
  unfold traceProductLogSigma
  simp_rw [diagonalOfRhoInSigmaBasis_self]
  unfold vonNeumannEntropy shannonEntropy
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold entropyTerm
  split_ifs with h
  · simp [h]
  · ring

/-!
## ENNReal Quantum Relative Entropy

The ENNReal version returns +∞ when supp(ρ) ⊄ supp(σ), matching the standard
mathematical definition. This version requires no support hypothesis.
-/

/-- Quantum relative entropy, returning ENNReal.
    D(ρ‖σ) = +∞ when supp(ρ) ⊄ supp(σ), matching the standard definition.
    Unconditional — no support hypothesis needed.

    When σ has full rank (all eigenvalues positive), this equals
    ENNReal.ofReal (relativeEntropyReal ρ σ).

    **Support condition**: The definition uses an eigenvalue-based condition
    (basis-dependent in appearance, but provably equivalent to the basis-independent
    kernel condition):
      eigenvalue form : ∀ i, eigenvaluesOf σ i = 0 → diagonalOfRhoInSigmaBasis ρ σ i = 0
      kernel form     : ∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0  (ker σ ⊆ ker ρ)

    These are equivalent for PSD matrices; see `eigenvalue_support_iff_ker_sub`.
    The eigenvalue form is used internally for computational purposes; the kernel form
    is more natural mathematically. Both are available via the bridge theorems:
      `relativeEntropy_eq_ofReal_of_ker_sub` and
      `relativeEntropy_eq_top_of_not_ker_sub`. -/
noncomputable def relativeEntropy {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) : ENNReal :=
  -- Case split on support containment:
  -- supp(ρ) ⊆ supp(σ) iff every zero eigenvalue of σ is also a zero of ρ in that eigenspace.
  -- When supp(ρ) ⊆ supp(σ): D(ρ‖σ) is finite (relativeEntropyReal ρ σ ≥ 0 by Klein).
  -- When supp(ρ) ⊄ supp(σ): D(ρ‖σ) = +∞ by convention.
  if ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
      diagonalOfRhoInSigmaBasis ρ σ i = 0
  then ENNReal.ofReal (relativeEntropyReal ρ σ)
  else ⊤

/-- The ENNReal quantum relative entropy is non-negative (trivially, as ENNReal ≥ 0). -/
theorem relativeEntropy_nonneg {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    0 ≤ relativeEntropy ρ σ :=
  zero_le

/-- Classical KL divergence is non-negative under the support condition
    (generalizes `classicalRelEntropy_nonneg` which requires full rank). -/
private theorem classicalRelEntropy_nonneg_support {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n)
    (h_supp : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0) :
    0 ≤ classicalRelEntropy ρ σ := by
  unfold classicalRelEntropy
  apply Math.ClassicalEntropy.log_sum_inequality
  · exact diagonalOfRhoInSigmaBasis_nonneg ρ σ
  · exact (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec σ).1
  · exact diagonalOfRhoInSigmaBasis_sum ρ σ
  · exact (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec σ).2.1
  · -- Support condition (contrapositive): r_i > 0 → μ_i > 0
    intro i hri
    by_contra h
    push Not at h
    have hμ := (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec σ).1 i
    have hμ_zero : InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 :=
      le_antisymm h hμ
    linarith [h_supp i hμ_zero]

/-- The classical relative entropy equals -H(diag) - Tr(ρ log σ) under support condition
    (generalizes `classicalRelEntropy_eq` which requires full rank). -/
private theorem classicalRelEntropy_eq_support {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n)
    (h_supp : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0) :
    classicalRelEntropy ρ σ =
      -diagonalEntropy ρ σ - traceProductLogSigma ρ σ := by
  unfold classicalRelEntropy diagonalEntropy
    Math.ClassicalEntropy.shannonEntropy Math.ClassicalEntropy.entropyTerm
  unfold traceProductLogSigma
  simp only
  have h_split : ∑ j, (if diagonalOfRhoInSigmaBasis ρ σ j = 0 then 0
      else diagonalOfRhoInSigmaBasis ρ σ j *
        Real.log (diagonalOfRhoInSigmaBasis ρ σ j /
          InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j)) =
    (∑ j, (if diagonalOfRhoInSigmaBasis ρ σ j = 0 then 0
        else diagonalOfRhoInSigmaBasis ρ σ j *
          Real.log (diagonalOfRhoInSigmaBasis ρ σ j))) -
    ∑ j, diagonalOfRhoInSigmaBasis ρ σ j *
      Real.log (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j) := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext j
    by_cases hrj : diagonalOfRhoInSigmaBasis ρ σ j = 0
    · simp [hrj]
    · simp only [hrj, ↓reduceIte]
      have hμj : InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j ≠ 0 := by
        intro hμ0
        exact hrj (h_supp j hμ0)
      rw [Real.log_div hrj hμj]
      ring
  rw [h_split]
  have h_neg : (-∑ i, (if diagonalOfRhoInSigmaBasis ρ σ i = 0 then 0
        else -diagonalOfRhoInSigmaBasis ρ σ i *
          Real.log (diagonalOfRhoInSigmaBasis ρ σ i))) =
      ∑ i, (if diagonalOfRhoInSigmaBasis ρ σ i = 0 then 0
        else diagonalOfRhoInSigmaBasis ρ σ i *
          Real.log (diagonalOfRhoInSigmaBasis ρ σ i)) := by
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext i
    by_cases h : diagonalOfRhoInSigmaBasis ρ σ i = 0 <;> simp [h]
  rw [h_neg]

/-- Klein's inequality under support condition: relative entropy is non-negative
    whenever the eigenvalue support condition holds. -/
theorem klein_inequality_support {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n)
    (h_supp : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0) :
    0 ≤ relativeEntropyReal ρ σ := by
  have h_classical_eq := classicalRelEntropy_eq_support ρ σ h_supp
  have h_classical_nonneg := classicalRelEntropy_nonneg_support ρ σ h_supp
  have h_entropy_ineq := vonNeumannEntropy_le_diagonalEntropy ρ σ
  calc relativeEntropyReal ρ σ
      = -InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ -
          traceProductLogSigma ρ σ := rfl
    _ ≥ -diagonalEntropy ρ σ - traceProductLogSigma ρ σ := by linarith only [h_entropy_ineq]
    _ = classicalRelEntropy ρ σ := h_classical_eq.symm
    _ ≥ 0 := h_classical_nonneg

/-- Extract the two scalar equalities needed in the equality case of Klein's inequality. -/
private theorem relativeEntropyReal_nonpos_data {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n)
    (h_supp : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0)
    (h_le : relativeEntropyReal ρ σ ≤ 0) :
    classicalRelEntropy ρ σ = 0 ∧
      InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ = diagonalEntropy ρ σ := by
  have h_ge := klein_inequality_support ρ σ h_supp
  have h_eq : relativeEntropyReal ρ σ = 0 := le_antisymm h_le h_ge
  have h_class_eq := classicalRelEntropy_eq_support ρ σ h_supp
  have h_class_nonneg := classicalRelEntropy_nonneg_support ρ σ h_supp
  have h_chain : relativeEntropyReal ρ σ ≥ classicalRelEntropy ρ σ := by
    calc relativeEntropyReal ρ σ
        = -InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ -
            traceProductLogSigma ρ σ := rfl
      _ ≥ -diagonalEntropy ρ σ - traceProductLogSigma ρ σ := by
          linarith [vonNeumannEntropy_le_diagonalEntropy ρ σ]
      _ = classicalRelEntropy ρ σ := h_class_eq.symm
  have h_class_zero : classicalRelEntropy ρ σ = 0 :=
    le_antisymm (by linarith only [h_chain, h_eq]) h_class_nonneg
  have h_entropy_eq :
      InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ = diagonalEntropy ρ σ := by
    have hv : -InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ -
        traceProductLogSigma ρ σ = 0 := h_eq
    have hd : -diagonalEntropy ρ σ - traceProductLogSigma ρ σ = 0 := by
      linarith only [h_class_eq, h_class_zero]
    linarith only [hv, hd]
  exact ⟨h_class_zero, h_entropy_eq⟩

/-- **Support-sum saturation for a vanishing reverse KL sum.** If `r, μ` are subprobability
    weights (`r` a probability vector on the finite support `S`) whose reverse KL sum
    `∑_{S} rⱼ log(μⱼ/rⱼ)` vanishes, then `μ` also puts full mass on `S`. This is the concavity
    half of the KL-equality argument, isolated so the main proof reads as a composition. -/
private lemma klSupport_muSum_eq_one {n : ℕ} (r μ : Fin n → ℝ)
    (S : Finset (Fin n)) (hS_mem : ∀ i, i ∈ S ↔ r i ≠ 0)
    (hr_nonneg : ∀ i, 0 ≤ r i) (hμ_nonneg : ∀ i, 0 ≤ μ i)
    (hμ_sum : ∑ i, μ i = 1)
    (h_supp_pos : ∀ i, r i > 0 → μ i > 0)
    (hS_r_sum : ∑ j ∈ S, r j = 1)
    (h_reversed : ∑ j ∈ S, r j * Real.log (μ j / r j) = 0) :
    ∑ j ∈ S, μ j = 1 := by
  by_contra h_ne
  have hS_μ_le : ∑ j ∈ S, μ j ≤ 1 := by
    calc ∑ j ∈ S, μ j
        ≤ ∑ j, μ j :=
          Finset.sum_le_univ_sum_of_nonneg (fun i => hμ_nonneg i)
      _ = 1 := hμ_sum
  have hS_μ_lt : ∑ j ∈ S, μ j < 1 :=
    lt_of_le_of_ne hS_μ_le h_ne
  have hconcave : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have h_in_dom : ∀ j ∈ S, μ j / r j ∈ Set.Ioi 0 := by
    intro j hj
    have hrj := (hS_mem j).mp hj
    have hrj_pos := lt_of_le_of_ne (hr_nonneg j) (Ne.symm hrj)
    exact div_pos (h_supp_pos j hrj_pos) hrj_pos
  have h_wt_nonneg : ∀ j ∈ S, 0 ≤ r j :=
    fun j _ => hr_nonneg j
  have h_log_lt : Real.log (∑ j ∈ S, μ j) < 0 :=
    Real.log_neg (by
      have hSne : S.Nonempty := by
        by_contra h_empty
        simp only [Finset.not_nonempty_iff_eq_empty] at h_empty
        rw [h_empty] at hS_r_sum; simp at hS_r_sum
      obtain ⟨j, hj⟩ := hSne
      apply Finset.sum_pos' (fun i _ => hμ_nonneg i)
      exact ⟨j, hj, h_supp_pos j
        (lt_of_le_of_ne (hr_nonneg j) (Ne.symm ((hS_mem j).mp hj)))⟩
    ) hS_μ_lt
  have h_mul_eq : ∑ j ∈ S, r j * (μ j / r j) = ∑ j ∈ S, μ j := by
    apply Finset.sum_congr rfl; intro j hj
    have hrj := (hS_mem j).mp hj
    field_simp
  have h_ineq : ∑ j ∈ S, r j * Real.log (μ j / r j) ≤
      Real.log (∑ j ∈ S, μ j) := by
    have hJ := hconcave.le_map_sum h_wt_nonneg hS_r_sum h_in_dom
    simp only [smul_eq_mul] at hJ
    rw [h_mul_eq] at hJ
    linarith [hJ]
  linarith [h_ineq, h_log_lt, h_reversed]

/-- **KL divergence vanishes ⟹ agreement on the support.** Under the support condition, if the
    reverse KL sum over `S` vanishes then `r` and `μ` coincide on `S`. This is the strict-concavity
    equality case of Jensen for `log`, isolated from the main proof. -/
private lemma klSupport_eq_on_support {n : ℕ} (r μ : Fin n → ℝ)
    (S : Finset (Fin n)) (hS_mem : ∀ i, i ∈ S ↔ r i ≠ 0)
    (hr_nonneg : ∀ i, 0 ≤ r i)
    (h_supp_pos : ∀ i, r i > 0 → μ i > 0)
    (hS_r_sum : ∑ j ∈ S, r j = 1)
    (hS_μ_sum : ∑ j ∈ S, μ j = 1)
    (h_reversed : ∑ j ∈ S, r j * Real.log (μ j / r j) = 0) :
    ∀ i ∈ S, r i = μ i := by
  intro i hi_in_S
  have hri_ne : r i ≠ 0 := (hS_mem i).mp hi_in_S
  have hri_pos : 0 < r i :=
    lt_of_le_of_ne (hr_nonneg i) (Ne.symm hri_ne)
  have hμi_pos : 0 < μ i := h_supp_pos i hri_pos
  have hstrict := strictConcaveOn_log_Ioi
  have h_in_dom : ∀ j ∈ S, μ j / r j ∈ Set.Ioi (0 : ℝ) := by
    intro j hj
    have hrj := (hS_mem j).mp hj
    exact div_pos (h_supp_pos j
      (lt_of_le_of_ne (hr_nonneg j) (Ne.symm hrj)))
      (lt_of_le_of_ne (hr_nonneg j) (Ne.symm hrj))
  have h_wt_nonneg : ∀ j ∈ S, 0 ≤ r j :=
    fun j _ => hr_nonneg j
  have h_weighted_sum_eq_one : ∑ j ∈ S, r j • (μ j / r j) = 1 := by
    have hcancel : ∑ j ∈ S, r j • (μ j / r j) = ∑ j ∈ S, μ j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [smul_eq_mul]
      have hrj := (hS_mem j).mp hj
      field_simp
    rw [hcancel, hS_μ_sum]
  have h_lhs_zero : Real.log (∑ j ∈ S, r j • (μ j / r j)) = 0 := by
    rw [h_weighted_sum_eq_one, Real.log_one]
  have h_rhs_zero :
      ∑ j ∈ S, r j • Real.log (μ j / r j) = 0 := by
    simp only [smul_eq_mul]; exact h_reversed
  have h_jensen_eq :
      Real.log (∑ j ∈ S, r j • (μ j / r j)) =
        ∑ j ∈ S, r j • Real.log (μ j / r j) := by
    rw [h_lhs_zero, h_rhs_zero]
  have h_all_eq :=
    (hstrict.map_sum_eq_iff' h_wt_nonneg hS_r_sum h_in_dom).mp
      h_jensen_eq
  have h_ratio_eq := h_all_eq i hi_in_S hri_ne
  rw [h_weighted_sum_eq_one] at h_ratio_eq
  linarith [div_eq_one_iff_eq (ne_of_gt hri_pos) |>.mp h_ratio_eq]

/-- Vanishing classical KL divergence forces the diagonal distribution to equal the
    eigenvalue distribution of `σ`. -/
private theorem classicalRelEntropy_zero_implies_diagonal_eq_eigenvalues {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n)
    (h_supp : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0)
    (h_class_zero : classicalRelEntropy ρ σ = 0) :
    ∀ i, diagonalOfRhoInSigmaBasis ρ σ i = InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i := by
  set r := diagonalOfRhoInSigmaBasis ρ σ
  set μ := InfoTheory.VonNeumannEntropy.eigenvaluesOf σ
  have hr_nonneg := diagonalOfRhoInSigmaBasis_nonneg ρ σ
  have hμ_nonneg := (eigenvaluesOf_spec σ).1
  have hr_sum := diagonalOfRhoInSigmaBasis_sum ρ σ
  have hμ_sum := (eigenvaluesOf_spec σ).2.1
  have h_r_eq_μ : ∀ i, r i = μ i := by
    let S := Finset.univ.filter (fun i => r i ≠ 0)
    have hS_mem : ∀ i, i ∈ S ↔ r i ≠ 0 := fun i => by simp [S]
    have h_supp_pos : ∀ i, r i > 0 → μ i > 0 := by
      intro i hri
      by_contra h
      push Not at h
      have := le_antisymm h (hμ_nonneg i)
      linarith [h_supp i this]
    have h_kl_eq : ∑ j ∈ S, r j * Real.log (r j / μ j) = 0 := by
      have h_class_as_S :
          classicalRelEntropy ρ σ =
            ∑ j ∈ S, r j * Real.log (r j / μ j) := by
        change ∑ j, (if r j = 0 then 0
          else r j * Real.log (r j / μ j)) =
          ∑ j ∈ S, r j * Real.log (r j / μ j)
        trans (∑ j ∈ S,
          (if r j = 0 then (0 : ℝ) else r j * Real.log (r j / μ j)) +
          ∑ j ∈ Finset.univ \ S,
          (if r j = 0 then (0 : ℝ) else r j * Real.log (r j / μ j)))
        · rw [← Finset.sum_union (Finset.disjoint_sdiff)]
          apply Finset.sum_congr
          · ext x; simp [S]
          · intros; rfl
        · have h1 : ∀ j ∈ S,
              (if r j = 0 then (0 : ℝ)
               else r j * Real.log (r j / μ j)) =
              r j * Real.log (r j / μ j) := by
            intro j hj; simp [(hS_mem j).mp hj]
          have h2 : ∑ j ∈ Finset.univ \ S,
              (if r j = 0 then (0 : ℝ)
               else r j * Real.log (r j / μ j)) = 0 := by
            apply Finset.sum_eq_zero; intro j hj
            simp only [S, Finset.mem_sdiff, Finset.mem_filter,
              Finset.mem_univ, true_and, not_not] at hj
            simp [hj]
          rw [Finset.sum_congr rfl h1, h2, add_zero]
      linarith only [h_class_as_S, h_class_zero]
    have h_reversed : ∑ j ∈ S, r j * Real.log (μ j / r j) = 0 := by
      have h_neg : ∑ j ∈ S, r j * Real.log (r j / μ j) =
          -(∑ j ∈ S, r j * Real.log (μ j / r j)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hrj : r j ≠ 0 := (hS_mem j).mp hj
        have hrj_pos : 0 < r j :=
          lt_of_le_of_ne (hr_nonneg j) (Ne.symm hrj)
        have hμj_pos : 0 < μ j := h_supp_pos j hrj_pos
        rw [Real.log_div hrj (ne_of_gt hμj_pos),
            Real.log_div (ne_of_gt hμj_pos) hrj]
        ring
      linarith only [h_neg, h_kl_eq]
    have hS_r_sum : ∑ j ∈ S, r j = 1 := by
      have h_full : ∑ j, r j =
          ∑ j ∈ S, r j + ∑ j ∈ (Finset.univ \ S), r j := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff)]
        congr 1; ext x
        simp only [Finset.mem_union, Finset.mem_sdiff,
          Finset.mem_univ, true_and]; tauto
      rw [hr_sum] at h_full
      have : ∑ j ∈ (Finset.univ \ S), r j = 0 := by
        apply Finset.sum_eq_zero; intro j hj
        simp only [S, Finset.mem_sdiff, Finset.mem_filter,
          Finset.mem_univ, true_and, not_not] at hj
        exact hj
      linarith only [h_full, this]
    have hS_μ_sum : ∑ j ∈ S, μ j = 1 :=
      klSupport_muSum_eq_one r μ S hS_mem hr_nonneg hμ_nonneg hμ_sum
        h_supp_pos hS_r_sum h_reversed
    have hμ_zero_outside : ∀ j, j ∉ S → μ j = 0 := by
      intro j hj
      have h1 : ∑ k ∈ (Finset.univ \ S), μ k = 0 := by
        have : ∑ k, μ k =
            ∑ k ∈ S, μ k + ∑ k ∈ (Finset.univ \ S), μ k := by
          rw [← Finset.sum_union (Finset.disjoint_sdiff)]
          congr 1; ext x
          simp only [Finset.mem_union, Finset.mem_sdiff,
            Finset.mem_univ, true_and]; tauto
        rw [hμ_sum, hS_μ_sum] at this; linarith only [this]
      have hj_sdiff : j ∈ Finset.univ \ S := by
        simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using hj
      exact le_antisymm
        (Finset.single_le_sum (fun k _ => hμ_nonneg k) hj_sdiff
          |>.trans (le_of_eq h1))
        (hμ_nonneg j)
    intro i
    by_cases hi_in_S : i ∈ S
    · exact klSupport_eq_on_support r μ S hS_mem hr_nonneg h_supp_pos hS_r_sum
        hS_μ_sum h_reversed i hi_in_S
    · have hri_zero : r i = 0 := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
          not_not] at hi_in_S
        exact hi_in_S
      have hμi_zero : μ i = 0 := hμ_zero_outside i hi_in_S
      rw [hri_zero, hμi_zero]
  intro i
  simpa [r, μ] using h_r_eq_μ i

/-- **Row-wise Jensen saturation for a doubly stochastic mixture.** If a doubly stochastic `D`
    maps the nonnegative vector `p` to `q` (`q i = ∑ⱼ Dᵢⱼ pⱼ`) with no loss of Shannon entropy
    (`∑ negMulLog q = ∑ negMulLog p`), then Jensen is tight in every row:
    `negMulLog (qᵢ) = ∑ⱼ Dᵢⱼ · negMulLog (pⱼ)`. -/
private lemma doublyStochastic_negMulLog_row_eq {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n → ℝ)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_row : ∀ i, ∑ j, D i j = 1)
    (hD_col : ∀ j, ∑ i, D i j = 1)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_eq : ∀ i, q i = ∑ j, D i j * p j)
    (h_entropy_eq : ∑ i, Real.negMulLog (q i) = ∑ j, Real.negMulLog (p j)) :
    ∀ i, Real.negMulLog (q i) = ∑ j, D i j * Real.negMulLog (p j) := by
  have h_sum_diff :
      ∑ i, (Real.negMulLog (q i) -
        ∑ j, D i j * Real.negMulLog (p j)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hcol_sum : ∑ i, ∑ j, D i j * Real.negMulLog (p j) =
        ∑ j, Real.negMulLog (p j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [← Finset.sum_mul, hD_col j, one_mul]
    rw [hcol_sum, h_entropy_eq, sub_self]
  have h_each_nonneg : ∀ i,
      Real.negMulLog (q i) ≥
        ∑ j, D i j * Real.negMulLog (p j) := by
    intro i
    have hJensen := Real.concaveOn_negMulLog.le_map_sum
      (fun j _ => hD_nonneg i j) (hD_row i)
      (fun j _ => hp_nonneg j : ∀ j, j ∈ Finset.univ →
        p j ∈ Set.Ici (0 : ℝ))
    simp only [smul_eq_mul] at hJensen
    rw [← hq_eq i] at hJensen
    linarith [hJensen]
  intro i
  have h_all_zero :=
    Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => by linarith [h_each_nonneg j])
      |>.mp h_sum_diff
  linarith [h_all_zero i (Finset.mem_univ i)]

/-- **Strict-concavity equality case for a doubly stochastic mixture.** If Jensen is tight in every
    row (as produced by `doublyStochastic_negMulLog_row_eq`), then wherever a weight `Dᵢⱼ` is
    nonzero the corresponding source value equals the mixed value: `pⱼ = qᵢ`. -/
private lemma doublyStochastic_negMulLog_col_eq_imp {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n → ℝ)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_row : ∀ i, ∑ j, D i j = 1)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_eq : ∀ i, q i = ∑ j, D i j * p j)
    (h_row_eq : ∀ i, Real.negMulLog (q i) =
      ∑ j, D i j * Real.negMulLog (p j)) :
    ∀ i j, D i j ≠ 0 → p j = q i := by
  intro i j hDij
  have h_smul_eq :
      Real.negMulLog (∑ k ∈ Finset.univ, D i k • p k) =
        ∑ k ∈ Finset.univ, D i k • Real.negMulLog (p k) := by
    simp only [smul_eq_mul]; rw [← hq_eq i]; exact h_row_eq i
  have h_all_eq :=
    (Real.strictConcaveOn_negMulLog.map_sum_eq_iff'
      (fun k _ => hD_nonneg i k) (hD_row i)
      (fun k _ => hp_nonneg k : ∀ k, k ∈ Finset.univ →
        p k ∈ Set.Ici (0 : ℝ))).mp h_smul_eq
  have hkey := h_all_eq j (Finset.mem_univ j) hDij
  simp only [smul_eq_mul] at hkey; rw [← hq_eq i] at hkey
  exact hkey

/-- **A unitary conjugation that diagonalises `ρ` to `σ`'s spectrum forces `ρ = σ`.** If `V_σ`
    diagonalises `σ` to `diag μ`, the same conjugation sends `ρ` to `W · diag(ev_ρ) · W†`, and the
    key cancellation `Wᵢⱼ · ev_ρ ⱼ = Wᵢⱼ · μ ᵢ` holds (with `W` unitary), then `V_σ ρ V_σ†` is
    itself `diag μ`, hence `ρ = σ` after conjugating back. -/
private lemma conjDiag_imp_densityOp_eq {n : ℕ} (ρ σ : DensityOp n)
    (V_σ W : Matrix (Fin n) (Fin n) ℂ) (ev_ρ μ : Fin n → ℝ)
    (hV_σ_L : V_σ† * V_σ = 1)
    (hW_W_adj : W * W† = 1)
    (hσ_diag : V_σ * σ.toOp * V_σ† = Matrix.diagonal (fun i => (μ i : ℂ)))
    (h_VρV : V_σ * ρ.toOp * V_σ† =
      W * Matrix.diagonal (fun j => (ev_ρ j : ℂ)) * W†)
    (h_key_product : ∀ i j, W i j * (ev_ρ j : ℂ) = W i j * (μ i : ℂ)) :
    ρ = σ := by
  have h_diag_mul_entry : ∀ i x,
      (∑ x_1, W i x_1 *
        (if x_1 = x then (ev_ρ x_1 : ℂ) else 0)) =
          W i x * (ev_ρ x : ℂ) := by
    intro i x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hyx
      simp [hyx]
    · intro hx
      exact (hx (Finset.mem_univ x)).elim
  have h_VρV_eq_diag :
      V_σ * ρ.toOp * V_σ† =
        Matrix.diagonal (fun i => (μ i : ℂ)) := by
    rw [h_VρV]
    ext i k
    simp only [Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply]
    simp_rw [h_diag_mul_entry i]
    have h_factor :
        ∑ x, W i x * (ev_ρ x : ℂ) * star (W k x) =
          ∑ x, (μ i : ℂ) * (W i x * star (W k x)) := by
      apply Finset.sum_congr rfl; intro x _
      rw [h_key_product i x]; ring
    rw [h_factor]
    rw [← Finset.mul_sum]
    have h_WW : ∑ x, W i x * star (W k x) = if i = k then 1 else 0 := by
      have hWWik : (W * W†) i k = if i = k then (1 : ℂ) else 0 := by
        rw [hW_W_adj]; simp [Matrix.one_apply]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hWWik
      convert hWWik using 1
    rw [h_WW]
    split_ifs with hik
    · simp [hik]
    · simp
  have h_conj_eq :
      V_σ * ρ.toOp * V_σ† = V_σ * σ.toOp * V_σ† := by
    rw [h_VρV_eq_diag, hσ_diag]
  have h_toOp_eq : ρ.toOp = σ.toOp := by
    calc ρ.toOp
        = 1 * ρ.toOp * 1 := by simp
      _ = (V_σ† * V_σ) * ρ.toOp * (V_σ† * V_σ) := by rw [hV_σ_L]
      _ = V_σ† * (V_σ * ρ.toOp * V_σ†) * V_σ := by
          simp only [Matrix.mul_assoc]
      _ = V_σ† * (V_σ * σ.toOp * V_σ†) * V_σ := by rw [h_conj_eq]
      _ = (V_σ† * V_σ) * σ.toOp * (V_σ† * V_σ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * σ.toOp * 1 := by rw [hV_σ_L]
      _ = σ.toOp := by simp
  exact DensityOp.ext h_toOp_eq

/-- **Own-eigenbasis conjugation diagonalises a density operator.** Conjugating `σ` by its own
    eigenbasis `eigenbasisOf σ` produces the diagonal matrix of its eigenvalues. -/
private lemma eigenbasisOf_conj_self_eq_diagonal {n : ℕ} (σ : DensityOp n) :
    eigenbasisOf σ * σ.toOp * (eigenbasisOf σ)† =
      Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) := by
  have hV_σ_R : eigenbasisOf σ * (eigenbasisOf σ)† = 1 := eigenbasisOf_unitary_right σ
  have hσ_decomp' : σ.toOp =
      (eigenbasisOf σ)† * Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) *
        eigenbasisOf σ :=
    (Classical.choose_spec (eigenvaluesOf_spec σ).2.2.2).2.2
  calc eigenbasisOf σ * σ.toOp * (eigenbasisOf σ)†
      = eigenbasisOf σ * ((eigenbasisOf σ)† *
          Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) * eigenbasisOf σ) *
          (eigenbasisOf σ)† := by rw [hσ_decomp']
    _ = (eigenbasisOf σ * (eigenbasisOf σ)†) *
          Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) *
          (eigenbasisOf σ * (eigenbasisOf σ)†) := by simp only [Matrix.mul_assoc]
    _ = 1 * Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) * 1 := by rw [hV_σ_R]
    _ = Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) := by simp

/-- Once the diagonal distribution matches `σ`'s eigenvalues and the entropy gap closes,
    the density operators themselves coincide. -/
private theorem diagonal_eq_eigenvalues_and_entropy_eq_imply_eq {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n)
    (h_diag_eq : ∀ i,
      diagonalOfRhoInSigmaBasis ρ σ i = InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i)
    (h_entropy_eq : InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ = diagonalEntropy ρ σ) :
    ρ = σ := by
  set V_σ := eigenbasisOf σ with hV_σ_def
  set V_ρ := eigenbasisOf ρ with hV_ρ_def
  set μ := InfoTheory.VonNeumannEntropy.eigenvaluesOf σ with hμ_def
  set ev_ρ := eigenvaluesOf ρ with hev_ρ_def
  have h_diag_eq_μ : ∀ i, diagonalOfRhoInSigmaBasis ρ σ i = μ i := by
    intro i
    simpa [μ] using h_diag_eq i
  have hV_σ_L : V_σ† * V_σ = 1 := eigenbasisOf_unitary_left σ
  have hV_σ_R : V_σ * V_σ† = 1 := eigenbasisOf_unitary_right σ
  have hV_ρ_L : V_ρ† * V_ρ = 1 := eigenbasisOf_unitary_left ρ
  have hV_ρ_R : V_ρ * V_ρ† = 1 := eigenbasisOf_unitary_right ρ
  have hρ_decomp := (Classical.choose_spec
    (eigenvaluesOf_spec ρ).2.2.2).2.2
  have hσ_decomp := (Classical.choose_spec
    (eigenvaluesOf_spec σ).2.2.2).2.2
  have hev_nonneg := (eigenvaluesOf_spec ρ).1
  have hev_sum := (eigenvaluesOf_spec ρ).2.1
  set W := V_σ * V_ρ† with hW_def
  have hW_W_adj : W * W† = 1 := by
    simp only [hW_def, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc V_σ * V_ρ† * (V_ρ * V_σ†)
        = V_σ * (V_ρ† * V_ρ) * V_σ† := by
          simp only [Matrix.mul_assoc]
      _ = V_σ * 1 * V_σ† := by rw [hV_ρ_L]
      _ = V_σ * V_σ† := by simp only [Matrix.mul_one]
      _ = 1 := hV_σ_R
  let D' : Matrix (Fin n) (Fin n) ℝ := fun i j => Complex.normSq (W i j)
  have hD'_nonneg : ∀ i j, 0 ≤ D' i j := fun i j =>
    Complex.normSq_nonneg (W i j)
  have hD'_row : ∀ i, ∑ j, D' i j = 1 := by
    intro i
    have h_row : ∑ j, Complex.normSq (W i j) =
        ((W * W†) i i).re := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl; intro j _
      simp only [Complex.normSq_apply, Complex.mul_re,
        Complex.star_def, Complex.conj_re, Complex.conj_im]; ring
    rw [h_row, hW_W_adj]; simp
  have hW_adj_W : W† * W = 1 := by
    simp only [hW_def, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc V_ρ * V_σ† * (V_σ * V_ρ†)
        = V_ρ * (V_σ† * V_σ) * V_ρ† := by
          simp only [Matrix.mul_assoc]
      _ = V_ρ * 1 * V_ρ† := by rw [hV_σ_L]
      _ = V_ρ * V_ρ† := by simp only [Matrix.mul_one]
      _ = 1 := hV_ρ_R
  have hD'_col : ∀ j, ∑ i, D' i j = 1 := by
    intro j
    have h_col : ∑ i, Complex.normSq (W i j) =
        ((W† * W) j j).re := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _
      simp only [Complex.normSq_apply, Complex.mul_re,
        Complex.star_def, Complex.conj_re, Complex.conj_im]; ring
    rw [h_col, hW_adj_W]; simp
  have hρ_decomp' : ρ.toOp =
      V_ρ† * Matrix.diagonal (fun j => (ev_ρ j : ℂ)) * V_ρ := by
    have hV_ρ_eq : V_ρ = eigenbasisOf ρ := rfl
    rw [hV_ρ_eq]; exact hρ_decomp
  have h_VρV :
      V_σ * ρ.toOp * V_σ† =
        W * Matrix.diagonal (fun j => (ev_ρ j : ℂ)) * W† := by
    rw [hρ_decomp', hW_def]
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have h_diag_mul_entry : ∀ i x,
      (∑ x_1, W i x_1 *
        (if x_1 = x then (ev_ρ x_1 : ℂ) else 0)) =
          W i x * (ev_ρ x : ℂ) := by
    intro i x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hyx
      simp [hyx]
    · intro hx
      exact (hx (Finset.mem_univ x)).elim
  have h_D'ev_eq : ∀ i,
      ∑ j, D' i j * ev_ρ j = diagonalOfRhoInSigmaBasis ρ σ i := by
    intro i
    change _ = ((V_σ * ρ.toOp * V_σ†) i i).re
    rw [h_VρV]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply]
    have h_sum_eq :
        (∑ x, (∑ x_1, W i x_1 *
          (if x_1 = x then (ev_ρ x_1 : ℂ) else 0)) *
          star (W i x)) =
        ∑ x, W i x * (ev_ρ x : ℂ) * star (W i x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [h_diag_mul_entry i x]
    rw [h_sum_eq, Complex.re_sum]
    apply Finset.sum_congr rfl; intro x _
    show D' i x * ev_ρ x = (W i x * (ev_ρ x : ℂ) * star (W i x)).re
    simp only [D', Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]; ring
  have h_D'ev_eq_μ : ∀ i, ∑ j, D' i j * ev_ρ j = μ i := by
    intro i; rw [h_D'ev_eq i, h_diag_eq_μ i]
  have hSρ_eq_Sσ :
      vonNeumannEntropy ρ = vonNeumannEntropy σ := by
    have : diagonalEntropy ρ σ = vonNeumannEntropy σ := by
      unfold diagonalEntropy vonNeumannEntropy
        Math.ClassicalEntropy.shannonEntropy
      congr 1; ext i
      rw [show diagonalOfRhoInSigmaBasis ρ σ i = μ i from h_diag_eq_μ i]
    linarith [h_entropy_eq]
  have h_entropy_sum_eq :
      ∑ i, Real.negMulLog (μ i) = ∑ j, Real.negMulLog (ev_ρ j) := by
    have h1 : ∑ i, Real.negMulLog (μ i) = vonNeumannEntropy σ := by
      unfold vonNeumannEntropy Math.ClassicalEntropy.shannonEntropy
      congr 1; ext i
      exact (Math.ClassicalEntropy.entropyTerm_eq_negMulLog
        (μ i) ((eigenvaluesOf_spec σ).1 i)).symm
    have h3 : ∑ j, Real.negMulLog (ev_ρ j) = vonNeumannEntropy ρ := by
      unfold vonNeumannEntropy Math.ClassicalEntropy.shannonEntropy
      congr 1; ext j
      exact (Math.ClassicalEntropy.entropyTerm_eq_negMulLog
        (ev_ρ j) (hev_nonneg j)).symm
    rw [h1, h3, hSρ_eq_Sσ]
  have h_row_jensen : ∀ i,
      Real.negMulLog (μ i) =
        ∑ j, D' i j * Real.negMulLog (ev_ρ j) :=
    doublyStochastic_negMulLog_row_eq D' ev_ρ μ hD'_nonneg hD'_row hD'_col
      hev_nonneg (fun i => (h_D'ev_eq_μ i).symm) h_entropy_sum_eq
  have h_ev_eq_when_W_ne : ∀ i j, W i j ≠ 0 → ev_ρ j = μ i := by
    intro i j hWij
    have hD'ij_ne : D' i j ≠ 0 := by
      simpa only [D'] using ne_of_gt (Complex.normSq_pos.mpr hWij)
    exact doublyStochastic_negMulLog_col_eq_imp D' ev_ρ μ hD'_nonneg hD'_row
      hev_nonneg (fun i => (h_D'ev_eq_μ i).symm) h_row_jensen i j hD'ij_ne
  have h_key_product : ∀ i j,
      W i j * (ev_ρ j : ℂ) = W i j * (μ i : ℂ) := by
    intro i j
    by_cases hWij : W i j = 0
    · simp [hWij]
    · congr 1
      exact_mod_cast h_ev_eq_when_W_ne i j hWij
  have h_VσσVσ :
      V_σ * σ.toOp * V_σ† =
        Matrix.diagonal (fun i => (μ i : ℂ)) :=
    eigenbasisOf_conj_self_eq_diagonal σ
  exact conjDiag_imp_densityOp_eq ρ σ V_σ W ev_ρ μ hV_σ_L hW_W_adj h_VσσVσ h_VρV
    h_key_product

/-- If the support condition holds and `relativeEntropyReal ρ σ ≤ 0`, then ρ = σ. -/
private theorem relativeEntropyReal_nonpos_imp_eq {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n)
    (h_supp : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0)
    (h_le : relativeEntropyReal ρ σ ≤ 0) : ρ = σ := by
  obtain ⟨h_class_zero, h_entropy_eq⟩ :=
    relativeEntropyReal_nonpos_data ρ σ h_supp h_le
  have h_diag_eq :=
    classicalRelEntropy_zero_implies_diagonal_eq_eigenvalues ρ σ h_supp h_class_zero
  exact diagonal_eq_eigenvalues_and_entropy_eq_imply_eq ρ σ h_diag_eq h_entropy_eq

/-- **Klein's inequality — equality characterization**: D(ρ‖σ) = 0 if and only if ρ = σ.

    The backward direction (ρ = σ → D = 0) follows from `relativeEntropyReal_self`.
    The forward direction (D = 0 → ρ = σ) uses Jensen equality on the doubly stochastic
    decomposition.

    Note: This is the *equality characterization* (D = 0 ↔ ρ = σ), not the standard
    non-negativity form (D ≥ 0). Non-negativity is trivial for ENNReal
    (see `relativeEntropy_nonneg`); the substantive non-negativity result for the
    ℝ-valued version is `klein_inequality_full_rank`.
    (Nielsen & Chuang Theorem 11.7, Wilde Theorem 11.8.1) -/
theorem klein_inequality {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    relativeEntropy ρ σ = 0 ↔ ρ = σ := by
  constructor
  · -- Hard direction: D(ρ‖σ) = 0 → ρ = σ
    intro h
    unfold relativeEntropy at h
    split_ifs at h with h_supp
    · -- Support condition holds, ENNReal.ofReal (relativeEntropyReal ρ σ) = 0
      -- This means relativeEntropyReal ρ σ ≤ 0
      have h_le : relativeEntropyReal ρ σ ≤ 0 := by
        by_contra h_pos
        push Not at h_pos
        exact absurd h (ne_of_gt (ENNReal.ofReal_pos.mpr h_pos))
      exact relativeEntropyReal_nonpos_imp_eq ρ σ h_supp h_le
    · -- Support condition fails, D = ⊤ ≠ 0
      exact absurd h ENNReal.top_ne_zero
  · -- Easy direction: ρ = σ → D(ρ‖σ) = 0
    intro h
    subst h
    unfold relativeEntropy
    split_ifs
    · -- Support condition holds: show ENNReal.ofReal (relativeEntropyReal ρ ρ) = 0
      rw [relativeEntropyReal_self]
      simp
    · -- Support condition fails: impossible when ρ = σ = ρ
      rename_i h_not
      exact absurd (fun i hi => by rw [diagonalOfRhoInSigmaBasis_self, hi])
        h_not

/-- When supp(ρ) ⊆ supp(σ) (eigenvalue support condition),
    the ENNReal relative entropy equals ofReal of the ℝ version. -/
theorem relativeEntropy_eq_ofReal_of_support {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_support : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0) :
    relativeEntropy ρ σ = ENNReal.ofReal (relativeEntropyReal ρ σ) := by
  -- Unfold the definition and discharge the if-condition.
  simp only [relativeEntropy, ite_eq_left h_support]

/-- When σ has full rank (all eigenvalues positive), the support condition holds trivially
    (no eigenvalue equals 0), so the ENNReal relative entropy equals ofReal of the ℝ version. -/
theorem relativeEntropy_eq_ofReal {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_full : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i > 0) :
    relativeEntropy ρ σ = ENNReal.ofReal (relativeEntropyReal ρ σ) := by
  -- Full rank means no eigenvalue is zero, so the support condition is vacuously true.
  apply relativeEntropy_eq_ofReal_of_support
  intro i hi
  exact absurd hi (ne_of_gt (h_full i))

/-- When supp(ρ) ⊄ supp(σ), the ENNReal relative entropy is +∞. -/
theorem relativeEntropy_eq_top {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_not_support : ¬ ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0) :
    relativeEntropy ρ σ = ⊤ := by
  simp only [relativeEntropy, ite_eq_right h_not_support]

/-!
## Basis-independent support characterization

The support condition used in `relativeEntropy` is equivalent to the
basis-independent kernel condition ker(σ) ⊆ ker(ρ). This section provides bridge
theorems so that users can work with either formulation.
-/

/-- **Kernel condition implies eigenvalue support condition** (one direction of the equivalence).

    If ker(σ) ⊆ ker(ρ) — i.e., `σv = 0 → ρv = 0` for all v — then the eigenvalue-based
    support condition holds: whenever eigenvalue μₗ = 0, the diagonal element
    (V ρ V†)ₗₗ = 0 (where V is the eigenbasis of σ).

    **Proof**: When μₗ = 0, the vector `wₗ = V† eₗ` (where eₗ is the l-th standard basis vector)
    satisfies σ(wₗ) = V† diag(μ)(eₗ) = V† (μₗ eₗ) = 0. So by the kernel condition, ρ(wₗ) = 0.
    Then `(VρV†)ₗₗ = ⟨eₗ | V ρ V† | eₗ⟩ = ⟨wₗ | ρ | wₗ⟩ = 0` because ρ(wₗ) = 0 and
    ρ is PSD (so `⟨v | ρ | v⟩ = 0 ↔ ρv = 0`). -/
theorem eigenvalue_support_of_ker_sub {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_ker : ∀ v : Fin n → ℂ, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    ∀ l, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ l = 0 →
        diagonalOfRhoInSigmaBasis ρ σ l = 0 := by
  intro l hl
  -- V = eigenbasis of σ, with V†V = 1 and VV† = 1
  have hVL : (eigenbasisOf σ)† * (eigenbasisOf σ) = 1 := eigenbasisOf_unitary_left σ
  have hVR : (eigenbasisOf σ) * (eigenbasisOf σ)† = 1 := eigenbasisOf_unitary_right σ
  -- wₗ = (eigenbasisOf σ)† eₗ is killed by σ when μₗ = 0
  -- σ = V† diag(μ) V by spectral decomposition
  have hsd : σ.toOp = (eigenbasisOf σ)† * Matrix.diagonal
      (fun k => (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ k : ℂ)) * (eigenbasisOf σ) :=
    (Classical.choose_spec (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec σ).2.2.2).2.2
  -- σ(V† eₗ) = 0 because the l-th entry of diag(μ)(V V† eₗ) = μₗ eₗ = 0 eₗ = 0
  have h_σ_wl : σ.toOp.mulVec ((eigenbasisOf σ)†.mulVec (Pi.single l 1)) = 0 := by
    conv_lhs => rw [hsd]
    -- Expand: (V† * diag * V) *ᵥ (V† *ᵥ eₗ)
    --       = V† *ᵥ (diag *ᵥ (V *ᵥ (V† *ᵥ eₗ)))
    --       = V† *ᵥ (diag *ᵥ eₗ)   [since V * V† = 1]
    --       = V† *ᵥ (μₗ eₗ) = 0    [since μₗ = 0]
    have hVVadj : (eigenbasisOf σ).mulVec ((eigenbasisOf σ)†.mulVec (Pi.single l 1)) =
        Pi.single l 1 := by
      rw [Matrix.mulVec_mulVec, hVR, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hVVadj]
    -- Goal: V† *ᵥ (diag(μ) *ᵥ eₗ) = 0. Show diag(μ) *ᵥ eₗ = 0 first (μₗ = 0).
    suffices h : (Matrix.diagonal (fun k => (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ k :
        ℂ))).mulVec
        (Pi.single l 1) = 0 by
      rw [h]; exact Matrix.mulVec_zero _
    ext k
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.zero_apply,
               Pi.single_apply, mul_ite, mul_one, mul_zero,
               Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    split_ifs with hkl
    · exact_mod_cast (show InfoTheory.VonNeumannEntropy.eigenvaluesOf σ k = 0 from hkl ▸ hl)
    · rfl
  -- ker condition: ρ(V† eₗ) = 0
  have h_ρ_wl : ρ.toOp.mulVec ((eigenbasisOf σ)†.mulVec (Pi.single l 1)) = 0 :=
    h_ker _ h_σ_wl
  -- (V ρ V†)ₗₗ = 0: the (l,l) entry of V ρ V† is (V (ρ (V† eₗ)))ₗ = (V · 0)ₗ = 0
  unfold diagonalOfRhoInSigmaBasis
  -- Compute: (V * ρ * V†) *ᵥ eₗ = V *ᵥ (ρ *ᵥ (V† *ᵥ eₗ)) = V *ᵥ 0 = 0
  have h_mulvec_zero : (eigenbasisOf σ * ρ.toOp * (eigenbasisOf σ)†).mulVec
      (Pi.single l 1) = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h_ρ_wl, Matrix.mulVec_zero]
  -- The (l,l) entry equals the l-th component of ((V * ρ * V†) *ᵥ eₗ)
  have h_entry_eq : (eigenbasisOf σ * ρ.toOp * (eigenbasisOf σ)†) l l =
      ((eigenbasisOf σ * ρ.toOp * (eigenbasisOf σ)†).mulVec (Pi.single l 1)) l := by
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
               Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h_entry_eq, h_mulvec_zero]
  simp

/-- **Equivalence of support conditions** for PSD matrices.

    The eigenvalue-based support condition is equivalent to the kernel condition
    for density operators (which are positive semidefinite):
      (∀ i, eigenvaluesOf σ i = 0 → diagonalOfRhoInSigmaBasis ρ σ i = 0)
      ↔ (∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0)

    Note: The forward direction (eigenvalue → kernel) is proved in
    `ker_sigma_sub_ker_rho_of_eigenvalue_support`. The reverse direction
    (kernel → eigenvalue) is proved here in `eigenvalue_support_of_ker_sub`.
    This theorem simply combines them into an `Iff`. -/
theorem eigenvalue_support_iff_ker_sub {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    (∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0) ↔
    (∀ v : Fin n → ℂ, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) := by
  constructor
  · -- eigenvalue support → ker containment (proved in KLCoarsening, restated here)
    -- We prove it directly using the same argument as ker_sigma_sub_ker_rho_of_eigenvalue_support.
    intro h_eig v hv
    set V := eigenbasisOf σ
    have hVL : V† * V = 1 := eigenbasisOf_unitary_left σ
    have hVR : V * V† = 1 := eigenbasisOf_unitary_right σ
    have hρ_psd : ρ.toOp.PosSemidef := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
    set w := V.mulVec v
    set M := V * ρ.toOp * V† with hM_def
    have hM_psd : M.PosSemidef := posSemidef_conj_aux ρ.toOp V hρ_psd
    have hsd : σ.toOp = V† * Matrix.diagonal
        (fun k => (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ k : ℂ)) * V :=
      (Classical.choose_spec (InfoTheory.VonNeumannEntropy.eigenvaluesOf_spec σ).2.2.2).2.2
    have h_diagw : (Matrix.diagonal
        (fun k => (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ k : ℂ))).mulVec w = 0 := by
      have h1 : V.mulVec (σ.toOp.mulVec v) = 0 := by rw [hv, Matrix.mulVec_zero]
      have h2 : V * σ.toOp = Matrix.diagonal
          (fun k => (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ k : ℂ)) * V := by
        rw [hsd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hVR, Matrix.one_mul]
      rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec] at h1; exact h1
    have h_coeff : ∀ l, (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ l : ℂ) * w l = 0 := by
      intro l; have := congr_fun h_diagw l
      simp only [Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.zero_apply] at this
      simpa using this
    have h_col_zero : ∀ k l, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ l = 0 → M k l = 0 := by
      intro k l hl
      have h_bound := pos_semidef_off_diag_bound
        (⟨⟨M, hM_psd.isHermitian⟩,
          fun x => hM_psd.re_dotProduct_nonneg x⟩ : Quantum.Operators.PosSemidefOp n) k l
      simp only at h_bound
      have h_Mll_re : (M l l).re = 0 := h_eig l hl
      have : Complex.normSq (M k l) ≤ 0 :=
        le_trans h_bound (by rw [h_Mll_re, mul_zero])
      exact Complex.normSq_eq_zero.mp (le_antisymm this (Complex.normSq_nonneg _))
    have h_Mw : M.mulVec w = 0 := by
      ext k; simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      apply Finset.sum_eq_zero; intro l _
      by_cases hl : InfoTheory.VonNeumannEntropy.eigenvaluesOf σ l = 0
      · rw [h_col_zero k l hl, zero_mul]
      · have hne : (InfoTheory.VonNeumannEntropy.eigenvaluesOf σ l : ℂ) ≠ 0 := by exact_mod_cast hl
        rw [show w l = 0 from (mul_eq_zero.mp (h_coeff l)).resolve_left hne, mul_zero]
    have h_rho_eq : ρ.toOp = V† * M * V := by
      rw [hM_def, Matrix.mul_assoc, Matrix.mul_assoc, hVL, Matrix.mul_one,
          ← Matrix.mul_assoc, hVL, Matrix.one_mul]
    have : ρ.toOp.mulVec v = V†.mulVec (M.mulVec w) := by
      rw [h_rho_eq, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [this, h_Mw, Matrix.mulVec_zero]
  · -- kernel condition → eigenvalue support
    exact eigenvalue_support_of_ker_sub ρ σ

/-- **Basis-independent support**: when ker(σ) ⊆ ker(ρ), the quantum relative entropy
    equals `ENNReal.ofReal (relativeEntropyReal ρ σ)`.

    This is the kernel-condition version of `relativeEntropy_eq_ofReal_of_support`.
    The kernel condition `∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0` is
    basis-independent and equivalent to the eigenvalue support condition by
    `eigenvalue_support_iff_ker_sub`. -/
theorem relativeEntropy_eq_ofReal_of_ker_sub {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_ker : ∀ v : Fin n → ℂ, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    relativeEntropy ρ σ = ENNReal.ofReal (relativeEntropyReal ρ σ) :=
  relativeEntropy_eq_ofReal_of_support ρ σ
    ((eigenvalue_support_iff_ker_sub ρ σ).mpr h_ker)

/-- When ker(σ) ⊄ ker(ρ), the quantum relative entropy is +∞.

    This is the kernel-condition version of `relativeEntropy_eq_top`. -/
theorem relativeEntropy_eq_top_of_not_ker_sub {n : ℕ} [NeZero n] (ρ σ : DensityOp n)
    (h_not_ker : ¬ ∀ v : Fin n → ℂ, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    relativeEntropy ρ σ = ⊤ :=
  relativeEntropy_eq_top ρ σ
    (fun h => h_not_ker ((eigenvalue_support_iff_ker_sub ρ σ).mp h))

end InfoTheory.RelativeEntropy

end
