import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.Basic.Basic
import QCryptLean.Quantum.Operators.Types

/-!
# Variational Data-Processing Basics — perturbed logs and diagonal Peierls-Bogoliubov

This file introduces the perturbed logarithm matrix used in the Holevo-bound
data-processing argument and proves the diagonal Peierls-Bogoliubov estimate
derived from its spectral decomposition.

## Main definitions
- `perturbedLogMatrix`: a spectral-log perturbation matrix built from explicit spectral data
- `densityOpPerturbedLogMatrix`: the zero-on-kernel spectral log of `σ`, plus `diag(h)`

## Main statements
- `perturbedLogMatrix_isHermitian`: the perturbation matrix is Hermitian
- `trace_perturbedLogMatrix_identity`: trace identity for the perturbed logarithm matrix
- `peierls_bogoliubov_diagonal`: diagonal Peierls-Bogoliubov inequality
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-- The perturbation matrix built from explicit matrix data, plus `diag(h)` in the
standard basis.

    This is the algebraic matrix `A = V†·diag(log μ)·V + diag(h)` for arbitrary
    `V : Matrix ...` and `μ h : Fin N → ℝ`, where `log` means Lean's globally
    defined `Real.log` applied entrywise to `μ`. In particular, this definition
    accepts arbitrary real inputs `μ i`: Lean uses the totalized conventions
    `Real.log 0 = 0` and `Real.log (-x) = Real.log x`, so `perturbedLogMatrix`
    is not, in general, the genuine matrix logarithm associated to spectral data
    unless the relevant entries of `μ` are positive and `V` is the unitary
    eigenbasis implementing the corresponding diagonalization. When `V` and `μ`
    come from the eigenbasis and eigenvalues of a density operator `σ`, this
    specializes to `densityOpPerturbedLogMatrix σ h`. -/
noncomputable def perturbedLogMatrix {N : ℕ}
    (V : Matrix (Fin N) (Fin N) ℂ) (μ h : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  V.conjTranspose *
    Matrix.diagonal (fun i => (Real.log (μ i) : ℂ)) *
    V +
    Matrix.diagonal (fun j => (h j : ℂ))

/-- The zero-on-kernel spectral-log perturbation attached to a density operator.

    This abbreviates `perturbedLogMatrix` applied to the eigenbasis and
    eigenvalues of `σ`. If `σ` is singular, its zero eigenvalues contribute
    `Real.log 0 = 0`, so this is the totalized spectral log used in this
    development rather than the genuine matrix logarithm on `ker σ`. -/
noncomputable abbrev densityOpPerturbedLogMatrix {N : ℕ}
    (σ : DensityOp N) (h : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  perturbedLogMatrix (eigenbasisOf σ) (eigenvaluesOf σ) h

/-- The perturbation matrix is Hermitian.

    Both summands are Hermitian:
    - `V†·diag(real)·V` is Hermitian for any `V`
    - diag(real) is Hermitian -/
lemma perturbedLogMatrix_isHermitian {N : ℕ}
    (V : Matrix (Fin N) (Fin N) ℂ) (μ h : Fin N → ℝ) :
    (perturbedLogMatrix V μ h).IsHermitian := by
  unfold perturbedLogMatrix
  apply Matrix.IsHermitian.add
  · have : ∀ i, star ((Real.log (μ i) : ℂ)) =
        (Real.log (μ i) : ℂ) := by
      intro i; exact Complex.conj_ofReal _
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose]
    have hd : (star fun i => (Real.log (μ i) : ℂ)) =
        (fun i => (Real.log (μ i) : ℂ)) := by ext i; exact this i
    rw [hd, Matrix.mul_assoc]
  · have : ∀ j, star ((h j : ℂ)) = (h j : ℂ) := by
      intro j; exact Complex.conj_ofReal _
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1; ext j; exact this j

/-- The density-operator perturbation matrix is Hermitian. -/
lemma densityOpPerturbedLogMatrix_isHermitian {N : ℕ}
    (σ : DensityOp N) (h : Fin N → ℝ) :
    (densityOpPerturbedLogMatrix σ h).IsHermitian := by
  simpa [densityOpPerturbedLogMatrix] using
    perturbedLogMatrix_isHermitian (V := eigenbasisOf σ) (μ := eigenvaluesOf σ) (h := h)

/-- The real part of the trace against a real diagonal matrix only depends on the
    real parts of the diagonal entries. -/
lemma trace_mul_real_diagonal_re {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) (d : Fin N → ℝ) :
    (M * Matrix.diagonal (fun j => (d j : ℂ))).trace.re =
      ∑ j, (M j j).re * d j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  · intro b _ hbj
    simp [hbj]
  · simp

/-- Conjugating a real diagonal matrix by `U` turns the trace pairing with `M`
into the diagonal pairing in the `U`-basis. -/
lemma trace_mul_conj_real_diagonal_re {N : ℕ}
    (M U : Matrix (Fin N) (Fin N) ℂ) (d : Fin N → ℝ) :
    (M * (U * Matrix.diagonal (RCLike.ofReal ∘ d) * U.conjTranspose)).trace.re =
      ∑ i, ((U.conjTranspose * M * U) i i).re * d i := by
  have h1 : M * (U * Matrix.diagonal (RCLike.ofReal ∘ d) * U.conjTranspose) =
      (M * U) * (Matrix.diagonal (RCLike.ofReal ∘ d) * U.conjTranspose) := by
    simp [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : Matrix.diagonal (RCLike.ofReal ∘ d) * U.conjTranspose * (M * U) =
      Matrix.diagonal (RCLike.ofReal ∘ d) * (U.conjTranspose * M * U) := by
    simp [Matrix.mul_assoc]
  rw [h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Function.comp]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_comm]

/-- The perturbed logarithm trace identity expresses the spectral pairing with
`densityOpPerturbedLogMatrix σ h` as `traceProductLogSigma ρ σ` plus the diagonal
term. -/
lemma trace_perturbedLogMatrix_identity {N : ℕ} [NeZero N]
    (ρ σ : DensityOp N) (h : Fin N → ℝ) :
    let hA := densityOpPerturbedLogMatrix_isHermitian σ h
    let U := (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
    ∑ i, ((U.conjTranspose * ρ.toOp * U) i i).re * hA.eigenvalues i =
    traceProductLogSigma ρ σ + ∑ j, (ρ.toOp j j).re * h j := by
  intro hA U
  set A := densityOpPerturbedLogMatrix σ h
  have hspectral : A = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
      U.conjTranspose := by
    exact hA.spectral_theorem
  have lhs_eq : (∑ i, ((U.conjTranspose * ρ.toOp * U) i i).re * hA.eigenvalues i) =
      (ρ.toOp * A).trace.re := by
    conv_rhs => rw [hspectral]
    simpa using (trace_mul_conj_real_diagonal_re ρ.toOp U hA.eigenvalues).symm
  have rhs_eq : traceProductLogSigma ρ σ + ∑ j, (ρ.toOp j j).re * h j =
      (ρ.toOp * A).trace.re := by
    set V := eigenbasisOf σ
    set logD := Matrix.diagonal (fun i => (Real.log (eigenvaluesOf σ i) : ℂ))
    set diagH := Matrix.diagonal (fun j => (h j : ℂ))
    have hA_unfold : A = V.conjTranspose * logD * V + diagH := rfl
    rw [hA_unfold, Matrix.mul_add, Matrix.trace_add]
    have h_tpls := traceProductLogSigma_eq_trace ρ σ
    have h_assoc : ρ.toOp * (V.conjTranspose * logD * V) =
        (ρ.toOp * V.conjTranspose * logD) * V := by simp [Matrix.mul_assoc]
    rw [h_assoc]
    have h_diag_trace : (ρ.toOp * diagH).trace.re = ∑ j, (ρ.toOp j j).re * h j := by
      simpa [diagH] using trace_mul_real_diagonal_re ρ.toOp h
    rw [Complex.add_re, h_tpls, h_diag_trace]
  rw [lhs_eq, rhs_eq]

/-- The diagonal of a unitary conjugate of a density operator has total mass `1`. -/
lemma densityOp_conj_diag_re_sum_one {N : ℕ}
    (ρ : DensityOp N) (U : Matrix (Fin N) (Fin N) ℂ) (hU : U * U.conjTranspose = 1) :
    ∑ i, ((U.conjTranspose * ρ.toOp * U) i i).re = 1 := by
  have htrace : (U.conjTranspose * ρ.toOp * U).trace = ρ.toOp.trace := by
    have h_assoc : U.conjTranspose * ρ.toOp * U = U.conjTranspose * (ρ.toOp * U) :=
      Matrix.mul_assoc _ _ _
    rw [h_assoc, Matrix.trace_mul_cycle']
    rw [show U * (U.conjTranspose * ρ.toOp) = (U * U.conjTranspose) * ρ.toOp from
      (Matrix.mul_assoc _ _ _).symm]
    rw [hU, Matrix.one_mul]
  have hdiag : ∑ i, ((U.conjTranspose * ρ.toOp * U) i i).re =
      (U.conjTranspose * ρ.toOp * U).trace.re := by
    unfold Matrix.trace
    simp [Complex.re_sum]
  rw [hdiag, htrace, ρ.trace_one]
  simp

/-- Diagonal Peierls-Bogoliubov inequality for `densityOpPerturbedLogMatrix σ h`. -/
lemma peierls_bogoliubov_diagonal {N : ℕ} [NeZero N]
    (ρ σ : DensityOp N) (h : Fin N → ℝ) :
    (∑ j, (ρ.toOp j j).re * h j) -
      Real.log (∑ i, Real.exp ((densityOpPerturbedLogMatrix_isHermitian σ h).eigenvalues i)) ≤
    relativeEntropyReal ρ σ := by
  set hA := densityOpPerturbedLogMatrix_isHermitian σ h
  set U := (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  set α := hA.eigenvalues
  set r := fun i => ((U.conjTranspose * ρ.toOp * U) i i).re
  have hstarU_U : U.conjTranspose * U = 1 :=
    Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  have hU_starU : U * U.conjTranspose = 1 :=
    (Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2)
  have hSchur : vonNeumannEntropy ρ ≤ shannonEntropy r := by
    have h1 := vonNeumannEntropy_le_arbitrary_diagonal_entropy
      U.conjTranspose
      (by simp [Matrix.conjTranspose_conjTranspose, hstarU_U])
      ρ
    simp only [Matrix.conjTranspose_conjTranspose] at h1
    exact h1
  have hr_nonneg : ∀ i, 0 ≤ r i := by
    intro i
    have := psd_conj_diag_nonneg
      (A := ρ.toOp) (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) U.conjTranspose i
    simp only [Matrix.conjTranspose_conjTranspose] at this
    exact this
  have hr_sum : ∑ i, r i = 1 := by
    simpa [r] using densityOp_conj_diag_re_sum_one ρ U hU_starU
  have hGibbs := classical_gibbs_variational r α hr_nonneg hr_sum
  have hTrace := trace_perturbedLogMatrix_identity ρ σ h
  unfold relativeEntropyReal
  linarith

end InfoTheory.RelativeEntropy

end
