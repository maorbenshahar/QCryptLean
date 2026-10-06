import
  QCryptLean.InfoTheory.RelativeEntropy.Variational.Basic
import QCryptLean.Quantum.Operators.Types
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Hermitian Matrix Exponential Identities — spectral trace formulas, positivity, and diagonal bounds

This file isolates low-level spectral facts about matrix exponentials of
Hermitian matrices. It records the spectral trace formula for `exp H`, the
positivity of `exp H`, the exponential/logarithm reconstruction for a
full-rank density operator, and the Jensen-type diagonal bound used in the
singular variational argument.

## Main statements
- `hermitian_exp_trace_eq`: `Tr(exp H)` is the sum of the exponentials of the
  eigenvalues of `H`
- `exp_log_diag_conj_eq_sigma`: exponentiating the spectral logarithm of a
  full-rank density operator recovers the operator
- `exp_hermitian_posSemidef`: `exp H` is positive semidefinite for Hermitian `H`
- `exp_diagonal_entry_ge_of_isHermitian`: diagonal entries of `exp H` dominate
  the exponentials of the diagonal entries of `H`
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open InfoTheory.VonNeumannEntropy

/-- For Hermitian `M`, `Tr(exp M).re = Σ exp(eigenvalues_i)`.
    Uses spectral decomposition + matrix exp conjugation + diagonal exp + trace cyclicity. -/
lemma hermitian_exp_trace_eq {N : ℕ} {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.IsHermitian) :
    (NormedSpace.exp M).trace.re = ∑ i, Real.exp (hM.eigenvalues i) := by
  set U_unitary := hM.eigenvectorUnitary
  set U_units := Unitary.toUnits U_unitary
  set ev := hM.eigenvalues
  set Λ : Matrix (Fin N) (Fin N) ℂ := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ ev)
  have hspec := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hstarU : star (U_unitary : Matrix (Fin N) (Fin N) ℂ) = (U_units⁻¹).val := by
    simp [U_units, Unitary.toUnits]
  have hU_eq : (U_unitary : Matrix (Fin N) (Fin N) ℂ) = U_units.val := rfl
  have hM_eq : M = U_units.val * Λ * (U_units⁻¹).val := by
    rw [hspec, hstarU, hU_eq]
  have hexpM : NormedSpace.exp M = U_units.val * NormedSpace.exp Λ * (U_units⁻¹).val := by
    rw [hM_eq]
    exact Matrix.exp_units_conj U_units Λ
  rw [hexpM, Matrix.exp_diagonal, mul_assoc, Matrix.trace_mul_comm U_units.val, mul_assoc]
  have hU_inv_U : (U_units⁻¹).val * U_units.val = 1 := by
    exact_mod_cast U_units.inv_mul
  rw [hU_inv_U, mul_one, Matrix.trace_diagonal, Complex.re_sum]
  congr 1
  ext i
  change (NormedSpace.exp ((RCLike.ofReal : ℝ → ℂ) ∘ ev) i).re = Real.exp (ev i)
  rw [Pi.coe_exp, Function.comp_apply, ← Complex.exp_eq_exp_ℂ]
  rw [RCLike.ofReal_alg]
  simp [← Complex.ofReal_exp]

/-- `exp(V† diag(log μ) V) = σ` when `μ_i > 0` and `V` diagonalizes `σ`. -/
lemma exp_log_diag_conj_eq_sigma {N : ℕ}
    (σ : DensityOp N)
    (hσ_pd : ∀ i, 0 < eigenvaluesOf σ i) :
    let V := eigenbasisOf σ
    let A := V.conjTranspose * diagonal (fun i => (Real.log (eigenvaluesOf σ i) : ℂ)) * V
    NormedSpace.exp A = σ.toOp := by
  letI : NeZero N := neZero_of_densityOp σ
  intro V A
  have hVL : V.conjTranspose * V = 1 := eigenbasisOf_unitary_left σ
  have hVR : V * V.conjTranspose = 1 := eigenbasisOf_unitary_right σ
  set V_unit : (Matrix (Fin N) (Fin N) ℂ)ˣ := {
    val := V
    inv := V.conjTranspose
    val_inv := hVR
    inv_val := hVL
  }
  have hA_eq : A = (V_unit⁻¹).val *
      diagonal (fun i => (Real.log (eigenvaluesOf σ i) : ℂ)) * V_unit.val := by
    simp [V_unit, A]
  rw [hA_eq, Matrix.exp_units_conj' V_unit, Matrix.exp_diagonal]
  have hexp_log : NormedSpace.exp (fun i => (Real.log (eigenvaluesOf σ i) : ℂ)) =
      fun i => (eigenvaluesOf σ i : ℂ) := by
    ext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    rw [Complex.ofReal_log (le_of_lt (hσ_pd i))]
    exact Complex.exp_log (by exact_mod_cast ne_of_gt (hσ_pd i))
  rw [hexp_log]
  have hV_inv_eq : (V_unit⁻¹).val = V.conjTranspose := by simp [V_unit]
  rw [hV_inv_eq]
  exact (eigenbasisOf_spectral_decomp σ).symm

/-- The matrix exponential of a Hermitian matrix is positive semidefinite. -/
lemma exp_hermitian_posSemidef {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) (hM : M.IsHermitian) :
    (NormedSpace.exp M).PosSemidef := by
  set half_M := (2 : ℂ)⁻¹ • M with half_M_def
  set X := NormedSpace.exp half_M
  have hHalf : half_M.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hM]
    simp [← half_M_def]
  have hX_herm : X.IsHermitian := hHalf.exp
  have hM_eq : NormedSpace.exp M = X * X := by
    have hM_two : M = 2 • half_M := by
      simp [half_M_def, ← smul_assoc, nsmul_eq_mul]
    rw [hM_two, Matrix.exp_nsmul, pow_succ, pow_one]
  rw [hM_eq]
  suffices h : (X * X.conjTranspose).PosSemidef by rwa [hX_herm] at h
  exact Matrix.posSemidef_self_mul_conjTranspose X

/-- The squared moduli in a row of the spectral unitary sum to `1`. -/
lemma hermitian_eigenvector_row_normSq_sum_one {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (i : Fin N) :
    ∑ j, Complex.normSq ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i j) = 1 := by
  let U : Matrix (Fin N) (Fin N) ℂ := hH.eigenvectorUnitary
  have hUU : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  simpa [U, hUU] using sum_normSq_row_eq_diag_mul_conjTranspose U i

/-- The spectral weights coming from a row of the eigenvector unitary are nonnegative. -/
lemma hermitian_eigenvector_row_normSq_nonneg {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (i j : Fin N) :
    0 ≤ Complex.normSq ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i j) :=
  Complex.normSq_nonneg _

/-- A Hermitian matrix is conjugate to the diagonal matrix of its eigenvalues by its
spectral unitary. -/
lemma hermitian_eq_eigenvector_unitary_mul_diagonal_mul_conjTranspose {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    H =
      (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *
        Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) *
        ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)).conjTranspose := by
  simpa [Function.comp] using hH.spectral_theorem

/-- The diagonal entries of a Hermitian matrix are weighted averages of its eigenvalues,
with weights given by the squared moduli of the spectral-unitary row. -/
lemma hermitian_diag_eq_weighted_eigenvalues {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (i : Fin N) :
    (H i i).re =
      ∑ j, Complex.normSq ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i j) *
        hH.eigenvalues j := by
  conv_lhs => rw [hermitian_eq_eigenvector_unitary_mul_diagonal_mul_conjTranspose hH]
  simpa using
    conj_diagonal_diag_eq_sum_normSq
      (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) hH.eigenvalues i

/-- A Hermitian matrix is conjugate to the diagonal matrix of its eigenvalues by the
unit corresponding to its spectral unitary. -/
lemma hermitian_eq_eigenvector_units_mul_diagonal_mul_inv {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    H =
      (Unitary.toUnits hH.eigenvectorUnitary).val *
        Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) *
        ((Unitary.toUnits hH.eigenvectorUnitary)⁻¹).val := by
  let U_unitary := hH.eigenvectorUnitary
  let U_units := Unitary.toUnits U_unitary
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hstarU : star (U_unitary : Matrix (Fin N) (Fin N) ℂ) = (U_units⁻¹).val := by
    simp [U_units, Unitary.toUnits]
  have hU_eq : (U_unitary : Matrix (Fin N) (Fin N) ℂ) = U_units.val := rfl
  simpa [U_units, U_unitary, Function.comp] using hspec

/-- The diagonal entries of `exp H` are the same weighted averages of `exp` applied to
the eigenvalues of a Hermitian matrix. -/
lemma hermitian_exp_diag_eq_weighted_exp_eigenvalues {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (i : Fin N) :
    ((NormedSpace.exp H) i i).re =
      ∑ j, Complex.normSq ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i j) *
        Real.exp (hH.eigenvalues j) := by
  conv_lhs => rw [hermitian_eq_eigenvector_units_mul_diagonal_mul_inv hH]
  rw [Matrix.exp_units_conj (Unitary.toUnits hH.eigenvectorUnitary)
      (Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ))),
    Matrix.exp_diagonal]
  have hexp_diag :
      Matrix.diagonal (NormedSpace.exp fun j => (hH.eigenvalues j : ℂ)) =
        Matrix.diagonal (fun j => (Real.exp (hH.eigenvalues j) : ℂ)) := by
    congr 1
    ext j
    simp [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
  rw [hexp_diag]
  simpa [Unitary.toUnits] using
    conj_diagonal_diag_eq_sum_normSq
      ((Unitary.toUnits hH.eigenvectorUnitary).val) (fun j => Real.exp (hH.eigenvalues j)) i

/-- For a Hermitian matrix, each diagonal entry of `exp H` dominates the exponential
of the corresponding diagonal entry of `H`. -/
lemma exp_diagonal_entry_ge_of_isHermitian {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (i : Fin N) :
    Real.exp ((H i i).re) ≤ ((NormedSpace.exp H) i i).re := by
  rw [hermitian_diag_eq_weighted_eigenvalues hH i,
    hermitian_exp_diag_eq_weighted_exp_eigenvalues hH i]
  have hweights_nonneg :
      ∀ j ∈ Finset.univ,
        0 ≤ Complex.normSq ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i j) := by
    intro j _
    exact hermitian_eigenvector_row_normSq_nonneg hH i j
  have hweights_sum :
      ∑ j, Complex.normSq ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i j) = 1 :=
    hermitian_eigenvector_row_normSq_sum_one hH i
  simpa [smul_eq_mul] using
    (convexOn_exp.map_sum_le hweights_nonneg hweights_sum (by
      intro j _
      simp))

end InfoTheory.RelativeEntropy

end
