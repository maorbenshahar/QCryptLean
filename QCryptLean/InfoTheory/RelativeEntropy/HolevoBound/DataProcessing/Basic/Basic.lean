import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.IsometricInvariance
import QCryptLean.Math.ClassicalEntropy.KLDivergence

/-!
# Data Processing Basics — diagonal entropy bounds and PSD diagonal estimates

Core diagonal-basis lemmas used throughout the Holevo-bound data-processing
argument: quadratic-form identification of diagonal entries, positivity of
conjugated diagonals for positive semidefinite matrices, Schur concavity of von
Neumann entropy in an arbitrary basis, and standard-basis diagonal facts for
density operators.

## Main statements
- `quadraticForm_single_eq_diag`: the basis-vector quadratic form equals a diagonal entry
- `psd_conj_diag_nonneg`: conjugated PSD diagonals have nonnegative real part
- `vonNeumannEntropy_le_arbitrary_diagonal_entropy`: `S(ρ)` is bounded by diagonal Shannon entropy
- `densityOp_diag_re_sum_one`: the standard-basis diagonal of a density operator sums to `1`
- `Quantum.Operators.psd_diag_re_nonneg`: the standard-basis diagonal of a density operator is
nonnegative
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-- The quadratic form ⟨eⱼ | M | eⱼ⟩ equals the (j,j) diagonal entry of M. -/
lemma quadraticForm_single_eq_diag {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    star (Pi.single j 1) ⬝ᵥ (M *ᵥ Pi.single j 1) = M j j := by
  simp only [dotProduct, mulVec, Pi.star_apply, Pi.single_apply]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single j]
  · simp only [if_true, star_one, one_mul, mul_one]
  · intro b _ hbj; simp [hbj]
  · simp
  · intro b _ hbj; simp [hbj]
  · simp

/-- A zero diagonal entry of a PSD matrix forces the corresponding standard basis
vector into its kernel, so full kernel containment transfers the diagonal zero. -/
lemma diag_zero_of_ker_sub {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℂ)
    (hA_psd : A.PosSemidef)
    (h_ker : ∀ v : Fin N → ℂ, A.mulVec v = 0 → B.mulVec v = 0)
    {j : Fin N}
    (hAjj : (A j j).re = 0) :
    (B j j).re = 0 := by
  have h_quad_A := quadraticForm_single_eq_diag A j
  have h_nonneg : 0 ≤ A j j := by
    rw [← h_quad_A]
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA_psd).2 (Pi.single j 1)
  have h_im_zero : (A j j).im = 0 := by
    have := (Complex.nonneg_iff.mp h_nonneg).2
    linarith
  have h_A_zero : A j j = 0 :=
    Complex.ext hAjj h_im_zero
  have h_A_mulvec_zero : A.mulVec (Pi.single j 1) = 0 :=
    (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hA_psd _).mp (by
      rw [h_quad_A]
      exact h_A_zero)
  have h_B_mulvec_zero : B.mulVec (Pi.single j 1) = 0 :=
    h_ker (Pi.single j 1) h_A_mulvec_zero
  have h_quad_B := quadraticForm_single_eq_diag B j
  have h_B_zero : B j j = 0 := by
    rw [← h_quad_B, h_B_mulvec_zero]
    simp [dotProduct, mul_zero, Finset.sum_const_zero]
  rw [h_B_zero, Complex.zero_re]

/-- Diagonal entries of a conjugated positive semidefinite matrix are non-negative.
    For `A ≥ 0`, `((W * A * W†) j j).re ≥ 0`. -/
lemma psd_conj_diag_nonneg {m n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hApsd : A.PosSemidef)
    (W : Matrix (Fin m) (Fin n) ℂ) (j : Fin m) :
    0 ≤ ((W * A * W.conjTranspose) j j).re := by
  set M := W * A * W.conjTranspose
  have hMpsd : M.PosSemidef := by
    simpa [M, Matrix.conjTranspose_conjTranspose] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hApsd W.conjTranspose
  have hpsd_form : 0 ≤ star (Pi.single j 1) ⬝ᵥ (M *ᵥ Pi.single j 1) :=
    (Matrix.posSemidef_iff_dotProduct_mulVec.mp hMpsd).2 _
  rw [quadraticForm_single_eq_diag] at hpsd_form
  exact Complex.nonneg_iff.mp hpsd_form |>.1

/-- The squared moduli in row `i` sum to the real diagonal entry of `T * T†`. -/
lemma sum_normSq_row_eq_diag_mul_conjTranspose {m n : ℕ}
    (T : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) :
    ∑ j, Complex.normSq (T i j) = ((T * T.conjTranspose) i i).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The squared moduli in column `j` sum to the real diagonal entry of `T† * T`. -/
lemma sum_normSq_col_eq_diag_conjTranspose_mul {m n : ℕ}
    (T : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    ∑ i, Complex.normSq (T i j) = ((T.conjTranspose * T) j j).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Conjugating a real diagonal matrix by `T` turns diagonal entries into
weighted sums with weights `|T i j|²`. -/
lemma conj_diagonal_diag_eq_sum_normSq {m n : ℕ}
    (T : Matrix (Fin m) (Fin n) ℂ) (diag : Fin n → ℝ) (i : Fin m) :
    ((T * Matrix.diagonal (fun j => (diag j : ℂ)) * T.conjTranspose) i i).re =
      ∑ j, Complex.normSq (T i j) * diag j := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  have h_simp : ∀ x,
      (∑ x_1, T i x_1 * (if x_1 = x then (diag x_1 : ℂ) else 0)) =
      T i x * (diag x : ℂ) := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hyx; simp [hyx]
    · intro hx; exact (hx (Finset.mem_univ x)).elim
  have h_sum_eq :
      (∑ x, (∑ x_1, T i x_1 * (if x_1 = x then (diag x_1 : ℂ) else 0)) *
        star (T i x)) =
      ∑ x, T i x * (diag x : ℂ) * star (T i x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [h_simp x]
  rw [h_sum_eq, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- **Schur concavity for arbitrary basis**: The von Neumann entropy of ρ is at most
    the Shannon entropy of the diagonal elements of ρ in any orthonormal basis.

    For any unitary W, the diagonal d_j = (WρW†)_{jj}.re satisfies d = D·λ(ρ) where D is
    doubly stochastic (D_{jk} = |T_{jk}|² for T = W·V_ρ† unitary). By concavity of
    Shannon entropy under doubly stochastic maps, H(d) ≥ H(λ(ρ)) = S(ρ). -/
lemma vonNeumannEntropy_le_arbitrary_diagonal_entropy {N : ℕ} [NeZero N]
    (W : Matrix (Fin N) (Fin N) ℂ)
    (hWU : W * W.conjTranspose = 1)
    (ρ : DensityOp N) :
    vonNeumannEntropy ρ ≤
    shannonEntropy (fun j => ((W * ρ.toOp * W.conjTranspose) j j).re) := by
  have hWU' : W.conjTranspose * W = 1 := mul_eq_one_comm.mpr hWU
  set V_ρ := eigenbasisOf ρ
  have hspec_ρ := eigenvaluesOf_spec ρ
  have hV_ρ_props := Classical.choose_spec hspec_ρ.2.2.2
  have hV_ρ_adj_V_ρ : V_ρ.conjTranspose * V_ρ = 1 := hV_ρ_props.1
  have hV_ρ_V_ρ_adj : V_ρ * V_ρ.conjTranspose = 1 := hV_ρ_props.2.1
  have hρ_decomp : ρ.toOp = V_ρ.conjTranspose *
      (Matrix.diagonal (fun i => (eigenvaluesOf ρ i : ℂ))) * V_ρ := hV_ρ_props.2.2
  set T := W * V_ρ.conjTranspose with hT_def
  have hT_adj_T : T.conjTranspose * T = 1 := by
    simp only [hT_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc V_ρ * W.conjTranspose * (W * V_ρ.conjTranspose)
        = V_ρ * (W.conjTranspose * W) * V_ρ.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = V_ρ * 1 * V_ρ.conjTranspose := by rw [hWU']
      _ = V_ρ * V_ρ.conjTranspose := by simp only [Matrix.mul_one]
      _ = 1 := hV_ρ_V_ρ_adj
  have hT_T_adj : T * T.conjTranspose = 1 := by
    simp only [hT_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc W * V_ρ.conjTranspose * (V_ρ * W.conjTranspose)
        = W * (V_ρ.conjTranspose * V_ρ) * W.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = W * 1 * W.conjTranspose := by rw [hV_ρ_adj_V_ρ]
      _ = W * W.conjTranspose := by simp only [Matrix.mul_one]
      _ = 1 := hWU
  let D : Matrix (Fin N) (Fin N) ℝ := fun i j => Complex.normSq (T i j)
  have hD_nonneg : ∀ i j, 0 ≤ D i j := fun i j => Complex.normSq_nonneg (T i j)
  have hD_row : ∀ i, ∑ j, D i j = 1 := by
    intro i
    change ∑ j, Complex.normSq (T i j) = 1
    rw [sum_normSq_row_eq_diag_mul_conjTranspose, hT_T_adj]
    simp
  have hD_col : ∀ j, ∑ i, D i j = 1 := by
    intro j
    change ∑ i, Complex.normSq (T i j) = 1
    rw [sum_normSq_col_eq_diag_conjTranspose_mul, hT_adj_T]
    simp
  have hdiag_eq : (fun i => ((W * ρ.toOp * W.conjTranspose) i i).re) =
      fun i => ∑ j, D i j * eigenvaluesOf ρ j := by
    ext i
    rw [hρ_decomp]
    have h_conj :
        W * (V_ρ.conjTranspose *
          Matrix.diagonal (fun j => (eigenvaluesOf ρ j : ℂ)) *
          V_ρ) * W.conjTranspose =
        T * Matrix.diagonal (fun j => (eigenvaluesOf ρ j : ℂ)) *
          T.conjTranspose := by
      simp only [hT_def, Matrix.mul_assoc, Matrix.conjTranspose_mul,
                 Matrix.conjTranspose_conjTranspose]
    rw [h_conj]
    simpa [D] using conj_diagonal_diag_eq_sum_normSq T (eigenvaluesOf ρ) i
  have hp_nonneg : ∀ i, 0 ≤ eigenvaluesOf ρ i := hspec_ρ.1
  have hp_sum : ∑ i, eigenvaluesOf ρ i = 1 := hspec_ρ.2.1
  have hp_le : ∀ i, eigenvaluesOf ρ i ≤ 1 := hspec_ρ.2.2.1
  unfold vonNeumannEntropy
  rw [hdiag_eq]
  exact shannonEntropy_doubly_stochastic_ge (eigenvaluesOf ρ) D hp_nonneg
    hD_nonneg hD_row hD_col

/-- Sum of diagonal real parts equals `1` for a Hermitian matrix of trace `1`. -/
lemma densityOp_diag_re_sum_one {N : ℕ} (ρ : Matrix (Fin N) (Fin N) ℂ)
    (hρ_herm : ρ.IsHermitian) (hρ_trace : ρ.trace = 1) :
    ∑ j : Fin N, (ρ j j).re = 1 := by
  rw [← hermitian_trace_eq_sum_diag_re ρ hρ_herm]
  rw [hρ_trace]
  simp

end InfoTheory.RelativeEntropy

end
