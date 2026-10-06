import QCryptLean.InfoTheory.VonNeumannEntropy.Defs
import QCryptLean.Math.ClassicalEntropy.KLDivergence
import QCryptLean.Quantum.TensorProducts.Basic

/-!
# Von Neumann Entropy — basic bounds, unitary invariance, tensor product helpers

Von Neumann entropy S(ρ) defined as Shannon entropy of the eigenvalue spectrum.
Core definitions (`IsEigenvalueSpectrum`, `eigenvaluesOf`, `vonNeumannEntropy`) live in
`VonNeumannEntropy/Defs.lean` to avoid circular imports with the RelativeEntropy namespace.

## Main definitions
- `coefficientMatrix`: Bipartite coefficient matrix for Schmidt decomposition

## Main statements
- `vonNeumannEntropy_nonneg`: S(ρ) ≥ 0
- `vonNeumannEntropy_le_log_dim`: S(ρ) ≤ log n
- `vonNeumannEntropy_pure`: S(ρ) = 0 for pure states
- `vonNeumannEntropy_maxMixed`: S(I/n) = log n
- `vonNeumannEntropy_unitary_evolve`: S(UρU†) = S(ρ)
- `eigenvalueSpectrum_entropy_eq`: entropy depends only on the spectrum
- `vonNeumannEntropy_eq_shannonEntropy`: S(ρ) = H(eigenvalues)
- `Op_tensor_diagonal`: tensor product of diagonal matrices is diagonal

Note: `vonNeumannEntropy_concave` is proved in
`HolevoBound/Concavity.lean` (via Klein's inequality).
`vonNeumannEntropy_concave_unitary_average` is proved in
`HolevoBound/Main.lean`.
-/

open Math.ClassicalEntropy

noncomputable section

namespace InfoTheory.VonNeumannEntropy

open Quantum.Operators Quantum.TensorProducts


/-- For pure states (ρ² = ρ), all eigenvalues are 0 or 1. -/
lemma pure_eigenvalues_zero_or_one {n : ℕ} (ρ : DensityOp n)
    (hpure : ρ.toOp * ρ.toOp = ρ.toOp)
    (eigenvalues : Fin n → ℝ) (heig : IsEigenvalueSpectrum ρ eigenvalues) :
    ∀ i, eigenvalues i = 0 ∨ eigenvalues i = 1 := by
  intro i
  obtain ⟨_, _, _, U, hUU, hUU', hspec⟩ := heig
  let D := Matrix.diagonal (fun j => (eigenvalues j : ℂ))
  -- Compute ρ² = U† * D² * U
  have h_rho_sq' : ρ.toOp * ρ.toOp = U† * (D * D) * U := by
    calc ρ.toOp * ρ.toOp = U† * D * U * (U† * D * U) := by rw [hspec]
      _ = U† * D * (U * U†) * D * U := by simp only [Matrix.mul_assoc]
      _ = U† * D * 1 * D * U := by rw [hUU']
      _ = U† * D * D * U := by simp only [Matrix.mul_one]
      _ = U† * (D * D) * U := by simp only [Matrix.mul_assoc]
  -- From ρ² = ρ: U† * D² * U = U† * D * U
  have h_eq : U† * (D * D) * U = U† * D * U := by rw [← h_rho_sq', hpure, hspec]
  -- D² = D
  have h_D_eq : D * D = D := by
    have h1 : U * (U† * (D * D) * U) * U† = U * (U† * D * U) * U† := by rw [h_eq]
    have h_lhs : U * (U† * (D * D) * U) * U† = D * D := by
      calc U * (U† * (D * D) * U) * U†
        = (U * U†) * (D * D) * (U * U†) := by simp only [Matrix.mul_assoc]
        _ = 1 * (D * D) * 1 := by rw [hUU']
        _ = D * D := by simp only [Matrix.one_mul, Matrix.mul_one]
    have h_rhs : U * (U† * D * U) * U† = D := by
      calc U * (U† * D * U) * U†
        = (U * U†) * D * (U * U†) := by simp only [Matrix.mul_assoc]
        _ = 1 * D * 1 := by rw [hUU']
        _ = D := by simp only [Matrix.one_mul, Matrix.mul_one]
    rw [h_lhs, h_rhs] at h1; exact h1
  -- D * D = diagonal(λᵢ * λᵢ)
  have h_D_sq : D * D = Matrix.diagonal (fun j => (eigenvalues j : ℂ) * (eigenvalues j : ℂ)) :=
    Matrix.diagonal_mul_diagonal _ _
  -- Extract diagonal entry: λᵢ * λᵢ = λᵢ (as complex)
  have h_diag_eq : (eigenvalues i : ℂ) * (eigenvalues i : ℂ) = (eigenvalues i : ℂ) := by
    have h_entry : (Matrix.diagonal (fun j => (eigenvalues j : ℂ) * (eigenvalues j : ℂ))) i i =
                   (Matrix.diagonal (fun j => (eigenvalues j : ℂ))) i i := by rw [← h_D_sq, h_D_eq]
    simp only [Matrix.diagonal_apply_eq] at h_entry; exact h_entry
  -- Convert complex to real
  have h_real : eigenvalues i * eigenvalues i = eigenvalues i := by
    have h_cplx : ((eigenvalues i * eigenvalues i : ℝ) : ℂ) = ((eigenvalues i : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul]; exact h_diag_eq
    exact Complex.ofReal_inj.mp h_cplx
  -- λ² = λ implies λ = 0 or λ = 1
  have h_sq : (eigenvalues i)^2 = eigenvalues i := by linarith [sq (eigenvalues i)]
  exact sq_eq_self_iff_zero_or_one (eigenvalues i) |>.mp h_sq

/-- Entropy is non-negative. -/
theorem vonNeumannEntropy_nonneg {n : ℕ} [NeZero n] (ρ : DensityOp n) :
    0 ≤ vonNeumannEntropy ρ := by
  unfold vonNeumannEntropy
  have hspec := eigenvaluesOf_spec ρ
  unfold IsEigenvalueSpectrum at hspec
  obtain ⟨h_nonneg, _, h_le_one, _⟩ := hspec
  exact shannonEntropy_nonneg (eigenvaluesOf ρ) h_nonneg h_le_one

/-- Entropy is bounded by log(n). -/
theorem vonNeumannEntropy_le_log_dim {n : ℕ} [NeZero n] (ρ : DensityOp n) :
    vonNeumannEntropy ρ ≤ Real.log n := by
  unfold vonNeumannEntropy
  have hspec := eigenvaluesOf_spec ρ
  unfold IsEigenvalueSpectrum at hspec
  obtain ⟨h_nonneg, h_sum, _, _⟩ := hspec
  exact shannonEntropy_le_log (eigenvaluesOf ρ) h_nonneg h_sum

/-- Pure states have zero entropy. -/
theorem vonNeumannEntropy_pure {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (hpure : ρ.IsPure) : vonNeumannEntropy ρ = 0 := by
  unfold vonNeumannEntropy
  have hspec := eigenvaluesOf_spec ρ
  have h_zero_or_one : ∀ i, eigenvaluesOf ρ i = 0 ∨ eigenvaluesOf ρ i = 1 :=
    pure_eigenvalues_zero_or_one ρ hpure (eigenvaluesOf ρ) hspec
  exact shannonEntropy_zero_of_zero_or_one (eigenvaluesOf ρ) h_zero_or_one

/-!
## Maximally Mixed State
-/

/-- For the maximally mixed state, all eigenvalues are 1/n. -/
lemma maxMixed_eigenvalues_eq {n : ℕ} [NeZero n] (eigenvalues : Fin n → ℝ)
    (heig : IsEigenvalueSpectrum (DensityOp.maxMixed n) eigenvalues) :
    ∀ i, eigenvalues i = (1 : ℝ) / n := by
  intro i
  obtain ⟨_, _, _, U, hUU, hUU', hspec⟩ := heig
  let D := Matrix.diagonal (fun j => (eigenvalues j : ℂ))
  have h_commute : U * ((1 / n : ℂ) • (1 : Op n)) * U† = (1 / n : ℂ) • (1 : Op n) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]; rw [hUU']
  have h_D_eq : D = (1 / n : ℂ) • (1 : Op n) := by
    calc D = 1 * D * 1 := by simp only [Matrix.one_mul, Matrix.mul_one]
      _ = (U * U†) * D * (U * U†) := by rw [hUU']
      _ = U * (U† * D * U) * U† := by simp only [Matrix.mul_assoc]
      _ = U * (DensityOp.maxMixed n).toOp * U† := by rw [← hspec]
      _ = U * ((1 / n : ℂ) • (1 : Op n)) * U† := by rfl
      _ = (1 / n : ℂ) • (1 : Op n) := h_commute
  have h_entry : D i i = (1 / n : ℂ) := by
    calc D i i = ((1 / n : ℂ) • (1 : Op n)) i i := by rw [h_D_eq]
      _ = (1 / n : ℂ) * (1 : Op n) i i := by rfl
      _ = (1 / n : ℂ) * 1 := by simp only [Matrix.one_apply_eq]
      _ = (1 / n : ℂ) := by ring
  have h_D_diag : D i i = (eigenvalues i : ℂ) := Matrix.diagonal_apply_eq _ i
  have h_cplx : (eigenvalues i : ℂ) = (1 / n : ℂ) := by rw [← h_D_diag, h_entry]
  have h_coerce : (1 / n : ℂ) = ((1 / n : ℝ) : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  rw [h_coerce] at h_cplx
  exact Complex.ofReal_inj.mp h_cplx

/-- Maximally mixed state has maximum entropy. -/
theorem vonNeumannEntropy_maxMixed (n : ℕ) [NeZero n] :
    vonNeumannEntropy (DensityOp.maxMixed n) = Real.log n := by
  unfold vonNeumannEntropy
  have heig := eigenvaluesOf_spec (DensityOp.maxMixed n)
  have h_all_eq : ∀ i, eigenvaluesOf (DensityOp.maxMixed n) i = (1 : ℝ) / n :=
    maxMixed_eigenvalues_eq (eigenvaluesOf (DensityOp.maxMixed n)) heig
  have h_eq : shannonEntropy (eigenvaluesOf (DensityOp.maxMixed n)) =
              shannonEntropy (fun _ : Fin n => (1 : ℝ) / n) :=
    shannonEntropy_congr _ _ h_all_eq
  rw [h_eq, shannonEntropy_uniform]

/-!
## Eigenvalue Spectrum Uniqueness
-/

/-- Helper: Convert eigenvalue spectrum to multiset. -/
private def eigenvalueMultiset {n : ℕ} (evs : Fin n → ℝ) : Multiset ℝ :=
  Finset.univ.val.map evs

/-- Two eigenvalue spectra for the same density operator have the same multiset.
    This follows from uniqueness of the characteristic polynomial. -/
lemma eigenvalueSpectrum_multiset_eq {n : ℕ} (ρ : DensityOp n)
    (evs1 evs2 : Fin n → ℝ)
    (h1 : IsEigenvalueSpectrum ρ evs1)
    (h2 : IsEigenvalueSpectrum ρ evs2) :
    eigenvalueMultiset evs1 = eigenvalueMultiset evs2 := by
  obtain ⟨_, _, _, U1, hU1U, hUU1, hspec1⟩ := h1
  obtain ⟨_, _, _, U2, hU2U, hUU2, hspec2⟩ := h2
  let D1 := Matrix.diagonal (fun i => (evs1 i : ℂ))
  let D2 := Matrix.diagonal (fun i => (evs2 i : ℂ))
  let starU1_unit : Units (Matrix (Fin n) (Fin n) ℂ) :=
    Units.mk U1.conjTranspose U1 hU1U hUU1
  let starU2_unit : Units (Matrix (Fin n) (Fin n) ℂ) :=
    Units.mk U2.conjTranspose U2 hU2U hUU2
  have hcharpoly1 : ρ.toOp.charpoly = D1.charpoly := by
    have hconj : ρ.toOp = starU1_unit.val * D1 * starU1_unit⁻¹.val := by
      change ρ.toOp = U1.conjTranspose * D1 * U1
      rw [Matrix.mul_assoc]
      convert hspec1 using 1
      rw [Matrix.mul_assoc]
    rw [hconj]
    simpa only [Matrix.coe_units_inv] using Matrix.charpoly_units_conj starU1_unit D1
  have hcharpoly2 : ρ.toOp.charpoly = D2.charpoly := by
    have hconj : ρ.toOp = starU2_unit.val * D2 * starU2_unit⁻¹.val := by
      change ρ.toOp = U2.conjTranspose * D2 * U2
      rw [Matrix.mul_assoc]
      convert hspec2 using 1
      rw [Matrix.mul_assoc]
    rw [hconj]
    simpa only [Matrix.coe_units_inv] using Matrix.charpoly_units_conj starU2_unit D2
  have hD_charpoly : D1.charpoly = D2.charpoly := by
    rw [← hcharpoly1, hcharpoly2]
  -- From equal charpolys of complex diagonal matrices, get equal complex multisets
  have h_complex : Finset.univ.val.map (fun i => (evs1 i : ℂ)) =
                   Finset.univ.val.map (fun i => (evs2 i : ℂ)) := by
    -- charpoly of diagonal is ∏(X - C(λᵢ))
    have h1 : D1.charpoly = ∏ i, (Polynomial.X - Polynomial.C (evs1 i : ℂ)) :=
      Matrix.charpoly_diagonal _
    have h2 : D2.charpoly = ∏ i, (Polynomial.X - Polynomial.C (evs2 i : ℂ)) :=
      Matrix.charpoly_diagonal _
    -- Convert finset prod to multiset prod
    have h1' : ∏ i : Fin n, (Polynomial.X - Polynomial.C (evs1 i : ℂ)) =
               (Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (evs1 i : ℂ))).prod := by
      rw [← Finset.prod_eq_multiset_prod]
    have h2' : ∏ i : Fin n, (Polynomial.X - Polynomial.C (evs2 i : ℂ)) =
               (Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (evs2 i : ℂ))).prod := by
      rw [← Finset.prod_eq_multiset_prod]
    -- Rewrite map to composition using Multiset.map_map
    have map1 : Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (evs1 i : ℂ)) =
                ((Finset.univ.val.map (fun i => (evs1 i : ℂ))).map
                 (fun a => Polynomial.X - Polynomial.C a)) := by
      rw [Multiset.map_map]; rfl
    have map2 : Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (evs2 i : ℂ)) =
                ((Finset.univ.val.map (fun i => (evs2 i : ℂ))).map
                 (fun a => Polynomial.X - Polynomial.C a)) := by
      rw [Multiset.map_map]; rfl
    -- Roots of multiset prod (X - C a) equals the multiset
    have roots1 : ((Finset.univ.val.map (fun i => (evs1 i : ℂ))).map
                   (fun a => Polynomial.X - Polynomial.C a)).prod.roots =
                  Finset.univ.val.map (fun i => (evs1 i : ℂ)) :=
      Polynomial.roots_multiset_prod_X_sub_C _
    have roots2 : ((Finset.univ.val.map (fun i => (evs2 i : ℂ))).map
                   (fun a => Polynomial.X - Polynomial.C a)).prod.roots =
                  Finset.univ.val.map (fun i => (evs2 i : ℂ)) :=
      Polynomial.roots_multiset_prod_X_sub_C _
    -- Equal charpolys means equal product polynomials
    have h_prod_eq :
        (Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (evs1 i : ℂ))).prod =
        (Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (evs2 i : ℂ))).prod := by
      rw [← h1', ← h2', ← h1, ← h2, hD_charpoly]
    rw [map1, map2] at h_prod_eq
    have h_roots_eq :
        ((Finset.univ.val.map (fun i => (evs1 i : ℂ))).map
         (fun a => Polynomial.X - Polynomial.C a)).prod.roots =
        ((Finset.univ.val.map (fun i => (evs2 i : ℂ))).map
         (fun a => Polynomial.X - Polynomial.C a)).prod.roots := by
      rw [h_prod_eq]
    rw [roots1, roots2] at h_roots_eq
    exact h_roots_eq
  -- Now use injectivity of the complex coercion to get real multisets equal
  have h_inj : Function.Injective (fun x : ℝ => (x : ℂ)) := Complex.ofReal_injective
  have h_map_inj : Function.Injective (Multiset.map (fun x : ℝ => (x : ℂ))) :=
    Multiset.map_injective h_inj
  unfold eigenvalueMultiset
  apply h_map_inj
  -- Convert map (ofReal) (map evs s) = map (ofReal ∘ evs) s
  have h_conv1 : Multiset.map (fun x : ℝ => (x : ℂ)) (Finset.univ.val.map evs1) =
                 Finset.univ.val.map (fun i => (evs1 i : ℂ)) := by
    rw [Multiset.map_map]; rfl
  have h_conv2 : Multiset.map (fun x : ℝ => (x : ℂ)) (Finset.univ.val.map evs2) =
                 Finset.univ.val.map (fun i => (evs2 i : ℂ)) := by
    rw [Multiset.map_map]; rfl
  rw [h_conv1, h_conv2, h_complex]

/-- Shannon entropy equals the sum over the eigenvalue multiset. -/
private lemma shannonEntropy_eq_multiset_sum {n : ℕ} (evs : Fin n → ℝ) :
    shannonEntropy evs = ((eigenvalueMultiset evs).map entropyTerm).sum := by
  unfold shannonEntropy eigenvalueMultiset
  rw [← Finset.sum_map_val]
  congr 1
  rw [Multiset.map_map]
  rfl

/-- Two eigenvalue spectra have the same Shannon entropy. -/
theorem eigenvalueSpectrum_entropy_eq {n : ℕ} (ρ : DensityOp n)
    (evs1 evs2 : Fin n → ℝ)
    (h1 : IsEigenvalueSpectrum ρ evs1)
    (h2 : IsEigenvalueSpectrum ρ evs2) :
    shannonEntropy evs1 = shannonEntropy evs2 := by
  -- Shannon entropy equals sum over multiset, and multisets are equal
  have h_multiset_eq : eigenvalueMultiset evs1 = eigenvalueMultiset evs2 :=
    eigenvalueSpectrum_multiset_eq ρ evs1 evs2 h1 h2
  rw [shannonEntropy_eq_multiset_sum, shannonEntropy_eq_multiset_sum, h_multiset_eq]

/-- Entropy equals Shannon entropy of any valid eigenvalue spectrum. -/
theorem vonNeumannEntropy_eq_shannonEntropy {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (eigenvalues : Fin n → ℝ) (heig : IsEigenvalueSpectrum ρ eigenvalues) :
    vonNeumannEntropy ρ = shannonEntropy eigenvalues := by
  unfold vonNeumannEntropy
  exact eigenvalueSpectrum_entropy_eq ρ (eigenvaluesOf ρ) eigenvalues (eigenvaluesOf_spec ρ) heig

/-!
## Unitary Invariance of Entropy

Unitary conjugation preserves eigenvalues, hence entropy.
-/

/-- Eigenvalue spectrum is preserved under unitary evolution.
    If `evs` is an eigenvalue spectrum for `ρ`, then `evs` is also an eigenvalue
    spectrum for `U.evolve ρ` (= U ρ U†). This follows from:
    if ρ = V† D V, then U ρ U† = W† D W where W = V U† is unitary. -/
lemma IsEigenvalueSpectrum_unitary_evolve {n : ℕ} (U : UnitaryOp n)
    (ρ : DensityOp n) (evs : Fin n → ℝ)
    (h : IsEigenvalueSpectrum ρ evs) :
    IsEigenvalueSpectrum (U.evolve ρ) evs := by
  obtain ⟨h_nn, h_sum, h_le, V, hVV, hVV', hspec⟩ := h
  refine ⟨h_nn, h_sum, h_le, ?_⟩
  -- New unitary: W = V * U†, so W† = U * V†
  use V * U.toOp.conjTranspose
  refine ⟨?_, ?_, ?_⟩
  · -- W† * W = U * V† * V * U† = U * U† = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc U.toOp * V.conjTranspose * (V * U.toOp.conjTranspose)
        = U.toOp * (V.conjTranspose * V) * U.toOp.conjTranspose := by
          simp only [Matrix.mul_assoc]
      _ = U.toOp * 1 * U.toOp.conjTranspose := by rw [hVV]
      _ = U.toOp * U.toOp.conjTranspose := by rw [Matrix.mul_one]
      _ = 1 := U.unitary_right
  · -- W * W† = V * U† * U * V† = V * V† = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc (V * U.toOp.conjTranspose) * (U.toOp * V.conjTranspose)
        = V * (U.toOp.conjTranspose * U.toOp) * V.conjTranspose := by
          simp only [Matrix.mul_assoc]
      _ = V * 1 * V.conjTranspose := by rw [U.unitary_left]
      _ = V * V.conjTranspose := by rw [Matrix.mul_one]
      _ = 1 := hVV'
  · -- (U.evolve ρ).toOp = W† * D * W
    change U.toOp * ρ.toOp * U.toOp.conjTranspose =
      (V * U.toOp.conjTranspose).conjTranspose *
      Matrix.diagonal (fun i => (evs i : ℂ)) *
      (V * U.toOp.conjTranspose)
    rw [hspec, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]

/-- **Unitary invariance of von Neumann entropy**: S(UρU†) = S(ρ).

    Unitary conjugation preserves eigenvalues, so the Shannon entropy of the
    eigenvalue spectrum is unchanged. -/
theorem vonNeumannEntropy_unitary_evolve {n : ℕ} [NeZero n] (U : UnitaryOp n)
    (ρ : DensityOp n) :
    vonNeumannEntropy (U.evolve ρ) = vonNeumannEntropy ρ := by
  -- The eigenvalues of ρ are also valid eigenvalues for U.evolve ρ
  have h_spec_evolved :=
    IsEigenvalueSpectrum_unitary_evolve U ρ (eigenvaluesOf ρ) (eigenvaluesOf_spec ρ)
  -- Entropy depends only on the eigenvalue multiset
  unfold vonNeumannEntropy
  exact eigenvalueSpectrum_entropy_eq (U.evolve ρ) (eigenvaluesOf (U.evolve ρ))
    (eigenvaluesOf ρ) (eigenvaluesOf_spec (U.evolve ρ)) h_spec_evolved

/-!
### Tensor product and Schmidt decomposition helpers
-/

open Matrix
open scoped Matrix BigOperators ComplexConjugate TensorProduct Kronecker

/-- Helper: Reindexed diagonal of Kronecker product is diagonal of products. -/
private lemma reindex_diagonal_kronecker {n m : ℕ} (a : Fin n → ℂ) (b : Fin m → ℂ) :
    reindex finProdFinEquiv finProdFinEquiv
      (kroneckerMap (· * ·) (diagonal a) (diagonal b)) =
    diagonal (fun k => a (finProdFinEquiv.symm k).1 * b (finProdFinEquiv.symm k).2) := by
  rw [diagonal_kronecker_diagonal]
  ext i j
  simp only [reindex_apply, submatrix_apply, diagonal, of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : finProdFinEquiv.symm i ≠ finProdFinEquiv.symm j := by
      intro heq; exact h (finProdFinEquiv.symm.injective heq)
    simp only [h, ite_false, h']

/-- Helper: Op.tensor of diagonals is diagonal of products (reindexed). -/
lemma Op_tensor_diagonal {n m : ℕ} (a : Fin n → ℂ) (b : Fin m → ℂ) :
    Op.tensor (diagonal a) (diagonal b) =
    diagonal (fun k => a (finProdFinEquiv.symm k).1 * b (finProdFinEquiv.symm k).2) := by
  unfold Op.tensor
  exact reindex_diagonal_kronecker a b


/-- Coefficient matrix of a pure bipartite state: ψ = Σᵢⱼ Cᵢⱼ |i⟩⊗|j⟩.

    For a ket |ψ⟩ in the tensor product space H_A ⊗ H_B (dimension n × m),
    the coefficient matrix C is the n×m matrix such that:
      ψ = Σᵢⱼ Cᵢⱼ |i⟩_A ⊗ |j⟩_B

    The Schmidt decomposition states that C = UΣV† where Σ has the
    Schmidt coefficients on the diagonal.

    **Note**: The indexing uses finProdFinEquiv to relate Fin (n*m) to Fin n × Fin m. -/
def coefficientMatrix {n m : ℕ} (ψ : Ket (n * m)) : Matrix (Fin n) (Fin m) ℂ :=
  Matrix.of fun i j => ψ.vec (finProdFinEquiv (i, j))

end InfoTheory.VonNeumannEntropy

end
