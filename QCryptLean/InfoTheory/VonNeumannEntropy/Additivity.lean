import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Math.SpectralTheory.Basic
import QCryptLean.Quantum.Operators.DensityOperator

/-!
# Entropy Additivity and Araki–Lieb — tensor product entropy, Schmidt eigenvalues

Additivity of von Neumann entropy under tensor products and the Araki-Lieb equality
for pure bipartite states.

## Main statements
- `vonNeumannEntropy_tensor_additive`: S(ρ ⊗ σ) = S(ρ) + S(σ)
- `vonNeumannEntropy_tensorPowGen`: S(ρ^⊗n) = n · S(ρ)
- `schmidt_same_nonzero_eigenvalues`: Partial traces of a pure state share eigenvalue spectra
- `purification_entropy_equality`: S(Tr_A ρ) = S(Tr_B ρ) for pure ρ
-/

open Quantum.Operators Quantum.TensorProducts Math.ClassicalEntropy InfoTheory.VonNeumannEntropy
open Matrix

noncomputable section

namespace InfoTheory.VonNeumannEntropy

/-!
## Helper Lemmas for Tensor Product Eigenvalues
-/

/-- Helper: Symmetrized form of tensor_mul. -/
private lemma Op_tensor_mul_symm {n m : ℕ} (A C : Op n) (B D : Op m) :
    Op.tensor (A * C) (B * D) = Op.tensor A B * Op.tensor C D :=
  (Op.tensor_mul A C B D).symm

/-!
## Dimension Casting
-/

/-- Von Neumann entropy is invariant under dimension casting.
    Since castDim is defined by transport (h ▸ ρ), the eigenvalues are unchanged. -/
lemma vonNeumannEntropy_castDim {n m : ℕ} [inst_n : NeZero n] [inst_m : NeZero m]
    (h : n = m) (ρ : DensityOp n) :
    vonNeumannEntropy (DensityOp.castDim h ρ) = vonNeumannEntropy ρ := by
  subst h
  simp [DensityOp.castDim]

/-!
## Trivial States
-/

/-- Von Neumann entropy of the trivial (1-dimensional) density operator is zero.
    The trivial density operator is pure (rank 1), so its entropy vanishes. -/
lemma vonNeumannEntropy_trivial :
    vonNeumannEntropy DensityOp.trivial = 0 := by
  apply vonNeumannEntropy_pure
  -- Need to show DensityOp.trivial is pure (i.e., ρ² = ρ)
  unfold DensityOp.IsPure
  -- Goal: !![1] * !![1] = !![1]
  simp [DensityOp.trivial]

/-!
## Tensor Product Additivity

The key theorem is that von Neumann entropy is additive for tensor products:
S(ρ ⊗ σ) = S(ρ) + S(σ)
-/

/-- Additivity of von Neumann entropy for tensor products.

For independent systems: S(ρ ⊗ σ) = S(ρ) + S(σ)

This extends to n-fold tensor powers: S(ρ^⊗n) = n · S(ρ)

**Proof strategy (using SpectralTheory directly)**:
1. Define product eigenvalues: λₖ = λᵢ · μⱼ where k = (i,j)
2. Show these form a valid eigenvalue spectrum for ρ.tensor σ
3. Use `vonNeumannEntropy_eq_shannonEntropy` with this spectrum
4. Apply `shannonEntropy_product` to get additivity

Proved directly: the spectral decompositions of `ρ` and `σ` are combined into an explicit
`IsEigenvalueSpectrum` witness for `ρ.tensor σ` (unitary `Uρ ⊗ Uσ`, diagonal `diagonal
(λᵢ·μⱼ)`), so this does not go through a general Kronecker-eigenvalue theorem such as
`Math.SpectralTheory.eigenvalue_kronecker_multiset_eq`. -/
theorem vonNeumannEntropy_tensor_additive {n m : ℕ} [NeZero n] [NeZero m]
    (ρ : DensityOp n) (σ : DensityOp m) :
    vonNeumannEntropy (DensityOp.castDim (by ring : n * m = n * m) (ρ.tensor σ)) =
    vonNeumannEntropy ρ + vonNeumannEntropy σ := by
  -- Remove castDim using invariance
  have h_cast := vonNeumannEntropy_castDim (by ring : n * m = n * m) (ρ.tensor σ)
  rw [h_cast]
  -- Get the eigenvalue spectra
  have hρ := eigenvaluesOf_spec ρ
  have hσ := eigenvaluesOf_spec σ
  unfold IsEigenvalueSpectrum at hρ hσ
  obtain ⟨hρ_nonneg, hρ_sum, hρ_le, hρ_spec⟩ := hρ
  obtain ⟨hσ_nonneg, hσ_sum, hσ_le, hσ_spec⟩ := hσ
  -- Define product eigenvalues: λₖ = λᵢ · μⱼ where k corresponds to (i,j)
  let prodEigs : Fin (n * m) → ℝ := fun k =>
    let ⟨i, j⟩ := finProdFinEquiv.symm k
    eigenvaluesOf ρ i * eigenvaluesOf σ j
  -- Prove that prodEigs is a valid eigenvalue spectrum for ρ.tensor σ
  have h_prodEigs_spec : IsEigenvalueSpectrum (ρ.tensor σ) prodEigs := by
    -- This requires proving:
    -- (a) Non-negativity: λᵢ · μⱼ ≥ 0 (follows from both factors ≥ 0)
    -- (b) Sum to 1: ∑ₖ λᵢ·μⱼ = (∑ᵢ λᵢ)·(∑ⱼ μⱼ) = 1·1 = 1
    -- (c) ≤ 1: λᵢ·μⱼ ≤ 1 (follows from both factors ≤ 1)
    -- (d) Spectral decomposition using kronecker eigenvalue theorem
    refine ⟨?nonneg, ?sum_one, ?le_one, ?spec⟩
    case nonneg =>
      intro k
      simp only [prodEigs]
      exact mul_nonneg (hρ_nonneg _) (hσ_nonneg _)
    case sum_one =>
      -- Convert sum over Fin (n*m) to double sum
      have h_reindex : ∑ k : Fin (n * m), prodEigs k =
          ∑ k : Fin n × Fin m, eigenvaluesOf ρ k.1 * eigenvaluesOf σ k.2 := by
        apply Fintype.sum_equiv finProdFinEquiv.symm
        intro k; simp [prodEigs, finProdFinEquiv]
      rw [h_reindex, Fintype.sum_prod_type]
      calc ∑ i, ∑ j, eigenvaluesOf ρ i * eigenvaluesOf σ j
          = ∑ i, eigenvaluesOf ρ i * ∑ j, eigenvaluesOf σ j := by
            congr 1; ext i; rw [← Finset.mul_sum]
        _ = ∑ i, eigenvaluesOf ρ i * 1 := by rw [hσ_sum]
        _ = ∑ i, eigenvaluesOf ρ i := by simp only [mul_one]
        _ = 1 := hρ_sum
    case le_one =>
      intro k
      simp only [prodEigs]
      calc eigenvaluesOf ρ _ * eigenvaluesOf σ _
          ≤ 1 * 1 := mul_le_mul (hρ_le _) (hσ_le _) (hσ_nonneg _) (by linarith)
        _ = 1 := by ring
    case spec =>
      -- Construct the tensor of unitaries from spectral decompositions
      obtain ⟨Uρ, hUρU, hUρU', hspec_ρ⟩ := hρ_spec
      obtain ⟨Uσ, hUσU, hUσU', hspec_σ⟩ := hσ_spec
      -- Let Dρ and Dσ be the diagonal matrices
      set Dρ : Op n := diagonal (fun i => (eigenvaluesOf ρ i : ℂ)) with hDρ_def
      set Dσ : Op m := diagonal (fun j => (eigenvaluesOf σ j : ℂ)) with hDσ_def
      -- The combined unitary is Uρ ⊗ Uσ
      set V : Op (n * m) := Op.tensor Uρ Uσ with hV_def
      use V
      constructor
      · -- V† * V = 1
        calc V.conjTranspose * V
            = (Op.tensor Uρ Uσ).conjTranspose * Op.tensor Uρ Uσ := by rw [hV_def]
          _ = Op.tensor Uρ.conjTranspose Uσ.conjTranspose * Op.tensor Uρ Uσ := by
              rw [Op.tensor_conjTranspose]
          _ = Op.tensor (Uρ.conjTranspose * Uρ) (Uσ.conjTranspose * Uσ) := by
              rw [Op.tensor_mul]
          _ = Op.tensor 1 1 := by rw [hUρU, hUσU]
          _ = 1 := Op.tensor_one
      constructor
      · -- V * V† = 1
        calc V * V.conjTranspose
            = Op.tensor Uρ Uσ * (Op.tensor Uρ Uσ).conjTranspose := by rw [hV_def]
          _ = Op.tensor Uρ Uσ * Op.tensor Uρ.conjTranspose Uσ.conjTranspose := by
              rw [Op.tensor_conjTranspose]
          _ = Op.tensor (Uρ * Uρ.conjTranspose) (Uσ * Uσ.conjTranspose) := by
              rw [Op.tensor_mul]
          _ = Op.tensor 1 1 := by rw [hUρU', hUσU']
          _ = 1 := Op.tensor_one
      · -- ρ⊗σ = V† * D * V where D = diagonal(prodEigs)
        have h_tensor_op : (ρ.tensor σ).toOp = Op.tensor ρ.toOp σ.toOp := rfl
        -- Key: show Op.tensor Dρ Dσ = diagonal prodEigs (as complex)
        have h_diag_eq : Op.tensor Dρ Dσ = diagonal (fun k => (prodEigs k : ℂ)) := by
          rw [hDρ_def, hDσ_def]
          rw [Op_tensor_diagonal]
          congr 1
          ext k
          simp only [prodEigs, Complex.ofReal_mul]
        -- Expand using spectral decompositions
        rw [h_tensor_op, hspec_ρ, hspec_σ]
        -- Use Op_tensor_mul_symm to expand the LHS
        have step1 : Op.tensor ((Uρ.conjTranspose * Dρ) * Uρ) ((Uσ.conjTranspose * Dσ) * Uσ) =
            Op.tensor (Uρ.conjTranspose * Dρ) (Uσ.conjTranspose * Dσ) * Op.tensor Uρ Uσ := by
          rw [Op_tensor_mul_symm]
        have step2 : Op.tensor (Uρ.conjTranspose * Dρ) (Uσ.conjTranspose * Dσ) =
            Op.tensor Uρ.conjTranspose Uσ.conjTranspose * Op.tensor Dρ Dσ := by
          rw [Op_tensor_mul_symm]
        calc Op.tensor ((Uρ.conjTranspose * Dρ) * Uρ) ((Uσ.conjTranspose * Dσ) * Uσ)
            = Op.tensor (Uρ.conjTranspose * Dρ) (Uσ.conjTranspose * Dσ) * Op.tensor Uρ Uσ := step1
          _ = (Op.tensor Uρ.conjTranspose Uσ.conjTranspose * Op.tensor Dρ Dσ) *
                Op.tensor Uρ Uσ := by rw [step2]
          _ = Op.tensor Uρ.conjTranspose Uσ.conjTranspose *
                (Op.tensor Dρ Dσ * Op.tensor Uρ Uσ) := by rw [mul_assoc]
          _ = Op.tensor Uρ.conjTranspose Uσ.conjTranspose * Op.tensor Dρ Dσ * Op.tensor Uρ Uσ := by
              rw [← mul_assoc]
          _ = (Op.tensor Uρ Uσ).conjTranspose * Op.tensor Dρ Dσ * Op.tensor Uρ Uσ := by
              rw [Op.tensor_conjTranspose]
          _ = V.conjTranspose * Op.tensor Dρ Dσ * V := by rw [hV_def]
          _ = V.conjTranspose * diagonal (fun k => (prodEigs k : ℂ)) * V := by
              rw [h_diag_eq]
  -- Apply von Neumann entropy formula with the product eigenvalue spectrum
  have h_entropy : vonNeumannEntropy (ρ.tensor σ) =
      shannonEntropy prodEigs := by
    exact vonNeumannEntropy_eq_shannonEntropy (ρ.tensor σ) prodEigs h_prodEigs_spec
  rw [h_entropy]
  -- Unfold prodEigs and apply shannonEntropy_product
  unfold vonNeumannEntropy
  exact shannonEntropy_product
    (eigenvaluesOf ρ)
    (eigenvaluesOf σ)
    hρ_nonneg hσ_nonneg hρ_sum hσ_sum

/-!
## Tensor Powers
-/

/-- Entropy of n-fold tensor power: S(ρ^⊗n) = n · S(ρ) (general dimension).

**Proof strategy**: Induction on n
- Base case n=0: tensorPowGen 0 = trivial (after castDim), which has entropy 0
- Inductive step: tensorPowGen (k+1) = ρ ⊗ (ρ^⊗k), use additivity

**Note**: This proof structure is established even though helper lemmas
(vonNeumannEntropy_tensor_additive) still contain sorries.
The proof architecture is sound and will complete once those are filled in. -/
-- Helper lemma without the NeZero instance parameter (to avoid induction issues)
private theorem vonNeumannEntropy_tensorPowGen_aux {d : ℕ} [NeZero d] (n : ℕ) (ρ : DensityOp d) :
    haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
    vonNeumannEntropy (ρ.tensorPowGen n) = n * vonNeumannEntropy ρ := by
  induction n with
  | zero =>
    -- Base case: tensorPowGen 0 = castDim trivial, entropy of trivial is 0
    simp only [DensityOp.tensorPowGen]
    haveI : NeZero (d ^ 0) := ⟨by simp⟩
    have hcast := @vonNeumannEntropy_castDim 1 (d ^ 0) (NeZero.one) _
      (by simp : 1 = d ^ 0) DensityOp.trivial
    rw [hcast]
    rw [vonNeumannEntropy_trivial]
    ring
  | succ k ih =>
    -- Inductive case: tensorPowGen (k+1) = castDim (ρ.tensor (ρ.tensorPowGen k))
    simp only [DensityOp.tensorPowGen]
    -- Need NeZero (d ^ k) for the inductive hypothesis
    haveI hk : NeZero (d ^ k) := ⟨pow_ne_zero k (NeZero.ne d)⟩
    haveI hdk : NeZero (d * d ^ k) := ⟨by simp [NeZero.ne d]⟩
    haveI hsucc : NeZero (d ^ (k + 1)) := ⟨pow_ne_zero (k + 1) (NeZero.ne d)⟩
    have hcast := @vonNeumannEntropy_castDim (d * d ^ k) (d ^ (k + 1)) hdk hsucc
      (by ring : d * d ^ k = d ^ (k + 1)) (ρ.tensor (ρ.tensorPowGen k))
    rw [hcast]
    -- Use additivity: S(ρ ⊗ σ) = S(ρ) + S(σ)
    have h_add := vonNeumannEntropy_tensor_additive ρ (ρ.tensorPowGen k)
    rw [vonNeumannEntropy_castDim] at h_add
    rw [h_add, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem vonNeumannEntropy_tensorPowGen {d : ℕ} [NeZero d] (n : ℕ) [NeZero (d ^ n)]
    (ρ : DensityOp d) :
    vonNeumannEntropy (ρ.tensorPowGen n) = n * vonNeumannEntropy ρ :=
  vonNeumannEntropy_tensorPowGen_aux n ρ

/-- Entropy of n-fold tensor power: S(ρ^⊗n) = n · S(ρ) (dimension 4 for BB84).

    Specialization of vonNeumannEntropy_tensorPowGen for d=4. -/
theorem vonNeumannEntropy_tensorPow (n : ℕ) [NeZero (4 ^ n)]
    (ρ : DensityOp 4) :
    vonNeumannEntropy (ρ.tensorPow n) = n * vonNeumannEntropy ρ := by
  -- tensorPow is defined as tensorPowGen for d=4
  unfold DensityOp.tensorPow
  exact vonNeumannEntropy_tensorPowGen n ρ

/-!
## Coefficient Matrix Infrastructure

For the Schmidt decomposition, we need to relate pure bipartite states
to their coefficient matrices.
-/

/-- Partial trace over B equals CC† for coefficient matrix C.

    For a pure state ρ = |ψ⟩⟨ψ| with coefficient matrix C:
    Tr_B(ρ) = CC†  (reduced state on first subsystem) -/
theorem partialTraceB_eq_mul_conjTranspose {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * m)]
    (ψ : Ket (n * m))
    (hρ : (Matrix.of fun i j => ψ.vec i * star (ψ.vec j)).IsHermitian) :
    let C := coefficientMatrix ψ
    let ρ_op : Op (n * m) := Matrix.of fun i j => ψ.vec i * star (ψ.vec j)
    (HermitianOp.partialTraceB ⟨ρ_op, hρ⟩).toOp = C * C.conjTranspose := by
  ext i k
  simp only [HermitianOp.partialTraceB]
  unfold partialTraceB coefficientMatrix
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Eigenvalues of Tr_A(ρ) equal eigenvalues of C†C (as multisets).

    For a pure state ρ = |ψ⟩⟨ψ| with coefficient matrix C:
    - Tr_A(ρ)[j,l] = ∑_i C[i,j] * star(C[i,l]) = star((C†C)[j,l])
    - Since Tr_A(ρ) = conj(C†C) (entry-wise conjugate), they have the same eigenvalues
      (conjugation preserves eigenvalues of Hermitian matrices)

    **Note**: Tr_A(ρ) ≠ C†C as matrices, but they share the same spectrum.
    This is sufficient for entropy calculations. -/
theorem partialTraceA_eigenvalues_eq_conjTranspose_mul {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * m)]
    (ψ : Ket (n * m))
    (hρ : (Matrix.of fun i j => ψ.vec i * star (ψ.vec j)).IsHermitian) :
    let C := coefficientMatrix ψ
    let ρ_op : Op (n * m) := Matrix.of fun i j => ψ.vec i * star (ψ.vec j)
    let hTrA := partialTraceA_hermitian ρ_op hρ
    let hCtC := Math.SpectralTheory.conjTranspose_mul_isHermitian C
    shannonEntropy hTrA.eigenvalues = shannonEntropy hCtC.eigenvalues := by
  intro C ρ_op hTrA hCtC
  -- Step 1: Show partialTraceA ρ_op = (C†C).map star
  have h_eq : partialTraceA ρ_op = (C.conjTranspose * C).map star := by
    ext j l
    unfold partialTraceA
    simp only [of_apply, mul_apply, conjTranspose_apply, map_apply]
    rw [star_sum]
    congr 1
    ext k
    have hC : C k j = ψ.vec (finProdFinEquiv (k, j)) := rfl
    have hC' : C k l = ψ.vec (finProdFinEquiv (k, l)) := rfl
    rw [hC, hC']
    simp only [star_mul', star_star]
    change (of fun i k => ψ.vec i * star (ψ.vec k)) (finProdFinEquiv (k, j))
        (finProdFinEquiv (k, l)) = _
    simp only [of_apply]
  -- Step 2: Use shannonEntropy preservation under entry-wise conjugation
  have h_map_star_herm := Math.SpectralTheory.map_star_isHermitian (C.conjTranspose * C) hCtC
  -- Step 3: Shannon entropy of (C†C).map star equals Shannon entropy of C†C
  have h_key : shannonEntropy h_map_star_herm.eigenvalues = shannonEntropy hCtC.eigenvalues := by
    have h_ev_eq := Math.SpectralTheory.eigenvalues_map_star_eq (C.conjTranspose * C) hCtC
    unfold shannonEntropy
    have h_sum : Finset.univ.val.map (entropyTerm ∘ h_map_star_herm.eigenvalues) =
        Finset.univ.val.map (entropyTerm ∘ hCtC.eigenvalues) := by
      calc Finset.univ.val.map (entropyTerm ∘ h_map_star_herm.eigenvalues)
          = (Finset.univ.val.map h_map_star_herm.eigenvalues).map entropyTerm := by
            rw [Multiset.map_map]
        _ = (Finset.univ.val.map hCtC.eigenvalues).map entropyTerm := by rw [h_ev_eq]
        _ = Finset.univ.val.map (entropyTerm ∘ hCtC.eigenvalues) := by rw [← Multiset.map_map]
    conv_lhs =>
      rw [show ∑ i : Fin m, entropyTerm (h_map_star_herm.eigenvalues i) =
          (Finset.univ.val.map (entropyTerm ∘ h_map_star_herm.eigenvalues)).sum from by
        simp only [Function.comp_apply, ← Finset.sum_map_val]]
    conv_rhs =>
      rw [show ∑ i : Fin m, entropyTerm (hCtC.eigenvalues i) =
          (Finset.univ.val.map (entropyTerm ∘ hCtC.eigenvalues)).sum from by
        simp only [Function.comp_apply, ← Finset.sum_map_val]]
    rw [h_sum]
  -- Step 4: Show hTrA.eigenvalues = h_map_star_herm.eigenvalues since matrices are equal
  have h_eigen_eq : ∀ i, hTrA.eigenvalues i = h_map_star_herm.eigenvalues i :=
    Math.SpectralTheory.eigenvalues_eq_of_matrix_eq _ _ hTrA h_map_star_herm h_eq
  -- Step 5: Conclude
  calc shannonEntropy hTrA.eigenvalues
      = shannonEntropy h_map_star_herm.eigenvalues := by
        unfold shannonEntropy
        congr 1
        ext i
        rw [h_eigen_eq i]
    _ = shannonEntropy hCtC.eigenvalues := h_key

/-- Non-zero eigenvalues of CC† and C†C are equal (spectral theorem for SVD).

    This is a fundamental result in linear algebra: for any matrix C,
    the non-zero singular values of C are the square roots of the
    non-zero eigenvalues of both CC† and C†C.

    **Consequence**: If ρ_A = CC† and ρ_B = C†C, then
      spec_nonzero(ρ_A) = spec_nonzero(ρ_B)

    **Reference**: Horn & Johnson, "Matrix Analysis", Theorem 7.3.3.

    **BLOCKED ON**: SVD infrastructure in Mathlib. -/
theorem eigenvalues_conjTranspose_mul_eq {n m : ℕ} [NeZero n] [NeZero m]
    (C : Matrix (Fin n) (Fin m) ℂ)
    (hCC : (C * C.conjTranspose).IsHermitian)
    (hCtC : (C.conjTranspose * C).IsHermitian) :
    -- The Shannon entropies of the eigenvalue spectra are equal
    -- (This is weaker than saying the non-zero eigenvalues are equal,
    -- but sufficient for entropy calculations)
    shannonEntropy (fun i => hCC.eigenvalues i) =
    shannonEntropy (fun j => hCtC.eigenvalues j) := by
  -- Uses the proven theorem from SpectralTheory:
  -- nonzero_eigenvalues_conjTranspose_mul_eq: non-zero eigenvalues are equal (as multisets)
  -- Since entropyTerm 0 = 0, Shannon entropy equals sum over non-zero eigenvalues only
  --
  -- Abbrevations for the canonical Hermitian proofs
  let hCC' := Math.SpectralTheory.mul_conjTranspose_isHermitian C
  let hCtC' := Math.SpectralTheory.conjTranspose_mul_isHermitian C
  --
  -- Step 1: Express Shannon entropy in terms of multiset sums
  unfold shannonEntropy
  simp only [← Finset.sum_map_val]
  --
  -- Rewrite as multiset map
  have h_sum_CC : Finset.univ.val.map (fun i => entropyTerm (hCC.eigenvalues i)) =
      (Finset.univ.val.map hCC.eigenvalues).map entropyTerm := by
    rw [Multiset.map_map]; rfl
  have h_sum_CtC : Finset.univ.val.map (fun i => entropyTerm (hCtC.eigenvalues i)) =
      (Finset.univ.val.map hCtC.eigenvalues).map entropyTerm := by
    rw [Multiset.map_map]; rfl
  rw [h_sum_CC, h_sum_CtC]
  --
  -- Step 2: Eigenvalues depend on the matrix only, not the proof of Hermitian
  -- Both hCC and hCC' are proofs of (C * Cᴴ).IsHermitian, so eigenvalues are equal
  -- For two different proofs of IsHermitian for the same matrix,
  -- the eigenvalues are equal because eigenvalues depends only on the matrix
  have h_ev_CC : Finset.univ.val.map hCC.eigenvalues = Finset.univ.val.map hCC'.eigenvalues := rfl
  have h_ev_CtC : Finset.univ.val.map hCtC.eigenvalues = Finset.univ.val.map hCtC'.eigenvalues :=
      rfl
  rw [h_ev_CC, h_ev_CtC]
  --
  -- Step 3: Apply nonzero_eigenvalues_conjTranspose_mul_eq
  -- The non-zero eigenvalue multisets are equal
  have h_nonzero_eq := Math.SpectralTheory.nonzero_eigenvalues_conjTranspose_mul_eq C
  unfold Math.SpectralTheory.nonzeroEigenvalues
      Math.SpectralTheory.hermitianEigenvalues at h_nonzero_eq
  --
  -- Step 4: Decompose into zero and non-zero parts and show equality
  -- Since entropyTerm 0 = 0, sum = sum over non-zero eigenvalues only
  -- Helper lemma: Shannon entropy sum = sum over non-zero eigenvalues
  have h_entropy_nonzero : ∀ (evs : Multiset ℝ),
      (evs.map entropyTerm).sum = ((evs.filter (· ≠ 0)).map entropyTerm).sum := by
    intro evs
    have h_filter_zero : ((evs.filter (· = 0)).map entropyTerm).sum = 0 := by
      rw [Multiset.sum_eq_zero]
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨a, ha_mem, ha_eq⟩ := hx
      rw [Multiset.mem_filter] at ha_mem
      rw [← ha_eq, ha_mem.2, entropyTerm_zero]
    have h_filter_decomp : evs = evs.filter (· ≠ 0) + evs.filter (· = 0) := by
      symm
      have h := Multiset.filter_add_not (· ≠ 0) evs
      simp only [ne_eq, Decidable.not_not] at h
      exact h
    conv_lhs => rw [h_filter_decomp, Multiset.map_add, Multiset.sum_add, h_filter_zero, add_zero]
  --
  -- Apply the helper to both sides
  rw [h_entropy_nonzero (Finset.univ.val.map hCC'.eigenvalues)]
  rw [h_entropy_nonzero (Finset.univ.val.map hCtC'.eigenvalues)]
  -- Now apply the nonzero eigenvalue equality
  rw [h_nonzero_eq]

/-!
## Schmidt Decomposition and Araki-Lieb
-/

/-- **Schmidt decomposition eigenvalue equality**: For a pure bipartite state,
the reduced density matrices have the same non-zero eigenvalues.

For ρ : DensityOp (n * m) pure, let:
- ρ_A = Tr_B(ρ) : DensityOp n  (partial trace over second subsystem)
- ρ_B = Tr_A(ρ) : DensityOp m  (partial trace over first subsystem)

Then spec(ρ_A) and spec(ρ_B) have the same non-zero eigenvalues.

**Proof sketch** (via coefficient matrix):
1. Write pure state as |ψ⟩ = Σᵢⱼ cᵢⱼ |i⟩⊗|j⟩ for some coefficient matrix C
2. Form the coefficient matrix C with entries cᵢⱼ
3. Apply SVD: C = UΣV† where Σ has singular values √λᵢ
4. Then ρ_A = CC† has eigenvalues λᵢ (with possible zeros)
5. And ρ_B = C†C has eigenvalues λᵢ (with possible zeros)
6. Therefore spec(ρ_A) = spec(ρ_B) (as multisets, counting multiplicities)

Note: The dimensions of ρ_A (dim m) and ρ_B (dim n) may differ, but the
non-zero eigenvalues match. Zero eigenvalues pad the smaller spectrum.

**BLOCKED ON**: Coefficient matrix infrastructure for pure states.
Once `Math.SpectralTheory.nonzero_eigenvalues_conjTranspose_mul_eq` is connected
to the partial trace definitions via coefficient matrices, this theorem follows. -/
theorem schmidt_same_nonzero_eigenvalues {n m : ℕ} [NeZero n] [NeZero m]
    (ρ : DensityOp (n * m)) (hpure : ρ.IsPure) :
    -- The non-zero eigenvalues of both reduced states are equal (as multisets)
    -- This is stated via the Shannon entropy being equal
    shannonEntropy (eigenvaluesOf ρ.partialTraceA) =
    shannonEntropy (eigenvaluesOf ρ.partialTraceB) := by
  /-
  **PROOF STRATEGY**:

  1. Extract the underlying ket ψ from pure state ρ using pureKetOf
  2. Form the coefficient matrix C = coefficientMatrix ψ
  3. Use pureKetOf_entry to show ρ.toOp i j = ψ.vec i * star (ψ.vec j)
  4. Show partialTraceB(ρ) = CC† and partialTraceA(ρ) relates to C†C
  5. Apply eigenvalues_conjTranspose_mul_eq to get Shannon entropy equality
  6. Use eigenvalueSpectrum_entropy_eq to relate eigenvaluesOf to Hermitian eigenvalues
  -/
  -- Step 1: Extract the ket from the pure state
  haveI : NeZero (n * m) := ⟨Nat.mul_pos (NeZero.pos n) (NeZero.pos m) |>.ne'⟩
  let ψ := ρ.pureKetOf hpure
  -- Step 2: Form the coefficient matrix
  let C := coefficientMatrix ψ
  -- Step 3: Show the relationship between ρ and ψ
  have h_entry : ∀ i j, ρ.toOp i j = ψ.vec i * star (ψ.vec j) := by
    intro i j
    exact ρ.pureKetOf_entry hpure i j
  -- Step 4: Construct the Hermitian proofs for the partial traces
  let hTrA := ρ.partialTraceA.toPosSemidefOp.toHermitianOp.isHermitian
  let hTrB := ρ.partialTraceB.toPosSemidefOp.toHermitianOp.isHermitian
  -- Step 5: Get Hermitian proofs for CC† and C†C
  let hCC := Math.SpectralTheory.mul_conjTranspose_isHermitian C
  let hCtC := Math.SpectralTheory.conjTranspose_mul_isHermitian C
  -- Step 6: Show partialTraceB(ρ) = CC†
  have h_traceB_eq : ρ.partialTraceB.toOp = C * C.conjTranspose := by
    ext i k
    unfold DensityOp.partialTraceB PosSemidefOp.partialTraceB partialTraceB
    simp only [Matrix.of_apply]
    -- LHS: ∑ j, ρ (finProdFinEquiv (i, j)) (finProdFinEquiv (k, j))
    -- RHS: (C * C†)_{i,k} = ∑ j, C_{i,j} * conj(C_{k,j})
    rw [mul_apply]
    congr 1
    ext j
    rw [conjTranspose_apply, h_entry]
    -- C is defined as coefficientMatrix ψ, so C i j = ψ.vec (finProdFinEquiv (i, j))
    change ψ.vec (finProdFinEquiv (i, j)) * star (ψ.vec (finProdFinEquiv (k, j))) =
         (coefficientMatrix ψ) i j * star ((coefficientMatrix ψ) k j)
    simp only [coefficientMatrix, Matrix.of_apply]
  -- Step 7: Show partialTraceA(ρ) relates to C†C through conjugation
  -- partialTraceA(ρ)[j,l] = ∑_i ρ[(i,j), (i,l)] = ∑_i ψ[i,j] * conj(ψ[i,l])
  --                       = ∑_i C[i,j] * conj(C[i,l]) = (C†C)[j,l].map star
  have h_traceA_eq : ρ.partialTraceA.toOp = (C.conjTranspose * C).map star := by
    ext j l
    unfold DensityOp.partialTraceA PosSemidefOp.partialTraceA partialTraceA
    simp only [Matrix.of_apply, map_apply]
    rw [mul_apply]
    rw [star_sum]
    congr 1
    ext i
    rw [conjTranspose_apply, h_entry]
    -- Goal: ψ.vec (finProdFinEquiv (i, j)) * star (ψ.vec (finProdFinEquiv (i, l))) =
    --       star (star (C i j) * C i l)
    -- C i j = (coefficientMatrix ψ) i j = ψ.vec (finProdFinEquiv (i, j))
    have hCij : C i j = ψ.vec (finProdFinEquiv (i, j)) := rfl
    have hCil : C i l = ψ.vec (finProdFinEquiv (i, l)) := rfl
    rw [hCij, hCil]
    simp only [star_mul', star_star]
  -- Step 8: Use eigenvalue equality for CC† and C†C
  -- First, show Shannon entropy of eigenvalues of CC† equals that of C†C
  have h_CC_CtC := eigenvalues_conjTranspose_mul_eq C hCC hCtC
  -- Step 9: Connect eigenvaluesOf to Hermitian eigenvalues via IsEigenvalueSpectrum
  -- For partialTraceB: eigenvaluesOf gives same entropy as hTrB.eigenvalues
  have hspec_TrB : IsEigenvalueSpectrum ρ.partialTraceB hTrB.eigenvalues := by
    have := density_has_spectrum ρ.partialTraceB
    have hPSD := posSemidefOp_implies_mathlib ρ.partialTraceB.toPosSemidefOp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; exact hPSD.eigenvalues_nonneg i
    · have h_trace := ρ.partialTraceB.trace_one
      have h_sum := hTrB.trace_eq_sum_eigenvalues
      have h_eq : (1 : ℂ) = ∑ k, (hTrB.eigenvalues k : ℂ) := by
        calc (1 : ℂ) = ρ.partialTraceB.toOp.trace := h_trace.symm
          _ = ∑ k, (hTrB.eigenvalues k : ℂ) := h_sum
      have h_re_rhs : (∑ k, (hTrB.eigenvalues k : ℂ)).re = ∑ k, hTrB.eigenvalues k := by
        simp only [Complex.re_sum, Complex.ofReal_re]
      calc ∑ j, hTrB.eigenvalues j = (∑ j, (hTrB.eigenvalues j : ℂ)).re := h_re_rhs.symm
        _ = (1 : ℂ).re := by rw [← h_eq]
        _ = 1 := rfl
    · intro i
      have h_nonneg : ∀ j, 0 ≤ hTrB.eigenvalues j := fun j => hPSD.eigenvalues_nonneg j
      have h_sum : ∑ j, hTrB.eigenvalues j = 1 := by
        have h_trace := ρ.partialTraceB.trace_one
        have h_sum_eq := hTrB.trace_eq_sum_eigenvalues
        have h_eq : (1 : ℂ) = ∑ k, (hTrB.eigenvalues k : ℂ) := by
          calc (1 : ℂ) = ρ.partialTraceB.toOp.trace := h_trace.symm
            _ = ∑ k, (hTrB.eigenvalues k : ℂ) := h_sum_eq
        have h_re_rhs : (∑ k, (hTrB.eigenvalues k : ℂ)).re = ∑ k, hTrB.eigenvalues k := by
          simp only [Complex.re_sum, Complex.ofReal_re]
        calc ∑ j, hTrB.eigenvalues j = (∑ j, (hTrB.eigenvalues j : ℂ)).re := h_re_rhs.symm
          _ = (1 : ℂ).re := by rw [← h_eq]
          _ = 1 := rfl
      calc hTrB.eigenvalues i ≤ ∑ j, hTrB.eigenvalues j :=
              Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)
        _ = 1 := h_sum
    · let U := (hTrB.eigenvectorUnitary.val : Op n)
      let V := star U
      use V
      have h_star_mul : star U * U = 1 := Unitary.coe_star_mul_self hTrB.eigenvectorUnitary
      have h_mul_star : U * star U = 1 := by
        have h := Unitary.coe_mul_star_self hTrB.eigenvectorUnitary
        simp only [Unitary.coe_star] at h
        exact h
      constructor
      · calc star V * V = star (star U) * star U := rfl
          _ = U * star U := by rw [star_star]
          _ = 1 := h_mul_star
      constructor
      · calc V * star V = star U * star (star U) := rfl
          _ = star U * U := by rw [star_star]
          _ = 1 := h_star_mul
      · have h_spec := hTrB.spectral_theorem
        rw [Unitary.conjStarAlgAut_apply] at h_spec
        calc ρ.partialTraceB.toOp =
              U * Matrix.diagonal (fun i => (hTrB.eigenvalues i : ℂ)) * star U := h_spec
          _ = star (star U) * Matrix.diagonal (fun i => (hTrB.eigenvalues i : ℂ)) * star U := by
              rw [star_star]
          _ = star V * Matrix.diagonal (fun i => (hTrB.eigenvalues i : ℂ)) * V := rfl
  -- For partialTraceA: eigenvaluesOf gives same entropy as hTrA.eigenvalues
  have hspec_TrA : IsEigenvalueSpectrum ρ.partialTraceA hTrA.eigenvalues := by
    have := density_has_spectrum ρ.partialTraceA
    have hPSD := posSemidefOp_implies_mathlib ρ.partialTraceA.toPosSemidefOp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; exact hPSD.eigenvalues_nonneg i
    · have h_trace := ρ.partialTraceA.trace_one
      have h_sum := hTrA.trace_eq_sum_eigenvalues
      have h_eq : (1 : ℂ) = ∑ k, (hTrA.eigenvalues k : ℂ) := by
        calc (1 : ℂ) = ρ.partialTraceA.toOp.trace := h_trace.symm
          _ = ∑ k, (hTrA.eigenvalues k : ℂ) := h_sum
      have h_re_rhs : (∑ k, (hTrA.eigenvalues k : ℂ)).re = ∑ k, hTrA.eigenvalues k := by
        simp only [Complex.re_sum, Complex.ofReal_re]
      calc ∑ j, hTrA.eigenvalues j = (∑ j, (hTrA.eigenvalues j : ℂ)).re := h_re_rhs.symm
        _ = (1 : ℂ).re := by rw [← h_eq]
        _ = 1 := rfl
    · intro i
      have h_nonneg : ∀ j, 0 ≤ hTrA.eigenvalues j := fun j => hPSD.eigenvalues_nonneg j
      have h_sum : ∑ j, hTrA.eigenvalues j = 1 := by
        have h_trace := ρ.partialTraceA.trace_one
        have h_sum_eq := hTrA.trace_eq_sum_eigenvalues
        have h_eq : (1 : ℂ) = ∑ k, (hTrA.eigenvalues k : ℂ) := by
          calc (1 : ℂ) = ρ.partialTraceA.toOp.trace := h_trace.symm
            _ = ∑ k, (hTrA.eigenvalues k : ℂ) := h_sum_eq
        have h_re_rhs : (∑ k, (hTrA.eigenvalues k : ℂ)).re = ∑ k, hTrA.eigenvalues k := by
          simp only [Complex.re_sum, Complex.ofReal_re]
        calc ∑ j, hTrA.eigenvalues j = (∑ j, (hTrA.eigenvalues j : ℂ)).re := h_re_rhs.symm
          _ = (1 : ℂ).re := by rw [← h_eq]
          _ = 1 := rfl
      calc hTrA.eigenvalues i ≤ ∑ j, hTrA.eigenvalues j :=
              Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)
        _ = 1 := h_sum
    · let U := (hTrA.eigenvectorUnitary.val : Op m)
      let V := star U
      use V
      have h_star_mul : star U * U = 1 := Unitary.coe_star_mul_self hTrA.eigenvectorUnitary
      have h_mul_star : U * star U = 1 := by
        have h := Unitary.coe_mul_star_self hTrA.eigenvectorUnitary
        simp only [Unitary.coe_star] at h
        exact h
      constructor
      · calc star V * V = star (star U) * star U := rfl
          _ = U * star U := by rw [star_star]
          _ = 1 := h_mul_star
      constructor
      · calc V * star V = star U * star (star U) := rfl
          _ = star U * U := by rw [star_star]
          _ = 1 := h_star_mul
      · have h_spec := hTrA.spectral_theorem
        rw [Unitary.conjStarAlgAut_apply] at h_spec
        calc ρ.partialTraceA.toOp =
              U * Matrix.diagonal (fun i => (hTrA.eigenvalues i : ℂ)) * star U := h_spec
          _ = star (star U) * Matrix.diagonal (fun i => (hTrA.eigenvalues i : ℂ)) * star U := by
              rw [star_star]
          _ = star V * Matrix.diagonal (fun i => (hTrA.eigenvalues i : ℂ)) * V := rfl
  -- Step 10: Use eigenvalueSpectrum_entropy_eq to relate eigenvaluesOf to Hermitian eigenvalues
  have h_TrB_entropy : shannonEntropy (eigenvaluesOf ρ.partialTraceB) =
      shannonEntropy hTrB.eigenvalues :=
    eigenvalueSpectrum_entropy_eq ρ.partialTraceB _ _ (eigenvaluesOf_spec _) hspec_TrB
  have h_TrA_entropy : shannonEntropy (eigenvaluesOf ρ.partialTraceA) =
      shannonEntropy hTrA.eigenvalues :=
    eigenvalueSpectrum_entropy_eq ρ.partialTraceA _ _ (eigenvaluesOf_spec _) hspec_TrA
  -- Step 11: Connect hTrB to hCC (they're for the same matrix by h_traceB_eq)
  have h_TrB_CC : shannonEntropy hTrB.eigenvalues = shannonEntropy hCC.eigenvalues := by
    have h_eig_eq := Math.SpectralTheory.eigenvalues_eq_of_matrix_eq
      (C * C.conjTranspose) ρ.partialTraceB.toOp hCC hTrB h_traceB_eq.symm
    unfold shannonEntropy
    congr 1
    ext i
    rw [h_eig_eq i]
  -- Step 12: Connect hTrA to hCtC via map star relationship
  -- partialTraceA(ρ) = (C†C).map star, and they have the same eigenvalues
  have h_TrA_CtC : shannonEntropy hTrA.eigenvalues = shannonEntropy hCtC.eigenvalues := by
    -- Use eigenvalues_map_star_eq: eigenvalues of A.map star = eigenvalues of A (for Hermitian A)
    have h_map_star_herm := Math.SpectralTheory.map_star_isHermitian (C.conjTranspose * C) hCtC
    have h_ev_eq := Math.SpectralTheory.eigenvalues_map_star_eq (C.conjTranspose * C) hCtC
    -- Show hTrA.eigenvalues = h_map_star_herm.eigenvalues
    have h_eig_TrA := Math.SpectralTheory.eigenvalues_eq_of_matrix_eq
      ((C.conjTranspose * C).map star) ρ.partialTraceA.toOp h_map_star_herm hTrA h_traceA_eq.symm
    -- Shannon entropy through the chain
    have h1 : shannonEntropy hTrA.eigenvalues = shannonEntropy h_map_star_herm.eigenvalues := by
      unfold shannonEntropy
      congr 1
      ext i
      rw [h_eig_TrA i]
    have h2 : shannonEntropy h_map_star_herm.eigenvalues = shannonEntropy hCtC.eigenvalues := by
      -- Shannon entropy is sum of entropyTerm over eigenvalues
      -- Since the multisets of eigenvalues are equal, the sums are equal
      unfold shannonEntropy
      -- Convert to multiset sum form and use multiset equality
      have h_lhs : ∑ i, entropyTerm (h_map_star_herm.eigenvalues i) =
          ((Finset.univ.val.map h_map_star_herm.eigenvalues).map entropyTerm).sum := by
        rw [← Finset.sum_map_val, Multiset.map_map]; rfl
      have h_rhs : ∑ i, entropyTerm (hCtC.eigenvalues i) =
          ((Finset.univ.val.map hCtC.eigenvalues).map entropyTerm).sum := by
        rw [← Finset.sum_map_val, Multiset.map_map]; rfl
      rw [h_lhs, h_rhs, h_ev_eq]
    exact h1.trans h2
  -- Step 13: Chain everything together
  calc shannonEntropy (eigenvaluesOf ρ.partialTraceA)
      = shannonEntropy hTrA.eigenvalues := h_TrA_entropy
    _ = shannonEntropy hCtC.eigenvalues := h_TrA_CtC
    _ = shannonEntropy hCC.eigenvalues := h_CC_CtC.symm
    _ = shannonEntropy hTrB.eigenvalues := h_TrB_CC.symm
    _ = shannonEntropy (eigenvaluesOf ρ.partialTraceB) := h_TrB_entropy.symm

/-- **Purification entropy equality**: For a pure bipartite state ρ on `A ⊗ B`,
the two reduced states have equal von Neumann entropy: S(Tr_A ρ) = S(Tr_B ρ).

This is the key equality used when treating one factor as Eve's purifying system:
e.g. for a pure tripartite ρ_ABE, S(ρ_AB) = S(ρ_E).

**Application**: For BB84, the tripartite attack state is pure, so bounding
S(ρ_AB) also bounds S(ρ_E) (Eve's entropy).

**Proof**: Follows from the Schmidt decomposition — the two reduced states share
their non-zero eigenvalues (this is also the equality case of Araki–Lieb on pure
states). -/
theorem purification_entropy_equality {n m : ℕ} [NeZero n] [NeZero m]
    (ρ : DensityOp (n * m)) (hpure : ρ.IsPure) :
    vonNeumannEntropy ρ.partialTraceA = vonNeumannEntropy ρ.partialTraceB := by
  -- Apply Schmidt decomposition: reduced states have same non-zero eigenvalues
  -- This implies same Shannon entropy, hence same von Neumann entropy
  unfold vonNeumannEntropy
  exact schmidt_same_nonzero_eigenvalues ρ hpure

end InfoTheory.VonNeumannEntropy

end
