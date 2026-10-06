import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.Quantum.Operators.ProjectorBlocks
import Mathlib.Data.Finset.Sort

/-!
# The support projector of a density operator

The orthogonal projector onto `supp σ = range σ` for a density operator `σ`, built from the
eigenbasis of `σ`: the columns of `supportIsometry σ` are the eigenvectors with strictly
positive eigenvalue, and `supportProjector σ = V · Vᴴ` for that isometry `V`.

Everything here is about the projector itself — its idempotence and positivity, the two
annihilation laws for `σ` and its kernel, the absorption of a Löwner-dominated positive
semidefinite operator, and covariance under a unitary that fixes `σ`.  The compression of
states to `supp σ` built on top of it lives in
`QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.SupportCompression`.

## Main definitions
- `positiveSpectrumIndices`, `positiveSpectrumDim`, `positiveSpectrumEmb`: the
  positive-eigenvalue coordinates of `σ` and their enumeration
- `supportIsometry`: the isometry whose columns are the eigenvectors on `supp σ`
- `supportSelector`, `supportCoordinateProjector`: the same data in the eigenbasis
- `supportProjector`: the orthogonal projector onto `supp σ` in the ambient space

## Main statements
- `supportIsometry_isometry`: the support isometry has orthonormal columns
- `supportProjector_mul_self`, `supportProjector_posSemidef`, `supportProjector_isHermitian`:
  the projector is a positive semidefinite Hermitian idempotent
- `sigma_mul_supportProjector`, `supportProjector_mul_of_right_supported`: the projector fixes
  `σ` from either side, and `sigma_mul_supportProjector_compl`,
  `compl_supportProjector_mul_sigma`: its complement annihilates `σ` from either side
- `supportProjector_mul_of_opLe` and its three siblings: a positive semidefinite `C ⪯ σ`
  lives on `supp σ`, so the projector fixes it and the complement annihilates it
- `rho_mul_supportProjector_of_ker_sub`, `supportProjector_mulVec_eq_zero_of_ker`: the
  kernel-side characterisations
- `supportProjector_unitary_conj`: a unitary fixing `σ` by conjugation commutes with the
  projector, so `supp σ` and `ker σ` are invariant
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open InfoTheory.VonNeumannEntropy

/-! ### The positive-spectrum coordinates of a state -/

/-- Indices of the strictly positive eigenvalues of `σ`. -/
def positiveSpectrumIndices {N : ℕ} (σ : DensityOp N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => eigenvaluesOf σ i ≠ 0)

/-- Dimension of the support of `σ`, counted via its positive eigenvalues. -/
def positiveSpectrumDim {N : ℕ} (σ : DensityOp N) : ℕ :=
  (positiveSpectrumIndices σ).card

lemma positiveSpectrumDim_pos {N : ℕ} (σ : DensityOp N) :
    0 < positiveSpectrumDim σ := by
  classical
  by_contra hdim
  have hdim0 : positiveSpectrumDim σ = 0 := Nat.eq_zero_of_not_pos hdim
  have h_all_zero : ∀ i, eigenvaluesOf σ i = 0 := by
    intro i
    by_contra hi
    have hi_mem : i ∈ positiveSpectrumIndices σ := by
      simp [positiveSpectrumIndices, hi]
    have hcard_pos : 0 < (positiveSpectrumIndices σ).card :=
      Finset.card_pos.mpr ⟨i, hi_mem⟩
    have : 0 < positiveSpectrumDim σ := by
      simpa [positiveSpectrumDim] using hcard_pos
    exact (hdim this).elim
  have h_sum_zero : ∑ i, eigenvaluesOf σ i = 0 := by
    simp [h_all_zero]
  have h_sum_one : ∑ i, eigenvaluesOf σ i = 1 := (eigenvaluesOf_spec σ).2.1
  linarith

instance positiveSpectrumDim_neZero {N : ℕ} (σ : DensityOp N) :
    NeZero (positiveSpectrumDim σ) :=
  ⟨Nat.ne_of_gt (positiveSpectrumDim_pos σ)⟩

/-- The order embedding enumerating the positive-eigenvalue indices of `σ`. -/
noncomputable def positiveSpectrumEmb {N : ℕ} (σ : DensityOp N) :
    Fin (positiveSpectrumDim σ) ↪o Fin N :=
  (positiveSpectrumIndices σ).orderEmbOfFin rfl

lemma positiveSpectrumEmb_mem {N : ℕ} (σ : DensityOp N)
    (i : Fin (positiveSpectrumDim σ)) :
    positiveSpectrumEmb σ i ∈ positiveSpectrumIndices σ :=
  Finset.orderEmbOfFin_mem _ _ i

/-- The selected eigenvalues are strictly positive by construction. -/
lemma positiveSpectrumEmb_eigenvalue_pos {N : ℕ} (σ : DensityOp N)
    (i : Fin (positiveSpectrumDim σ)) :
    0 < eigenvaluesOf σ (positiveSpectrumEmb σ i) := by
  have hnn : 0 ≤ eigenvaluesOf σ (positiveSpectrumEmb σ i) := (eigenvaluesOf_spec σ).1 _
  have hne : eigenvaluesOf σ (positiveSpectrumEmb σ i) ≠ 0 := by
    exact (Finset.mem_filter.mp (positiveSpectrumEmb_mem σ i)).2
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-- The isometry whose columns are the positive-eigenvalue eigenvectors of `σ`. -/
noncomputable def supportIsometry {N : ℕ} (σ : DensityOp N) :
    Matrix (Fin N) (Fin (positiveSpectrumDim σ)) ℂ :=
  fun i j => (eigenbasisOf σ).conjTranspose i (positiveSpectrumEmb σ j)

lemma supportIsometry_isometry {N : ℕ} (σ : DensityOp N) :
    (supportIsometry σ).conjTranspose * supportIsometry σ = 1 := by
  classical
  ext i j
  have hW := congr_fun₂ (eigenbasisOf_unitary_right σ)
    (positiveSpectrumEmb σ i) (positiveSpectrumEmb σ j)
  by_cases hij : i = j
  · subst hij
    simpa [supportIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply] using hW
  · have hneq :
        positiveSpectrumEmb σ i ≠ positiveSpectrumEmb σ j :=
      fun h => hij ((positiveSpectrumEmb σ).injective h)
    simpa [supportIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      hij, hneq] using hW

/-! ### The same data read in the eigenbasis

`supportSelector σ` picks out the positive-spectrum coordinates and
`supportCoordinateProjector σ` is the corresponding diagonal projector, so the ambient
support isometry factors as `(eigenbasisOf σ)ᴴ · supportSelector σ`. -/

/-- The selector matrix picking out the positive-spectrum coordinates. -/
noncomputable def supportSelector {N : ℕ} (σ : DensityOp N) :
    Matrix (Fin N) (Fin (positiveSpectrumDim σ)) ℂ :=
  fun i j => if i = positiveSpectrumEmb σ j then 1 else 0

lemma supportSelector_apply {N : ℕ} (σ : DensityOp N)
    (i : Fin N) (j : Fin (positiveSpectrumDim σ)) :
    supportSelector σ i j = if i = positiveSpectrumEmb σ j then 1 else 0 :=
  rfl

lemma supportSelector_isometry {N : ℕ} (σ : DensityOp N) :
    (supportSelector σ).conjTranspose * supportSelector σ = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [supportSelector, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · have hji : ¬j = i := by simpa [eq_comm] using hij
    simp [supportSelector, Matrix.mul_apply, Matrix.conjTranspose_apply, hij, hji]

/-- The coordinate projector onto the positive-spectrum coordinates. -/
noncomputable def supportCoordinateProjector {N : ℕ} (σ : DensityOp N) :
    Matrix (Fin N) (Fin N) ℂ :=
  supportSelector σ * (supportSelector σ).conjTranspose

lemma supportCoordinateProjector_apply {N : ℕ} (σ : DensityOp N)
    (i k : Fin N) :
    supportCoordinateProjector σ i k =
      if i = k ∧ i ∈ positiveSpectrumIndices σ then 1 else 0 := by
  classical
  have hrange :
      Set.range (positiveSpectrumEmb σ) = (positiveSpectrumIndices σ : Set (Fin N)) := by
    rw [positiveSpectrumEmb]
    exact Finset.range_orderEmbOfFin (positiveSpectrumIndices σ) rfl
  by_cases hik : i = k
  · subst hik
    by_cases hi_range : i ∈ Set.range (positiveSpectrumEmb σ)
    · rcases hi_range with ⟨j, rfl⟩
      rw [supportCoordinateProjector, Matrix.mul_apply]
      rw [Finset.sum_eq_single j]
      · have hmem : positiveSpectrumEmb σ j ∈ positiveSpectrumIndices σ :=
          positiveSpectrumEmb_mem σ j
        have hne : eigenvaluesOf σ (positiveSpectrumEmb σ j) ≠ 0 := by
          exact (Finset.mem_filter.mp hmem).2
        simp [supportSelector, Matrix.conjTranspose_apply, positiveSpectrumIndices, hne]
      · intro b _ hb
        have hneq : positiveSpectrumEmb σ b ≠ positiveSpectrumEmb σ j := by
          intro h
          exact hb ((positiveSpectrumEmb σ).injective h)
        have hbj : ¬j = b := by
          simpa [eq_comm] using hb
        simp [supportSelector, Matrix.conjTranspose_apply, hbj]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
    · have hi : i ∉ positiveSpectrumIndices σ := by
        simpa [hrange] using hi_range
      have hi0 : eigenvaluesOf σ i = 0 := by
        simpa [positiveSpectrumIndices] using hi
      simp only [true_and, hi, if_false]
      rw [supportCoordinateProjector, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro x hx
      have hix : i ≠ positiveSpectrumEmb σ x := by
        intro h
        exact hi_range ⟨x, h.symm⟩
      simp [supportSelector, Matrix.conjTranspose_apply, hix]
  · simp only [hik, false_and, if_false]
    rw [supportCoordinateProjector, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hkx : k = positiveSpectrumEmb σ x
    · have hix : i ≠ positiveSpectrumEmb σ x := by
        intro hix
        exact hik (hix.trans hkx.symm)
      simp [supportSelector, Matrix.conjTranspose_apply, hkx, hix]
    · simp [supportSelector, Matrix.conjTranspose_apply, hkx]

lemma supportCoordinateProjector_eq_diagonal {N : ℕ} (σ : DensityOp N) :
    supportCoordinateProjector σ =
      Matrix.diagonal (fun i => if i ∈ positiveSpectrumIndices σ then (1 : ℂ) else 0) := by
  ext i k
  by_cases hik : i = k
  · subst hik
    simp [supportCoordinateProjector_apply]
  · simp [supportCoordinateProjector_apply, hik]

/-- In the eigenbasis of `σ`, the support coordinate projector acts as the identity
on the diagonal eigenvalue matrix of `σ`. -/
lemma eigenvalueDiagonal_mul_supportCoordinateProjector {N : ℕ}
    (σ : DensityOp N) :
    Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) * supportCoordinateProjector σ =
      Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) := by
  rw [supportCoordinateProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  by_cases hi : i ∈ positiveSpectrumIndices σ
  · simp [hi]
  · have hi0 : eigenvaluesOf σ i = 0 := by
      simpa [positiveSpectrumIndices] using hi
    simp [hi, hi0]

lemma supportIsometry_eq_mul_supportSelector {N : ℕ} (σ : DensityOp N) :
    supportIsometry σ = (eigenbasisOf σ).conjTranspose * supportSelector σ := by
  ext i j
  simp [supportIsometry, supportSelector, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Sandwiching by `supportSelector σ` extracts the principal submatrix indexed by
the positive-spectrum embedding of `σ`. -/
lemma supportSelector_conjTranspose_mul_mul_supportSelector_apply
    {N : ℕ} (σ : DensityOp N)
    (A : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin (positiveSpectrumDim σ)) :
    (((supportSelector σ).conjTranspose * A * supportSelector σ) i j) =
      A (positiveSpectrumEmb σ i) (positiveSpectrumEmb σ j) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (positiveSpectrumEmb σ j)]
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (positiveSpectrumEmb σ i)]
    · simp [supportSelector, Matrix.conjTranspose_apply]
    · intro b _ hbi
      simp [supportSelector, Matrix.conjTranspose_apply, hbi]
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  · intro b _ hbj
    simp [supportSelector, hbj]
  · intro hj
    exact False.elim (hj (Finset.mem_univ _))

/-! ### The support projector -/

/-- The orthogonal projector onto `supp(σ)` in the ambient space. -/
noncomputable def supportProjector {N : ℕ} (σ : DensityOp N) :
    Matrix (Fin N) (Fin N) ℂ :=
  supportIsometry σ * (supportIsometry σ).conjTranspose

lemma supportProjector_eq {N : ℕ} (σ : DensityOp N) :
    supportProjector σ =
      (eigenbasisOf σ).conjTranspose *
        supportCoordinateProjector σ *
        eigenbasisOf σ := by
  rw [supportProjector, supportIsometry_eq_mul_supportSelector]
  simp [supportCoordinateProjector, Matrix.mul_assoc]

lemma supportProjector_isHermitian {N : ℕ} (σ : DensityOp N) :
    Matrix.IsHermitian (supportProjector σ) := by
  unfold supportProjector
  simp [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

lemma sigma_mul_supportProjector {N : ℕ} (σ : DensityOp N) :
    σ.toOp * supportProjector σ = σ.toOp := by
  set V := eigenbasisOf σ
  set D : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ))
  have hVL : V.conjTranspose * V = 1 := eigenbasisOf_unitary_left σ
  have hVR : V * V.conjTranspose = 1 := eigenbasisOf_unitary_right σ
  have hsd : σ.toOp = V.conjTranspose * D * V := by
    simpa [V, D, Matrix.mul_assoc] using (eigenbasisOf_spectral_decomp σ)
  calc
    σ.toOp * supportProjector σ = (V.conjTranspose * D * V) * supportProjector σ := by
      rw [hsd]
    _ = V.conjTranspose * D * V *
        ((eigenbasisOf σ).conjTranspose * supportCoordinateProjector σ * eigenbasisOf σ) := by
      rw [supportProjector_eq]
    _ = V.conjTranspose * D * V * (V.conjTranspose * supportCoordinateProjector σ * V) := by
      simp [V]
    _ = V.conjTranspose * D * (V * V.conjTranspose) * supportCoordinateProjector σ * V := by
            simp [Matrix.mul_assoc]
    _ = V.conjTranspose * D * supportCoordinateProjector σ * V := by
      rw [hVR, Matrix.mul_one]
    _ = V.conjTranspose * (D * supportCoordinateProjector σ) * V := by
      simp [Matrix.mul_assoc]
    _ = V.conjTranspose * D * V := by
      rw [eigenvalueDiagonal_mul_supportCoordinateProjector]
    _ = σ.toOp := by
      exact hsd.symm

lemma sigma_mul_supportProjector_compl {N : ℕ} (σ : DensityOp N) :
    σ.toOp * ((1 : Matrix (Fin N) (Fin N) ℂ) - supportProjector σ) = 0 := by
  rw [Matrix.mul_sub, sigma_mul_supportProjector]
  simp

/-- The support projector is idempotent: `P_σ · P_σ = P_σ`, from `Vᴴ·V = 1` for the support
isometry `V`. -/
lemma supportProjector_mul_self {N : ℕ} (σ : DensityOp N) :
    supportProjector σ * supportProjector σ = supportProjector σ := by
  rw [supportProjector, Matrix.mul_assoc, ← Matrix.mul_assoc (supportIsometry σ).conjTranspose,
    supportIsometry_isometry, Matrix.one_mul]

/-- The support projector is positive semidefinite: it is `V·Vᴴ` for the support isometry. -/
lemma supportProjector_posSemidef {N : ℕ} (σ : DensityOp N) :
    (supportProjector σ).PosSemidef := by
  rw [supportProjector]
  exact Matrix.posSemidef_self_mul_conjTranspose (supportIsometry σ)

/-- The complementary projector annihilates the state from the left, `(1 − P_σ)·σ = 0`; the
adjoint of `sigma_mul_supportProjector_compl`, both factors being Hermitian. -/
lemma compl_supportProjector_mul_sigma {N : ℕ} (σ : DensityOp N) :
    ((1 : Matrix (Fin N) (Fin N) ℂ) - supportProjector σ) * σ.toOp = 0 := by
  have h := congrArg Matrix.conjTranspose (sigma_mul_supportProjector_compl σ)
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, (supportProjector_isHermitian σ).eq,
    σ.toPosSemidefOp.toHermitianOp.isHermitian.eq] at h

lemma supportProjector_mul_of_right_supported {N : ℕ}
    (σ ρ : DensityOp N)
    (hρP : ρ.toOp * supportProjector σ = ρ.toOp) :
    supportProjector σ * ρ.toOp = ρ.toOp := by
  have hρP_ct := congrArg Matrix.conjTranspose hρP
  simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    (supportProjector_isHermitian σ).eq, ρ.toPosSemidefOp.toHermitianOp.isHermitian.eq] using hρP_ct

/-! ### Löwner-dominated operators live on the support

A positive semidefinite `C` with `C ⪯ σ` has no component outside `supp σ`: the support
projector fixes it from either side and the complementary projector annihilates it.  These
are the Quantum.Operators module's projector-absorption laws, whose two inputs here are
`supportProjector_isHermitian` and `sigma_mul_supportProjector`. -/

section Absorption

variable {N : ℕ} (σ : DensityOp N) {C : Matrix (Fin N) (Fin N) ℂ}

/-- `C·(1 − P_σ) = 0` for positive semidefinite `C ⪯ σ`. -/
lemma mul_compl_supportProjector_of_opLe
    (hC : C.PosSemidef) (hCσ : Quantum.Operators.opLe C σ.toOp) :
    C * ((1 : Matrix (Fin N) (Fin N) ℂ) - supportProjector σ) = 0 :=
  Quantum.Operators.mul_compl_proj_of_opLe (sigma_mul_supportProjector σ) hC hCσ

/-- `(1 − P_σ)·C = 0` for positive semidefinite `C ⪯ σ`. -/
lemma compl_supportProjector_mul_of_opLe
    (hC : C.PosSemidef) (hCσ : Quantum.Operators.opLe C σ.toOp) :
    ((1 : Matrix (Fin N) (Fin N) ℂ) - supportProjector σ) * C = 0 :=
  Quantum.Operators.compl_proj_mul_of_opLe (supportProjector_isHermitian σ)
    (sigma_mul_supportProjector σ) hC hCσ

/-- `C·P_σ = C` for positive semidefinite `C ⪯ σ`. -/
lemma mul_supportProjector_of_opLe
    (hC : C.PosSemidef) (hCσ : Quantum.Operators.opLe C σ.toOp) :
    C * supportProjector σ = C :=
  Quantum.Operators.mul_proj_of_opLe (sigma_mul_supportProjector σ) hC hCσ

/-- `P_σ·C = C` for positive semidefinite `C ⪯ σ`. -/
lemma supportProjector_mul_of_opLe
    (hC : C.PosSemidef) (hCσ : Quantum.Operators.opLe C σ.toOp) :
    supportProjector σ * C = C :=
  Quantum.Operators.proj_mul_of_opLe (supportProjector_isHermitian σ)
    (sigma_mul_supportProjector σ) hC hCσ

end Absorption

/-! ### Kernel characterisations and unitary covariance -/

lemma rho_mul_supportProjector_of_ker_sub {N : ℕ}
    (ρ σ : DensityOp N)
    (h_ker : ∀ v : Fin N → ℂ, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    ρ.toOp * supportProjector σ = ρ.toOp := by
  set V := eigenbasisOf σ
  have hVL : V.conjTranspose * V = 1 := eigenbasisOf_unitary_left σ
  have hVR : V * V.conjTranspose = 1 := eigenbasisOf_unitary_right σ
  let M : Matrix (Fin N) (Fin N) ℂ := V * ρ.toOp * V.conjTranspose
  have hM_support :
      M * supportCoordinateProjector σ = M := by
    ext k l
    rw [supportCoordinateProjector_eq_diagonal, Matrix.mul_apply, Finset.sum_eq_single l]
    · by_cases hl : l ∈ positiveSpectrumIndices σ
      · simp [M, hl]
      · have hl0 : eigenvaluesOf σ l = 0 := by
          simpa [positiveSpectrumIndices] using hl
        have hcol_zero :
            M.mulVec (Pi.single l 1) = 0 := by
          have hsd :
              σ.toOp = V.conjTranspose *
                Matrix.diagonal (fun j => (eigenvaluesOf σ j : ℂ)) * V :=
            eigenbasisOf_spectral_decomp σ
          have hσ_zero : σ.toOp.mulVec (V.conjTranspose.mulVec (Pi.single l 1)) = 0 := by
            rw [Matrix.mulVec_mulVec, hsd, Matrix.mul_assoc, Matrix.mul_assoc, hVR,
              Matrix.mul_one, ← Matrix.mulVec_mulVec]
            have hdiag :
                (Matrix.diagonal (fun j => (eigenvaluesOf σ j : ℂ))).mulVec (Pi.single l 1) =
                  Pi.single l (eigenvaluesOf σ l : ℂ) := by
              ext j
              by_cases hj : j = l
              · subst hj
                simp [Matrix.mulVec_diagonal]
              · simp [Matrix.mulVec_diagonal, hj]
            rw [hdiag, show (eigenvaluesOf σ l : ℂ) = 0 from by exact_mod_cast hl0,
              Pi.single_zero, Matrix.mulVec_zero]
          have hρ_zero : ρ.toOp.mulVec (V.conjTranspose.mulVec (Pi.single l 1)) = 0 :=
            h_ker _ hσ_zero
          change (V * ρ.toOp * V.conjTranspose).mulVec (Pi.single l 1) = 0
          rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            hρ_zero, Matrix.mulVec_zero]
        have hentry_zero : M k l = 0 := by
          have h := congr_fun hcol_zero k
          rwa [show (M.mulVec (Pi.single l 1)) k = M k l from by
            simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
              mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]] at h
        simp [M, hl, hentry_zero]
    · intro b _ hbl
      simp [hbl]
    · intro hl
      exact False.elim (hl (Finset.mem_univ l))
  calc
    ρ.toOp * supportProjector σ = (V.conjTranspose * V) * ρ.toOp * supportProjector σ := by
      rw [hVL, Matrix.one_mul]
    _ = V.conjTranspose * (V * ρ.toOp * V.conjTranspose * supportCoordinateProjector σ) * V := by
      rw [supportProjector_eq]
      simp [V, Matrix.mul_assoc]
    _ = V.conjTranspose * (M * supportCoordinateProjector σ) * V := by
      rfl
    _ = V.conjTranspose * M * V := by
      rw [hM_support]
    _ = V.conjTranspose * (V * ρ.toOp) := by
      rw [show M = V * ρ.toOp * V.conjTranspose from rfl]
      simp [Matrix.mul_assoc, hVL]
    _ = (V.conjTranspose * V) * ρ.toOp := by
      simp [Matrix.mul_assoc]
    _ = ρ.toOp := by
      rw [hVL, Matrix.one_mul]

/-- **The support projector annihilates the kernel of the state.**

The orthogonal projector `P_R := supportProjector σ` onto `range σ` kills every vector in
`ker σ`: `σ *ᵥ v = 0 → P_R *ᵥ v = 0`.  This is the dual of `sigma_mul_supportProjector`
(which says `P_R` *fixes* `range σ`): in the eigenbasis, `σ *ᵥ v = 0` forces the
positive-eigenvalue coordinates of `V *ᵥ v` to vanish, and the support coordinate projector
keeps exactly those coordinates, so it annihilates `V *ᵥ v`.  It is the kernel-side primitive
behind the unitary-covariance commutation `supportProjector_unitary_conj`. -/
lemma supportProjector_mulVec_eq_zero_of_ker {N : ℕ} (σ : DensityOp N)
    {v : Fin N → ℂ} (hv : σ.toOp.mulVec v = 0) :
    (supportProjector σ).mulVec v = 0 := by
  set V := eigenbasisOf σ with hVdef
  have hVR : V * V.conjTranspose = 1 := eigenbasisOf_unitary_right σ
  have hsd : σ.toOp =
      V.conjTranspose * Matrix.diagonal (fun j => (eigenvaluesOf σ j : ℂ)) * V :=
    eigenbasisOf_spectral_decomp σ
  have hCsd : supportProjector σ = V.conjTranspose * supportCoordinateProjector σ * V := by
    rw [supportProjector_eq]
  rw [hCsd, supportCoordinateProjector_eq_diagonal]
  set w := V.mulVec v with hw
  -- `σ *ᵥ v = 0` pushes through the unitary to `D *ᵥ (V *ᵥ v) = 0`.
  have hDw : (Matrix.diagonal (fun j => (eigenvaluesOf σ j : ℂ))).mulVec w = 0 := by
    have hVann : V.mulVec (σ.toOp.mulVec v) = 0 := by rw [hv, Matrix.mulVec_zero]
    rw [hsd] at hVann
    rw [show V.mulVec
          ((V.conjTranspose * Matrix.diagonal (fun j => (eigenvaluesOf σ j : ℂ)) * V).mulVec v)
        = (V * (V.conjTranspose * Matrix.diagonal (fun j => (eigenvaluesOf σ j : ℂ)) * V)).mulVec v
        from by rw [Matrix.mulVec_mulVec]] at hVann
    rw [show V * (V.conjTranspose * Matrix.diagonal (fun j => (eigenvaluesOf σ j : ℂ)) * V)
          = (V * V.conjTranspose)
              * (Matrix.diagonal (fun j => (eigenvaluesOf σ j : ℂ)) * V) from by noncomm_ring,
      hVR, Matrix.one_mul, ← Matrix.mulVec_mulVec] at hVann
    exact hVann
  -- The support coordinate projector keeps only the positive-eigenvalue coordinates,
  -- which `D *ᵥ w = 0` already annihilated.
  have hCw :
      (Matrix.diagonal (fun i => if i ∈ positiveSpectrumIndices σ then (1 : ℂ) else 0)).mulVec w
        = 0 := by
    ext i
    rw [Matrix.mulVec_diagonal]
    have hi := congr_fun hDw i
    rw [Matrix.mulVec_diagonal] at hi
    by_cases hpos : i ∈ positiveSpectrumIndices σ
    · have hne : (eigenvaluesOf σ i : ℂ) ≠ 0 := by
        simp only [positiveSpectrumIndices, Finset.mem_filter] at hpos
        exact_mod_cast hpos.2
      rcases mul_eq_zero.1 hi with h | h
      · exact absurd h hne
      · simp [hpos, h]
    · simp [hpos]
  calc ((V.conjTranspose
          * Matrix.diagonal (fun i => if i ∈ positiveSpectrumIndices σ then (1 : ℂ) else 0))
          * V).mulVec v
      = V.conjTranspose.mulVec
          ((Matrix.diagonal (fun i => if i ∈ positiveSpectrumIndices σ then (1 : ℂ) else 0)).mulVec
            (V.mulVec v)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = 0 := by rw [← hw, hCw, Matrix.mulVec_zero]

/-- **Range-block vanishing of an invariant unitary — one side.**

For a unitary `U` (`U·Uᴴ = Uᴴ·U = 1`) fixing the state by conjugation (`U·σ·Uᴴ = σ`), the
projector mismatch `P_R·U·(1 - P_R)` vanishes: `U` maps `ker σ` into `ker σ`, and `P_R`
annihilates `ker σ` (`supportProjector_mulVec_eq_zero_of_ker`).  Helper for
`supportProjector_unitary_conj`. -/
lemma supportProjector_mul_unitary_mul_compl_eq_zero {N : ℕ} (σ : DensityOp N) (U : Op N)
    (hU2 : U.conjTranspose * U = 1) (hconj : U * σ.toOp * U.conjTranspose = σ.toOp) :
    supportProjector σ * U * (1 - supportProjector σ) = 0 := by
  -- Conjugation invariance gives the commutation `U·σ = σ·U`.
  have hUcomm : U * σ.toOp = σ.toOp * U := by
    have h := congrArg (· * U) hconj
    simpa [Matrix.mul_assoc, hU2, Matrix.mul_one] using h
  ext i j
  set P := supportProjector σ with hPdef
  have hcol : (P * U * (1 - P)).mulVec (Pi.single j 1) = 0 := by
    set y := (1 - P).mulVec (Pi.single j 1) with hy
    -- `y = (1 - P)·e_j ∈ ker σ` and `U` preserves `ker σ`, so `P` annihilates `U·y`.
    have hPy : σ.toOp.mulVec y = 0 := by
      have hz : σ.toOp * (1 - P) = 0 := sigma_mul_supportProjector_compl σ
      rw [hy, Matrix.mulVec_mulVec, hz, Matrix.zero_mulVec]
    have hUy : σ.toOp.mulVec (U.mulVec y) = 0 := by
      rw [Matrix.mulVec_mulVec, ← hUcomm, ← Matrix.mulVec_mulVec, hPy, Matrix.mulVec_zero]
    have hPUy : P.mulVec (U.mulVec y) = 0 := supportProjector_mulVec_eq_zero_of_ker σ hUy
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy, hPUy]
  have hfin := congr_fun hcol i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hfin

/-- **The support projector commutes with a state-fixing unitary.**

If a unitary `U` (`U·Uᴴ = Uᴴ·U = 1`) fixes the density operator under conjugation,
`U·σ·Uᴴ = σ`, then it commutes with the orthogonal projector onto the state's support:

  `U · supportProjector σ = supportProjector σ · U`.

Equivalently `U·P_R·Uᴴ = P_R`, so the support of `σ` (and its orthogonal complement, the
kernel) is `U`-invariant.  This is the load-bearing covariance commutation: a unitary that
fixes a Hermitian operator fixes every spectral projection, here the support (positive-spectrum)
projection.  Proof: both projector-block mismatches `P_R·U·(1 - P_R)` and `(1 - P_R)·U·P_R`
vanish (`supportProjector_mul_unitary_mul_compl_eq_zero`, applied to `U` and to `Uᴴ`), so
`P_R·U = P_R·U·P_R = U·P_R`. -/
lemma supportProjector_unitary_conj {N : ℕ} (σ : DensityOp N) (U : Op N)
    (hU1 : U * U.conjTranspose = 1) (hU2 : U.conjTranspose * U = 1)
    (hconj : U * σ.toOp * U.conjTranspose = σ.toOp) :
    U * supportProjector σ = supportProjector σ * U := by
  set P := supportProjector σ with hPdef
  -- `P·U·(1 - P) = 0`, i.e. `P·U = P·U·P`.
  have hPU : P * U * (1 - P) = 0 :=
    supportProjector_mul_unitary_mul_compl_eq_zero σ U hU2 hconj
  -- The conjugate hypothesis for `Uᴴ`: `Uᴴ·σ·U = σ`.
  have hconj' : U.conjTranspose * σ.toOp * U = σ.toOp := by
    have h := congrArg (fun M => U.conjTranspose * M * U) hconj
    simp only at h
    rw [show U.conjTranspose * (U * σ.toOp * U.conjTranspose) * U
        = (U.conjTranspose * U) * σ.toOp * (U.conjTranspose * U) from by noncomm_ring,
      hU2, Matrix.one_mul, Matrix.mul_one] at h
    exact h.symm
  -- `P·Uᴴ·(1 - P) = 0`; transpose gives `(1 - P)·U·P = 0`, i.e. `U·P = P·U·P`.
  have hPUadj : P * U.conjTranspose * (1 - P) = 0 :=
    supportProjector_mul_unitary_mul_compl_eq_zero σ U.conjTranspose
      (by rw [Matrix.conjTranspose_conjTranspose]; exact hU1)
      (by rw [Matrix.conjTranspose_conjTranspose]; exact hconj')
  have hUP : (1 - P) * U * P = 0 := by
    have h := congrArg Matrix.conjTranspose hPUadj
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose,
      (supportProjector_isHermitian σ).eq, Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at h
    exact h
  -- `P·U = P·U·P` and `U·P = P·U·P`, hence `U·P = P·U`.
  have hPU' : P * U = P * U * P := by
    have hexp : P * U * (1 - P) = P * U - P * U * P := by noncomm_ring
    rw [hexp] at hPU
    linear_combination (norm := module) hPU
  have hUP' : U * P = P * U * P := by
    have hexp : (1 - P) * U * P = U * P - P * U * P := by noncomm_ring
    rw [hexp] at hUP
    linear_combination (norm := module) hUP
  rw [hUP', ← hPU']

end InfoTheory.RelativeEntropy

end
