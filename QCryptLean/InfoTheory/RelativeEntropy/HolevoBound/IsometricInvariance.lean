import QCryptLean.InfoTheory.RelativeEntropy.Basic

/-!
# Isometric Invariance of Relative Entropy — embedding, spectral decomposition, invariance

Isometric embedding of density operators, spectral decomposition helpers, and the
proof that von Neumann entropy and relative entropy are invariant under isometric
embedding: S(VρV†) = S(ρ) and D(VρV† ‖ VσV†) = D(ρ ‖ σ).

## Main definitions
- `measurementKLDivReal`: Classical KL divergence induced by a POVM
  measurement (ℝ-valued, proof helper)
- `measurementKLDiv`: Classical KL divergence induced by a POVM measurement
  (ENNReal, canonical)
- `DensityOp.isometryEmbed`: Isometric embedding V ρ V† of a density operator

## Main statements
- `vonNeumannEntropy_isometry_invariance`: S(VρV†) = S(ρ)
- `mulVec_injective_of_conjTranspose_mul_eq_one`: an isometry acts injectively
  on vectors
- `ker_mulVec_zero_conj`: kernel containment transfers under isometric
  conjugation
- `kernel_containment_isometry_embed`: kernel containment is preserved by isometric embedding
- `relativeEntropyReal_isometry_invariance`: D(VρV† ‖ VσV†) = D(ρ ‖ σ)
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-!
## Isometric Embeddings and Measurement Helpers

This file packages the linear-algebraic ingredients used to transport spectral
data through isometric embeddings. It also records the classical KL-divergence
quantities attached to a POVM, which are used as helpers in later Holevo-bound
arguments.
-/

/-- Classical KL divergence between conditional measurement distributions (ℝ-valued, proof helper).

    For a fixed POVM M and states ρ, σ, this is:
    D_KL(p_ρ || p_σ) = Σᵧ p_ρ(y) log(p_ρ(y)/p_σ(y))

    where p_ρ(y) = Tr(Mᵧ ρ) and p_σ(y) = Tr(Mᵧ σ).

    **WARNING**: This definition returns a junk value when classical support fails,
    i.e. when p_σ(y) = 0 but p_ρ(y) > 0 for some y. In that case `Real.log` applied
    to division by zero gives garbage. Mathematically D_KL should be +∞ there.
    For the canonical definition that correctly returns ⊤ in this case, use
    `measurementKLDiv` (ENNReal-valued). This ℝ version is kept public for
    arithmetic convenience inside support-conditioned proofs. -/
def measurementKLDivReal {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) (ρ σ : DensityOp n) : ℝ :=
  let p_rho := fun y => M.prob ρ y
  let p_sigma := fun y => M.prob σ y
  ∑ y, if p_rho y = 0 then 0 else p_rho y * Real.log (p_rho y / p_sigma y)

/-- Classical KL divergence between conditional measurement distributions (ENNReal, canonical).

    D_KL(p_ρ || p_σ) = +∞ when classical support fails (p_σ(y) = 0 but p_ρ(y) > 0),
    matching the mathematical convention. Unconditional — no support hypothesis needed. -/
noncomputable def measurementKLDiv {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) (ρ σ : DensityOp n) : ENNReal :=
  if ∀ y, M.prob σ y = 0 → M.prob ρ y = 0
  then ENNReal.ofReal (measurementKLDivReal M ρ σ)
  else ⊤

/-- When classical support holds, `measurementKLDiv` equals `ofReal` of the ℝ version. -/
theorem measurementKLDiv_eq_ofReal_of_support {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) (ρ σ : DensityOp n)
    (h_support : ∀ y, M.prob σ y = 0 → M.prob ρ y = 0) :
    measurementKLDiv M ρ σ = ENNReal.ofReal (measurementKLDivReal M ρ σ) := by
  simp only [measurementKLDiv, if_pos h_support]

/-- When classical support fails, `measurementKLDiv` equals ⊤. -/
theorem measurementKLDiv_eq_top {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) (ρ σ : DensityOp n)
    (h_not_support : ¬ ∀ y, M.prob σ y = 0 → M.prob ρ y = 0) :
    measurementKLDiv M ρ σ = ⊤ := by
  simp only [measurementKLDiv, if_neg h_not_support]

/-!
### Naimark Dilation and Data Processing Inequality

The proof of `measurement_monotonicity` decomposes via Naimark dilation:
1. Embed the POVM measurement into a projective measurement on a larger space
2. Use isometric invariance of relative entropy
3. Apply the projective measurement DPI

Each sub-step is stated as a separate sorry lemma.
-/

/-- Isometric embedding of a density operator: V ρ V† is a valid density operator
    when V†V = I (isometry). -/
noncomputable def DensityOp.isometryEmbed {n N : ℕ} [NeZero N]
    (V : Matrix (Fin N) (Fin n) ℂ) (hV : V.conjTranspose * V = 1)
    (ρ : DensityOp n) : DensityOp N where
  toPosSemidefOp :=
    { toHermitianOp :=
        { toOp := V * ρ.toOp * V.conjTranspose
          isHermitian := by
            unfold Matrix.IsHermitian
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
                Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
            exact congrArg (V * ·) (congrArg (· * V.conjTranspose)
              ρ.toPosSemidefOp.toHermitianOp.isHermitian) }
      pos_semidef := fun x => by
        have h_psd := (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).mul_mul_conjTranspose_same V
        have h_nn := h_psd.dotProduct_mulVec_nonneg x
        rw [Complex.nonneg_iff] at h_nn
        exact h_nn.1 }
  trace_one := by
    -- Tr(VρV†) = Tr(V†Vρ) = Tr(ρ) = 1
    change (V * ρ.toOp * V.conjTranspose).trace = 1
    rw [Matrix.trace_mul_comm (V * ρ.toOp) V.conjTranspose]
    rw [show V.conjTranspose * (V * ρ.toOp) = (V.conjTranspose * V) * ρ.toOp from
        by rw [Matrix.mul_assoc]]
    rw [hV, Matrix.one_mul, ρ.trace_one]

/-- A matrix with `W† * W = 1` acts injectively on vectors by `mulVec`. -/
lemma mulVec_injective_of_conjTranspose_mul_eq_one {n N : ℕ}
    (W : Matrix (Fin N) (Fin n) ℂ)
    (hW : W.conjTranspose * W = 1) :
    Function.Injective W.mulVec := by
  intro a b hab
  have step :
      W.conjTranspose.mulVec (W.mulVec a) =
      W.conjTranspose.mulVec (W.mulVec b) := by
    rw [hab]
  simp only [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec] at step
  exact step

/-- Kernel inclusion transfers under conjugation by an injective linear action.
    If `W.mulVec` is injective and `A·v = 0 → B·v = 0`, then
    `(WAW†)·v = 0 → (WBW†)·v = 0`. -/
lemma ker_mulVec_zero_conj {n N : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (W : Matrix (Fin N) (Fin n) ℂ)
    (hW_inj : Function.Injective W.mulVec)
    (h_ker : ∀ v, A.mulVec v = 0 → B.mulVec v = 0) :
    ∀ v, (W * A * W.conjTranspose).mulVec v = 0 →
      (W * B * W.conjTranspose).mulVec v = 0 := by
  intro v hv
  set u := W.conjTranspose.mulVec v with hu_def
  have h_A_u : A.mulVec u = 0 := by
    have h5 : W.mulVec (A.mulVec u) = 0 := by
      calc W.mulVec (A.mulVec u)
          = (W * A).mulVec u := by
            rw [Matrix.mulVec_mulVec]
        _ = (W * A).mulVec
              (W.conjTranspose.mulVec v) := by
            rw [hu_def]
        _ = (W * A * W.conjTranspose).mulVec v := by
            rw [Matrix.mulVec_mulVec]
        _ = 0 := hv
    exact hW_inj (by rw [h5, Matrix.mulVec_zero])
  have h_B_u : B.mulVec u = 0 := h_ker u h_A_u
  calc (W * B * W.conjTranspose).mulVec v
      = (W * (B * W.conjTranspose)).mulVec v := by
        rw [Matrix.mul_assoc]
    _ = W.mulVec
          ((B * W.conjTranspose).mulVec v) := by
        rw [← Matrix.mulVec_mulVec]
    _ = W.mulVec
          (B.mulVec (W.conjTranspose.mulVec v)) := by
        rw [← Matrix.mulVec_mulVec]
    _ = W.mulVec (B.mulVec u) := by rw [← hu_def]
    _ = W.mulVec 0 := by rw [h_B_u]
    _ = 0 := Matrix.mulVec_zero _

/-- Isometric embedding preserves kernel containment.
    If `ker(σ) ⊆ ker(ρ)` and `V†V = 1`, then `ker(VσV†) ⊆ ker(VρV†)`. -/
lemma kernel_containment_isometry_embed {n N : ℕ}
    (V : Matrix (Fin N) (Fin n) ℂ) (hV : V† * V = 1)
    (ρ σ : DensityOp n)
    (h_ker : ∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    ∀ u, (V * σ.toOp * V†).mulVec u = 0 →
      (V * ρ.toOp * V†).mulVec u = 0 := by
  exact ker_mulVec_zero_conj σ.toOp ρ.toOp V
    (mulVec_injective_of_conjTranspose_mul_eq_one V hV) h_ker

/-- Shannon entropy is preserved when appending zeros to a spectrum. -/
lemma shannonEntropy_append_zeros {n k : ℕ} (evs : Fin n → ℝ) :
    shannonEntropy (Fin.addCases evs (fun _ : Fin k => (0 : ℝ))) =
    shannonEntropy evs := by
  unfold shannonEntropy
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, entropyTerm_zero,
             Finset.sum_const_zero, add_zero]

/-- Shannon entropy is preserved under zero-padding of eigenvalues.
    If we extend `evs : Fin n → ℝ` to `Fin N → ℝ` by setting new entries to 0,
    the Shannon entropy is unchanged since `entropyTerm 0 = 0`. -/
lemma shannonEntropy_zeroPad {n N : ℕ} (hn : n ≤ N) (evs : Fin n → ℝ) :
    shannonEntropy
      (fun i : Fin N => if h : i.val < n then evs ⟨i.val, h⟩ else 0) =
    shannonEntropy evs := by
  have hNk : n + (N - n) = N := Nat.add_sub_cancel' hn
  -- Reindex via finCongr : Fin (n + (N-n)) ≃ Fin N
  have h_reindex :
      shannonEntropy
        (fun i : Fin N =>
          if h : i.val < n then evs ⟨i.val, h⟩ else 0) =
      shannonEntropy
        (fun i : Fin (n + (N - n)) =>
          if h : i.val < n then evs ⟨i.val, h⟩ else 0) := by
    unfold shannonEntropy
    exact (Fintype.sum_equiv (finCongr hNk) _ _
      (fun i => by simp [finCongr])).symm
  rw [h_reindex]
  -- The dite function agrees pointwise with Fin.addCases
  have h_congr :
      shannonEntropy
        (fun i : Fin (n + (N - n)) =>
          if h : i.val < n then evs ⟨i.val, h⟩ else 0) =
      shannonEntropy
        (Fin.addCases evs (fun _ : Fin (N - n) => (0 : ℝ))) := by
    apply shannonEntropy_congr
    intro i; simp only [Fin.addCases]; split <;> [rfl; simp]
  rw [h_congr]
  exact shannonEntropy_append_zeros evs

/-- `V†V = 1` for `V : N × n` implies `n ≤ N`.
    An N×n isometry has n orthonormal columns in ℂ^N, requiring n ≤ N. -/
lemma n_le_N_of_isometry {n N : ℕ}
    (V : Matrix (Fin N) (Fin n) ℂ)
    (hV : V.conjTranspose * V = 1) : n ≤ N := by
  -- V†V = I means V.mulVecLin is injective
  have h_inj : Function.Injective V.mulVecLin := by
    intro x y hxy; simp only [Matrix.mulVecLin_apply] at hxy
    have h1 : V.conjTranspose *ᵥ (V *ᵥ x) =
              V.conjTranspose *ᵥ (V *ᵥ y) :=
      congrArg (V.conjTranspose.mulVec ·) hxy
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hV,
        Matrix.one_mulVec, Matrix.one_mulVec] at h1
    exact h1
  -- Injective linear map ℂ^n → ℂ^N implies n ≤ N by dimension
  have h := LinearMap.finrank_le_finrank_of_injective h_inj
  simp only [Module.finrank_fin_fun] at h
  exact h

/-- Zero-padded sum: extending a function by zeros preserves its sum. -/
lemma sum_zeroPad_eq {n N : ℕ} (hn : n ≤ N) (f : Fin n → ℝ) :
    (∑ i : Fin N, if h : i.val < n then f ⟨i.val, h⟩ else 0) =
    ∑ j : Fin n, f j := by
  have hNk : n + (N - n) = N := Nat.add_sub_cancel' hn
  rw [show (∑ i : Fin N,
      if h : i.val < n then f ⟨i.val, h⟩ else 0) =
    (∑ i : Fin (n + (N - n)),
      if h : i.val < n then f ⟨i.val, h⟩ else 0) from
    (Fintype.sum_equiv (finCongr hNk) _ _
      (fun i => by simp [finCongr])).symm, Fin.sum_univ_add]
  have h1 : (∑ i : Fin n,
      if h : (Fin.castAdd (N - n) i).val < n
      then f ⟨(Fin.castAdd (N - n) i).val, h⟩ else 0) =
    ∑ i : Fin n, f i := by
    congr 1; ext i; simp [Fin.castAdd, i.isLt]
  have h2 : (∑ i : Fin (N - n),
      if h : (Fin.natAdd n i).val < n
      then f ⟨(Fin.natAdd n i).val, h⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    simp [Fin.natAdd, show ¬(n + i.val < n) from by omega]
  rw [h1, h2, add_zero]

/-- A sum over `Fin N` with a `dite` guard `↑k < n` equals the corresponding
    sum over `Fin n`, when the else-branch is zero. -/
lemma sum_dite_fin_eq {N n : ℕ} {M : Type*} [AddCommMonoid M] (hn : n ≤ N)
    (g : (k : Fin N) → (k : ℕ) < n → M) (f : Fin n → M)
    (hgf : ∀ (k : Fin N) (h : (k : ℕ) < n), g k h = f ⟨k, h⟩) :
    (∑ k : Fin N, if h : (k : ℕ) < n then g k h else 0) =
    ∑ k : Fin n, f k := by
  simp_rw [hgf]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Fin.sum_univ_add]
  have h1 : (∑ i : Fin n, if h : (Fin.castAdd m i : ℕ) < n
      then f ⟨(Fin.castAdd m i : ℕ), h⟩ else 0) = ∑ i : Fin n, f i := by
    congr 1; ext i; simp only [Fin.val_castAdd]; rw [dif_pos i.isLt]
  have h2 : (∑ i : Fin m, if h : (Fin.natAdd n i : ℕ) < n
      then f ⟨(Fin.natAdd n i : ℕ), h⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    simp only [Fin.val_natAdd]; exact dif_neg (by omega)
  rw [h1, h2, add_zero]

-- Helper: columns of an isometry are orthonormal in EuclideanSpace
private lemma isometry_cols_orthonormal {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℂ) (hA : A.conjTranspose * A = 1) :
    Orthonormal ℂ (fun j : Fin n =>
      (WithLp.equiv 2 (Fin N → ℂ)).symm (fun i => A i j)) := by
  rw [orthonormal_iff_ite]; intro i j
  have : @inner ℂ _ _
      ((WithLp.equiv 2 (Fin N → ℂ)).symm (fun k => A k i))
      ((WithLp.equiv 2 (Fin N → ℂ)).symm (fun k => A k j)) =
      (A.conjTranspose * A) i j := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Matrix.conjTranspose_apply, Matrix.mul_apply, WithLp.equiv_symm_apply,
      Pi.star_apply]
    congr 1; ext k; ring
  rw [this, hA]; simp [Matrix.one_apply]

-- Helper: matrix built from ONB columns is unitary
private lemma onb_matrix_unitary {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    let U : Matrix (Fin N) (Fin N) ℂ := fun i j => (b j : Fin N → ℂ) i
    U.conjTranspose * U = 1 := by
  intro U
  ext i j
  simp only [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have := (orthonormal_iff_ite.mp b.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simp only [dotProduct, Pi.star_apply] at this
  convert this using 1; congr 1; ext k; simp [mul_comm]

-- Helper: first n columns of ONB-extended matrix match the original isometry
private lemma onb_extension_cols {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℂ) (hn : n ≤ N)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (hb : ∀ (i : Fin N), i ∈ Set.range
      (fun j : Fin n => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ : Fin N)) →
      (b i : EuclideanSpace ℂ (Fin N)) =
        (fun k : Fin N => if h : k.val < n then
          (WithLp.equiv 2 (Fin N → ℂ)).symm (fun r => A r ⟨k.val, h⟩)
        else 0) i) :
    let U : Matrix (Fin N) (Fin N) ℂ := fun i j => (b j : Fin N → ℂ) i
    ∀ (j : Fin n) (i : Fin N),
      U i ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ = A i j := by
  intro U j i
  have hbv := hb ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩
    (show _ ∈ Set.range
      (fun j : Fin n => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ : Fin N))
      from ⟨j, rfl⟩)
  have hlt : j.val < N := Nat.lt_of_lt_of_le j.isLt hn
  change (b ⟨j.val, hlt⟩ : Fin N → ℂ) i = A i j
  have : (b ⟨j.val, hlt⟩ : Fin N → ℂ) =
      ((WithLp.equiv 2 (Fin N → ℂ)).symm (fun r => A r ⟨j.val, j.isLt⟩) :
        Fin N → ℂ) := by
    have := congr_arg (WithLp.equiv 2 (Fin N → ℂ)) hbv
    simpa [dif_pos j.isLt] using this
  rw [this]; rfl

-- Helper: the entry-by-entry conjugation equality
private lemma diagonal_conjugation_entries {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℂ) (hn : n ≤ N)
    (U : Matrix (Fin N) (Fin N) ℂ) (d : Fin n → ℂ)
    (hU_cols : ∀ (j : Fin n) (i : Fin N),
      U i ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ = A i j) :
    A * Matrix.diagonal d * A.conjTranspose =
      U * Matrix.diagonal (fun i : Fin N =>
        if h : i.val < n then d ⟨i.val, h⟩ else 0) * U.conjTranspose := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  simp_rw [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have rhs_simp : ∀ k : Fin N,
      U i k * (if h : (k : ℕ) < n then d ⟨k, h⟩ else 0) * star (U j k) =
      if h : (k : ℕ) < n then
        A i ⟨k, h⟩ * d ⟨k, h⟩ * star (A j ⟨k, h⟩) else 0 := by
    intro k; split_ifs with h
    · have hkk : (⟨(⟨k.val, h⟩ : Fin n).val,
          Nat.lt_of_lt_of_le (⟨k.val, h⟩ : Fin n).isLt hn⟩ : Fin N) =
          k := Fin.ext rfl
      have h1 := hU_cols ⟨k, h⟩ i; rw [hkk] at h1
      have h2 := hU_cols ⟨k, h⟩ j; rw [hkk] at h2
      rw [h1, h2]
    · ring
  simp_rw [rhs_simp]
  symm
  exact sum_dite_fin_eq hn
    (fun k h => A i ⟨k, h⟩ * d ⟨k, h⟩ * star (A j ⟨k, h⟩))
    (fun k => A i k * d k * star (A j k))
    (fun _ _ => rfl)

-- ONB extension computation is expensive due to matrix algebra
/-- An `N × n` isometry can be completed to an `N × N` unitary whose first `n`
columns agree with the original isometry. -/
lemma exists_unitary_extension_of_isometry {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℂ) (hA : A.conjTranspose * A = 1)
    (hn : n ≤ N) :
    ∃ U : Matrix (Fin N) (Fin N) ℂ,
      U.conjTranspose * U = 1 ∧
      U * U.conjTranspose = 1 ∧
      ∀ (j : Fin n) (i : Fin N),
        U i ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ = A i j := by
  open Matrix in
  let cols : Fin n → EuclideanSpace ℂ (Fin N) :=
    fun j => (WithLp.equiv 2 (Fin N → ℂ)).symm (fun i => A i j)
  have hcols : Orthonormal ℂ cols := isometry_cols_orthonormal A hA
  let v : Fin N → EuclideanSpace ℂ (Fin N) := fun i =>
    if h : i.val < n then cols ⟨i.val, h⟩ else 0
  let s : Set (Fin N) := Set.range
    (fun j : Fin n => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ : Fin N))
  have hs_restrict : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨i', rfl⟩ := hi
    obtain ⟨j', rfl⟩ := hj
    simp only [v, s, Set.restrict_apply, dif_pos i'.isLt, dif_pos j'.isLt, Fin.eta]
    rw [(orthonormal_iff_ite.mp hcols) i' j']
    simp [Fin.val_inj]
  have hcard :
      Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N) := by
    simp [EuclideanSpace]
  obtain ⟨b, hb⟩ := hs_restrict.exists_orthonormalBasis_extension_of_card_eq hcard
  let U : Matrix (Fin N) (Fin N) ℂ := fun i j => (b j : Fin N → ℂ) i
  have hUU : U.conjTranspose * U = 1 := onb_matrix_unitary b
  have hUU' : U * U.conjTranspose = 1 := mul_eq_one_comm.mpr hUU
  have hU_cols : ∀ (j : Fin n) (i : Fin N),
      U i ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ = A i j :=
    onb_extension_cols A hn b hb
  exact ⟨U, hUU, hUU', hU_cols⟩

/-- After completing an isometry to a unitary, the small-space compression
`Aᴴ * M * A` is the principal submatrix of `Uᴴ * M * U` on the first `n`
coordinates. -/
lemma compression_eq_submatrix_unitary_conj {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℂ) (hA : A.conjTranspose * A = 1)
    (hn : n ≤ N) (M : Matrix (Fin N) (Fin N) ℂ) :
    ∃ U : Matrix (Fin N) (Fin N) ℂ,
      U.conjTranspose * U = 1 ∧
      U * U.conjTranspose = 1 ∧
      (U.conjTranspose * M * U).submatrix
          (fun i : Fin n => (⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ : Fin N))
          (fun i : Fin n => (⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ : Fin N)) =
        A.conjTranspose * M * A := by
  obtain ⟨U, hU_left, hU_right, hU_cols⟩ :=
    exists_unitary_extension_of_isometry A hA hn
  refine ⟨U, hU_left, hU_right, ?_⟩
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hU_cols j k]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [hU_cols i x]

/-- An N×n isometry (A†A = I_n, n ≤ N) can be extended to an N×N unitary.
    The first n columns of U match A, so A * D * A† = U * (D ⊕ 0) * U†
    for any n×n diagonal D. -/
lemma isometry_diagonal_conjugation {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℂ) (hA : A.conjTranspose * A = 1)
    (hn : n ≤ N) (d : Fin n → ℂ) :
    ∃ U : Matrix (Fin N) (Fin N) ℂ,
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      A * Matrix.diagonal d * A.conjTranspose =
        U * Matrix.diagonal (fun i : Fin N =>
          if h : i.val < n then d ⟨i.val, h⟩ else 0) * U.conjTranspose := by
  obtain ⟨U, hUU, hUU', hU_cols⟩ :=
    exists_unitary_extension_of_isometry A hA hn
  exact ⟨U, hUU, hUU', diagonal_conjugation_entries A hn U d hU_cols⟩

/-- Eigenvalue spectrum of an isometry-embedded density operator.
    If `evs` is a valid eigenvalue spectrum for `ρ`, then the zero-padded
    version is a valid spectrum for `VρV†`. -/
lemma IsEigenvalueSpectrum_isometryEmbed {n N : ℕ} [NeZero n] [NeZero N]
    (V : Matrix (Fin N) (Fin n) ℂ) (hV : V.conjTranspose * V = 1)
    (ρ : DensityOp n) (evs : Fin n → ℝ)
    (h : IsEigenvalueSpectrum ρ evs) :
    IsEigenvalueSpectrum (DensityOp.isometryEmbed V hV ρ)
      (fun i : Fin N =>
        if hi : i.val < n then evs ⟨i.val, hi⟩ else 0) := by
  obtain ⟨h_nn, h_sum, h_le, W, hWW, hWW', hspec⟩ := h
  have hn := n_le_N_of_isometry V hV
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Nonneg
    intro i; dsimp only; split_ifs with hi
    · exact h_nn ⟨i.val, hi⟩
    · exact le_refl 0
  · -- Sum = 1
    dsimp only
    rw [sum_zeroPad_eq hn evs]
    exact h_sum
  · -- Each eigenvalue ≤ 1
    intro i; dsimp only; split_ifs with hi
    · exact h_le ⟨i.val, hi⟩
    · linarith
  · -- Unitary decomposition via isometry_diagonal_conjugation
    -- A = V * W† is an N×n isometry: A†A = W V†V W† = WW† = I
    set A := V * W.conjTranspose with hA_def
    have hAA : A.conjTranspose * A = 1 := by
      rw [hA_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc W * V.conjTranspose * (V * W.conjTranspose)
          = W * (V.conjTranspose * V) * W.conjTranspose := by
            simp only [Matrix.mul_assoc]
        _ = W * 1 * W.conjTranspose := by rw [hV]
        _ = W * W.conjTranspose := by rw [Matrix.mul_one]
        _ = 1 := hWW'
    -- Get unitary U with A * D * A† = U * D_ext * U†
    obtain ⟨U, hUU, hUU', hU_spec⟩ :=
      isometry_diagonal_conjugation A hAA hn (fun i => (evs i : ℂ))
    -- Use U† as our unitary (swapping U† and U in the decomposition)
    use U.conjTranspose
    refine ⟨?_, ?_, ?_⟩
    · -- (U†)† * U† = U * U† = 1
      rw [Matrix.conjTranspose_conjTranspose]; exact hUU'
    · -- U† * (U†)† = U† * U = 1
      rw [Matrix.conjTranspose_conjTranspose]; exact hUU
    · -- (VρV†) = (U†)† * D_ext * U† = U * D_ext * U†
      change V * ρ.toOp * V.conjTranspose =
        (U.conjTranspose).conjTranspose *
        Matrix.diagonal (fun i : Fin N =>
          ↑(if hi : ↑i < n then evs ⟨↑i, hi⟩ else 0)) *
        U.conjTranspose
      rw [Matrix.conjTranspose_conjTranspose]
      -- Rewrite VρV† = A * diag(evs) * A†
      have h_VρV : V * ρ.toOp * V.conjTranspose =
          A * Matrix.diagonal (fun i => (evs i : ℂ)) * A.conjTranspose := by
        rw [hA_def, hspec, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]
      rw [h_VρV, hU_spec]
      -- The two diagonal matrices agree up to cast placement
      congr 1; congr 1
      ext i j
      simp only [Matrix.diagonal_apply]
      split_ifs <;> simp [Complex.ofReal_zero]

/-- Von Neumann entropy is invariant under isometric embedding: S(VρV†) = S(ρ).

    The nonzero eigenvalues of VρV† equal those of ρ, with additional zero eigenvalues.
    Since 0 · log(0) = 0, the Shannon entropy (and hence von Neumann entropy) is preserved. -/
lemma vonNeumannEntropy_isometry_invariance {n N : ℕ} [NeZero n] [NeZero N]
    (V : Matrix (Fin N) (Fin n) ℂ) (hV : V.conjTranspose * V = 1)
    (ρ : DensityOp n) :
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy (DensityOp.isometryEmbed V hV ρ) =
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ := by
  -- Build zero-padded eigenvalue spectrum for the embedded operator
  set evs := eigenvaluesOf ρ
  have h_spec := eigenvaluesOf_spec ρ
  have h_embed_spec :=
    IsEigenvalueSpectrum_isometryEmbed V hV ρ evs h_spec
  -- Use vonNeumannEntropy_eq_shannonEntropy to rewrite LHS
  rw [vonNeumannEntropy_eq_shannonEntropy _ _ h_embed_spec]
  -- Goal: shannonEntropy (zeroPad evs) = vonNeumannEntropy ρ
  -- RHS unfolds to shannonEntropy (eigenvaluesOf ρ) = shannonEntropy evs
  unfold vonNeumannEntropy
  exact shannonEntropy_zeroPad (n_le_N_of_isometry V hV) evs

/-- Two spectral decompositions of the same matrix yield the same functional calculus.
    If R is unitary and R * diag(λ) * R† = diag(μ), then R * diag(f(λ)) * R† = diag(f(μ))
    for any function f : ℝ → ℝ. -/
lemma unitary_diagonal_conjugation_function {n : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ)
    (hR_left : R† * R = 1) (hR_right : R * R† = 1)
    (evs1 μ : Fin n → ℝ)
    (h_diag : R * Matrix.diagonal (fun i => (evs1 i : ℂ)) * R† =
              Matrix.diagonal (fun i => (μ i : ℂ)))
    (f : ℝ → ℝ) :
    R * Matrix.diagonal (fun i => (f (evs1 i) : ℂ)) * R† =
    Matrix.diagonal (fun i => (f (μ i) : ℂ)) := by
  -- From hypothesis: R * diag(evs1) = diag(μ) * R
  have hcomm : R * Matrix.diagonal (fun i => (evs1 i : ℂ)) =
               Matrix.diagonal (fun i => (μ i : ℂ)) * R := by
    have h1 := congr_arg (· * R) h_diag
    simp only [Matrix.mul_assoc] at h1
    rw [show R† * R = 1 from hR_left] at h1
    simp only [Matrix.mul_one] at h1
    exact h1
  -- Entry-wise: R i j * evs1 j = μ i * R i j
  have h_entry : ∀ i j, R i j * (evs1 j : ℂ) = (μ i : ℂ) * R i j := by
    intro i j
    have h := congr_fun (congr_fun hcomm i) j
    simp only [Matrix.mul_apply, Matrix.diagonal_apply] at h
    rw [Finset.sum_eq_single j (fun b _ hbj => by simp [hbj]) (by simp)] at h
    simp only [ite_true] at h
    rw [Finset.sum_eq_single i (fun b _ hbi => by simp [Ne.symm hbi])
        (by simp)] at h
    simpa using h
  -- R i j * f(evs1 j) = R i j * f(μ i) (case split on R i j = 0)
  have h_f_entry : ∀ i j, R i j * (f (evs1 j) : ℂ) = R i j * (f (μ i) : ℂ) := by
    intro i j
    by_cases hRij : R i j = 0
    · simp [hRij]
    · have hev : (evs1 j : ℂ) = (μ i : ℂ) := by
        have h := h_entry i j
        have : R i j * (evs1 j : ℂ) = R i j * (μ i : ℂ) := by rw [h]; ring
        exact mul_left_cancel₀ hRij this
      congr 1
      exact congrArg (fun x => (f x : ℂ)) (Complex.ofReal_injective hev)
  -- Now prove the matrix equation entry-by-entry
  ext i k
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  simp_rw [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- Rewrite each summand using h_f_entry
  have h_sum_eq : ∀ j, R i j * (↑(f (evs1 j)) : ℂ) * star (R k j) =
      (↑(f (μ i)) : ℂ) * (R i j * star (R k j)) := by
    intro j; rw [h_f_entry i j]; ring
  simp_rw [h_sum_eq]
  rw [← Finset.mul_sum]
  -- ∑ j, R i j * conj(R k j) = (R * R†) i k = δ i k
  have h_RRt : ∑ j, R i j * star (R k j) = if i = k then 1 else 0 := by
    have := congr_fun (congr_fun hR_right i) k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
    exact this
  rw [h_RRt]
  split_ifs with hik
  · subst hik; simp
  · simp

/-- Spectral decomposition invariance for matrix functional calculus.
    Two spectral decompositions of the same matrix yield the same result
    when applying any function f to the eigenvalues. -/
lemma spectral_decomp_function_invariance {n : ℕ}
    (U₁ U₂ : Matrix (Fin n) (Fin n) ℂ)
    (hU₁_left : U₁† * U₁ = 1) (hU₁_right : U₁ * U₁† = 1)
    (hU₂_left : U₂† * U₂ = 1) (hU₂_right : U₂ * U₂† = 1)
    (evs₁ evs₂ : Fin n → ℝ)
    (h₁ : U₁† * Matrix.diagonal (fun i => (evs₁ i : ℂ)) * U₁ =
           U₂† * Matrix.diagonal (fun i => (evs₂ i : ℂ)) * U₂)
    (f : ℝ → ℝ) :
    U₁† * Matrix.diagonal (fun i => (f (evs₁ i) : ℂ)) * U₁ =
    U₂† * Matrix.diagonal (fun i => (f (evs₂ i) : ℂ)) * U₂ := by
  -- Let R = U₂ * U₁†, R is unitary
  set R := U₂ * U₁† with hR_def
  have hR_left : R† * R = 1 := by
    rw [hR_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc U₁ * U₂† * (U₂ * U₁†)
        = U₁ * (U₂† * U₂) * U₁† := by simp only [Matrix.mul_assoc]
      _ = U₁ * 1 * U₁† := by rw [hU₂_left]
      _ = U₁ * U₁† := by rw [Matrix.mul_one]
      _ = 1 := hU₁_right
  have hR_right : R * R† = 1 := by
    rw [hR_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc U₂ * U₁† * (U₁ * U₂†)
        = U₂ * (U₁† * U₁) * U₂† := by simp only [Matrix.mul_assoc]
      _ = U₂ * 1 * U₂† := by rw [hU₁_left]
      _ = U₂ * U₂† := by rw [Matrix.mul_one]
      _ = 1 := hU₂_right
  -- From h₁: U₁† diag(evs₁) U₁ = U₂† diag(evs₂) U₂
  -- Multiply by U₂ on left and U₂† on right:
  -- U₂ U₁† diag(evs₁) U₁ U₂† = diag(evs₂)
  -- i.e., R * diag(evs₁) * R† = diag(evs₂)
  have h_R_diag : R * Matrix.diagonal (fun i => (evs₁ i : ℂ)) * R† =
                  Matrix.diagonal (fun i => (evs₂ i : ℂ)) := by
    rw [hR_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc U₂ * U₁† * Matrix.diagonal (fun i => (evs₁ i : ℂ)) * (U₁ * U₂†)
        = U₂ * (U₁† * Matrix.diagonal (fun i => (evs₁ i : ℂ)) * U₁) * U₂† := by
          simp only [Matrix.mul_assoc]
      _ = U₂ * (U₂† * Matrix.diagonal (fun i => (evs₂ i : ℂ)) * U₂) * U₂† := by
          rw [h₁]
      _ = (U₂ * U₂†) * Matrix.diagonal (fun i => (evs₂ i : ℂ)) * (U₂ * U₂†) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * Matrix.diagonal (fun i => (evs₂ i : ℂ)) * 1 := by rw [hU₂_right]
      _ = Matrix.diagonal (fun i => (evs₂ i : ℂ)) := by simp
  -- Apply unitary_diagonal_conjugation_function
  have h_f := unitary_diagonal_conjugation_function R hR_left hR_right evs₁ evs₂ h_R_diag f
  -- Unwind R: R * diag(f(evs₁)) * R† = diag(f(evs₂))
  -- means U₂ U₁† diag(f(evs₁)) U₁ U₂† = diag(f(evs₂))
  -- means U₁† diag(f(evs₁)) U₁ = U₂† diag(f(evs₂)) U₂
  rw [hR_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h_f
  have : U₂† * (U₂ * U₁† * Matrix.diagonal (fun i => (f (evs₁ i) : ℂ)) *
    (U₁ * U₂†)) * U₂ =
    U₂† * Matrix.diagonal (fun i => (f (evs₂ i) : ℂ)) * U₂ := by
    rw [h_f]
  have key : U₂† * (U₂ * U₁† * Matrix.diagonal (fun i => (f (evs₁ i) : ℂ)) *
      (U₁ * U₂†)) * U₂ =
      U₁† * Matrix.diagonal (fun i => (f (evs₁ i) : ℂ)) * U₁ := by
    calc U₂† * (U₂ * U₁† * Matrix.diagonal (fun i => (f (evs₁ i) : ℂ)) *
        (U₁ * U₂†)) * U₂
        = (U₂† * U₂) * U₁† * Matrix.diagonal (fun i => (f (evs₁ i) : ℂ)) *
          U₁ * (U₂† * U₂) := by simp only [Matrix.mul_assoc]
      _ = 1 * U₁† * Matrix.diagonal (fun i => (f (evs₁ i) : ℂ)) * U₁ * 1 := by
          rw [hU₂_left]
      _ = U₁† * Matrix.diagonal (fun i => (f (evs₁ i) : ℂ)) * U₁ := by
          simp
  rw [← key, this]

/-- traceProductLogSigma equals a matrix trace expression. -/
lemma traceProductLogSigma_eq_trace {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    traceProductLogSigma ρ σ =
    (ρ.toOp * (eigenbasisOf σ)† *
      Matrix.diagonal (fun i => (Real.log (eigenvaluesOf σ i) : ℂ))
      * eigenbasisOf σ).trace.re := by
  unfold traceProductLogSigma diagonalOfRhoInSigmaBasis
  set W := eigenbasisOf σ
  set μ := eigenvaluesOf σ
  -- Step 1: Use trace cyclicity to rewrite RHS
  have h_cyc : (ρ.toOp * W† * Matrix.diagonal (fun i => (Real.log (μ i) : ℂ)) * W).trace =
    (W * ρ.toOp * W† * Matrix.diagonal (fun i => (Real.log (μ i) : ℂ))).trace := by
    conv_lhs => rw [show ρ.toOp * W† * Matrix.diagonal (fun i => (Real.log (μ i) : ℂ)) * W =
      (ρ.toOp * W† * Matrix.diagonal (fun i => (Real.log (μ i) : ℂ))) * W from
      by simp only [Matrix.mul_assoc]]
    conv_rhs => rw [show W * ρ.toOp * W† *
      Matrix.diagonal (fun i => (Real.log (μ i) : ℂ)) =
      W * (ρ.toOp * W† *
        Matrix.diagonal (fun i => (Real.log (μ i) : ℂ))) from
        by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
  -- Step 2: Rewrite RHS using trace cyclicity
  conv_rhs =>
    rw [show (ρ.toOp * W† *
        Matrix.diagonal (fun i => (Real.log (μ i) : ℂ)) *
        W).trace.re =
      (W * ρ.toOp * W† *
        Matrix.diagonal (fun i => (Real.log (μ i) : ℂ))
      ).trace.re from by rw [h_cyc]]
  -- Step 3: Expand trace and show sums are equal
  set M := W * ρ.toOp * W†
  -- RHS = (M * diag(log μ)).trace.re = (∑ i, (M * diag(log μ)) i i).re
  -- = (∑ i, M i i * (log μ i : ℂ)).re  since (M * diag(d)) i i = M i i * d i
  -- = ∑ i, (M i i * (log μ i : ℂ)).re  by Complex.re_sum
  -- = ∑ i, (M i i).re * log(μ i)       since log(μ i) is real
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Complex.re_sum]
  congr 1; ext i
  -- Show (M * diag(log μ)) i i = M i i * (log μ i : ℂ)
  have h_mul_diag : (M * Matrix.diagonal (fun j => (Real.log (μ j) : ℂ))) i i =
      M i i * (Real.log (μ i) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · simp
  rw [h_mul_diag]
  -- (z * (r : ℂ)).re = z.re * r for real r
  exact (Complex.re_mul_ofReal _ _).symm

-- Needed for ONB extension computation
/-- Like `isometry_diagonal_conjugation` but with ∀ d inside the ∃. -/
lemma isometry_diagonal_conjugation_forall {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℂ) (hA : A.conjTranspose * A = 1) (hn : n ≤ N) :
    ∃ U : Matrix (Fin N) (Fin N) ℂ,
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      ∀ d : Fin n → ℂ,
        A * Matrix.diagonal d * A.conjTranspose =
          U * Matrix.diagonal (fun i : Fin N =>
            if h : i.val < n then d ⟨i.val, h⟩ else 0) * U.conjTranspose := by
  obtain ⟨U, hUU, hUU', hU_cols⟩ :=
    exists_unitary_extension_of_isometry A hA hn
  exact ⟨U, hUU, hUU', fun d => diagonal_conjugation_entries A hn U d hU_cols⟩

/-- Trace product log is invariant under isometric embedding:
    Tr(VρV† · log(VσV†)) = Tr(ρ · log σ).

    The matrix logarithm commutes with isometric conjugation in the sense that
    log(VσV†) restricted to the range of V equals V(log σ)V†. -/
lemma traceProductLogSigma_isometry_invariance {n N : ℕ} [NeZero n] [NeZero N]
    (V : Matrix (Fin N) (Fin n) ℂ) (hV : V.conjTranspose * V = 1)
    (ρ σ : DensityOp n) :
    traceProductLogSigma (DensityOp.isometryEmbed V hV ρ)
      (DensityOp.isometryEmbed V hV σ) =
    traceProductLogSigma ρ σ := by
  -- Abbreviations
  set W := eigenbasisOf σ with hW_def
  set μ := eigenvaluesOf σ with hμ_def
  have hn := n_le_N_of_isometry V hV
  -- Rewrite both sides using traceProductLogSigma_eq_trace
  rw [traceProductLogSigma_eq_trace, traceProductLogSigma_eq_trace]
  -- LHS = ((VρV†) * logMatrix(VσV†)).trace.re
  -- RHS = (ρ * logMatrix(σ)).trace.re
  -- Define the "matrix log" of σ
  set L := W† * Matrix.diagonal (fun i => (Real.log (μ i) : ℂ)) * W
    with hL_def
  -- Get the isometric extension unitary for A = V * W†
  set A := V * W† with hA_def
  have hAA : A† * A = 1 := by
    rw [hA_def, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    calc W * V† * (V * W†)
        = W * (V† * V) * W† := by simp only [Matrix.mul_assoc]
      _ = W * 1 * W† := by rw [hV]
      _ = W * W† := by rw [Matrix.mul_one]
      _ = 1 := eigenbasisOf_unitary_right σ
  obtain ⟨U_ext, hU_ext_left, hU_ext_right, hU_ext_spec⟩ :=
    isometry_diagonal_conjugation_forall A hAA hn
  -- From hU_ext_spec: A * diag(d) * A† = U_ext * diag(zeroPad d) * U_ext†
  -- VσV† = A * diag(μ) * A† = U_ext * diag(zeroPad μ) * U_ext†
  have h_sigma_embed :
    (DensityOp.isometryEmbed V hV σ).toOp =
    U_ext * Matrix.diagonal (fun i : Fin N =>
      if h : i.val < n then (μ ⟨i.val, h⟩ : ℂ) else 0) *
    U_ext† := by
    change V * σ.toOp * V† = _
    rw [eigenbasisOf_spectral_decomp σ]
    rw [show V * (W† * Matrix.diagonal (fun i => (μ i : ℂ)) * W) * V† =
      A * Matrix.diagonal (fun i => (μ i : ℂ)) * A† from by
      rw [hA_def]; simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]]
    exact hU_ext_spec (fun i => (μ i : ℂ))
  -- A * diag(log μ) * A† = U_ext * diag(zeroPad(log μ)) * U_ext†
  have h_logMatrix_embed :
    A * Matrix.diagonal (fun i => (Real.log (μ i) : ℂ)) * A† =
    U_ext * Matrix.diagonal (fun i : Fin N =>
      if h : i.val < n then (Real.log (μ ⟨i.val, h⟩) : ℂ) else 0) *
    U_ext† :=
    hU_ext_spec (fun i => (Real.log (μ i) : ℂ))
  -- Two spectral decompositions of VσV†:
  set W' := eigenbasisOf (DensityOp.isometryEmbed V hV σ) with hW'_def
  set μ' := eigenvaluesOf (DensityOp.isometryEmbed V hV σ)
    with hμ'_def
  have h_decomp1 := eigenbasisOf_spectral_decomp
    (DensityOp.isometryEmbed V hV σ)
  -- (1) VσV† = W'† * diag(μ') * W'
  -- (2) VσV† = U_ext * diag(zeroPad μ) * U_ext†
  -- Rewrite (2) as (U_ext†)† * diag(zeroPad μ) * U_ext†
  -- to match the U† D U convention in spectral_decomp_function_invariance
  set zeroPadMu : Fin N → ℝ :=
    fun i => if h : i.val < n then μ ⟨i.val, h⟩ else 0
    with h_zeroPadMu_def
  -- Need: diag used in h_sigma_embed matches (zeroPadMu i : ℂ)
  have h_diag_cast : (fun i : Fin N =>
      if h : i.val < n then (μ ⟨i.val, h⟩ : ℂ) else 0) =
    (fun i => (zeroPadMu i : ℂ)) := by
    ext i; simp only [h_zeroPadMu_def]
    split_ifs <;> simp
  have h_sigma_embed' :
    (DensityOp.isometryEmbed V hV σ).toOp =
    U_ext * Matrix.diagonal (fun i => (zeroPadMu i : ℂ)) *
    U_ext† := by
    rw [← h_diag_cast]; exact h_sigma_embed
  have h_two_decomps :
    W'† * Matrix.diagonal (fun i => (μ' i : ℂ)) * W' =
    (U_ext†)† *
      Matrix.diagonal (fun i => (zeroPadMu i : ℂ)) * U_ext† := by
    rw [Matrix.conjTranspose_conjTranspose]
    rw [← h_decomp1]; exact h_sigma_embed'
  have hW'_left := eigenbasisOf_unitary_left
    (DensityOp.isometryEmbed V hV σ)
  have hW'_right := eigenbasisOf_unitary_right
    (DensityOp.isometryEmbed V hV σ)
  have hU_ext_adj_left : (U_ext†)† * U_ext† = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact hU_ext_right
  have hU_ext_adj_right : U_ext† * (U_ext†)† = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact hU_ext_left
  -- Apply spectral FC: two decompositions → same functional calculus
  have h_fc := spectral_decomp_function_invariance
    W' U_ext†
    hW'_left hW'_right
    hU_ext_adj_left hU_ext_adj_right
    μ' zeroPadMu h_two_decomps Real.log
  -- h_fc: W'† * diag(log μ') * W' = U_ext * diag(log(zeroPadMu)) * U_ext†
  -- log(zeroPadMu i) = zeroPad(log μ) since log 0 = 0
  have h_log_zeroPad : (fun i : Fin N =>
      Real.log (zeroPadMu i)) =
    (fun i : Fin N =>
      if h : i.val < n then Real.log (μ ⟨i.val, h⟩) else 0) := by
    ext i; simp only [h_zeroPadMu_def]
    split_ifs with h
    · rfl
    · exact Real.log_zero
  rw [Matrix.conjTranspose_conjTranspose] at h_fc
  -- h_fc: W'† * diag(log μ') * W' = U_ext * diag(f∘zeroPadMu) * U_ext†
  -- And h_logMatrix_embed: A * diag(log μ) * A† = U_ext * diag(zeroPad(log μ)) * U_ext†
  -- Show these RHS are equal, hence logMatrix(VσV†) = A * diag(log μ) * A†
  have h_rhs_eq : Matrix.diagonal (fun i =>
      (Real.log (zeroPadMu i) : ℂ)) =
    Matrix.diagonal (fun i : Fin N =>
      if h : i.val < n then
        (Real.log (μ ⟨i.val, h⟩) : ℂ) else 0) := by
    congr 1; ext i
    simp only [h_zeroPadMu_def]
    split_ifs with h
    · rfl
    · simp [Real.log_zero]
  rw [h_rhs_eq] at h_fc
  -- Now h_fc and h_logMatrix_embed have same RHS
  have h_logMatrix_eq : W'† * Matrix.diagonal (fun i =>
      (Real.log (μ' i) : ℂ)) * W' =
    A * Matrix.diagonal (fun i => (Real.log (μ i) : ℂ)) * A† := by
    rw [h_fc, ← h_logMatrix_embed]
  -- Unpack: A = V * W†, A† = W * V†
  -- A * diag(log μ) * A† = V * W† * diag(log μ) * W * V† = V * L * V†
  have h_logMatrix_VLV : W'† * Matrix.diagonal (fun i =>
      (Real.log (μ' i) : ℂ)) * W' =
    V * L * V† := by
    rw [h_logMatrix_eq, hA_def, hL_def]
    simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  -- Substitute logMatrix(VσV†) = V * L * V† in LHS
  conv_lhs =>
    rw [show (DensityOp.isometryEmbed V hV ρ).toOp * W'† *
      Matrix.diagonal (fun i => (Real.log (μ' i) : ℂ)) * W' =
      (DensityOp.isometryEmbed V hV ρ).toOp *
      (W'† * Matrix.diagonal (fun i =>
        (Real.log (μ' i) : ℂ)) * W') from
      by simp only [Matrix.mul_assoc]]
    rw [h_logMatrix_VLV]
  -- LHS = (V * ρ * V† * V * L * V†).trace.re
  change (V * ρ.toOp * V† * (V * L * V†)).trace.re = _
  -- Simplify V†V = I
  have h_simplify : V * ρ.toOp * V† * (V * L * V†) =
    V * (ρ.toOp * L) * V† := by
    have hVtV : V† * V =
      (1 : Matrix (Fin n) (Fin n) ℂ) := hV
    calc V * ρ.toOp * V† * (V * L * V†)
        = V * ρ.toOp * (V† * V) * L * V† := by
          simp only [Matrix.mul_assoc]
      _ = V * ρ.toOp *
          (1 : Matrix (Fin n) (Fin n) ℂ) * L * V† := by
          rw [hVtV]
      _ = V * (ρ.toOp * L) * V† := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [h_simplify]
  -- Use trace cyclicity: Tr(V * M * V†) = Tr(V† * V * M) = Tr(M)
  have h_trace_cyc : (V * (ρ.toOp * L) * V†).trace =
    (ρ.toOp * L).trace := by
    rw [show V * (ρ.toOp * L) * V† =
      (V * (ρ.toOp * L)) * V† from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show V† * (V * (ρ.toOp * L)) =
      (V† * V) * (ρ.toOp * L) from by
      simp only [Matrix.mul_assoc]]
    rw [hV, Matrix.one_mul]
  rw [h_trace_cyc]
  -- RHS: (ρ * L).trace.re = (ρ * W† * diag(log μ) * W).trace.re
  simp only [hL_def, hW_def, hμ_def, Matrix.mul_assoc]

/-- Isometric invariance of relative entropy: D(VρV† ‖ VσV†) = D(ρ ‖ σ).

    Isometries preserve eigenvalues (and hence all spectral quantities),
    so relative entropy is invariant under isometric embedding. -/
lemma relativeEntropyReal_isometry_invariance {n N : ℕ} [NeZero n] [NeZero N]
    (V : Matrix (Fin N) (Fin n) ℂ) (hV : V.conjTranspose * V = 1)
    (ρ σ : DensityOp n) :
    relativeEntropyReal (DensityOp.isometryEmbed V hV ρ)
      (DensityOp.isometryEmbed V hV σ) = relativeEntropyReal ρ σ := by
  unfold relativeEntropyReal
  rw [vonNeumannEntropy_isometry_invariance V hV ρ,
      traceProductLogSigma_isometry_invariance V hV ρ σ]

end InfoTheory.RelativeEntropy

end
