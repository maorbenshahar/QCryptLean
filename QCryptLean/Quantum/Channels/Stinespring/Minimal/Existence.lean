import QCryptLean.Math.SpectralTheory.PSDDecomposition
import QCryptLean.Quantum.Channels.Stinespring.Minimal.Basic

/-!
# Minimal Stinespring Dilation — existence

This file builds a `MinimalStinespringDilation` for every CPTP linear map.  The
construction proceeds in two steps:

* `choiRank_kraus_isometric_packing` — the spectral decomposition of the Choi matrix
  yields exactly `rank(C_Φ)` Kraus operators that pack into an isometry recovering Φ.
* `dilation_envDim_ge_choiRank` — any isometric dilation has environment dimension at
  least the Choi rank.

Combining both gives `minimal_stinespring_exists` whose witnessed environment
dimension equals the Choi rank of `Φ`.

## Main statements
- `choiRank_kraus_isometric_packing`: spectral decomposition of the Choi matrix yields
  exactly `rank(C_Φ)` Kraus operators packing into an isometric dilation of `Φ`.
- `dilation_envDim_ge_choiRank`: any dilation recovering `Φ` (in particular any isometric
  one) has environment dimension at least the Choi rank, since each "slice" of the dilation
  yields a Kraus operator.
- `minimal_stinespring_exists`: every CPTP linear map admits a `MinimalStinespringDilation`
  whose `envDim` equals `Matrix.rank (ChoiMatrix n m Φ)`.

## References
- Stinespring (1955) "Positive functions on C*-algebras"
- Watrous (2018) "Theory of Quantum Information", §2.2, Theorem 2.22
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- **Choi-rank Stinespring packing.**

    For a CPTP linear map Φ with Choi matrix C_Φ of rank `r`, there exists a family of
    `r` Kraus operators whose stack `V` is an isometry `V†V = 1` and recovers Φ via
    `Φ(A) = partialTraceB(V A V†)`.

    Mathematical content: spectral decomposition of the PSD Choi matrix gives `r`
    nonzero eigenvalues with eigenvectors `(vᵢ)`; reshaping each `√λᵢ · vᵢ` via the
    Choi–Jamiołkowski isomorphism yields Kraus operators `Kᵢ`.  Trace preservation
    forces `∑ Kᵢ† Kᵢ = 1`, which converts the stacked Kraus operators into an isometry
    and guarantees `r ≥ 1` (so `envDim` is nonzero). -/
theorem choiRank_kraus_isometric_packing
    {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (hCP : IsCompletelyPositive ⇑Φ)
    (hTP : IsTracePreserving ⇑Φ) :
    ∃ (envDim : ℕ) (_ : NeZero envDim) (_ : NeZero (m * envDim))
      (V : Matrix (Fin (m * envDim)) (Fin n) ℂ),
      envDim = Matrix.rank (ChoiMatrix n m ⇑Φ) ∧
      V† * V = 1 ∧
      DilationRecovers (⇑Φ) V := by
  -- Step 1: rank-minimal PSD decomposition of the Choi matrix.
  set r := Matrix.rank (ChoiMatrix n m ⇑Φ) with hr_def
  obtain ⟨v, hv⟩ := Math.SpectralTheory.psd_eq_sum_rank_vecMulVec hCP
  -- Step 2: extract Kraus operators (same reshape as `cptp_eq_kraus_sum`).
  set K : Fin r → Matrix (Fin m) (Fin n) ℂ :=
    fun k => Matrix.of fun a i => v k (finProdFinEquiv (i, a)) with hK_def
  -- Step 3: Φ has Kraus decomposition Φ A = ∑_k K_k A K_k† — by the same
  -- computation as `cptp_eq_kraus_sum`, which only needs *some* PSD decomposition
  -- of the Choi matrix.
  have hKraus : ∀ A : Op n, Φ A = ∑ k, K k * A * (K k)† := by
    intro A; ext a b
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      K, Matrix.of_apply]
    -- Expand Φ A using linearity over the matrix-unit basis.
    set E := fun i j : Fin n => Matrix.of fun r c =>
      if r = i ∧ c = j then (1:ℂ) else 0 with hE_def
    have hA_decomp : A = ∑ i, ∑ j, A i j • E i j := by
      ext rr cc
      simp only [E, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.of_apply, mul_ite, mul_one, mul_zero]
      symm; exact Finset.sum_eq_single rr
        (fun i _ hi => Finset.sum_eq_zero (fun j _ => by
          exact if_neg (fun ⟨h1, _⟩ => hi h1.symm)))
        (fun h => absurd (Finset.mem_univ rr) h) |>.trans
          (Finset.sum_eq_single cc
            (fun j _ hj => if_neg (fun ⟨_, h2⟩ => hj h2.symm))
            (fun h => absurd (Finset.mem_univ cc) h) |>.trans (by simp))
    have hΦ_entry : Φ A a b = ∑ i, ∑ j, A i j *
        ChoiMatrix n m ⇑Φ (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) := by
      conv_lhs => rw [hA_decomp, map_sum]
      simp_rw [map_sum, LinearMap.map_smul, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul]
      congr 1; ext i; congr 1; ext j
      congr 1
      simp only [E, ChoiMatrix, Matrix.of_apply,
        Equiv.symm_apply_apply]
    rw [hΦ_entry, hv]
    simp only [vecMulVec, Pi.star_apply]
    have h_push : ∀ i j : Fin n,
        (∑ k, Matrix.of fun x_2 y => v k x_2 * star (v k y))
          (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
        ∑ k, v k (finProdFinEquiv (i, a)) * star (v k (finProdFinEquiv (j, b))) :=
      fun i j => Matrix.sum_apply _ _ Finset.univ _
    simp_rw [h_push]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    have reorder : ∀ (f : Fin n → Fin n → Fin r → ℂ),
        ∑ a, ∑ b, ∑ k, f a b k = ∑ k, ∑ b, ∑ a, f a b k := by
      intro f
      calc ∑ a, ∑ b, ∑ k, f a b k
          = ∑ a, ∑ k, ∑ b, f a b k := by
            congr 1; ext a; exact Finset.sum_comm
        _ = ∑ k, ∑ a, ∑ b, f a b k := Finset.sum_comm
        _ = ∑ k, ∑ b, ∑ a, f a b k := by
            congr 1; ext k; exact Finset.sum_comm
    rw [reorder]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    ring
  -- Step 4: r ≠ 0, i.e. Choi rank is positive.  Otherwise Φ = 0, but Φ preserves
  -- trace so Tr(Φ 1) = Tr 1 = n ≠ 0.
  have hr_ne : r ≠ 0 := by
    intro hr0
    -- With r = 0, the Kraus sum is empty so Φ A = 0 for every A.
    have hΦ0 : ∀ A : Op n, Φ A = 0 := by
      intro A
      rw [hKraus A]
      -- Sum over `Fin 0` is empty.
      have hcard : (Finset.univ : Finset (Fin r)).card = 0 := by
        rw [Finset.card_univ, Fintype.card_fin]; exact hr0
      rw [Finset.card_eq_zero.mp hcard, Finset.sum_empty]
    -- Trace preservation: Tr(Φ 1) = Tr 1 = n
    have htp1 := hTP (1 : Op n)
    rw [hΦ0 1, Matrix.trace_zero] at htp1
    have hne : (1 : Op n).trace ≠ 0 := by
      simp only [Matrix.trace_one, Fintype.card_fin]
      exact Nat.cast_ne_zero.mpr (NeZero.ne n)
    exact hne htp1.symm
  haveI hrNZ : NeZero r := ⟨hr_ne⟩
  haveI hmrNZ : NeZero (m * r) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos m) (NeZero.pos r))⟩
  -- Step 5: pack Kraus operators into isometry V.
  let V : Matrix (Fin (m * r)) (Fin n) ℂ :=
    Matrix.of fun α i =>
      let ak := finProdFinEquiv.symm α
      K ak.2 ak.1 i
  refine ⟨r, hrNZ, hmrNZ, V, rfl, ?_, ?_⟩
  · -- V†V = 1, using Kraus completeness from trace preservation.
    have hcomp : ∑ k, (K k)† * K k = 1 := by
      apply kraus_sum_completeness K
      intro A
      rw [← hKraus A]
      exact hTP A
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.one_apply, V,
      Matrix.of_apply]
    trans (∑ k : Fin r, ((K k)† * K k) i j)
    · trans (∑ p : Fin m × Fin r, star (K p.2 p.1 i) * K p.2 p.1 j)
      · exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun x => by simp)
      · rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _
        simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
    · rw [← Matrix.sum_apply, hcomp, Matrix.one_apply]
  · -- DilationRecovers: Φ A = partialTraceB (V * A * V†), by same proof as in
    -- `stinespring_dilation`.
    intro A; ext a b
    rw [hKraus A]
    simp only [Quantum.TensorProducts.partialTraceB, Matrix.of_apply]
    simp only [Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, V, Matrix.of_apply]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro i _
    congr 1
    · apply Finset.sum_congr rfl; intro j _
      simp [finProdFinEquiv.symm_apply_apply]
    · simp [finProdFinEquiv.symm_apply_apply]

/-- **Stinespring environment lower bound.**

    Any dilation `V'` recovering Φ (`Φ(ρ) = Tr_E(V' ρ V'†)`, `hrec`) has environment
    dimension at least the Choi rank; in particular every isometric dilation does. Neither
    complete positivity of Φ (implied by `hrec`) nor the isometry condition on `V'` is used.

    Mathematical content: an isometric dilation `V : ℂⁿ → ℂᵐ ⊗ ℂ^(envDim')` gives a
    family of `envDim'` Kraus operators `Kₖ` (the "slices" of V along the
    environment).  The Choi matrix decomposes as `C_Φ = ∑_k vec(Kₖ) vec(Kₖ)†`,
    so its rank is at most `envDim'`. -/
theorem dilation_envDim_ge_choiRank
    {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m)
    (envDim' : ℕ) [NeZero envDim'] [NeZero (m * envDim')]
    (V' : Matrix (Fin (m * envDim')) (Fin n) ℂ)
    (hrec : DilationRecovers (⇑Φ) V') :
    Matrix.rank (ChoiMatrix n m ⇑Φ) ≤ envDim' := by
  -- Encode V' as W : Matrix (Fin (n*m)) (Fin envDim') ℂ via "slicing".
  -- W α k = V'(finProdFinEquiv(a, k), i)  where (i, a) = finProdFinEquiv.symm α.
  -- This is the matrix of the family of Kraus operators K_k = (id_m ⊗ ⟨k|) V'
  -- arranged column-by-column under the Choi–Jamiołkowski reshape.
  let W : Matrix (Fin (n * m)) (Fin envDim') ℂ :=
    Matrix.of fun α k =>
      V' (finProdFinEquiv ((finProdFinEquiv.symm α).2, k)) (finProdFinEquiv.symm α).1
  -- Key claim: the Choi matrix factors as `W * W†`.
  have hC : ChoiMatrix n m ⇑Φ = W * W† := by
    ext α β
    -- Unfold Choi matrix entry, apply dilation, expand partial trace.
    simp only [ChoiMatrix, Matrix.of_apply]
    rw [hrec]
    simp only [Quantum.TensorProducts.partialTraceB, Matrix.of_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, W]
    -- Match summands.
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- Sandwich with matrix unit yields the slice product.
    have hsand :=
      mul_unitMatrix_conjTranspose_apply V'
        (finProdFinEquiv.symm α).1 (finProdFinEquiv.symm β).1
        (finProdFinEquiv ((finProdFinEquiv.symm α).2, k))
        (finProdFinEquiv ((finProdFinEquiv.symm β).2, k))
    -- Massage LHS into the sandwich form.
    exact hsand
  -- Now use rank(W * W†) = rank(W) and rank(W) ≤ envDim'.
  rw [hC, Matrix.rank_self_mul_conjTranspose]
  exact Matrix.rank_le_width W

/-- Every CPTP linear map admits a minimal Stinespring dilation.

    The environment dimension of the minimal dilation equals the Choi rank
    `Matrix.rank (ChoiMatrix n m Φ)`.

    Trace preservation is required: a merely CP map Φ = 0 has rank(C_Φ) = 0, making
    `envDim = 0` which violates the `NeZero envDim` requirement of
    `MinimalStinespringDilation`.  For CPTP maps, tr(Φ(1)) = n > 0 forces rank ≥ 1.

    The proof has two parts, isolated as named lemmas above:
    1. `choiRank_kraus_isometric_packing` — the Choi matrix PSD decomposition
       `C_Φ = ∑ vᵢ vᵢ†` (with `rank(C_Φ)` summands) gives Kraus operators whose stack
       is the minimal isometry V.
    2. `dilation_envDim_ge_choiRank` — any other Stinespring dilation has environment
       dimension at least `rank(C_Φ)`, since each "slice" of the dilation yields a
       Kraus operator and the Choi matrix is the sum of `envDim'` rank-1 PSD pieces. -/
theorem minimal_stinespring_exists
    {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (hCP : IsCompletelyPositive ⇑Φ) (hTP : IsTracePreserving ⇑Φ) :
    ∃ (envDim : ℕ) (_ : NeZero envDim) (_ : NeZero (m * envDim)),
      ∃ _ : MinimalStinespringDilation Φ envDim,
        envDim = Matrix.rank (ChoiMatrix n m ⇑Φ) := by
  -- Step 1: package the Choi spectral decomposition as an isometric dilation
  -- with environment dimension exactly `rank(C_Φ)`.
  obtain ⟨envDim, henv, hme, V, hEnvEq, hVV, hrec⟩ :=
    choiRank_kraus_isometric_packing Φ hCP hTP
  -- Step 2: assemble the `MinimalStinespringDilation` record.  The minimality
  -- witness invokes the Stinespring lower bound sub-stub.
  refine ⟨envDim, henv, hme, ?_, hEnvEq⟩
  refine
    { isometry := V
      isometry_adj_mul := hVV
      recovers := hrec
      env_minimal := ?_ }
  intro envDim' _ _ V' _ hrec'
  -- `envDim = rank(C_Φ) ≤ envDim'` by the lower bound lemma.
  rw [hEnvEq]
  exact dilation_envDim_ge_choiRank Φ envDim' V' hrec'

end Quantum.Channels

end -- noncomputable section
