import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.Channels.Stinespring.Reshape
import QCryptLean.Quantum.Channels.Stinespring.Minimal.Existence
import QCryptLean.Math.LinearAlgebra.UnitaryExtension
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Minimal Stinespring uniqueness (Watrous Thm 2.22) — reshape row-Gram, intertwining unitary

Any two minimal Stinespring isometries of the same CPTP map are related by a unitary
on the environment.  This file collects the sub-lemmas used in the proof together
with the main uniqueness statement.

The argument proceeds in three steps:

* **Sub-lemma 2 — equal row Grams.**  For two Stinespring isometries `U_A`, `U_B`
  recovering the same CPTP map `Φ`, the row Grams `Â · Âᴴ` and `B̂ · B̂ᴴ` of their
  reshapes are equal — both encode the Choi matrix of `Φ`.
* **Sub-lemma 3 — full column rank.**  For a minimal Stinespring isometry `U_A`
  of `Φ` with environment dimension `r`, `reshape U_A` has full column rank `r`.
* **Sub-lemma 4 — rectangular Gram-unitary extension.**  This pure linear-algebra
  step is provided by
  `Math.LinearAlgebra.UnitaryExtension.exists_unitary_right_mul_of_row_gram_eq_full_col_rank`:
  given two `(N × r)` matrices with equal row Grams `A · Aᴴ = B · Bᴴ` and `A` of
  full column rank, there exists a unitary `W : Op r` with
  `B = A · W`.

## Main statements
- `stinespringReshape_row_gram_eq_of_dilationRecovers_eq`: reshape row-Gram is
  determined by the recovered CPTP map.
- `choiMatrix_eq_reshape_row_gram_submatrix`: the Choi matrix of `Φ` equals the
  reshape row-Gram of any isometric dilation, up to the swap permutation.
- `rank_stinespringReshape_eq_choiRank`: the rank of the reshape of an isometric
  dilation equals the Choi rank of `Φ`.
- `isCompletelyPositive_of_isometric_dilation`: any isometric dilation of `Φ`
  witnesses complete positivity of `Φ`.
- `isTracePreserving_of_isometric_dilation`: any isometric dilation of `Φ`
  witnesses trace-preservation of `Φ`.
- `stinespringReshape_full_col_rank_of_minimal`: reshape of a minimal isometry has
  full column rank equal to the environment dimension.
- `minimal_stinespring_uniqueness_unitary`: two minimal Stinespring isometries of the
  same CPTP map are related by a unitary on the environment.

## References
- Watrous (2018) "Theory of Quantum Information", §2.2, Theorem 2.22
- Paulsen (2002) "Completely Bounded Maps and Operator Algebras", Theorem 4.6
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Bridge identity used in `stinespringReshape_row_gram_eq_of_dilationRecovers_eq`:
the `(a, b)` entry of `partialTraceB (U * E_{i,j} * Uᴴ)` equals the same
environment sum that appears in the row-Gram of `stinespringReshape U`
(see `stinespringReshape_mul_conjTranspose_apply`). -/
private lemma partialTraceB_mul_unitMatrix_conjTranspose_apply_eq_reshape_sum
    {n m r : ℕ}
    (U : Matrix (Fin (m * r)) (Fin n) ℂ)
    (a b : Fin m) (i j : Fin n) :
    partialTraceB
        (U * (Matrix.of fun (s c : Fin n) => if s = i ∧ c = j then (1:ℂ) else 0) * Uᴴ)
        a b
      = ∑ e : Fin r,
          U (finProdFinEquiv (a, e)) i * star (U (finProdFinEquiv (b, e)) j) := by
  simp only [partialTraceB, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  exact mul_unitMatrix_conjTranspose_apply U i j _ _

/-- Sub-lemma 2 — row-Gram of the reshape is determined by `Φ`. -/
lemma stinespringReshape_row_gram_eq_of_dilationRecovers_eq
    {n m r : ℕ} [NeZero n] [NeZero m] [NeZero r] [NeZero (m * r)]
    (Φ : Op n →ₗ[ℂ] Op m)
    (U_A U_B : Matrix (Fin (m * r)) (Fin n) ℂ)
    (hU_A_rec : DilationRecovers (⇑Φ) U_A)
    (hU_B_rec : DilationRecovers (⇑Φ) U_B) :
    stinespringReshape U_A * (stinespringReshape U_A)ᴴ
      = stinespringReshape U_B * (stinespringReshape U_B)ᴴ := by
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := finProdFinEquiv.surjective q
  -- Both sides equal `Φ(E_{i,j}) a b` via the helper identities and `DilationRecovers`.
  rw [stinespringReshape_mul_conjTranspose_apply U_A a b i j,
      stinespringReshape_mul_conjTranspose_apply U_B a b i j,
      ← partialTraceB_mul_unitMatrix_conjTranspose_apply_eq_reshape_sum U_A a b i j,
      ← partialTraceB_mul_unitMatrix_conjTranspose_apply_eq_reshape_sum U_B a b i j,
      ← hU_A_rec, ← hU_B_rec]

/-- Swap permutation `Fin (n * m) ≃ Fin (m * n)` exchanging the order of the two factors.
For `α = finProdFinEquiv (i, a)` we have `stinespringChoiSwap n m α = finProdFinEquiv (a, i)`. -/
private def stinespringChoiSwap (n m : ℕ) [NeZero n] [NeZero m] :
    Fin (n * m) ≃ Fin (m * n) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

@[simp] private lemma stinespringChoiSwap_apply (n m : ℕ) [NeZero n] [NeZero m]
    (i : Fin n) (a : Fin m) :
    stinespringChoiSwap n m (finProdFinEquiv (i, a)) = finProdFinEquiv (a, i) := by
  simp [stinespringChoiSwap, Equiv.prodComm]

/-- **Helper 1 — row-Gram of the reshape equals the Choi matrix up to swap.**
For an isometric dilation `U` of `Φ`, the row-Gram product `Â · Âᴴ` of the
Stinespring reshape, after permuting both row and column indices via
`stinespringChoiSwap`, equals the Choi matrix of `Φ`. -/
lemma choiMatrix_eq_reshape_row_gram_submatrix
    {n m r : ℕ} [NeZero n] [NeZero m] [NeZero r] [NeZero (m * r)]
    (Φ : Op n →ₗ[ℂ] Op m)
    (U : Matrix (Fin (m * r)) (Fin n) ℂ)
    (hrec : DilationRecovers (⇑Φ) U) :
    ChoiMatrix n m ⇑Φ
      = (stinespringReshape U * (stinespringReshape U)ᴴ).submatrix
          (stinespringChoiSwap n m) (stinespringChoiSwap n m) := by
  ext α β
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective α
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective β
  simp only [Matrix.submatrix_apply, stinespringChoiSwap_apply]
  -- RHS: row-Gram entry rewrites into env-sum, then partial-trace, then `Φ`.
  rw [stinespringReshape_mul_conjTranspose_apply U a b i j,
      ← partialTraceB_mul_unitMatrix_conjTranspose_apply_eq_reshape_sum U a b i j,
      ← hrec]
  -- LHS: unfold `ChoiMatrix` and reduce `finProdFinEquiv.symm (finProdFinEquiv _)`.
  simp only [ChoiMatrix, Matrix.of_apply, Equiv.symm_apply_apply]

/-- **Helper 2 — rank of the reshape equals the Choi rank.**
For any isometric dilation `U` of `Φ`, the rank of `stinespringReshape U` equals
the rank of `ChoiMatrix n m ⇑Φ`. -/
lemma rank_stinespringReshape_eq_choiRank
    {n m r : ℕ} [NeZero n] [NeZero m] [NeZero r] [NeZero (m * r)]
    (Φ : Op n →ₗ[ℂ] Op m)
    (U : Matrix (Fin (m * r)) (Fin n) ℂ)
    (hrec : DilationRecovers (⇑Φ) U) :
    Matrix.rank (stinespringReshape U) = Matrix.rank (ChoiMatrix n m ⇑Φ) := by
  rw [choiMatrix_eq_reshape_row_gram_submatrix Φ U hrec,
      Matrix.rank_submatrix _ (stinespringChoiSwap n m) (stinespringChoiSwap n m),
      Matrix.rank_self_mul_conjTranspose]

/-- **Helper 3 — any isometric dilation of `Φ` makes `Φ` completely positive.**
The Choi matrix factors through the row-Gram product `Â · Âᴴ` (which is PSD)
via a permutation `submatrix`. -/
lemma isCompletelyPositive_of_isometric_dilation
    {n m envDim : ℕ} [NeZero n] [NeZero m] [NeZero envDim] [NeZero (m * envDim)]
    (Φ : Op n →ₗ[ℂ] Op m)
    (U : Matrix (Fin (m * envDim)) (Fin n) ℂ)
    (hrec : DilationRecovers (⇑Φ) U) :
    IsCompletelyPositive ⇑Φ := by
  unfold IsCompletelyPositive
  rw [choiMatrix_eq_reshape_row_gram_submatrix Φ U hrec]
  exact ((Matrix.posSemidef_submatrix_equiv (stinespringChoiSwap n m)).mpr
    (Matrix.posSemidef_self_mul_conjTranspose _))

/-- **Helper 4 — any isometric dilation of `Φ` makes `Φ` trace-preserving.**
Standard cyclic-trace argument:
`tr(Φ A) = tr(partialTraceB(U A U†)) = tr(U A U†) = tr(A · Uᴴ U) = tr A`. -/
lemma isTracePreserving_of_isometric_dilation
    {n m envDim : ℕ} [NeZero n] [NeZero m] [NeZero envDim] [NeZero (m * envDim)]
    (Φ : Op n →ₗ[ℂ] Op m)
    (U : Matrix (Fin (m * envDim)) (Fin n) ℂ)
    (hU_iso : Uᴴ * U = 1)
    (hrec : DilationRecovers (⇑Φ) U) :
    IsTracePreserving ⇑Φ := by
  intro A
  rw [hrec A]
  rw [trace_partialTraceB]
  -- `tr(U * A * Uᴴ) = tr(Uᴴ * U * A) = tr(1 * A) = tr A`
  rw [Matrix.trace_mul_cycle, hU_iso, Matrix.one_mul]

/-- Sub-lemma 3 — reshape of a minimal Stinespring isometry has full column rank. -/
lemma stinespringReshape_full_col_rank_of_minimal
    {n m r : ℕ} [NeZero n] [NeZero m] [NeZero r] [NeZero (m * r)]
    (Φ : Op n →ₗ[ℂ] Op m)
    (U_A : Matrix (Fin (m * r)) (Fin n) ℂ)
    (hU_A_iso : U_Aᴴ * U_A = 1)
    (hU_A_rec : DilationRecovers (⇑Φ) U_A)
    (hU_A_min : ∀ (envDim' : ℕ) [NeZero envDim'] [NeZero (m * envDim')]
      (V' : Matrix (Fin (m * envDim')) (Fin n) ℂ),
      V'ᴴ * V' = 1 → DilationRecovers (⇑Φ) V' → r ≤ envDim') :
    Matrix.rank (stinespringReshape U_A) = r := by
  -- Strategy: pinch `rank Â` between `r` and `rank C_Φ` and use minimality.
  have hCP : IsCompletelyPositive ⇑Φ :=
    isCompletelyPositive_of_isometric_dilation Φ U_A hU_A_rec
  have hTP : IsTracePreserving ⇑Φ :=
    isTracePreserving_of_isometric_dilation Φ U_A hU_A_iso hU_A_rec
  have hrank_eq : Matrix.rank (stinespringReshape U_A) = Matrix.rank (ChoiMatrix n m ⇑Φ) :=
    rank_stinespringReshape_eq_choiRank Φ U_A hU_A_rec
  -- Upper bound: rank Â ≤ r (the number of columns of Â).
  have h_upper : Matrix.rank (stinespringReshape U_A) ≤ r :=
    Matrix.rank_le_width _
  -- Lower bound: r ≤ rank C_Φ via the Choi-rank packing dilation + minimality.
  obtain ⟨envDim, henv, hme, V', hEnvEq, hVV, hrec'⟩ :=
    choiRank_kraus_isometric_packing Φ hCP hTP
  have h_lower : r ≤ Matrix.rank (ChoiMatrix n m ⇑Φ) := by
    have := hU_A_min envDim V' hVV hrec'
    rw [hEnvEq] at this
    exact this
  -- Combine: r ≤ rank C_Φ = rank Â ≤ r.
  have h_lower' : r ≤ Matrix.rank (stinespringReshape U_A) := by
    rw [hrank_eq]; exact h_lower
  exact le_antisymm h_upper h_lower'

/-- **Stinespring uniqueness via minimal isometries** (Watrous Thm 2.22).

    If `U_A` and `U_B` are both minimal Stinespring isometries of the same CPTP
    map `Φ : Op n →ₗ[ℂ] Op m` with environment dimension `r` (so both have shape
    `Matrix (Fin (m * r)) (Fin n) ℂ`), then there exists a unitary `W` on `Fin r`
    such that `U_B = (id_m ⊗ W) * U_A`.

    Here `id_m ⊗ W` is the Kronecker block matrix with `W` on each diagonal `m`-block,
    i.e., the matrix `Matrix.of fun p q => if p.divNat = q.divNat then W p.modNat q.modNat else 0`
    (using the `Fin (m * r) ≃ Fin m × Fin r` identification).

    Mathematical content (Watrous 2018, §2.2, Theorem 2.22, uniqueness clause):
    define `W := (Reshape U_A)† * (Reshape U_B)` where `Reshape` is the
    Choi–Jamiołkowski column-to-row reshape sending
    `U : Matrix (Fin (m * r)) (Fin n) ℂ` to `Matrix (Fin (m * n)) (Fin r) ℂ`.
    Because both `U_A` and `U_B` recover `Φ`, their reshapes have the same
    row-Gram product; minimality of `U_A` forces `Reshape U_A` to have full column
    rank `r`, so `W` is unitary and the intertwining `U_B = (id_m ⊗ W) U_A` holds.

    References:
    - Watrous (2018) *Theory of Quantum Information*, §2.2, Theorem 2.22.
    - Paulsen (2002) *Completely Bounded Maps and Operator Algebras*, Theorem 4.6. -/
theorem minimal_stinespring_uniqueness_unitary
    {n m r : ℕ} [NeZero n] [NeZero m] [NeZero r] [NeZero (m * r)]
    (Φ : Op n →ₗ[ℂ] Op m)
    (U_A U_B : Matrix (Fin (m * r)) (Fin n) ℂ)
    (hU_A_iso : U_Aᴴ * U_A = 1)
    (hU_A_rec : DilationRecovers (⇑Φ) U_A)
    (hU_B_rec : DilationRecovers (⇑Φ) U_B)
    (hU_A_min : ∀ (envDim' : ℕ) [NeZero envDim'] [NeZero (m * envDim')]
      (V' : Matrix (Fin (m * envDim')) (Fin n) ℂ),
      V'ᴴ * V' = 1 → DilationRecovers (⇑Φ) V' → r ≤ envDim') :
    ∃ W : Op r,
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      U_B = (Matrix.of fun (p q : Fin (m * r)) =>
               let ⟨a, e⟩ := finProdFinEquiv.symm p
               let ⟨b, f⟩ := finProdFinEquiv.symm q
               if a = b then W e f else 0) * U_A := by
  -- Step 1: equal row Grams of the reshapes.
  have hgram :
      stinespringReshape U_A * (stinespringReshape U_A)ᴴ
        = stinespringReshape U_B * (stinespringReshape U_B)ᴴ :=
    stinespringReshape_row_gram_eq_of_dilationRecovers_eq Φ U_A U_B hU_A_rec hU_B_rec
  -- Step 2: `Â` has full column rank `r`.
  have hrank : Matrix.rank (stinespringReshape U_A) = r :=
    stinespringReshape_full_col_rank_of_minimal Φ U_A hU_A_iso hU_A_rec hU_A_min
  -- Step 3: rectangular Gram-unitary extension on the reshapes.
  obtain ⟨W', hW'CT, hW'TC, hW'eq⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_unitary_right_mul_of_row_gram_eq_full_col_rank
      (stinespringReshape U_A) (stinespringReshape U_B) hgram hrank
  -- Step 4: choose `W := W'ᵀ`.
  have hswap : (W'ᵀ)ᴴ = (W'ᴴ)ᵀ := by
    rw [Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose]
  refine ⟨W'ᵀ, ?_, ?_, ?_⟩
  · -- `Wᴴ * W = (W'ᵀ)ᴴ * W'ᵀ = (W'ᴴ)ᵀ * W'ᵀ = (W' * W'ᴴ)ᵀ = 1ᵀ = 1`.
    have htr := congr_arg Matrix.transpose hW'TC
    rw [Matrix.transpose_mul, Matrix.transpose_one] at htr
    rw [hswap]; exact htr
  · -- `W * Wᴴ = W'ᵀ * (W'ᵀ)ᴴ = W'ᵀ * (W'ᴴ)ᵀ = (W'ᴴ * W')ᵀ = 1ᵀ = 1`.
    have htr := congr_arg Matrix.transpose hW'CT
    rw [Matrix.transpose_mul, Matrix.transpose_one] at htr
    rw [hswap]; exact htr
  · -- Step 5: undo the reshape — `idTensorBlock W'ᵀ * U_A = U_B`.
    have hreshape :
        stinespringReshape (idTensorBlock (W'ᵀ) * U_A) = stinespringReshape U_B := by
      rw [stinespringReshape_idTensorBlock_mul, Matrix.transpose_transpose]
      exact hW'eq.symm
    have hUB : idTensorBlock (W'ᵀ) * U_A = U_B := by
      have := congr_arg stinespringUnreshape hreshape
      rwa [stinespringUnreshape_stinespringReshape,
           stinespringUnreshape_stinespringReshape] at this
    -- Step 6: unfold `idTensorBlock` to match the literal form in the statement.
    rw [← hUB]
    rfl

end Quantum.Channels

end -- noncomputable section
