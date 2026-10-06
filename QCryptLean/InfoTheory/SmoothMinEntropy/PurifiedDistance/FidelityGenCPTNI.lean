import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.DirectSumEmbed
import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.Metrics.FidelityCPTPMonotone
import QCryptLean.Quantum.TensorProducts.Hermitianization

/-!
# Generalized-fidelity data processing under CP trace-non-increasing maps

This file develops the data-processing inequality for the *generalized* fidelity
`fidelityGen` of sub-normalized states under completely positive maps, both in the
trace-preserving (CPTP) and the trace-non-increasing (CP-TNI) case.  The CP-TNI case
is reduced to the CPTP one via a block-diagonal CPTP completion (`cptnDilationMap`)
that routes the lost weight into one extra output dimension.

## Main definitions
- `cptnDilationMap`: the block-diagonal CPTP completion of a CP trace-non-increasing
  map, acting on one extra dimension and routing the lost weight into the new output.

## Main statements
- `SubDensityOp.fidelityGen_le_fidelityGen_cptp`: generalized fidelity is
  non-decreasing under a CPTP map (trace-preserving data processing).
- `SubDensityOp.exists_normalized_cptp_dilation_of_cp_tni`: a CP trace-non-increasing
  map admits a normalized CPTP dilation on one extra dimension.
- `SubDensityOp.fidelityGen_le_fidelityGen_cp_tni`: generalized fidelity is
  non-decreasing under a completely positive, trace-non-increasing map.
-/

open Quantum.Operators Matrix
open scoped ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Generalized fidelity is non-decreasing under a CPTP map** (trace-preserving
data-processing inequality for the *generalized* fidelity).

For a CPTP linear map `Ψ : Op a → Op b` and sub-normalized `ρ, σ : SubDensityOp a`
with sub-normalized images `ρ', σ'` realizing `ρ'.toOp = Ψ ρ.toOp`,
`σ'.toOp = Ψ σ.toOp`, the generalized fidelity does not decrease.

Since `Ψ` is trace preserving, the traces (and hence the correction term
`√((1-trρ)(1-trσ))`) are unchanged, so this reduces to the ordinary CPTP fidelity
DPI `Quantum.Metrics.fidelity_le_fidelity_cptp_image`. -/
theorem SubDensityOp.fidelityGen_le_fidelityGen_cptp
    {a b : ℕ} [NeZero a] [NeZero b]
    (Ψ : Op a → Op b)
    (hlin : IsLinearMap ℂ Ψ)
    (hcp : Quantum.Channels.IsCompletelyPositive Ψ)
    (htp : Quantum.Channels.IsTracePreserving Ψ)
    (ρ σ : SubDensityOp a) (ρ' σ' : SubDensityOp b)
    (hρ' : ρ'.toOp = Ψ ρ.toOp) (hσ' : σ'.toOp = Ψ σ.toOp) :
    fidelityGen ρ σ ≤ fidelityGen ρ' σ' := by
  -- Ordinary Uhlmann fidelity is non-decreasing under the CPTP map.
  have hfid :
      Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp ≤
        Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp :=
    Quantum.Metrics.fidelity_le_fidelity_cptp_image (IsLinearMap.mk' Ψ hlin)
      hcp htp ρ.toPosSemidefOp σ.toPosSemidefOp ρ'.toPosSemidefOp σ'.toPosSemidefOp
      hρ' hσ'
  -- Trace preservation fixes the correction terms.
  have htrρ : ρ'.trace = ρ.trace := by
    unfold SubDensityOp.trace; rw [hρ', htp ρ.toOp]
  have htrσ : σ'.trace = σ.trace := by
    unfold SubDensityOp.trace; rw [hσ', htp σ.toOp]
  unfold fidelityGen
  have hcorr :
      Real.sqrt ((1 - ρ.trace) * (1 - σ.trace)) =
        Real.sqrt ((1 - ρ'.trace) * (1 - σ'.trace)) := by rw [htrρ, htrσ]
  rw [hcorr]
  exact add_le_add hfid le_rfl

/-! ## The block-diagonal CPTP completion of a CP trace-non-increasing map -/

/-- The CPTP completion of a CP trace-non-increasing map `Φ : Op dIn → Op dOut`,
acting on one extra dimension `Op (dIn+1) → Op (dOut+1)`.

On the block decomposition `M = A ⊕ d` (top-left `dIn × dIn` block `A`, bottom-right
`1 × 1` scalar block `d`), it acts as

    Ψ(M) = Φ(A) ⊕ (tr A − tr Φ(A) + tr d),

routing the lost weight `tr A − tr Φ(A)` into the new output dimension.  On a
block-diagonal extension `ρ ⊕ (1 − tr ρ)` this gives `Φ ρ ⊕ (1 − tr Φ ρ)`, i.e.
the extension of the image, which is the content of `cptnDilationMap_extendOp`. -/
def cptnDilationMap {dIn dOut : ℕ} (Φ : Op dIn → Op dOut) (M : Op (dIn + 1)) :
    Op (dOut + 1) :=
  let M' := M.submatrix finSumFinEquiv finSumFinEquiv
  let A := M'.toBlocks₁₁
  let d := M'.toBlocks₂₂
  (Matrix.fromBlocks (Φ A) 0 0
      ((A.trace - (Φ A).trace + d.trace) • (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- On a block-diagonal extension, the dilation map sends `ρ`'s extension to the
extension of its image `Φ ρ = ρ'`. -/
lemma cptnDilationMap_extendOp {dIn dOut : ℕ}
    (Φ : Op dIn → Op dOut)
    (ρ : SubDensityOp dIn) (ρ' : SubDensityOp dOut) (hρ' : ρ'.toOp = Φ ρ.toOp) :
    cptnDilationMap Φ ρ.extendOp = ρ'.extendOp := by
  -- Reindex the extension back to block form: M' = fromBlocks ρ 0 0 ρ.defectBlock.
  have hM' : (ρ.extendOp).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ρ.toOp 0 0 ρ.defectBlock := by
    unfold SubDensityOp.extendOp
    rw [Matrix.submatrix_submatrix]
    simp
  -- Block components of M'.
  have hA : ((ρ.extendOp).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ = ρ.toOp := by
    rw [hM']; exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _
  have hd : ((ρ.extendOp).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ =
      ρ.defectBlock := by
    rw [hM']; exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _
  -- The bottom-right scalar simplifies to ρ'.defect.
  have hscalar : ρ.toOp.trace - (Φ ρ.toOp).trace + ρ.defectBlock.trace = ρ'.defect := by
    rw [ρ.trace_complex_eq, ← hρ', ρ'.trace_complex_eq, ρ.defectBlock_trace, SubDensityOp.defect,
      SubDensityOp.defect]
    push_cast; ring
  -- Assemble.
  simp only [cptnDilationMap]
  rw [hA, hd, hscalar, ← hρ']
  simp only [SubDensityOp.extendOp, SubDensityOp.defectBlock]

/-- Trace is invariant under reindexing by an equivalence on the index type. -/
lemma trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ κ ℂ) (e : ι ≃ κ) :
    (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Trace of a `Fin n ⊕ Fin 1` block matrix splits over the two diagonal blocks. -/
lemma trace_eq_toBlocks_add {n : ℕ}
    (N : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    N.trace = N.toBlocks₁₁.trace + N.toBlocks₂₂.trace := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.toBlocks₁₁,
    Matrix.toBlocks₂₂, Matrix.of_apply]

@[simp] lemma toBlocks₁₁_add {n : ℕ} (X Y : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    (X + Y).toBlocks₁₁ = X.toBlocks₁₁ + Y.toBlocks₁₁ := by
  ext i j; simp [Matrix.toBlocks₁₁]

@[simp] lemma toBlocks₂₂_add {n : ℕ} (X Y : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    (X + Y).toBlocks₂₂ = X.toBlocks₂₂ + Y.toBlocks₂₂ := by
  ext i j; simp [Matrix.toBlocks₂₂]

@[simp] lemma toBlocks₁₁_smul {n : ℕ} (c : ℂ) (X : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    (c • X).toBlocks₁₁ = c • X.toBlocks₁₁ := by
  ext i j; simp [Matrix.toBlocks₁₁]

@[simp] lemma toBlocks₂₂_smul {n : ℕ} (c : ℂ) (X : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    (c • X).toBlocks₂₂ = c • X.toBlocks₂₂ := by
  ext i j; simp [Matrix.toBlocks₂₂]

/-- The dilation map is linear. -/
lemma cptnDilationMap_isLinearMap {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    (Φ : Op dIn → Op dOut) (hlin : IsLinearMap ℂ Φ) :
    IsLinearMap ℂ (cptnDilationMap Φ) := by
  refine ⟨fun M N => ?_, fun c M => ?_⟩
  · -- additivity
    have hsub : (M + N).submatrix finSumFinEquiv finSumFinEquiv =
        M.submatrix finSumFinEquiv finSumFinEquiv +
          N.submatrix finSumFinEquiv finSumFinEquiv :=
      congrFun₂ (Matrix.submatrix_add M N) _ _
    simp only [cptnDilationMap, hsub, toBlocks₁₁_add, toBlocks₂₂_add, hlin.map_add,
      Matrix.trace_add]
    set AM := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ with hAM
    set AN := (N.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ with hAN
    set dM := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ with hdM
    set dN := (N.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ with hdN
    have hsplit :
        (AM.trace + AN.trace - ((Φ AM).trace + (Φ AN).trace) + (dM.trace + dN.trace))
          = (AM.trace - (Φ AM).trace + dM.trace) + (AN.trace - (Φ AN).trace + dN.trace) := by
      ring
    rw [hsplit, add_smul]
    have hfb : Matrix.fromBlocks (Φ AM + Φ AN) (0 : Matrix (Fin dOut) (Fin 1) ℂ)
          (0 : Matrix (Fin 1) (Fin dOut) ℂ)
          ((AM.trace - (Φ AM).trace + dM.trace) • 1 + (AN.trace - (Φ AN).trace + dN.trace) • 1)
        = Matrix.fromBlocks (Φ AM) 0 0 ((AM.trace - (Φ AM).trace + dM.trace) • 1)
          + Matrix.fromBlocks (Φ AN) 0 0 ((AN.trace - (Φ AN).trace + dN.trace) • 1) := by
      rw [Matrix.fromBlocks_add]; simp
    rw [hfb]
    exact congrFun₂ (Matrix.submatrix_add _ _) _ _
  · -- homogeneity
    have hsub : (c • M).submatrix finSumFinEquiv finSumFinEquiv =
        c • M.submatrix finSumFinEquiv finSumFinEquiv :=
      congrFun₂ (Matrix.submatrix_smul c M) _ _
    simp only [cptnDilationMap, hsub, toBlocks₁₁_smul, toBlocks₂₂_smul, hlin.map_smul,
      Matrix.trace_smul, smul_eq_mul]
    set A := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ with hA
    set d := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ with hd
    have hsplit : c * A.trace - c * (Φ A).trace + c * d.trace
        = c * (A.trace - (Φ A).trace + d.trace) := by ring
    rw [hsplit, ← smul_eq_mul, smul_assoc]
    have hfb : Matrix.fromBlocks (c • Φ A) (0 : Matrix (Fin dOut) (Fin 1) ℂ)
          (0 : Matrix (Fin 1) (Fin dOut) ℂ)
          (c • ((A.trace - (Φ A).trace + d.trace) • 1))
        = c • Matrix.fromBlocks (Φ A) 0 0 ((A.trace - (Φ A).trace + d.trace) • 1) := by
      rw [Matrix.fromBlocks_smul]; simp
    rw [hfb]
    exact congrFun₂ (Matrix.submatrix_smul _ _) _ _

/-- **Complete positivity from a Kraus-sum representation.**  If a map is of the
form `M ↦ ∑ₗ Lₗ · M · Lₗ†` then it is completely positive (its Choi matrix is a
sum of rank-one PSD outer products).  This mirrors the Kraus half of
`KrausRepresentation.is_cptp` but requires no completeness (trace) condition. -/
lemma isCompletelyPositive_of_kraus_sum {n m : ℕ} {ι : Type*} [Fintype ι]
    [NeZero n] [NeZero m]
    (L : ι → Matrix (Fin m) (Fin n) ℂ) (Ψ : Op n → Op m)
    (hΨ : ∀ M, Ψ M = ∑ l, L l * M * (L l)ᴴ) :
    Quantum.Channels.IsCompletelyPositive Ψ := by
  unfold Quantum.Channels.IsCompletelyPositive
  set w : ι → Fin (n * m) → ℂ := fun l α =>
    L l (finProdFinEquiv.symm α).2 (finProdFinEquiv.symm α).1 with hw
  suffices h_eq : Quantum.Channels.ChoiMatrix n m Ψ =
      ∑ l ∈ Finset.univ, Matrix.vecMulVec (w l) (star (w l)) by
    rw [h_eq]
    exact Matrix.posSemidef_sum Finset.univ
      (fun l _ => Matrix.posSemidef_vecMulVec_self_star (w l))
  have h_sum_entry : ∀ (f : ι → Op m) (a b : Fin m),
      (∑ l, f l) a b = ∑ l, f l a b := by
    intro f a b
    rw [show (∑ l, f l) a = ∑ l, (f l) a from Finset.sum_apply a Finset.univ f]
    exact Finset.sum_apply b Finset.univ _
  ext α β
  simp only [Quantum.Channels.ChoiMatrix, Matrix.of_apply]
  rw [hΨ, h_sum_entry]
  have h_rhs : (∑ l ∈ Finset.univ, Matrix.vecMulVec (w l) (star (w l))) α β =
      ∑ l, w l α * star (w l β) := by
    rw [show (∑ l ∈ Finset.univ, Matrix.vecMulVec (w l) (star (w l))) α =
        ∑ l, Matrix.vecMulVec (w l) (star (w l)) α from Finset.sum_apply α Finset.univ _]
    rw [show (∑ l, Matrix.vecMulVec (w l) (star (w l)) α) β =
        ∑ l, Matrix.vecMulVec (w l) (star (w l)) α β from Finset.sum_apply β Finset.univ _]
    simp only [Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply]
  rw [h_rhs]
  apply Finset.sum_congr rfl; intro l _
  simp only [hw]
  exact Quantum.Channels.mul_unitMatrix_conjTranspose_apply (L l) _ _ _ _

/-- **Kraus decomposition from complete positivity and linearity alone** (no
trace-preservation required): a linear CP map `Φ` has `Φ A = ∑ₖ Kₖ · A · Kₖ†`.
Local copy of the private `Quantum.Metrics.kraus_sum_of_cp_linear`. -/
lemma cp_linear_eq_kraus_sum {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ_linear : IsLinearMap ℂ Φ)
    (hΦ_cp : Quantum.Channels.IsCompletelyPositive Φ) :
    ∃ (r : ℕ) (K : Fin r → Matrix (Fin m) (Fin n) ℂ),
      ∀ A, Φ A = ∑ k, K k * A * (K k)ᴴ := by
  unfold Quantum.Channels.IsCompletelyPositive at hΦ_cp
  rw [Matrix.posSemidef_iff_eq_sum_vecMulVec] at hΦ_cp
  obtain ⟨r, v, hv⟩ := hΦ_cp
  set K : Fin r → Matrix (Fin m) (Fin n) ℂ :=
    fun k => Matrix.of fun a i => v k (finProdFinEquiv (i, a)) with hK
  refine ⟨r, K, ?_⟩
  intro A; ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    K, Matrix.of_apply]
  set E := fun i j : Fin n => Matrix.of fun r c =>
    if r = i ∧ c = j then (1:ℂ) else 0 with hE_def
  set hL := IsLinearMap.mk' Φ hΦ_linear
  have hA_decomp : A = ∑ i, ∑ j, A i j • E i j := by
    ext r c; simp only [E, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, mul_ite, mul_one, mul_zero]
    symm; exact Finset.sum_eq_single r
      (fun i _ hi => Finset.sum_eq_zero (fun j _ => by
        exact if_neg (fun ⟨h1, _⟩ => hi h1.symm)))
      (fun h => absurd (Finset.mem_univ r) h) |>.trans
        (Finset.sum_eq_single c
          (fun j _ hj => if_neg (fun ⟨_, h2⟩ => hj h2.symm))
          (fun h => absurd (Finset.mem_univ c) h) |>.trans (by simp))
  have hΦ_entry : Φ A a b = ∑ i, ∑ j, A i j *
      Quantum.Channels.ChoiMatrix n m Φ (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) := by
    conv_lhs => rw [hA_decomp, show Φ = hL from rfl, map_sum hL]
    simp_rw [map_sum hL, hL.map_smul, show ∀ x, (hL x : Op m) = Φ x from fun _ => rfl,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1; ext i; congr 1; ext j
    congr 1
    simp only [E, Quantum.Channels.ChoiMatrix, Matrix.of_apply,
      Equiv.symm_apply_apply]
  rw [hΦ_entry, hv]
  simp only [Matrix.vecMulVec, Pi.star_apply]
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

/-- Complete positivity is preserved by pointwise addition (Choi matrices add). -/
lemma isCompletelyPositive_add {n m : ℕ} [NeZero n] [NeZero m]
    (Φ Ψ : Op n → Op m)
    (hΦ : Quantum.Channels.IsCompletelyPositive Φ)
    (hΨ : Quantum.Channels.IsCompletelyPositive Ψ) :
    Quantum.Channels.IsCompletelyPositive (fun M => Φ M + Ψ M) := by
  unfold Quantum.Channels.IsCompletelyPositive at *
  have hC : Quantum.Channels.ChoiMatrix n m (fun M => Φ M + Ψ M) =
      Quantum.Channels.ChoiMatrix n m Φ + Quantum.Channels.ChoiMatrix n m Ψ := by
    ext α β
    simp only [Quantum.Channels.ChoiMatrix, Matrix.of_apply, Matrix.add_apply]
  rw [hC]
  exact hΦ.add hΨ

/-- Reindexing-conjugation: pulling a `Fin _ ⊕ Fin 1`-block operator `V` back through
the `finSumFinEquiv` reindexing commutes with conjugating the reindexed input. -/
lemma conj_submatrix_eq {dIn dOut : ℕ}
    (V : Matrix (Fin dOut ⊕ Fin 1) (Fin dIn ⊕ Fin 1) ℂ) (M : Op (dIn + 1)) :
    (V.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) * M *
        (V.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)ᴴ
      = (V * (M.submatrix finSumFinEquiv finSumFinEquiv) * Vᴴ).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [Matrix.conjTranspose_submatrix]
  conv_lhs => rw [show M = (M.submatrix finSumFinEquiv finSumFinEquiv).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm from by
      rw [Matrix.submatrix_submatrix]; simp]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/-- Trace of `N` against the rank-one PSD `|v⟩⟨v|` is the quadratic form. -/
lemma trace_mul_vecMulVec_self_star {d : ℕ} (N : Op d) (v : Fin d → ℂ) :
    (N * Matrix.vecMulVec v (star v)).trace = star v ⬝ᵥ N.mulVec v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec,
    Matrix.of_apply, Pi.star_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

/-- A finite sum of block matrices is the block matrix of the summed blocks. -/
lemma sum_fromBlocks {ι : Type*} [Fintype ι] {l m n o : Type*}
    (A : ι → Matrix n l ℂ) (B : ι → Matrix n m ℂ)
    (C : ι → Matrix o l ℂ) (D : ι → Matrix o m ℂ) :
    ∑ i, Matrix.fromBlocks (A i) (B i) (C i) (D i)
      = Matrix.fromBlocks (∑ i, A i) (∑ i, B i) (∑ i, C i) (∑ i, D i) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.fromBlocks, Matrix.sum_apply]

/-- Reindexing commutes with finite sums of matrices. -/
lemma submatrix_finset_sum {ι : Type*} [Fintype ι] {p q p' q' : Type*}
    (X : ι → Matrix p q ℂ) (f : p' → p) (g : q' → q) :
    (∑ i, X i).submatrix f g = ∑ i, (X i).submatrix f g := by
  ext x y
  simp [Matrix.submatrix_apply, Matrix.sum_apply]

/-- A `1×1` matrix equals its trace times the identity. -/
lemma fin_one_matrix_eq_trace_smul (X : Matrix (Fin 1) (Fin 1) ℂ) :
    X = X.trace • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  fin_cases a; fin_cases b
  simp [Matrix.trace, Matrix.diag]

/-- The dilation map is completely positive (Choi-PSD).  The flag block `Y ↦
tr((1 − Φ⋆ 1)·Y) • flag` is CP because the defect operator `1 − Φ⋆ 1` is PSD by
trace non-increase; the top-left block reuses `hcp`. -/
lemma cptnDilationMap_isCompletelyPositive {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    (Φ : Op dIn → Op dOut) (hlin : IsLinearMap ℂ Φ)
    (hcp : Quantum.Channels.IsCompletelyPositive Φ)
    (htni : ∀ A : Op dIn, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re) :
    Quantum.Channels.IsCompletelyPositive (cptnDilationMap Φ) := by
  -- Kraus decomposition of Φ.
  obtain ⟨r, K, hK⟩ := cp_linear_eq_kraus_sum Φ hlin hcp
  -- Defect operator `Ndef = 1 - ∑ Kₖ† Kₖ`.
  set G : Op dIn := ∑ k, (K k)ᴴ * (K k) with hG
  set Ndef : Op dIn := 1 - G with hNdef
  -- `tr(Φ A) = tr(G A)`.
  have hΦG : ∀ A : Op dIn, (Φ A).trace = (G * A).trace := by
    intro A
    rw [hK A, Matrix.trace_sum]
    have hcyc : ∀ k, ((K k) * A * (K k)ᴴ).trace = ((K k)ᴴ * (K k) * A).trace :=
      fun k => Matrix.trace_mul_cycle (K k) A (K k)ᴴ
    simp_rw [hcyc]
    rw [← Matrix.trace_sum, ← Finset.sum_mul]
  -- `tr(Ndef A) = tr A - tr Φ A`.
  have hNA : ∀ B : Op dIn, (Ndef * B).trace = B.trace - (Φ B).trace := by
    intro B
    rw [hNdef, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, ← hΦG]
  -- `G` and `Ndef` are Hermitian.
  have hGherm : G.IsHermitian := by
    change Gᴴ = G
    rw [hG, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hNherm : Ndef.IsHermitian := by
    change Ndefᴴ = Ndef
    rw [hNdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hGherm]
  -- `Ndef` is PSD by trace non-increase tested on rank-one inputs.
  have hNpsd : Ndef.PosSemidef := by
    refine Quantum.Operators.posSemidef_of_isHermitian_of_quadraticForm_re_nonneg hNherm
      (fun v => ?_)
    have hAv : (Matrix.vecMulVec v (star v)).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star v
    have hq : quadraticForm Ndef v = (Ndef * Matrix.vecMulVec v (star v)).trace :=
      (trace_mul_vecMulVec_self_star Ndef v).symm
    rw [hq, hNA (Matrix.vecMulVec v (star v)), Complex.sub_re]
    have htr := htni _ hAv
    linarith
  -- Spectral (vecMulVec) decomposition of `Ndef`.
  obtain ⟨numV, p, hp⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hNpsd
  -- Key decomposition into top / flag-defect / flag-extra pieces.
  have key : cptnDilationMap Φ = fun M : Op (dIn + 1) =>
      ((Matrix.fromBlocks (Φ (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁)
            (0 : Matrix (Fin dOut) (Fin 1) ℂ) (0 : Matrix (Fin 1) (Fin dOut) ℂ)
            (0 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
        + (Matrix.fromBlocks 0 0 0
            ((Ndef * (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁).trace
              • (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix
            finSumFinEquiv.symm finSumFinEquiv.symm)
      + (Matrix.fromBlocks 0 0 0
          ((M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂.trace
            • (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
    funext M
    simp only [cptnDilationMap]
    have hadd : ∀ X Y : Matrix (Fin dOut ⊕ Fin 1) (Fin dOut ⊕ Fin 1) ℂ,
        X.submatrix finSumFinEquiv.symm finSumFinEquiv.symm
          + Y.submatrix finSumFinEquiv.symm finSumFinEquiv.symm
          = (X + Y).submatrix finSumFinEquiv.symm finSumFinEquiv.symm :=
      fun X Y => by ext a b; simp [Matrix.submatrix_apply, Matrix.add_apply]
    rw [hadd, hadd]
    congr 1
    rw [Matrix.fromBlocks_add, Matrix.fromBlocks_add,
      hNA (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁]
    congr 1 <;> simp only [add_zero, zero_add, ← add_smul]
  rw [key]
  refine isCompletelyPositive_add _ _ (isCompletelyPositive_add _ _ ?_ ?_) ?_
  · -- top block: CP via Kraus `Kₖ ⊕ 0`
    apply isCompletelyPositive_of_kraus_sum
      (fun k => (Matrix.fromBlocks (K k) (0 : Matrix (Fin dOut) (Fin 1) ℂ)
        (0 : Matrix (Fin 1) (Fin dIn) ℂ) (0 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm)
    intro M
    set Mt := M.submatrix finSumFinEquiv finSumFinEquiv with hMt
    symm
    simp only [conj_submatrix_eq]
    rw [← submatrix_finset_sum]
    congr 1
    have hterm : ∀ k, (Matrix.fromBlocks (K k) (0 : Matrix (Fin dOut) (Fin 1) ℂ)
          (0 : Matrix (Fin 1) (Fin dIn) ℂ) (0 : Matrix (Fin 1) (Fin 1) ℂ)) * Mt
          * (Matrix.fromBlocks (K k) (0 : Matrix (Fin dOut) (Fin 1) ℂ)
            (0 : Matrix (Fin 1) (Fin dIn) ℂ) (0 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ
        = Matrix.fromBlocks (K k * Mt.toBlocks₁₁ * (K k)ᴴ) (0 : Matrix (Fin dOut) (Fin 1) ℂ)
            (0 : Matrix (Fin 1) (Fin dOut) ℂ) (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
      intro k
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks Mt]
      rw [Matrix.fromBlocks_conjTranspose]
      simp only [Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
        Matrix.mul_zero, Matrix.zero_mul, add_zero]
    rw [← hMt]
    simp only [hterm]
    rw [sum_fromBlocks]
    simp only [Finset.sum_const_zero]
    rw [← hK Mt.toBlocks₁₁]
  · -- flag-defect block: CP via the PSD decomposition of `Ndef`
    set qa : Fin numV → Matrix (Fin 1) (Fin dIn) ℂ :=
      fun j => Matrix.of fun _ i => star (p j i) with hqa_def
    apply isCompletelyPositive_of_kraus_sum
      (fun j : Fin numV => (Matrix.fromBlocks (0 : Matrix (Fin dOut) (Fin dIn) ℂ) 0
        (qa j) (0 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    intro M
    set Mt := M.submatrix finSumFinEquiv finSumFinEquiv with hMt
    symm
    simp only [conj_submatrix_eq]
    rw [← submatrix_finset_sum]
    congr 1
    rw [← hMt]
    have hterm : ∀ j : Fin numV,
        (Matrix.fromBlocks (0 : Matrix (Fin dOut) (Fin dIn) ℂ) 0 (qa j) 0) * Mt
          * (Matrix.fromBlocks (0 : Matrix (Fin dOut) (Fin dIn) ℂ) 0 (qa j) 0)ᴴ
        = Matrix.fromBlocks 0 0 0 (qa j * Mt.toBlocks₁₁ * (qa j)ᴴ) := by
      intro j
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks Mt]
      rw [Matrix.fromBlocks_conjTranspose]
      simp only [Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
        Matrix.mul_zero, Matrix.zero_mul, add_zero]
    simp only [hterm]
    rw [sum_fromBlocks]
    simp only [Finset.sum_const_zero]
    congr 1
    -- `(qaⱼ)† (qaⱼ) = |pⱼ⟩⟨pⱼ|`
    have hqq : ∀ j, (qa j)ᴴ * (qa j) = Matrix.vecMulVec (p j) (star (p j)) := by
      intro j
      ext i k
      simp only [hqa_def, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec,
        Matrix.of_apply, Fin.sum_univ_one, Pi.star_apply, star_star]
    -- per-term trace identity
    have hqaj : ∀ j, qa j * Mt.toBlocks₁₁ * (qa j)ᴴ =
        ((Matrix.vecMulVec (p j) (star (p j)) * Mt.toBlocks₁₁).trace)
          • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      intro j
      rw [fin_one_matrix_eq_trace_smul (qa j * Mt.toBlocks₁₁ * (qa j)ᴴ)]
      congr 1
      rw [Matrix.trace_mul_cycle (qa j) Mt.toBlocks₁₁ (qa j)ᴴ, hqq j]
    simp only [hqaj]
    rw [← Finset.sum_smul]
    congr 1
    rw [hp, Finset.sum_mul, Matrix.trace_sum]
  · -- flag-extra block: CP via the single Kraus `0 ⊕ 1`
    apply isCompletelyPositive_of_kraus_sum
      (fun _ : Fin 1 => (Matrix.fromBlocks (0 : Matrix (Fin dOut) (Fin dIn) ℂ) 0 0
        (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    intro M
    set Mt := M.submatrix finSumFinEquiv finSumFinEquiv with hMt
    symm
    simp only [conj_submatrix_eq]
    rw [← submatrix_finset_sum]
    congr 1
    rw [← hMt, Fin.sum_univ_one]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Mt]
    rw [Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
      Matrix.one_mul, add_zero, zero_add]
    congr 1
    exact fin_one_matrix_eq_trace_smul Mt.toBlocks₂₂

/-- The dilation map is trace preserving: the lost weight `tr A − tr Φ(A)` is
exactly recovered in the new output dimension. -/
lemma cptnDilationMap_isTracePreserving {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    (Φ : Op dIn → Op dOut) :
    Quantum.Channels.IsTracePreserving (cptnDilationMap Φ) := by
  intro M
  show (cptnDilationMap Φ M).trace = M.trace
  have hM : M.trace =
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁.trace +
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂.trace := by
    rw [← trace_eq_toBlocks_add, trace_submatrix_equiv]
  simp only [cptnDilationMap]
  rw [trace_submatrix_equiv, trace_eq_toBlocks_add, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₂₂]
  have hs : ((( (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁.trace
        - (Φ (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁).trace
        + (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂.trace))
      • (1 : Matrix (Fin 1) (Fin 1) ℂ)).trace =
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁.trace
        - (Φ (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁).trace
        + (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂.trace := by
    simp
  rw [hs, hM]; ring

/-- Generalized fidelity of the normalized block-diagonal extensions equals that of
the originals.  The extensions are normalized (trace 1), so their generalized
fidelity is the ordinary Uhlmann fidelity, which `toDensityOpExtend_fidelity`
identifies with `fidelityGen ρ σ`. -/
lemma fidelityGen_toDensityOpExtend {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    fidelityGen (DensityOp.toSubDensityOp ρ.toDensityOpExtend)
        (DensityOp.toSubDensityOp σ.toDensityOpExtend) = fidelityGen ρ σ := by
  rw [← toDensityOpExtend_fidelity ρ σ]
  unfold fidelityGen
  rw [toSubDensityOp_trace ρ.toDensityOpExtend, toSubDensityOp_trace σ.toDensityOpExtend]
  simp only [sub_self, mul_zero, Real.sqrt_zero, add_zero]
  have e : ∀ (d : DensityOp (n + 1)),
      (DensityOp.toSubDensityOp d).toPosSemidefOp = d.toPosSemidefOp :=
    fun d => by apply PosSemidefOp.ext; rfl
  rw [e, e]

/-- **Normalized CPTP dilation of a CP trace-non-increasing map** (existence form
of the Tomamichel block-extension).

A completely positive, trace-non-increasing map `Φ : Op dIn → Op dOut` together with
sub-normalized states `ρ, σ` and their images `ρ', σ'` admits a *normalized* CPTP
dilation on one extra dimension: there is a CPTP linear map
`Ψ : Op (dIn + 1) → Op (dOut + 1)` and sub-normalized "dilated" states
`ρe, σe : SubDensityOp (dIn + 1)`, `ρe', σe' : SubDensityOp (dOut + 1)` with
`ρe'.toOp = Ψ ρe.toOp`, `σe'.toOp = Ψ σe.toOp`, whose generalized fidelities agree
with those of the originals.

Construction (Tomamichel 2016, proof of the data-processing inequality for `F*`):
extend each sub-normalized state `ρ` to the normalized state `ρ ⊕ (1 - tr ρ)` on one
extra dimension (`SubDensityOp.toDensityOpExtend`), and extend `Φ` to the CPTP map
routing the lost weight `tr ρ - tr (Φ ρ)` into the new output dimension.
Block-diagonal additivity of the Uhlmann fidelity (`toDensityOpExtend_fidelity`)
then identifies `F(ρe, σe) = F*(ρ, σ)`.

This existence statement isolates the (block-extension) construction; the resulting
inequality is then the trace-preserving generalized-fidelity DPI
`SubDensityOp.fidelityGen_le_fidelityGen_cptp`. -/
theorem SubDensityOp.exists_normalized_cptp_dilation_of_cp_tni
    {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    (Φ : Op dIn → Op dOut)
    (hlin : IsLinearMap ℂ Φ)
    (hcp : Quantum.Channels.IsCompletelyPositive Φ)
    (htni : ∀ A : Op dIn, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re)
    (ρ σ : SubDensityOp dIn) (ρ' σ' : SubDensityOp dOut)
    (hρ' : ρ'.toOp = Φ ρ.toOp) (hσ' : σ'.toOp = Φ σ.toOp) :
    ∃ (Ψ : Op (dIn + 1) → Op (dOut + 1)),
      IsLinearMap ℂ Ψ ∧
      Quantum.Channels.IsCompletelyPositive Ψ ∧
      Quantum.Channels.IsTracePreserving Ψ ∧
      ∃ (ρe σe : SubDensityOp (dIn + 1)) (ρe' σe' : SubDensityOp (dOut + 1)),
        ρe'.toOp = Ψ ρe.toOp ∧ σe'.toOp = Ψ σe.toOp ∧
        fidelityGen ρe σe = fidelityGen ρ σ ∧
        fidelityGen ρe' σe' = fidelityGen ρ' σ' := by
  refine ⟨cptnDilationMap Φ,
    cptnDilationMap_isLinearMap Φ hlin,
    cptnDilationMap_isCompletelyPositive Φ hlin hcp htni,
    cptnDilationMap_isTracePreserving Φ,
    DensityOp.toSubDensityOp ρ.toDensityOpExtend,
    DensityOp.toSubDensityOp σ.toDensityOpExtend,
    DensityOp.toSubDensityOp ρ'.toDensityOpExtend,
    DensityOp.toSubDensityOp σ'.toDensityOpExtend,
    ?_, ?_, ?_, ?_⟩
  · -- ρe'.toOp = Ψ ρe.toOp
    change ρ'.extendOp = cptnDilationMap Φ ρ.extendOp
    exact (cptnDilationMap_extendOp Φ ρ ρ' hρ').symm
  · -- σe'.toOp = Ψ σe.toOp
    change σ'.extendOp = cptnDilationMap Φ σ.extendOp
    exact (cptnDilationMap_extendOp Φ σ σ' hσ').symm
  · exact fidelityGen_toDensityOpExtend ρ σ
  · exact fidelityGen_toDensityOpExtend ρ' σ'

/-- **Generalized fidelity is non-decreasing under a CP trace-non-increasing map**
(sub-channel data-processing inequality).

For sub-normalized `ρ, σ : SubDensityOp dIn`, a completely positive map
`Φ : Op dIn → Op dOut` that is *trace-non-increasing* on PSD inputs
(`(Φ A).trace.re ≤ A.trace.re` for `A.PosSemidef`), and sub-normalized targets
`ρ', σ' : SubDensityOp dOut` realizing the images blockwise (`ρ'.toOp = Φ ρ.toOp`,
`σ'.toOp = Φ σ.toOp`), the generalized fidelity does not decrease:
`fidelityGen ρ σ ≤ fidelityGen ρ' σ'`.

This is the trace-non-increasing (TNI) strengthening of the trace-preserving CPTP
data-processing inequality.  The proof completes the CP-TNI map to a *normalized*
CPTP dilation on one extra dimension
(`SubDensityOp.exists_normalized_cptp_dilation_of_cp_tni`) and applies the
trace-preserving generalized-fidelity DPI
`SubDensityOp.fidelityGen_le_fidelityGen_cptp`.

Linearity (`hlin`) is a separate hypothesis: this repo's `IsCompletelyPositive` is a
Choi-PSD predicate that does not include linearity, so the dilation route requires it
explicitly, mirroring the shape of `IsCPTP`. -/
theorem SubDensityOp.fidelityGen_le_fidelityGen_cp_tni
    {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    (Φ : Op dIn → Op dOut)
    (hlin : IsLinearMap ℂ Φ)
    (hcp : Quantum.Channels.IsCompletelyPositive Φ)
    (htni : ∀ A : Op dIn, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re)
    (ρ σ : SubDensityOp dIn) (ρ' σ' : SubDensityOp dOut)
    (hρ' : ρ'.toOp = Φ ρ.toOp) (hσ' : σ'.toOp = Φ σ.toOp) :
    fidelityGen ρ σ ≤ fidelityGen ρ' σ' := by
  obtain ⟨Ψ, hΨlin, hΨcp, hΨtp, ρe, σe, ρe', σe', hρe', hσe', hfρ, hfρ'⟩ :=
    SubDensityOp.exists_normalized_cptp_dilation_of_cp_tni Φ hlin hcp htni ρ σ ρ' σ' hρ' hσ'
  calc fidelityGen ρ σ = fidelityGen ρe σe := hfρ.symm
    _ ≤ fidelityGen ρe' σe' :=
        SubDensityOp.fidelityGen_le_fidelityGen_cptp Ψ hΨlin hΨcp hΨtp ρe σe ρe' σe' hρe' hσe'
    _ = fidelityGen ρ' σ' := hfρ'

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
