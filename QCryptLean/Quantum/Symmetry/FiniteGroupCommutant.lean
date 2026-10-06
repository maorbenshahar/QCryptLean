import QCryptLean.Quantum.Symmetry.TensorPowerCommutant

/-!
# Finite-group matrix commutants

The span of a finite-group matrix representation equals its double commutant.
The proof uses the vectorization and amplification maps from the matrix
Schur–Weyl argument, with a group-averaged projection onto the orbit span.
-/

open Matrix Quantum.Operators
open scoped BigOperators

noncomputable section

namespace Quantum.Symmetry

/-- Conjugation averaging for a finite-group matrix representation. -/
def finiteGroupMatrixAverage {G ι : Type*} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) (X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g * X * ρ g⁻¹

/-- A finite-group conjugation average commutes with its representation. -/
lemma finiteGroupMatrixAverage_commute {G ι : Type*} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) (X : Matrix ι ι ℂ) (g : G) :
    Commute (ρ g) (finiteGroupMatrixAverage ρ X) := by
  change ρ g * _ = _ * ρ g
  unfold finiteGroupMatrixAverage
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  change ρ g * (ρ h * X * ρ h⁻¹) = ρ (g * h) * X * ρ (g * h)⁻¹ * ρ g
  rw [_root_.mul_inv_rev, map_mul, map_mul]
  simp only [mul_assoc, ← map_mul, inv_mul_cancel, mul_one]
  rw [map_mul, mul_assoc]

/-- Finite-group conjugation averaging is complex linear. -/
def finiteGroupMatrixAverageLinear {G ι : Type*} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun := finiteGroupMatrixAverage ρ
  map_add' A B := by
    simp only [finiteGroupMatrixAverage, mul_add, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c A := by
    change finiteGroupMatrixAverage ρ (c • A) = c • finiteGroupMatrixAverage ρ A
    simp only [finiteGroupMatrixAverage, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
    exact smul_comm _ _ _

/-- A matrix already in the commutant is fixed by conjugation averaging. -/
lemma finiteGroupMatrixAverage_eq_self {G ι : Type*} [Group G] [Fintype G]
    [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) (X : Matrix ι ι ℂ)
    (hX : ∀ g, Commute (ρ g) X) : finiteGroupMatrixAverage ρ X = X := by
  have hterm (g : G) : ρ g * X * ρ g⁻¹ = X := by
    rw [(hX g).eq, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [finiteGroupMatrixAverage, hterm, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Amplification of a matrix representation is a representation on two copies. -/
def amplifiedMatrixRep {G : Type*} [Group G] {d : ℕ} (ρ : G →* Op d) :
    G →* Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ where
  toFun g := ampl d (ρ g)
  map_one' := by rw [map_one, ampl_one]
  map_mul' g h := by rw [map_mul, ampl_mul]

/-- The vectorized orbit span of a matrix representation. -/
def matrixRepOrbitSpan {G : Type*} [Group G] {d : ℕ} (ρ : G →* Op d) :
    Submodule ℂ (Fin d × Fin d → ℂ) :=
  Submodule.map (amplVecL d) (Submodule.span ℂ (Set.range ρ))

/-- The vectorized orbit span is invariant under the amplified representation. -/
lemma matrixRepOrbitSpan_invariant {G : Type*} [Group G] {d : ℕ} (ρ : G →* Op d)
    (g : G) (v : Fin d × Fin d → ℂ) (hv : v ∈ matrixRepOrbitSpan ρ) :
    (amplifiedMatrixRep ρ g).mulVec v ∈ matrixRepOrbitSpan ρ := by
  obtain ⟨A, hA, rfl⟩ := hv
  change (ampl d (ρ g)).mulVec (amplVec d A) ∈ _
  rw [ampl_mulVec_amplVec]
  refine ⟨ρ g * A, ?_, rfl⟩
  induction hA using Submodule.span_induction with
  | mem A hA =>
      obtain ⟨h, rfl⟩ := hA
      exact Submodule.subset_span ⟨g * h, map_mul ρ g h⟩
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [mul_add]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hA

/-- Averaging a projection onto an invariant subspace still maps into that subspace. -/
lemma finiteGroupMatrixAverage_range {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : G →* Op d) (v : Fin d × Fin d → ℂ) :
    (finiteGroupMatrixAverage (amplifiedMatrixRep ρ)
      (projMat d (matrixRepOrbitSpan ρ))).mulVec v ∈ matrixRepOrbitSpan ρ := by
  rw [finiteGroupMatrixAverage, Matrix.smul_mulVec, Matrix.sum_mulVec]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => ?_)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact matrixRepOrbitSpan_invariant ρ g _ (projMat_apply_mem _ _ _)

/-- Averaging a projection onto an invariant subspace fixes that subspace pointwise. -/
lemma finiteGroupMatrixAverage_fix {G : Type*} [Group G] [Fintype G] {d : ℕ}
    (ρ : G →* Op d) (v : Fin d × Fin d → ℂ) (hv : v ∈ matrixRepOrbitSpan ρ) :
    (finiteGroupMatrixAverage (amplifiedMatrixRep ρ)
      (projMat d (matrixRepOrbitSpan ρ))).mulVec v = v := by
  have hterm (g : G) :
      (amplifiedMatrixRep ρ g * projMat d (matrixRepOrbitSpan ρ) *
        amplifiedMatrixRep ρ g⁻¹).mulVec v = v := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      projMat_apply_eq_self _ _ _ (matrixRepOrbitSpan_invariant ρ g⁻¹ v hv),
      Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  rw [finiteGroupMatrixAverage, Matrix.smul_mulVec, Matrix.sum_mulVec]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [hterm, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Commutation with a matrix bicommutant passes to amplification, block by block. -/
lemma amplified_commute_of_bicommutant {d : ℕ} (S : Set (Op d)) (T : Op d)
    (hT : T ∈ commutant d (commutant d S))
    (Y : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hY : ∀ A ∈ S, Commute (ampl d A) Y) : Commute (ampl d T) Y := by
  have hblock (k l : Fin d) : blockOf d Y k l ∈ commutant d S := by
    intro A hA
    ext i j
    have h := congrFun (congrFun (hY A hA).eq (i, k)) (j, l)
    rwa [ampl_mul_apply_eq_mul_blockOf, mul_ampl_apply_eq_blockOf_mul] at h
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [ampl_mul_apply_eq_mul_blockOf, mul_ampl_apply_eq_blockOf_mul,
    hT _ (hblock k l)]

/-- A finite-group matrix representation spans its double commutant. -/
theorem finiteGroup_bicommutant {G : Type*} [Group G] [Finite G] {d : ℕ}
    (ρ : G →* Op d) :
    commutant d (commutant d (Set.range ρ)) = Submodule.span ℂ (Set.range ρ) := by
  let := Fintype.ofFinite G
  apply le_antisymm
  · intro T hT
    let P := finiteGroupMatrixAverage (amplifiedMatrixRep ρ)
      (projMat d (matrixRepOrbitSpan ρ))
    have hcomm : Commute (ampl d T) P :=
      amplified_commute_of_bicommutant _ T hT P (by
        rintro A ⟨g, rfl⟩
        exact finiteGroupMatrixAverage_commute (amplifiedMatrixRep ρ) _ g)
    have hone : amplVec d (1 : Op d) ∈ matrixRepOrbitSpan ρ := by
      refine ⟨1, Submodule.subset_span ?_, rfl⟩
      exact ⟨1, map_one ρ⟩
    have hfix : P.mulVec (amplVec d (1 : Op d)) = amplVec d (1 : Op d) :=
      finiteGroupMatrixAverage_fix ρ _ hone
    have hPT : P.mulVec (amplVec d T) = amplVec d T := by
      calc
        P.mulVec (amplVec d T) = P.mulVec ((ampl d T).mulVec (amplVec d (1 : Op d))) := by
          rw [ampl_mulVec_amplVec, mul_one]
        _ = (ampl d T).mulVec (P.mulVec (amplVec d (1 : Op d))) := by
          rw [Matrix.mulVec_mulVec, ← hcomm.eq, ← Matrix.mulVec_mulVec]
        _ = amplVec d T := by rw [hfix, ampl_mulVec_amplVec, mul_one]
    have hmem : amplVec d T ∈ matrixRepOrbitSpan ρ :=
      hPT ▸ finiteGroupMatrixAverage_range ρ (amplVec d T)
    obtain ⟨A, hA, heq⟩ := hmem
    exact (amplVec_injective d heq) ▸ hA
  · rw [Submodule.span_le]
    rintro A ⟨g, rfl⟩ M hM
    exact (hM _ ⟨g, rfl⟩).symm

end Quantum.Symmetry
