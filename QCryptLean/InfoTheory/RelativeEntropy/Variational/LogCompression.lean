import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.Basic.Basic
import QCryptLean.InfoTheory.RelativeEntropy.Variational.HermitianDiagonalExp
import QCryptLean.InfoTheory.RelativeEntropy.Variational.PrincipalBlock
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.IsometricInvariance
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.SupportCompression
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Log Compression — support-compressed logarithmic perturbations

This file records basic positivity and range-projection facts for support
compressions of diagonal exponentials, together with the corresponding
`exp_log` identity on the compressed space.

## Main statements
- `compression_exp_diagonal_isStrictlyPositive`: compressing an ambient diagonal
  exponential along an isometry yields a strictly positive matrix
- `exp_log_compression_exp_diagonal`: `exp (log A) = A` for the compressed
  diagonal exponential
- `compression_diagonal_le_log_compression_exp_diagonal`: Jensen-style
  comparison between the compressed diagonal term and the logarithm of the
  compressed exponential
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open InfoTheory.VonNeumannEntropy

noncomputable local instance instCStarAlgebraMatrix (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) := {}

/-- A diagonal matrix with real entries is Hermitian. -/
lemma diagonal_isHermitian_of_real {n : Type*} [Finite n] [DecidableEq n]
    (h : n → ℝ) :
    (Matrix.diagonal (fun j => (h j : ℂ))).IsHermitian := by
  letI := Fintype.ofFinite n
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  ext j
  exact Complex.conj_ofReal _

/-- Compressing the ambient diagonal exponential along an isometry produces a
strictly positive matrix on the compressed space. -/
lemma compression_exp_diagonal_isStrictlyPositive {N n : ℕ}
    (S : Matrix (Fin N) (Fin n) ℂ) (hS : S.conjTranspose * S = 1)
    (h : Fin N → ℝ) :
    IsStrictlyPositive
      (S.conjTranspose *
        NormedSpace.exp (Matrix.diagonal (fun j => (h j : ℂ))) *
        S) := by
  let D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun j => (h j : ℂ))
  have hD : D.IsHermitian := by
    simpa [D] using diagonal_isHermitian_of_real h
  have hExpPSD : (NormedSpace.exp D).PosSemidef :=
    exp_hermitian_posSemidef D hD
  have hExpPD : (NormedSpace.exp D).PosDef :=
    hExpPSD.posDef_iff_isUnit.mpr (Matrix.isUnit_exp D)
  have hS_inj : Function.Injective S.mulVec := by
    exact mulVec_injective_of_conjTranspose_mul_eq_one S hS
  exact (hExpPD.conjTranspose_mul_mul_same (B := S) hS_inj).isStrictlyPositive

/-- Exponentiating the logarithm of a compressed ambient diagonal exponential
recovers that compressed positive matrix exactly. -/
lemma exp_log_compression_exp_diagonal {N n : ℕ}
    (S : Matrix (Fin N) (Fin n) ℂ) (hS : S.conjTranspose * S = 1)
    (h : Fin N → ℝ) :
    NormedSpace.exp
        (CFC.log
          (S.conjTranspose *
            NormedSpace.exp (Matrix.diagonal (fun j => (h j : ℂ))) *
            S)) =
      (S.conjTranspose *
        NormedSpace.exp (Matrix.diagonal (fun j => (h j : ℂ))) *
        S) := by
  let A : Matrix (Fin n) (Fin n) ℂ :=
    S.conjTranspose *
      NormedSpace.exp (Matrix.diagonal (fun j => (h j : ℂ))) *
      S
  simpa [A] using
    (CFC.exp_log (a := A) (compression_exp_diagonal_isStrictlyPositive S hS h))

/-- The range projection of an isometry is a star projection. -/
lemma compression_range_isStarProjection {N n : ℕ}
    (S : Matrix (Fin N) (Fin n) ℂ) (hS : S.conjTranspose * S = 1) :
    IsStarProjection (S * S.conjTranspose) := by
  rw [isStarProjection_iff']
  constructor
  · calc
      (S * S.conjTranspose) * (S * S.conjTranspose)
          = S * (S.conjTranspose * S) * S.conjTranspose := by
              simp [Matrix.mul_assoc]
      _ = S * (1 : Matrix (Fin n) (Fin n) ℂ) * S.conjTranspose := by rw [hS]
      _ = S * S.conjTranspose := by simp
  · change (S * S.conjTranspose).conjTranspose = S * S.conjTranspose
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- The range projection of an isometry is bounded by the identity. -/
lemma compression_range_le_one {N n : ℕ}
    (S : Matrix (Fin N) (Fin n) ℂ) (hS : S.conjTranspose * S = 1) :
    S * S.conjTranspose ≤ (1 : Matrix (Fin N) (Fin N) ℂ) :=
  (compression_range_isStarProjection S hS).le_one

/-- Compressing a real diagonal matrix along an isometry remains Hermitian. -/
lemma compression_diagonal_isHermitian {N n : ℕ}
    (S : Matrix (Fin N) (Fin n) ℂ)
    (h : Fin N → ℝ) :
    (S.conjTranspose * Matrix.diagonal (fun j => (h j : ℂ)) * S).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul S (diagonal_isHermitian_of_real h)

/-- The exponential of the compressed real diagonal is strictly positive. -/
lemma exp_compression_diagonal_isStrictlyPositive {N n : ℕ}
    (S : Matrix (Fin N) (Fin n) ℂ)
    (h : Fin N → ℝ) :
    IsStrictlyPositive
      (NormedSpace.exp
        (S.conjTranspose * Matrix.diagonal (fun j => (h j : ℂ)) * S)) := by
  let A : Matrix (Fin n) (Fin n) ℂ :=
    S.conjTranspose * Matrix.diagonal (fun j => (h j : ℂ)) * S
  have hA : IsSelfAdjoint A := (compression_diagonal_isHermitian S h).isSelfAdjoint
  refine ⟨hA.exp_nonneg, Matrix.isUnit_exp A⟩

/-- Complete an isometry to a unitary and express every compression
`Aᴴ * M * A` as the `toBlocks₁₁` block of a reindexed unitary conjugate. -/
lemma exists_unitary_toBlocks₁₁_compression {n N : ℕ}
    (A : Matrix (Fin N) (Fin n) ℂ) (hA : A.conjTranspose * A = 1)
    (hn : n ≤ N) :
    ∃ U : Matrix (Fin N) (Fin N) ℂ,
      U.conjTranspose * U = 1 ∧
      U * U.conjTranspose = 1 ∧
      ∀ M : Matrix (Fin N) (Fin N) ℂ,
        let e : Fin n ⊕ Fin (N - n) ≃ Fin N :=
          finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hn))
        (Matrix.reindex e.symm e.symm (U.conjTranspose * M * U)).toBlocks₁₁ =
          A.conjTranspose * M * A := by
  obtain ⟨U, hUU, hUU', hU_cols⟩ := exists_unitary_extension_of_isometry A hA hn
  refine ⟨U, hUU, hUU', ?_⟩
  intro M
  ext i j
  let e : Fin n ⊕ Fin (N - n) ≃ Fin N :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hn))
  change (U.conjTranspose * M * U) (e (Sum.inl i)) (e (Sum.inl j)) =
    (A.conjTranspose * M * A) i j
  simp only [e]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : U k (e (Sum.inl j)) = A k j := by
    exact hU_cols j k
  rw [hkj]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hxi : U x (e (Sum.inl i)) = A x i := by
    exact hU_cols i x
  rw [hxi]

/-- Principal-block form of the exponential compression inequality. -/
lemma exp_reindex {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (M : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e M) =
      Matrix.reindex e e (NormedSpace.exp M) := by
  simpa [Matrix.coe_reindexAlgEquiv] using
    (NormedSpace.map_exp_of_mem_ball
      (𝕂 := ℂ)
      (f := (Matrix.reindexAlgEquiv ℂ ℂ e : Matrix m m ℂ →+* Matrix n n ℂ))
      ((Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap.continuous_of_finiteDimensional)
      M
      ((NormedSpace.expSeries_radius_eq_top ℂ (Matrix m m ℂ)).symm ▸ edist_lt_top _ _)).symm

/-- Matrix exponential commutes with conjugation by a unitary matrix. -/
lemma exp_unitary_conj {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hUU : U.conjTranspose * U = 1)
    (hUU' : U * U.conjTranspose = 1) (M : Matrix (Fin N) (Fin N) ℂ) :
    NormedSpace.exp (U.conjTranspose * M * U) =
      U.conjTranspose * NormedSpace.exp M * U := by
  let U_units : (Matrix (Fin N) (Fin N) ℂ)ˣ := {
    val := U
    inv := U.conjTranspose
    val_inv := hUU'
    inv_val := hUU
  }
  simpa [U_units] using Matrix.exp_units_conj' U_units M

/-- Jensen-style compression inequality for the operator logarithm on the
compressed ambient diagonal exponential.

It compares the compressed diagonal matrix with the logarithm of the
corresponding compressed diagonal exponential. -/
lemma compression_diagonal_le_log_compression_exp_diagonal {N n : ℕ}
    (S : Matrix (Fin N) (Fin n) ℂ) (hS : S.conjTranspose * S = 1)
    (h : Fin N → ℝ) :
    (S.conjTranspose *
        Matrix.diagonal (fun j => (h j : ℂ)) *
        S) ≤
      CFC.log
        (S.conjTranspose *
          NormedSpace.exp (Matrix.diagonal (fun j => (h j : ℂ))) *
          S) := by
  let D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun j => (h j : ℂ))
  have hD : D.IsHermitian := by
    simpa [D] using diagonal_isHermitian_of_real h
  let hn : n ≤ N := n_le_N_of_isometry S hS
  obtain ⟨U, hUU, hUU', hblock⟩ := exists_unitary_toBlocks₁₁_compression S hS hn
  let e : Fin n ⊕ Fin (N - n) ≃ Fin N :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hn))
  let M : Matrix (Fin n ⊕ Fin (N - n)) (Fin n ⊕ Fin (N - n)) ℂ :=
    Matrix.reindex e.symm e.symm (U.conjTranspose * D * U)
  have hM₁₁ : M.toBlocks₁₁ = S.conjTranspose * D * S := by
    exact hblock D
  have hUDU : (U.conjTranspose * D * U).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul U hD
  have hM : M.IsHermitian := by
    rw [Matrix.IsHermitian]
    simpa [M] using congrArg (Matrix.reindex e.symm e.symm) hUDU.eq
  have hMapExp :
      NormedSpace.exp M =
        Matrix.reindex e.symm e.symm (NormedSpace.exp (U.conjTranspose * D * U)) := by
    simpa [M] using exp_reindex e.symm (U.conjTranspose * D * U)
  have hExpConj :
      NormedSpace.exp (U.conjTranspose * D * U) =
        U.conjTranspose * NormedSpace.exp D * U :=
    exp_unitary_conj U hUU hUU' D
  have hExpM₁₁ :
      (NormedSpace.exp M).toBlocks₁₁ =
        S.conjTranspose * NormedSpace.exp D * S := by
    calc
      (NormedSpace.exp M).toBlocks₁₁
          = (Matrix.reindex e.symm e.symm
              (NormedSpace.exp (U.conjTranspose * D * U))).toBlocks₁₁ := by
              rw [hMapExp]
      _ = (Matrix.reindex e.symm e.symm
            (U.conjTranspose * NormedSpace.exp D * U)).toBlocks₁₁ := by
              rw [hExpConj]
      _ = S.conjTranspose * NormedSpace.exp D * S := by
            exact hblock (NormedSpace.exp D)
  have hExpM_nonneg : 0 ≤ NormedSpace.exp M := hM.isSelfAdjoint.exp_nonneg
  have hExpM_psd : (NormedSpace.exp M).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hExpM_nonneg
  have hExpM_pd : (NormedSpace.exp M).PosDef := by
    exact hExpM_psd.posDef_iff_isUnit.mpr (Matrix.isUnit_exp M)
  have hBlockLog :
      (CFC.log (NormedSpace.exp M)).toBlocks₁₁ ≤ CFC.log ((NormedSpace.exp M).toBlocks₁₁) :=
    toBlocks₁₁_log_le_log_toBlocks₁₁ hExpM_pd
  calc
    S.conjTranspose * D * S = M.toBlocks₁₁ := by
      rw [← hM₁₁]
    _ = (CFC.log (NormedSpace.exp M)).toBlocks₁₁ := by
      exact (congrArg Matrix.toBlocks₁₁ (CFC.log_exp M hM.isSelfAdjoint)).symm
    _ ≤ CFC.log ((NormedSpace.exp M).toBlocks₁₁) := hBlockLog
    _ = CFC.log (S.conjTranspose * NormedSpace.exp D * S) := by
      rw [hExpM₁₁]
    _ = CFC.log
        (S.conjTranspose *
          NormedSpace.exp (Matrix.diagonal (fun j => (h j : ℂ))) *
          S) := by
      rfl

end InfoTheory.RelativeEntropy

end
