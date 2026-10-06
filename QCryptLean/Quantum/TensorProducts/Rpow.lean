import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CfcSpectral
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Real powers of operator tensor products (`(A ⊗ B)^t = A^t ⊗ B^t`)

The continuous-functional-calculus real power (`CFC.rpow`, written `· ^ (· : ℝ)`)
of a tensor product of positive-semidefinite operators factorizes copy-by-copy:

  `Op.tensor_rpow : (A ⊗ B) ^ y = (A ^ y) ⊗ (B ^ y)`  (`0 ≤ A`, `0 ≤ B`).

This is the operator/Kronecker form of "the functional calculus commutes with the
tensor product", because `spectrum (A ⊗ B) = spectrum A · spectrum B`. It is the
load-bearing fact behind the per-copy factorization of Renner's tilted collision
trace `tr[R^{1+s} τ^{-s}]` (see
`InfoTheory/SmoothMinEntropy/Renner/IIDAEPCollisionMGF.lean`).

## Strategy

`A ⊗ B = (A ⊗ 1) · (1 ⊗ B)` with the two factors *commuting* and PSD. The maps
`A ↦ A ⊗ 1` (`Op.tensorRightOneHom`) and `B ↦ 1 ⊗ B` (`Op.tensorLeftOneHom`) are
*continuous unital star-algebra homomorphisms* between the matrix C⋆-algebras, so
the continuous functional calculus commutes with them
(`StarAlgHomClass.map_cfc`): `(A ⊗ 1) ^ y = A ^ y ⊗ 1` and `(1 ⊗ B) ^ y =
1 ⊗ B ^ y` (`Op.tensorRightOne_rpow`, `Op.tensorLeftOne_rpow`, both proven). The
remaining ingredient is the multiplicativity of the real power across the two
*commuting* PSD factors, `Op.rpow_mul_of_commute`, supplied by the matrix
simultaneous-diagonalization core `CfcSpectral.matrix_rpow_mul_of_commute`.

## Main statements

- `Op.tensorRightOne_rpow`, `Op.tensorLeftOne_rpow`: the single-sided embedding
  identities (proven via `map_cfc`).
- `Op.rpow_mul_of_commute`: `(c·d) ^ y = c ^ y · d ^ y` for commuting PSD `c, d`
  (proven via `CfcSpectral.matrix_rpow_mul_of_commute`).
- `Op.tensor_rpow`: the binary tensor-power rpow factorization.
-/

open scoped ComplexOrder MatrixOrder
open Matrix Quantum.Operators

noncomputable section

namespace Quantum.TensorProducts

variable {p q : ℕ}

/-! ## Single-sided embeddings `A ↦ A ⊗ 1` and `B ↦ 1 ⊗ B` -/

/-- The embedding `A ↦ A ⊗ 1` of `Op p` into `Op (p * q)` as a unital
star-algebra homomorphism. Multiplicativity, unitality and star-preservation are
the structural tensor lemmas `Op.tensor_mul`, `Op.tensor_one`,
`Op.tensor_conjTranspose`. -/
def Op.tensorRightOneHom (p q : ℕ) : Op p →⋆ₐ[ℂ] Op (p * q) where
  toFun A := Op.tensor A (1 : Op q)
  map_one' := Op.tensor_one
  map_mul' A A' := by rw [Op.tensor_mul, mul_one]
  map_zero' := by
    rw [show (0 : Op p) = (0 : ℂ) • (0 : Op p) from (zero_smul _ _).symm,
      Op.tensor_smul_left, zero_smul]
  map_add' A A' := Op.tensor_add_left A A' 1
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Op.tensor_smul_left, Op.tensor_one]
  map_star' A := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose, Op.tensor_conjTranspose,
      conjTranspose_one]

@[simp] lemma Op.tensorRightOneHom_apply (A : Op p) :
    Op.tensorRightOneHom p q A = Op.tensor A (1 : Op q) := rfl

/-- `A ↦ A ⊗ 1` is continuous (it is `ℂ`-linear on a finite-dimensional space). -/
lemma Op.tensorRightOneHom_continuous : Continuous (Op.tensorRightOneHom p q) :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun A => Op.tensorRightOneHom p q A
       map_add' := map_add _
       map_smul' := fun (r : ℂ) A => by
         simp only [Op.tensorRightOneHom_apply, RingHom.id_apply]
         rw [Op.tensor_smul_left] } : Op p →ₗ[ℂ] _)

/-- **Right-embedding rpow identity:** `(A ⊗ 1) ^ y = (A ^ y) ⊗ 1` for PSD `A`.
The continuous functional calculus commutes with the star-algebra homomorphism
`A ↦ A ⊗ 1` (`StarAlgHomClass.map_cfc`); continuity of `· ^ y` on the spectrum is
automatic because the spectrum of a matrix is finite. -/
lemma Op.tensorRightOne_rpow (A : Op p) (hA : 0 ≤ A) (y : ℝ) :
    (Op.tensor A (1 : Op q)) ^ y = Op.tensor (A ^ y) (1 : Op q) := by
  have hAk : (0 : Op (p * q)) ≤ Op.tensor A (1 : Op q) := by
    rw [Matrix.nonneg_iff_posSemidef] at hA ⊢
    exact Op.tensor_posSemidef_mathlib hA Matrix.PosSemidef.one
  have hAsa : IsSelfAdjoint A := (Matrix.nonneg_iff_posSemidef.mp hA).isHermitian
  have hAksa : IsSelfAdjoint (Op.tensor A (1 : Op q)) :=
    (Matrix.nonneg_iff_posSemidef.mp hAk).isHermitian
  have key : Op.tensorRightOneHom p q (A ^ y) = (Op.tensorRightOneHom p q A) ^ y := by
    rw [show Op.tensorRightOneHom p q A = Op.tensor A (1 : Op q) from rfl,
      CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real hAk]
    exact StarAlgHomClass.map_cfc (Op.tensorRightOneHom p q) (fun x : ℝ => x ^ y) A
      ((A.finite_real_spectrum).continuousOn _) Op.tensorRightOneHom_continuous hAsa hAksa
  simpa using key.symm

/-- **Right-embedding square-root identity:** `√(A ⊗ 1) = (√A) ⊗ 1` for PSD `A` —
the `y = 1/2` special case of `Op.tensorRightOne_rpow`. -/
lemma Op.tensorRightOne_sqrt {p q : ℕ} (A : Op p) (hA : A.PosSemidef) :
    CFC.sqrt (Op.tensor A (1 : Op q)) = Op.tensor (CFC.sqrt A) (1 : Op q) := by
  rw [CFC.sqrt_eq_rpow, Op.tensorRightOne_rpow A (Matrix.nonneg_iff_posSemidef.mpr hA),
    ← CFC.sqrt_eq_rpow]

/-- The embedding `B ↦ 1 ⊗ B` of `Op q` into `Op (p * q)` as a unital
star-algebra homomorphism. -/
def Op.tensorLeftOneHom (p q : ℕ) : Op q →⋆ₐ[ℂ] Op (p * q) where
  toFun B := Op.tensor (1 : Op p) B
  map_one' := Op.tensor_one
  map_mul' B B' := by rw [Op.tensor_mul, mul_one]
  map_zero' := by
    rw [show (0 : Op q) = (0 : ℂ) • (0 : Op q) from (zero_smul _ _).symm,
      Op.tensor_smul_right, zero_smul]
  map_add' B B' := Op.tensor_add_right 1 B B'
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Op.tensor_smul_right, Op.tensor_one]
  map_star' B := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose, Op.tensor_conjTranspose,
      conjTranspose_one]

@[simp] lemma Op.tensorLeftOneHom_apply (B : Op q) :
    Op.tensorLeftOneHom p q B = Op.tensor (1 : Op p) B := rfl

/-- `B ↦ 1 ⊗ B` is continuous. -/
lemma Op.tensorLeftOneHom_continuous : Continuous (Op.tensorLeftOneHom p q) :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun B => Op.tensorLeftOneHom p q B
       map_add' := map_add _
       map_smul' := fun (r : ℂ) B => by
         simp only [Op.tensorLeftOneHom_apply, RingHom.id_apply]
         rw [Op.tensor_smul_right] } : Op q →ₗ[ℂ] _)

/-- **Left-embedding rpow identity:** `(1 ⊗ B) ^ y = 1 ⊗ (B ^ y)` for PSD `B`. -/
lemma Op.tensorLeftOne_rpow (B : Op q) (hB : 0 ≤ B) (y : ℝ) :
    (Op.tensor (1 : Op p) B) ^ y = Op.tensor (1 : Op p) (B ^ y) := by
  have hBk : (0 : Op (p * q)) ≤ Op.tensor (1 : Op p) B := by
    rw [Matrix.nonneg_iff_posSemidef] at hB ⊢
    exact Op.tensor_posSemidef_mathlib Matrix.PosSemidef.one hB
  have hBsa : IsSelfAdjoint B := (Matrix.nonneg_iff_posSemidef.mp hB).isHermitian
  have hBksa : IsSelfAdjoint (Op.tensor (1 : Op p) B) :=
    (Matrix.nonneg_iff_posSemidef.mp hBk).isHermitian
  have key : Op.tensorLeftOneHom p q (B ^ y) = (Op.tensorLeftOneHom p q B) ^ y := by
    rw [show Op.tensorLeftOneHom p q B = Op.tensor (1 : Op p) B from rfl,
      CFC.rpow_eq_cfc_real hB, CFC.rpow_eq_cfc_real hBk]
    exact StarAlgHomClass.map_cfc (Op.tensorLeftOneHom p q) (fun x : ℝ => x ^ y) B
      ((B.finite_real_spectrum).continuousOn _) Op.tensorLeftOneHom_continuous hBsa hBksa
  simpa using key.symm

/-! ## Multiplicativity of the real power across commuting PSD factors -/

/-- **Real power is multiplicative across a commuting PSD pair:**
`(c · d) ^ y = c ^ y · d ^ y` whenever `c, d ≥ 0` commute (their product is then
also PSD, `commute_iff_mul_nonneg`).

After `CFC.rpow_eq_cfc_real` this is the continuous-functional-calculus identity
`cfc (·^y) (c·d) = cfc (·^y) c · cfc (·^y) d`: both sides act as
`λᵢμⱼ ↦ (λᵢμⱼ)^y = λᵢ^y μⱼ^y` on the simultaneous eigenbasis of the commuting pair.
Mathlib's `cfc_mul` only handles two functions of the *same* element, so the proof
goes through the explicit matrix simultaneous-diagonalization core
`CfcSpectral.matrix_rpow_mul_of_commute`: it builds the joint indicator spectral
resolution `{Q_l · R_m}` over `spectrum c × spectrum d` (the projectors `Q_l`, `R_m`
commute, being `cfc`-functions of the commuting factors) and evaluates all three
real powers `c^y`, `d^y`, `(c·d)^y` coefficientwise on the shared family. -/
lemma Op.rpow_mul_of_commute {N : ℕ} (c d : Op N) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcd : Commute c d) (y : ℝ) :
    (c * d) ^ y = c ^ y * d ^ y :=
  CfcSpectral.matrix_rpow_mul_of_commute c d hc hd hcd y

/-! ## Binary tensor-power rpow -/

/-- **Binary tensor-power real power:** `(A ⊗ B) ^ y = (A ^ y) ⊗ (B ^ y)` for PSD
`A, B`. Decompose `A ⊗ B = (A ⊗ 1) · (1 ⊗ B)` (commuting PSD factors), apply the
commuting-product multiplicativity `Op.rpow_mul_of_commute`, then the single-sided
embedding identities `Op.tensorRightOne_rpow` / `Op.tensorLeftOne_rpow`, and
recombine with `Op.tensor_mul`. -/
lemma Op.tensor_rpow (A : Op p) (B : Op q) (hA : 0 ≤ A) (hB : 0 ≤ B) (y : ℝ) :
    (Op.tensor A B) ^ y = Op.tensor (A ^ y) (B ^ y) := by
  have hsplit : Op.tensor A B = Op.tensor A (1 : Op q) * Op.tensor (1 : Op p) B := by
    rw [Op.tensor_mul, mul_one, one_mul]
  have hc : (0 : Op (p * q)) ≤ Op.tensor A (1 : Op q) := by
    rw [Matrix.nonneg_iff_posSemidef] at hA ⊢
    exact Op.tensor_posSemidef_mathlib hA Matrix.PosSemidef.one
  have hd : (0 : Op (p * q)) ≤ Op.tensor (1 : Op p) B := by
    rw [Matrix.nonneg_iff_posSemidef] at hB ⊢
    exact Op.tensor_posSemidef_mathlib Matrix.PosSemidef.one hB
  have hcomm : Commute (Op.tensor A (1 : Op q)) (Op.tensor (1 : Op p) B) := by
    unfold Commute SemiconjBy
    rw [Op.tensor_mul, Op.tensor_mul, mul_one, one_mul, mul_one, one_mul]
  rw [hsplit, Op.rpow_mul_of_commute _ _ hc hd hcomm, Op.tensorRightOne_rpow A hA,
    Op.tensorLeftOne_rpow B hB, Op.tensor_mul, mul_one, one_mul]

end Quantum.TensorProducts

end
