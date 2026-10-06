import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.InfoTheory.BellDiagonal.Basic
import QCryptLean.Quantum.Operators.BraKet.Projector

/-!
# Bell Dephasing Entropy Bounds — density operator realization, Bell-diagonal entropy, pinching

Entropy-oriented consequences of Bell dephasing. This file packages the Bell
dephasing map as a density operator and identifies its eigenvalues and von Neumann
entropy with the Bell fidelities.

## Main definitions
- `bellDephasingDensity`: Bell dephasing as a `DensityOp 4`

## Main statements
- `bellDephasing_eigenvalues`: the Bell-dephased state has Bell fidelities as eigenvalues
- `bellDephasing_entropy`: Bell-dephasing entropy is the Shannon entropy of Bell fidelities
-/

open Quantum.Operators Quantum.TensorProducts
open scoped ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

open Quantum.Basis.BellStates Math.CodingTheory.CSS InfoTheory.Measurement
open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy Quantum.Metrics InfoTheory.RelativeEntropy
open QKD.BB84.Model

/-!
## Bell Basis Dephasing

The dephasing (pinching) map in the Bell basis removes off-diagonal coherences
while preserving the diagonal elements (Bell fidelities).
-/

/-- The Bell dephasing map produces a Hermitian operator. -/
theorem bellDephasing_isHermitian (ρ : DensityOp 4) :
    (bellDephasing ρ).IsHermitian := by
  unfold bellDephasing
  simp only [Matrix.IsHermitian]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_add]
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
  rw [ketbra_hermitian bellState00, ketbra_hermitian bellState01,
      ketbra_hermitian bellState10, ketbra_hermitian bellState11]
  simp only [star_trivial]

/-- The Bell dephasing map produces a positive semidefinite operator. -/
theorem bellDephasing_posSemidef (ρ : DensityOp 4) :
    (bellDephasing ρ).PosSemidef := by
  unfold bellDephasing
  have : NeZero 4 := ⟨by norm_num⟩
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.add
    · apply Matrix.PosSemidef.add
      · exact Matrix.PosSemidef.smul (ketbra_posSemidef bellState00)
            (RCLike.ofReal_nonneg.mpr (fidelityPureSq_nonneg ρ bellState00 bellState00_normalized))
      · exact Matrix.PosSemidef.smul (ketbra_posSemidef bellState01)
            (RCLike.ofReal_nonneg.mpr (fidelityPureSq_nonneg ρ bellState01 bellState01_normalized))
    · exact Matrix.PosSemidef.smul (ketbra_posSemidef bellState10)
          (RCLike.ofReal_nonneg.mpr (fidelityPureSq_nonneg ρ bellState10 bellState10_normalized))
  · exact Matrix.PosSemidef.smul (ketbra_posSemidef bellState11)
        (RCLike.ofReal_nonneg.mpr (fidelityPureSq_nonneg ρ bellState11 bellState11_normalized))

/-- The Bell dephasing map preserves trace (trace = 1). -/
theorem bellDephasing_trace_one (ρ : DensityOp 4) :
    (bellDephasing ρ).trace = 1 := by
  unfold bellDephasing
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
  rw [Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul]
  rw [trace_ketbra_normalized bellState00 bellState00_normalized]
  rw [trace_ketbra_normalized bellState01 bellState01_normalized]
  rw [trace_ketbra_normalized bellState10 bellState10_normalized]
  rw [trace_ketbra_normalized bellState11 bellState11_normalized]
  set f00 := DensityOp.fidelitySq ρ (DensityOp.fromPure bellState00 bellState00_normalized)
  set f01 := DensityOp.fidelitySq ρ (DensityOp.fromPure bellState01 bellState01_normalized)
  set f10 := DensityOp.fidelitySq ρ (DensityOp.fromPure bellState10 bellState10_normalized)
  set f11 := DensityOp.fidelitySq ρ (DensityOp.fromPure bellState11 bellState11_normalized)
  have h1 : f00 • (1 : ℂ) = (f00 : ℂ) := by simp
  have h2 : f01 • (1 : ℂ) = (f01 : ℂ) := by simp
  have h3 : f10 • (1 : ℂ) = (f10 : ℂ) := by simp
  have h4 : f11 • (1 : ℂ) = (f11 : ℂ) := by simp
  rw [h1, h2, h3, h4]
  have h := bell_fidelity_sum_eq_one ρ
  have hcast : (f00 + f01 + f10 + f11 : ℂ) = ((f00 + f01 + f10 + f11) : ℝ) := by push_cast; ring
  rw [hcast, h]
  norm_cast

/-- The Bell dephasing map has non-negative quadratic form (pos_semidef field form). -/
theorem bellDephasing_quadraticForm_re_nonneg (ρ : DensityOp 4) :
    ∀ x : Fin 4 → ℂ, 0 ≤ (quadraticForm (bellDephasing ρ) x).re := by
  intro x
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (bellDephasing_posSemidef ρ)).2 x
  unfold quadraticForm
  rw [RCLike.nonneg_iff] at h
  exact h.1

/-- Bell dephasing as an explicit density operator record. -/
def bellDephasingDensity (ρ : DensityOp 4) : DensityOp 4 :=
  ⟨⟨⟨bellDephasing ρ, bellDephasing_isHermitian ρ⟩, bellDephasing_quadraticForm_re_nonneg ρ⟩,
   bellDephasing_trace_one ρ⟩

/-- The `toOp` coercion of `bellDephasingDensity` is the original Bell dephasing operator. -/
@[simp]
theorem bellDephasingDensity_toOp (ρ : DensityOp 4) :
    (bellDephasingDensity ρ).toOp = bellDephasing ρ := rfl

/-!
## Bell-Diagonal Entropy

For a Bell-diagonal state, the eigenvalues are exactly the Bell fidelities,
so the von Neumann entropy equals the Shannon entropy of those fidelities.
-/

/-- Each Bell fidelity of a density operator is at most `1`. -/
lemma bell_fidelity_le_one (ρ : DensityOp 4) (i : Fin 4) :
    (![DensityOp.fidelitySq ρ (DensityOp.fromPure bellState00 bellState00_normalized),
       DensityOp.fidelitySq ρ (DensityOp.fromPure bellState01 bellState01_normalized),
       DensityOp.fidelitySq ρ (DensityOp.fromPure bellState10 bellState10_normalized),
       DensityOp.fidelitySq ρ (DensityOp.fromPure bellState11 bellState11_normalized)] i) ≤ 1 := by
  fin_cases i
  · exact fidelitySq_le_one ρ (DensityOp.fromPure bellState00 bellState00_normalized)
  · exact fidelitySq_le_one ρ (DensityOp.fromPure bellState01 bellState01_normalized)
  · exact fidelitySq_le_one ρ (DensityOp.fromPure bellState10 bellState10_normalized)
  · exact fidelitySq_le_one ρ (DensityOp.fromPure bellState11 bellState11_normalized)

/-- Bell dephasing has Bell fidelities as its eigenvalue spectrum. -/
theorem bellDephasing_eigenvalues (ρ : DensityOp 4) :
    InfoTheory.VonNeumannEntropy.IsEigenvalueSpectrum (bellDephasingDensity ρ)
      ![DensityOp.fidelitySq ρ (DensityOp.fromPure bellState00 bellState00_normalized),
        DensityOp.fidelitySq ρ (DensityOp.fromPure bellState01 bellState01_normalized),
        DensityOp.fidelitySq ρ (DensityOp.fromPure bellState10 bellState10_normalized),
        DensityOp.fidelitySq ρ (DensityOp.fromPure bellState11 bellState11_normalized)] := by
  have : NeZero 4 := ⟨by norm_num⟩
  constructor
  · intro i; fin_cases i
    · exact fidelityPureSq_nonneg ρ bellState00 bellState00_normalized
    · exact fidelityPureSq_nonneg ρ bellState01 bellState01_normalized
    · exact fidelityPureSq_nonneg ρ bellState10 bellState10_normalized
    · exact fidelityPureSq_nonneg ρ bellState11 bellState11_normalized
  constructor
  · simp only [Fin.sum_univ_four]
    exact bell_fidelity_sum_eq_one ρ
  constructor
  · exact bell_fidelity_le_one ρ
  let states : Fin 4 → Ket 4 := ![bellState00, bellState01, bellState10, bellState11]
  let U : Op 4 := Matrix.of fun i j => (states i).vec j
  use U
  have hUUdag_entry : ∀ i j, (U * U†) i j = (states j).dag * (states i) := fun i j => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp only [Ket.dag]
    congr 1; ext k
    change
      (Matrix.of fun a b => (states a).vec b) i k *
          star ((Matrix.of fun a b => (states a).vec b) j k) =
        (starRingEnd ℂ) ((states j).vec k) * (states i).vec k
    simp only [Matrix.of_apply, starRingEnd_apply]
    ring
  constructor
  · have hUUdag : U * U† = 1 := by
      ext i j
      rw [hUUdag_entry, bellStates_orthonormal, Matrix.one_apply]
      simp only [eq_comm]
    exact (mul_eq_one_comm.mp hUUdag)
  constructor
  · ext i j
    rw [hUUdag_entry, bellStates_orthonormal, Matrix.one_apply]
    simp only [eq_comm]
  · let p : Fin 4 → ℝ :=
      ![DensityOp.fidelitySq ρ (DensityOp.fromPure bellState00 bellState00_normalized),
        DensityOp.fidelitySq ρ (DensityOp.fromPure bellState01 bellState01_normalized),
        DensityOp.fidelitySq ρ (DensityOp.fromPure bellState10 bellState10_normalized),
        DensityOp.fidelitySq ρ (DensityOp.fromPure bellState11 bellState11_normalized)]
    rw [bellDephasingDensity_toOp, bellDephasing]
    simpa [p, states, U, QKD.BB84.Engine.BellDephasing.bellStatesVec, Fin.sum_univ_four] using
      (QKD.BB84.Engine.BellDephasing.bell_basis_conj_diagonal p).symm

/-- Bell-dephasing entropy is the Shannon entropy of the Bell fidelities. -/
theorem bellDephasing_entropy (ρ : DensityOp 4) :
    vonNeumannEntropy (bellDephasingDensity ρ) =
      Math.ClassicalEntropy.shannonEntropy
        ![DensityOp.fidelitySq ρ (DensityOp.fromPure bellState00 bellState00_normalized),
          DensityOp.fidelitySq ρ (DensityOp.fromPure bellState01 bellState01_normalized),
          DensityOp.fidelitySq ρ (DensityOp.fromPure bellState10 bellState10_normalized),
          DensityOp.fidelitySq ρ (DensityOp.fromPure bellState11 bellState11_normalized)] := by
  have : NeZero 4 := ⟨by norm_num⟩
  exact InfoTheory.VonNeumannEntropy.vonNeumannEntropy_eq_shannonEntropy
    (bellDephasingDensity ρ) _ (bellDephasing_eigenvalues ρ)

/-!
## Main Entropy-Error Bound
-/

end QKD.BB84.Engine

end
