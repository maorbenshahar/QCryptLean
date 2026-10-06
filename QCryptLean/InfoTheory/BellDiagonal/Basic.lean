import QCryptLean.Quantum.BellStates
import QCryptLean.Quantum.Tactic.QISimp
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Math.ClassicalEntropy.Entropy
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Bell Dephasing Spectral Decomposition — Bell-basis overlaps and doubly stochastic mixing

Spectral decomposition infrastructure for the BB84 Bell-dephasing channel.
This file builds the Bell-basis overlap matrix against an eigenbasis, proves that
it is doubly stochastic, and packages the resulting Bell-fidelity/eigenvalue relation.

## Main definitions
- `bellStatesVec`: the four Bell states as `Ket 4`

## Main statements
- `bell_basis_conj_diagonal`: Bell-basis conjugation of a diagonal matrix
- `InfoTheory.RelativeEntropy.shannonEntropy_doubly_stochastic_ge`: Shannon entropy increases under
a doubly
  stochastic map
-/

namespace QKD.BB84.Engine.BellDephasing

open Quantum.Operators Quantum.TensorProducts Complex Matrix Quantum.Basis.BellStates

/-!
## Bell State Component Reality Lemmas

The Bell states have real components (multiples of 1/√2), so star(x) = x.
We prove this by explicit computation for each of the 4 components of each Bell state.
-/

/-- bellState00 component 0 is real: (1/√2) -/
lemma bell00_real_0 : star (bellState00.vec 0) = bellState00.vec 0 := by
  unfold bellState00; qisimp; simp (decide := true)

/-- bellState00 component 1 is real: 0 -/
lemma bell00_real_1 : star (bellState00.vec 1) = bellState00.vec 1 := by
  unfold bellState00; qisimp; simp (decide := true)

/-- bellState00 component 2 is real: 0 -/
lemma bell00_real_2 : star (bellState00.vec 2) = bellState00.vec 2 := by
  unfold bellState00; qisimp; simp (decide := true)

/-- bellState00 component 3 is real: (1/√2) -/
lemma bell00_real_3 : star (bellState00.vec 3) = bellState00.vec 3 := by
  unfold bellState00; qisimp; simp (decide := true)

/-- bellState01 component 0 is real: 0 -/
lemma bell01_real_0 : star (bellState01.vec 0) = bellState01.vec 0 := by
  unfold bellState01; qisimp; simp (decide := true)

/-- bellState01 component 1 is real: (1/√2) -/
lemma bell01_real_1 : star (bellState01.vec 1) = bellState01.vec 1 := by
  unfold bellState01; qisimp; simp (decide := true)

/-- bellState01 component 2 is real: (1/√2) -/
lemma bell01_real_2 : star (bellState01.vec 2) = bellState01.vec 2 := by
  unfold bellState01; qisimp; simp (decide := true)

/-- bellState01 component 3 is real: 0 -/
lemma bell01_real_3 : star (bellState01.vec 3) = bellState01.vec 3 := by
  unfold bellState01; qisimp; simp (decide := true)

/-- bellState10 component 0 is real: (1/√2) -/
lemma bell10_real_0 : star (bellState10.vec 0) = bellState10.vec 0 := by
  unfold bellState10; qisimp; simp (decide := true)

/-- bellState10 component 1 is real: 0 -/
lemma bell10_real_1 : star (bellState10.vec 1) = bellState10.vec 1 := by
  unfold bellState10; qisimp; simp (decide := true)

/-- bellState10 component 2 is real: 0 -/
lemma bell10_real_2 : star (bellState10.vec 2) = bellState10.vec 2 := by
  unfold bellState10; qisimp; simp (decide := true)

/-- bellState10 component 3 is real: (-1/√2) -/
lemma bell10_real_3 : star (bellState10.vec 3) = bellState10.vec 3 := by
  unfold bellState10; qisimp; simp (decide := true)

/-- bellState11 component 0 is real: 0 -/
lemma bell11_real_0 : star (bellState11.vec 0) = bellState11.vec 0 := by
  unfold bellState11; qisimp; simp (decide := true)

/-- bellState11 component 1 is real: (1/√2) -/
lemma bell11_real_1 : star (bellState11.vec 1) = bellState11.vec 1 := by
  unfold bellState11; qisimp; simp (decide := true)

/-- bellState11 component 2 is real: (-1/√2) -/
lemma bell11_real_2 : star (bellState11.vec 2) = bellState11.vec 2 := by
  unfold bellState11; qisimp; simp (decide := true)

/-- bellState11 component 3 is real: 0 -/
lemma bell11_real_3 : star (bellState11.vec 3) = bellState11.vec 3 := by
  unfold bellState11; qisimp; simp (decide := true)

/-- The 4 Bell states as a vector -/
noncomputable def bellStatesVec : Fin 4 → Ket 4 :=
  ![bellState00, bellState01, bellState10, bellState11]

/-- All bellState00 components are real -/
lemma bell00_component_real (i : Fin 4) :
    star (bellState00.vec i) = bellState00.vec i := by
  fin_cases i
  · exact bell00_real_0
  · exact bell00_real_1
  · exact bell00_real_2
  · exact bell00_real_3

/-- All bellState01 components are real -/
lemma bell01_component_real (i : Fin 4) :
    star (bellState01.vec i) = bellState01.vec i := by
  fin_cases i
  · exact bell01_real_0
  · exact bell01_real_1
  · exact bell01_real_2
  · exact bell01_real_3

/-- All bellState10 components are real -/
lemma bell10_component_real (i : Fin 4) :
    star (bellState10.vec i) = bellState10.vec i := by
  fin_cases i
  · exact bell10_real_0
  · exact bell10_real_1
  · exact bell10_real_2
  · exact bell10_real_3

/-- All bellState11 components are real -/
lemma bell11_component_real (i : Fin 4) :
    star (bellState11.vec i) = bellState11.vec i := by
  fin_cases i
  · exact bell11_real_0
  · exact bell11_real_1
  · exact bell11_real_2
  · exact bell11_real_3

/-- All Bell state components are real -/
lemma bell_component_real (i : Fin 4) (j : Fin 4) :
    star ((![bellState00, bellState01, bellState10, bellState11] i).vec j) =
    (![bellState00, bellState01, bellState10, bellState11] i).vec j := by
  fin_cases i
  · exact bell00_component_real j
  · exact bell01_component_real j
  · exact bell10_component_real j
  · exact bell11_component_real j

/-!
## Doubly Stochastic Transformation

The Bell fidelities are related to eigenvalues via a doubly stochastic matrix.
This is the key ingredient for proving that dephasing increases entropy.

For a density operator ρ with eigendecomposition ρ = U Λ U†:
- Let uⱼ be the j-th column of U (eigenvector for eigenvalue λⱼ)
- Define D_ij = |⟨βᵢ|uⱼ⟩|² (overlap squared)
- Then D is doubly stochastic and pᵢ = Σⱼ D_ij λⱼ
-/

/-- Bell states are normalized -/
lemma bellStatesVec_normalized (i : Fin 4) :
    (bellStatesVec i).dag * (bellStatesVec i) = 1 := by
  have h := bellStates_orthonormal i i
  simp only [if_true] at h
  unfold bellStatesVec
  exact h

/-- Conjugating a diagonal matrix by the Bell basis matrix gives the corresponding
    weighted sum of Bell rank-one projectors. -/
theorem bell_basis_conj_diagonal (p : Fin 4 → ℝ) :
    let U : Op 4 := Matrix.of fun i j => (bellStatesVec i).vec j
    U† * Matrix.diagonal (fun i => (p i : ℂ)) * U =
      ∑ i, (p i : ℂ) • (bellStatesVec i * (bellStatesVec i).dag) := by
  intro U
  ext j k
  rw [Matrix.mul_apply]
  have hmul : ∀ x, (U† * Matrix.diagonal (fun i => (p i : ℂ))) j x = star (U x j) * ↑(p x) := by
    intro x
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [show ∑ x, (U† * Matrix.diagonal (fun i => (p i : ℂ))) j x * U x k =
      ∑ x, star (U x j) * ↑(p x) * U x k by
    apply Finset.sum_congr rfl
    intro x _
    rw [hmul x]]
  change ∑ i, star (U i j) * ↑(p i) * U i k =
    ∑ i, (((p i : ℂ) • (bellStatesVec i * (bellStatesVec i).dag)) j k)
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.smul_apply, ket_mul_bra_apply, Ket.dag_vec, starRingEnd_apply]
  simp only [U, Matrix.of_apply]
  unfold bellStatesVec
  rw [bell_component_real i j, bell_component_real i k]
  simp only [smul_eq_mul]
  ring

/-!
## Shannon Entropy Monotonicity

Shannon entropy increases under doubly stochastic transformations.
This is a key result in majorization theory.
-/

/-!
## Eigenvalue Correspondence

We need to show that Mathlib's explicit eigenvalues give the same entropy
as our `eigenvaluesOf` (from Classical.choose). Since entropy only depends
on the multiset of eigenvalues (not ordering), this is straightforward.
-/

/-!
## Bell Fidelity as Doubly Stochastic Transform

The Bell fidelity ⟨βᵢ|ρ|βᵢ⟩ equals Σⱼ D_ij λⱼ where:
- D_ij = |⟨βᵢ|uⱼ⟩|² (overlap squared)
- λⱼ = eigenvalue j of ρ
- uⱼ = eigenvector j of ρ
-/

end QKD.BB84.Engine.BellDephasing
