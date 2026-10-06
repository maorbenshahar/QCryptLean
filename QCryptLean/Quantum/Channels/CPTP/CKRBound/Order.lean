import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# CKR Channel Order Helpers

Low-level monotonicity lemmas for the quadratic-form order `opLe` under
completely positive linear maps and first-factor tensor maps.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

namespace Quantum.Channels

/-- Rectangular Kraus conjugation pulls quadratic forms back through `K†`. -/
lemma quadraticForm_kraus_sandwich {n m : ℕ}
    (K : Matrix (Fin m) (Fin n) ℂ)
    (A : Op n) (v : Fin m → ℂ) :
    quadraticForm (K * A * Kᴴ) v =
      quadraticForm A (Kᴴ.mulVec v) := by
  unfold quadraticForm
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  congr 1
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

/-- Conjugating both sides by a rectangular Kraus operator preserves `opLe`. -/
lemma opLe_kraus_sandwich {n m : ℕ}
    (K : Matrix (Fin m) (Fin n) ℂ)
    {A B : Op n} (hAB : opLe A B) :
    opLe (K * A * Kᴴ) (K * B * Kᴴ) := by
  intro v
  rw [quadraticForm_kraus_sandwich K A v,
    quadraticForm_kraus_sandwich K B v]
  exact hAB (Kᴴ.mulVec v)

/-- Finite sums preserve `opLe` termwise. -/
lemma opLe_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (A B : ι → Op n) (hAB : ∀ i, opLe (A i) (B i)) :
    opLe (∑ i, A i) (∑ i, B i) := by
  intro v
  simp only [quadraticForm, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  exact Finset.sum_le_sum (fun i _ => hAB i v)

/-- Completely positive linear maps preserve the quadratic-form order `opLe`. -/
lemma cp_linear_preserves_opLe {n m : ℕ}
    [NeZero n] [NeZero m]
    (T : Op n →ₗ[ℂ] Op m)
    (hT_cp : IsCompletelyPositive ⇑T)
    {A B : Op n} (hAB : opLe A B) :
    opLe (T A) (T B) := by
  obtain ⟨r, K, hK⟩ := cp_linear_eq_kraus_sum T hT_cp
  rw [hK A, hK B]
  exact opLe_sum
    (fun k : Fin r => K k * A * (K k)ᴴ)
    (fun k : Fin r => K k * B * (K k)ᴴ)
    (fun k => opLe_kraus_sandwich (K k) hAB)

/-- Applying a completely positive map to the first tensor factor preserves `opLe`. -/
lemma mapTensorId_preserves_opLe {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (T : Op n →ₗ[ℂ] Op m)
    (hT_cp : IsCompletelyPositive ⇑T)
    {A B : Op (n * k)} (hAB : opLe A B) :
    opLe (mapTensorId T A) (mapTensorId T B) := by
  let Φ : Op (n * k) →ₗ[ℂ] Op (m * k) :=
    mapTensorIdLinear T
  have hΦ_cp : IsCompletelyPositive ⇑Φ :=
    mapTensorId_isCompletelyPositive T hT_cp
  exact cp_linear_preserves_opLe Φ hΦ_cp hAB

end Quantum.Channels
