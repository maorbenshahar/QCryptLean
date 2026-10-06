import QCryptLean.Quantum.Channels.TranscriptLocal
import QCryptLeanTest.Quantum.Channels.Separable

/-!
# The joint-XOR channel is not a product of independent local operations
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The joint-XOR channel cannot be an independent product of local operations. -/
theorem jointKeyChannel_not_isTranscriptLocal :
    ¬ IsTranscriptLocalOperation (rA := 2) (rB := 2) (sA := 2) (sB := 2) (D := 1)
        ((Op.castDimLinear (Nat.mul_one (2 * 2)).symm).comp jointKeyChannel) := by
  intro h
  obtain ⟨mA, mB, A, B, hprod⟩ := isTranscriptLocal_one_apply jointKeyChannel h
  have hfac : ∀ a b : Fin 2,
      Op.tensor (Matrix.single (a + b) (a + b) (1 : ℂ)) (Matrix.single (a + b) (a + b) (1 : ℂ))
        = Op.tensor (∑ i, A i * Matrix.single a a (1 : ℂ) * (A i)ᴴ)
            (∑ j, B j * Matrix.single b b (1 : ℂ) * (B j)ᴴ) := by
    intro a b
    rw [← jointKeyChannel_apply a b, hprod]
    have hterm : ∀ (i : Fin mA) (j : Fin mB),
        tensorRect (A i) (B j) *
            Op.tensor (Matrix.single a a (1 : ℂ)) (Matrix.single b b (1 : ℂ)) *
            (tensorRect (A i) (B j))ᴴ
          = tensorRect (A i * Matrix.single a a (1 : ℂ) * (A i)ᴴ)
              (B j * Matrix.single b b (1 : ℂ) * (B j)ᴴ) := by
      intro i j
      rw [← tensorRect_square (Matrix.single a a (1 : ℂ)) (Matrix.single b b (1 : ℂ)),
        tensorRect_conjTranspose, tensorRect_mul, tensorRect_mul]
    simp only [hterm]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => tensorRect_sum_right _ _,
      tensorRect_sum_left, tensorRect_square]
  have hent : ∀ a b : Fin 2,
      Matrix.single (a + b) (a + b) (1 : ℂ) (1 : Fin 2) (1 : Fin 2) *
          Matrix.single (a + b) (a + b) (1 : ℂ) (1 : Fin 2) (1 : Fin 2)
        = (∑ i, A i * Matrix.single a a (1 : ℂ) * (A i)ᴴ) (1 : Fin 2) (1 : Fin 2) *
          (∑ j, B j * Matrix.single b b (1 : ℂ) * (B j)ᴴ) (1 : Fin 2) (1 : Fin 2) := by
    intro a b
    have hh := congrFun (congrFun (hfac a b) (finProdFinEquiv ((1 : Fin 2), (1 : Fin 2))))
      (finProdFinEquiv ((1 : Fin 2), (1 : Fin 2)))
    simp only [Op_tensor_apply_finProd, Equiv.symm_apply_apply] at hh
    exact hh
  have hs1 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) (1 : Fin 2) (1 : Fin 2) = 1 := by
    simp
  have hs0 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) (1 : Fin 2) (1 : Fin 2) = 0 := by
    simp
  have e01 := hent 0 1
  rw [show (0 : Fin 2) + 1 = 1 from by decide, hs1, one_mul] at e01
  have e10 := hent 1 0
  rw [show (1 : Fin 2) + 0 = 1 from by decide, hs1, one_mul] at e10
  have e00 := hent 0 0
  rw [show (0 : Fin 2) + 0 = 0 from by decide, hs0, zero_mul] at e00
  have hA0 : (∑ i, A i * Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) * (A i)ᴴ)
      (1 : Fin 2) (1 : Fin 2) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at e01
    exact one_ne_zero e01
  have hB0 : (∑ j, B j * Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) * (B j)ᴴ)
      (1 : Fin 2) (1 : Fin 2) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at e10
    exact one_ne_zero e10
  exact mul_ne_zero hA0 hB0 e00.symm

end Quantum.Channels
