import QCryptLeanTest.Quantum.Channels.Separable

/-! # Joint XOR cannot factor into independent local operations -/
open Quantum.Operators Matrix
open scoped ComplexOrder
namespace Quantum.Channels

/-- Joint XOR has no factorization whose two outputs depend only on their local input. -/
theorem jointKeyChannel_not_independent
    (A B : Fin 2 → Op (Fin 2)) :
    ¬ ∀ a b : Fin 2,
      jointKeyChannel (Matrix.kronecker (Matrix.single a a 1) (Matrix.single b b 1)) =
        Matrix.kronecker (A a) (B b) := by
  intro h
  have hfac (a b : Fin 2) := (jointKeyChannel_apply a b).symm.trans (h a b)
  have hent : ∀ a b : Fin 2,
      Matrix.single (a + b) (a + b) (1 : ℂ) (1 : Fin 2) (1 : Fin 2) *
          Matrix.single (a + b) (a + b) (1 : ℂ) (1 : Fin 2) (1 : Fin 2)
        = (A a) (1 : Fin 2) (1 : Fin 2) *
          (B b) (1 : Fin 2) (1 : Fin 2) := by
    intro a b
    have hh := congrFun (congrFun (hfac a b) ((1 : Fin 2), (1 : Fin 2)))
      ((1 : Fin 2), (1 : Fin 2))
    simp only [Matrix.kroneckerMap_apply] at hh
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
  have hA0 : (A 0)
      (1 : Fin 2) (1 : Fin 2) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at e01
    exact one_ne_zero e01
  have hB0 : (B 0)
      (1 : Fin 2) (1 : Fin 2) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at e10
    exact one_ne_zero e10
  exact mul_ne_zero hA0 hB0 e00.symm

end Quantum.Channels
