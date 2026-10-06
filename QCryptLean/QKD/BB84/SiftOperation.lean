import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement

/-!
# BB84 sift/permutation operation

The local matrix operation `F U_π` used by the BB84 quantum prefix: it first
permutes the `n` local rounds by `π`, then applies the selector-defined Hadamard
mask `F`. This module contains only that operator and its unitarity certificate.

It contains no `LocalInstrument`, `Protocol`, transcript, or compiler syntax.
The communication needed for an LOCC implementation is established separately by
the typed stage that uses this operation.
-/

open Quantum.Operators Quantum.TensorProducts
open Math.RepresentationTheory
open scoped Matrix ComplexConjugate

noncomputable section

namespace QKD.BB84.Model

/-- The local BB84 sift/permutation operator `F U_π` on `n` qubit rounds. -/
def siftPermHalf (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) : Op (2 ^ n) :=
  tensorFamily (fun a => if peSel a && xSel a then Quantum.Gates.hadamard else (1 : Op 2)) *
    permutationRepresentation 2 n π

/-- One party's factor of the quantum prefix is unitary — a product of a tensor family of
Hadamards and identities with a permutation representation, both unitary. -/
theorem siftPermHalf_unitary (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (siftPermHalf n peSel xSel π)ᴴ * siftPermHalf n peSel xSel π = 1 := by
  have hfam : ∀ a : Fin n,
      (if peSel a && xSel a then Quantum.Gates.hadamard else (1 : Op 2))ᴴ *
        (if peSel a && xSel a then Quantum.Gates.hadamard else (1 : Op 2)) = 1 := by
    intro a
    by_cases h : peSel a && xSel a
    · rw [ite_eq_left h, Quantum.Gates.hadamard_hermitian, Quantum.Gates.hadamard_sq]
    · rw [ite_eq_right h, Matrix.conjTranspose_one, Matrix.one_mul]
  have hA := conjTranspose_tensorFamily_mul_self hfam
  have hU := (Math.RepresentationTheory.permutationRepresentation_unitary 2 n π).1
  unfold siftPermHalf
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ (permutationRepresentation 2 n π), hA, Matrix.one_mul, hU]

end QKD.BB84.Model
