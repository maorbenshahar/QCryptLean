import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Math.LinearAlgebra.PermutationMatrix

/-!
# Public Permutation-Announcement Register — indices, projectors, right multiplication

This file defines the finite register used to announce a BB84 input permutation
and proves that right-multiplication unitaries relabel its rank-one projectors.

Moved here from `QKD.BB84.Engine.Postselection.InputSymmetrizeRegister`: it is pure
register-index combinatorics for the model's announcement map
(`QKD.BB84.Model.bb84SiftedPEAnnounceLinear`), not Engine-specific security analysis, so it
belongs with the model rather than one Engine file.

## Main definitions
- `permAnnounceIndexEquiv`: identifies permutations of `Fin n` with the announcement register.
- `permAnnounceProjector`: rank-one announcement projector for a permutation.
- `permAnnounceRightMulUnitary`: unitary for right multiplication on announcements.

## Main statements
- `permAnnounceRightMulUnitary_projector`: right multiplication relabels projectors.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-- The finite index used for the public permutation-announcement register. -/
noncomputable def permAnnounceIndexEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ Fin n.factorial :=
  (Fintype.equivFin (Equiv.Perm (Fin n))).trans
    (finCongr (by simp [Fintype.card_perm]))

/-- The rank-1 projector `|perm⟩⟨perm|` on `Op n.factorial`,
    using `Fintype.equivFin` to index permutations. -/
noncomputable def permAnnounceProjector (n : ℕ) (perm : Equiv.Perm (Fin n)) :
    Op n.factorial :=
  stdKet n.factorial (permAnnounceIndexEquiv n perm) *
    (stdKet n.factorial (permAnnounceIndexEquiv n perm)).dag

/-- Right multiplication on the public permutation-announcement label. -/
def permAnnounceRightMulEquiv (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := σ * π
  invFun σ := σ * π⁻¹
  left_inv σ := by simp [mul_assoc]
  right_inv σ := by simp [mul_assoc]

/-- The induced right-multiplication permutation of the finite announcement register. -/
noncomputable def permAnnounceRightMulFinPerm (n : ℕ)
    (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n.factorial) :=
  (permAnnounceIndexEquiv n).symm.trans
    ((permAnnounceRightMulEquiv n π).trans (permAnnounceIndexEquiv n))

/-- The unitary that relabels the public permutation-announcement register by
right multiplication.  The inverse `permMatrix` convention makes conjugation send
the basis label `perm` to `perm * π`. -/
noncomputable def permAnnounceRightMulUnitary (n : ℕ)
    (π : Equiv.Perm (Fin n)) : Op n.factorial :=
  Equiv.Perm.permMatrix ℂ ((permAnnounceRightMulFinPerm n π).symm)

private lemma permAnnounceProjector_eq_single (n : ℕ)
    (perm : Equiv.Perm (Fin n)) :
    permAnnounceProjector n perm =
      Matrix.single (permAnnounceIndexEquiv n perm)
        (permAnnounceIndexEquiv n perm) (1 : ℂ) := by
  ext i j
  by_cases hi : (permAnnounceIndexEquiv n perm) = i
  · by_cases hj : (permAnnounceIndexEquiv n perm) = j
    · simp [permAnnounceProjector, Matrix.single_apply, hi]
    · simp [permAnnounceProjector, Matrix.single_apply, hi]
  · by_cases hj : (permAnnounceIndexEquiv n perm) = j
    · simp [permAnnounceProjector, Matrix.single_apply, hj]
    · simp [permAnnounceProjector, hi, hj]

/-- Right-multiplication on announcement labels carries each announcement projector
to the projector for the multiplied permutation. -/
lemma permAnnounceRightMulUnitary_projector (n : ℕ)
    (π perm : Equiv.Perm (Fin n)) :
    permAnnounceRightMulUnitary n π * permAnnounceProjector n perm *
        (permAnnounceRightMulUnitary n π)ᴴ =
      permAnnounceProjector n (perm * π) := by
  rw [permAnnounceProjector_eq_single, permAnnounceProjector_eq_single,
    permAnnounceRightMulUnitary]
  simpa [permAnnounceRightMulFinPerm, permAnnounceRightMulEquiv]
    using
      (Equiv.Perm.permMatrix_conj_single (permAnnounceRightMulFinPerm n π)
        (permAnnounceIndexEquiv n perm))

end QKD.BB84.Model

end -- noncomputable section
