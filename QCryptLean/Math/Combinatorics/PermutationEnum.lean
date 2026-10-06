import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic

/-!
# Permutation enumeration and small Fin / complex-arithmetic lemmas

General, protocol-independent permutation and small Fin/complex-arithmetic utilities.

## Main statements
- `permutationTwirlPermEnum`: a finite enumeration of `Equiv.Perm (Fin n)` by `Fin n!`.
- `fin_sum_ite_modNat_eq`: collapse a `Fin (k * m)` indicator sum over `modNat` to a `Fin k` sum.
- `complex_inv_sqrt_nat_factorial_mul_self`: reciprocal complex `√(n!)` squares to `(n!)⁻¹`.
-/

open scoped BigOperators

namespace QKD.BB84.Engine

/-- A finite enumeration of the round-permutation group by `Fin n!`.

The enumeration is used only to package the finite Kraus family required by
`KrausRepresentation`; all mathematical specifications below are stated as sums
over `Equiv.Perm (Fin n)`. -/
noncomputable def permutationTwirlPermEnum (n : ℕ) :
    Fin (Nat.factorial n) ≃ Equiv.Perm (Fin n) :=
  let card_eq : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    simp [Fintype.card_perm]
  (finCongr card_eq.symm).trans (Fintype.equivFin (Equiv.Perm (Fin n))).symm

lemma fin_sum_ite_modNat_eq
    {k m : ℕ} {α : Type*} [AddCommMonoid α]
    (s : Fin m) (f : Fin (k * m) → α) :
    (∑ x : Fin (k * m), if s = x.modNat then f x else 0) =
      ∑ i : Fin k, f (finProdFinEquiv (i, s)) := by
  classical
  calc
    (∑ x : Fin (k * m), if s = x.modNat then f x else 0) =
        ∑ p : Fin k × Fin m,
          if s = (finProdFinEquiv p).modNat then f (finProdFinEquiv p) else 0 := by
      exact (Fintype.sum_equiv
        (finProdFinEquiv : Fin k × Fin m ≃ Fin (k * m))
        (fun p : Fin k × Fin m =>
          if s = (finProdFinEquiv p).modNat then f (finProdFinEquiv p) else 0)
        (fun x : Fin (k * m) => if s = x.modNat then f x else 0)
        (by intro p; rfl)).symm
    _ = ∑ p : Fin k × Fin m, if s = p.2 then f (finProdFinEquiv p) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      rcases p with ⟨i, j⟩
      have hmod : (finProdFinEquiv (i, j)).modNat = j := by
        have h := finProdFinEquiv_symm_apply (finProdFinEquiv (i, j))
        rw [Equiv.symm_apply_apply] at h
        exact (congr_arg Prod.snd h).symm
      simp [hmod]
    _ = ∑ i : Fin k, f (finProdFinEquiv (i, s)) := by
      rw [Fintype.sum_prod_type_right]
      rw [Finset.sum_eq_single s]
      · simp
      · intro j _ hjs
        have hsj : s ≠ j := fun h => hjs h.symm
        simp [hsj]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ s))

/-- The reciprocal complex square root normalization squares to `1 / n!`. -/
lemma complex_inv_sqrt_nat_factorial_mul_self (n : ℕ) :
    ((Real.sqrt (Nat.factorial n : ℝ) : ℂ)⁻¹ *
        (Real.sqrt (Nat.factorial n : ℝ) : ℂ)⁻¹) =
      ((Nat.factorial n : ℂ)⁻¹) := by
  rw [← _root_.mul_inv_rev]
  congr
  rw [← sq]
  exact_mod_cast Real.sq_sqrt
    (Nat.cast_nonneg (Nat.factorial n) : (0 : ℝ) ≤ (Nat.factorial n : ℝ))

end QKD.BB84.Engine
