import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.ProdSigma
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Fintype Product Factoring

Index arithmetic for `List.product`.  These are combinatorial lemmas needed when reindexing
tensor-product amplitudes via the canonical bijection `Fin n × Fin m ≃ Fin (n * m)`.

## Main statements

- `List.idxOf_product`: the index of `(a, b)` in `l₁.product l₂` equals
  `l₁.idxOf a * l₂.length + l₂.idxOf b`.

## Downstream clients

`List.idxOf_product` is used when computing matrix indices in tensor-product constructions
that linearize `Fin n × Fin m` via `List.product (Finset.univ.val)`.

## Note

`Fintype.equivFin (X × X')` does not factor through `finProdFinEquiv` and the component
`equivFin`s: `Fintype.equivFin` is `noncomputable`, defined via `Classical.choice` from
`truncEquivFin`, and the choice made for `X × X'` is independent of the choices made for `X`
and `X'`. Use `finProdFinEquiv` or a `Trunc`-quotient argument directly instead.
-/

namespace List

/-- The index of the pair `(a, b)` in `l₁.product l₂` equals
`l₁.idxOf a * l₂.length + l₂.idxOf b`, provided `a ∈ l₁` and `b ∈ l₂`.

The proof proceeds by induction on `l₁`: in the base case `l₁ = []` the membership
hypothesis `ha : a ∈ []` is contradictory; in the inductive step one splits on whether
`a` equals the head of `l₁` and uses `List.idxOf_cons_eq`, `List.idxOf_cons_ne`, and
`List.product_cons` together with the length of the appended list. -/
theorem idxOf_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (l₁ : List α) (l₂ : List β) (a : α) (b : β) (ha : a ∈ l₁) (hb : b ∈ l₂) :
    (l₁.product l₂).idxOf (a, b) = l₁.idxOf a * l₂.length + l₂.idxOf b := by
  induction l₁ with
  | nil => exact (List.not_mem_nil ha).elim
  | cons x xs ih =>
    change ((x :: xs) ×ˢ l₂).idxOf (a, b) = (x :: xs).idxOf a * l₂.length + l₂.idxOf b
    rw [List.product_cons]
    by_cases hxa : x = a
    · subst hxa
      have hmem : (x, b) ∈ l₂.map (Prod.mk x) := List.mem_map.mpr ⟨b, hb, rfl⟩
      rw [idxOf_append_of_mem hmem]
      have hidx : (l₂.map (Prod.mk x)).idxOf (x, b) = l₂.idxOf b := by
        simp only [idxOf, List.findIdx_map]
        congr 1; ext y; simp
      rw [hidx, idxOf_cons_self, Nat.zero_mul, Nat.zero_add]
    · have hxa' : a ∈ xs := by
        rcases List.mem_cons.mp ha with rfl | h
        · exact absurd rfl hxa
        · exact h
      have hnotmem : (a, b) ∉ l₂.map (Prod.mk x) := by
        simp only [List.mem_map]
        rintro ⟨c, _, hc⟩
        exact hxa (Prod.mk.inj hc).1
      have ih' := ih hxa'
      rw [show (xs.product l₂).idxOf (a, b) = (xs ×ˢ l₂).idxOf (a, b) from rfl] at ih'
      rw [idxOf_append_of_notMem hnotmem, length_map, idxOf_cons_ne xs hxa, ih']
      rw [Nat.succ_mul]; omega

end List
