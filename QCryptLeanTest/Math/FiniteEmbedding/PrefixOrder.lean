import QCryptLean.Math.FiniteEmbedding.PrefixOrder
import Mathlib.Util.AssertNoSorry

/-!
# Tests for fixed-left restriction and fixed-prefix ordering

This test checks the fixed-left and fixed-prefix construction and evaluates empty, full, and
nonsorted-prefix instances of the definitions.
-/

namespace Math.FiniteEmbedding.PrefixOrderAudit

open Math.FiniteEmbedding

/-- Explicit equivalence between `Fin n` and the subtype of the universal finset. -/
def finUnivValueEquiv (n : ℕ) :
    Fin n ≃ {i : Fin n // i ∈ (Finset.univ : Finset (Fin n))} where
  toFun := fun i => ⟨i, Finset.mem_univ i⟩
  invFun := Subtype.val
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Explicit enumeration of the universal finset with its actual cardinality in the domain. -/
def finUnivEnumeration (n : ℕ) :
    Fin (Finset.univ : Finset (Fin n)).card ≃
      {i : Fin n // i ∈ (Finset.univ : Finset (Fin n))} :=
  (finCongr (by simp)).trans (finUnivValueEquiv n)

/-- The unique empty prefix embedding. -/
def emptyPrefixEmbedding :
    Fin 0 ↪ {i : Fin 0 // i ∈ (Finset.univ : Finset (Fin 0))} :=
  (finUnivValueEquiv 0).toEmbedding

/-- Empty target and prefix instantiate the literal fibre definition. -/
def emptyPrefixFiber :
    PrefixSequenceFiber (Finset.univ : Finset (Fin 0)) emptyPrefixEmbedding :=
  ⟨finUnivEnumeration 0, by decide⟩

/-- A full three-value prefix embedding in increasing order. -/
def fullPrefixEmbedding :
    Fin 3 ↪ {i : Fin 3 // i ∈ (Finset.univ : Finset (Fin 3))} :=
  (finUnivValueEquiv 3).toEmbedding

/-- Full prefix leaves a zero-cardinality residual coordinate. -/
def fullPrefixFiber :
    PrefixSequenceFiber (Finset.univ : Finset (Fin 3)) fullPrefixEmbedding :=
  ⟨finUnivEnumeration 3, by decide⟩

theorem fullPrefix_residual_card :
    ((Finset.univ : Finset (Fin 3)).card - 3) = 0 := by
  decide

/-- Swap the endpoints of the actual three-element enumeration domain. -/
def swapEnds : Equiv.Perm (Fin (Finset.univ : Finset (Fin 3)).card) :=
  Equiv.swap ⟨0, by decide⟩ ⟨2, by decide⟩

/-- Explicit nonsorted enumeration `2, 1, 0`. -/
def nonsortedEnumeration :
    Fin (Finset.univ : Finset (Fin 3)).card ≃
      {i : Fin 3 // i ∈ (Finset.univ : Finset (Fin 3))} :=
  swapEnds.trans (finUnivEnumeration 3)

/-- Its literal first two positions form the nonsorted embedded prefix `2, 1`. -/
def nonsortedPrefixEmbedding :
    Fin 2 ↪ {i : Fin 3 // i ∈ (Finset.univ : Finset (Fin 3))} :=
  (Fin.castLEEmb (by decide)).trans nonsortedEnumeration.toEmbedding

/-- The nonsorted enumeration inhabits the actual `.take`/`List.ofFn` fibre. -/
def nonsortedPrefixFiber :
    PrefixSequenceFiber (Finset.univ : Finset (Fin 3)) nonsortedPrefixEmbedding :=
  ⟨nonsortedEnumeration, by decide⟩

theorem nonsortedPrefix_first : (nonsortedPrefixEmbedding 0).1 = 2 := by
  decide

theorem nonsortedPrefix_second : (nonsortedPrefixEmbedding 1).1 = 1 := by
  decide

/-- Symbolic orientation probe: rebuilding uses `ρ k`, not `ρ.symm k`, on the residual block. -/
theorem residual_orientation_probe {N r : ℕ} (T : Finset (Fin N))
    (u : Fin r ↪ T) (ρ : Equiv.Perm (Fin (T.card - r))) (k : Fin (T.card - r)) :
    rebuildPrefixSequence T u ρ (prefixDomainEquiv T u (Sum.inr k)) =
      prefixTargetEquiv T u (Sum.inr (ρ k)) :=
  rebuildPrefixSequence_apply_residual T u ρ k

end Math.FiniteEmbedding.PrefixOrderAudit
