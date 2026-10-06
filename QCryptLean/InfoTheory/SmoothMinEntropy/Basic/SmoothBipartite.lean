import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.BipartiteMinMax
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistance

/-!
# Smooth general-bipartite conditional min-entropy (the smooth `H_min` on the guarded layer)

This module adds the ε-smooth, reference-optimized conditional min-entropy for a general
sub-normalized bipartite state `ρ_AB` on `A ⊗ B`, built on the *guarded* non-smooth
`bipartiteMinEntropyOptReal` (`BipartiteMinMax.lean`). It is the general-bipartite analogue of the
CQ-only smooth min-entropy `smoothMinEntropy`. `CanonicalPurification.lean` uses it on the
complementary register of a fixed purification to define a dual-form quantity; identification
with fidelity-form max-entropy is a separate, unproved result.

## Definition

Tomamichel (2016), Def. 6.5 (`eq:6.34`), in the general-bipartite formulation:
```
H_min^ε(A|B)_ρ := sup_{ρ̃ ∈ B^ε(ρ_AB)} H_min(A|B)_ρ̃,
```
the supremum of the guarded reference-optimized `bipartiteMinEntropyOptReal` over the
purified-distance ε-ball `B^ε(ρ_AB)` of `SubDensityOp (dA * dB)` (`purifiedDistance`,
`PurifiedDistance.lean`). The inner `bipartiteMinEntropyOptReal` already ranges over
`D_max`-feasible references only, so the `Real.log 0 = 0` sentinel of infeasible references does
not enter (see the `bipartiteMinEntropyOptReal` docstring); the smooth layer inherits that guard.

## Boundedness convention

This is an ℝ-valued `sSup`, so its interpretation as an entropy supremum requires a nonempty,
bounded-above optimization set. Member bounds and radius monotonicity retain `BddAbove`
explicitly. At ε = 0 the set is a singleton, so the collapse theorem needs no such premise.
`SmoothBipartiteRegularity.lean` supplies boundedness for normalized centres and `0 ≤ ε < 1`.
-/

open Quantum.Operators
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Membership predicate for the smooth bipartite min-entropy optimization set: `ρ'` lies in the
purified-distance ε-ball of `ρ` and achieves the guarded reference-optimized min-entropy value
`h`. -/
def isInSmoothBipartiteMinSet {dA dC : ℕ} [NeZero (dA * dC)]
    (ε : ℝ) (ρ : SubDensityOp (dA * dC)) (h : ℝ) : Prop :=
  ∃ ρ' : SubDensityOp (dA * dC),
    purifiedDistance ρ ρ' ≤ ε ∧ h = bipartiteMinEntropyOptReal ρ'

/-- ε-smooth reference-optimized conditional min-entropy `H_min^ε(A|C)_ρ` of a general
sub-normalized bipartite state `ρ_AC` on `A ⊗ C`.

Tomamichel (2016), Def. 6.5 (`eq:6.34`), general-bipartite form:
  `H_min^ε(A|C)_ρ := sup_{ρ̃ ∈ B^ε(ρ_AC)} H_min(A|C)_ρ̃`,
realized as the `sSup` over the purified-distance ε-ball of the guarded reference-optimized
`bipartiteMinEntropyOptReal`. ℝ-valued; the inner quantity carries the min-side feasibility
guard. -/
noncomputable def smoothBipartiteMinEntropyOptReal {dA dC : ℕ} [NeZero (dA * dC)]
    (ε : ℝ) (ρ : SubDensityOp (dA * dC)) : ℝ :=
  sSup (setOf (isInSmoothBipartiteMinSet ε ρ))

/-- The smooth bipartite min-entropy optimization set contains the center state's guarded
optimized min-entropy value when the smoothing radius is nonnegative. -/
theorem smoothBipartiteMinSet_nonempty {dA dC : ℕ} [NeZero (dA * dC)]
    {ε : ℝ} (hε : 0 ≤ ε) (ρ : SubDensityOp (dA * dC)) :
    (setOf (isInSmoothBipartiteMinSet ε ρ)).Nonempty :=
  ⟨bipartiteMinEntropyOptReal ρ, ρ, by rw [purifiedDistance_self_zero]; exact hε, rfl⟩

/-- Every ball member's guarded optimized min-entropy is a lower bound for the smooth bipartite
min-entropy (the `sSup` witness bound), given that the optimization set is bounded above. -/
theorem smoothBipartiteMinEntropyOptReal_ge_of_mem_ball {dA dC : ℕ} [NeZero (dA * dC)]
    (ε : ℝ) (ρ ρ' : SubDensityOp (dA * dC))
    (hbdd : BddAbove (setOf (isInSmoothBipartiteMinSet ε ρ)))
    (hd : purifiedDistance ρ ρ' ≤ ε) :
    bipartiteMinEntropyOptReal ρ' ≤ smoothBipartiteMinEntropyOptReal ε ρ :=
  le_csSup hbdd ⟨ρ', hd, rfl⟩

/-- Smooth bipartite min-entropy at ε = 0 equals the non-smooth guarded optimized min-entropy.

The ε-ball at ε = 0 collapses to the singleton `{ρ}`: purified distance is a metric, so
`P(ρ, ρ̃) ≤ 0` together with nonnegativity forces `ρ = ρ̃`, hence
`bipartiteMinEntropyOptReal ρ = bipartiteMinEntropyOptReal ρ̃`. Then `sSup` of a singleton is its
element. -/
theorem smoothBipartiteMinEntropyOptReal_zero_eq {dA dC : ℕ} [NeZero (dA * dC)]
    (ρ : SubDensityOp (dA * dC)) :
    smoothBipartiteMinEntropyOptReal 0 ρ = bipartiteMinEntropyOptReal ρ := by
  unfold smoothBipartiteMinEntropyOptReal
  have hset : setOf (isInSmoothBipartiteMinSet 0 ρ) = {bipartiteMinEntropyOptReal ρ} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨ρ, by rw [purifiedDistance_self_zero], rfl⟩, ?_⟩
    rintro h ⟨ρ', hd, rfl⟩
    have hd_zero : purifiedDistance ρ ρ' = 0 :=
      le_antisymm hd (purifiedDistance_nonneg ρ ρ')
    have hρ_eq : ρ = ρ' := (purifiedDistance_eq_zero_iff ρ ρ').mp hd_zero
    rw [hρ_eq]
  rw [hset, csSup_singleton]

/-- **A ball member above the real-valued supremum minus `δ`.** For a nonnegative smoothing
radius `ε` and every `δ > 0`, there is a purified-distance ε-ball member `ρ'` with

`∃ ρ' ∈ B^ε(ρ),  smoothBipartiteMinEntropyOptReal ε ρ − δ ≤ bipartiteMinEntropyOptReal ρ'` .

When the optimization set is bounded above, this is an approximate optimizer; the supremum need
not be attained. The displayed existential uses only nonemptiness and remains true in the
unbounded case, where the real-valued `sSup` does not represent the entropy optimization. -/
theorem smoothBipartiteMinEntropyOptReal_exists_ball_approx {dA dC : ℕ} [NeZero (dA * dC)]
    {ε : ℝ} (hε : 0 ≤ ε) (ρ : SubDensityOp (dA * dC))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ' : SubDensityOp (dA * dC),
      purifiedDistance ρ ρ' ≤ ε ∧
      smoothBipartiteMinEntropyOptReal ε ρ - δ ≤ bipartiteMinEntropyOptReal ρ' := by
  have hlt : smoothBipartiteMinEntropyOptReal ε ρ - δ < smoothBipartiteMinEntropyOptReal ε ρ := by
    linarith
  obtain ⟨v, hv_mem, hv_lt⟩ :=
    exists_lt_of_lt_csSup (smoothBipartiteMinSet_nonempty hε ρ) hlt
  obtain ⟨ρ', hd, rfl⟩ := hv_mem
  exact ⟨ρ', hd, le_of_lt hv_lt⟩

/-- Smooth bipartite min-entropy is monotone in the smoothing radius: a larger ball gives a larger
supremum. Requires `0 ≤ ε` (so the smaller ball is nonempty) and boundedness above of the
larger-ball optimization set. -/
theorem smoothBipartiteMinEntropyOptReal_monotone_eps {dA dC : ℕ} [NeZero (dA * dC)]
    {ε ε' : ℝ} (hε : 0 ≤ ε) (h : ε ≤ ε') (ρ : SubDensityOp (dA * dC))
    (hbdd : BddAbove (setOf (isInSmoothBipartiteMinSet ε' ρ))) :
    smoothBipartiteMinEntropyOptReal ε ρ ≤ smoothBipartiteMinEntropyOptReal ε' ρ := by
  unfold smoothBipartiteMinEntropyOptReal
  refine csSup_le_csSup hbdd (smoothBipartiteMinSet_nonempty hε ρ) ?_
  intro v hv
  obtain ⟨ρ', hd, hv_eq⟩ := hv
  exact ⟨ρ', le_trans hd h, hv_eq⟩

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
