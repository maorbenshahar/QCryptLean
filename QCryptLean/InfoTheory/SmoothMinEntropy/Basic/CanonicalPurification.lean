import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SmoothBipartite
import QCryptLean.Quantum.Metrics.SameAncillaPurification

/-!
# The canonical purification of a bipartite state, as a `PureTripartite`

`PureTripartite dA dB dC` (`BipartiteMinMax.lean`) is the normalized tripartite ket together with
its pairwise marginals. This file packages the standard instance: for a bipartite state `ρ_AB` on
`A ⊗ B`, the **canonical purification** on `A ⊗ B ⊗ C` with `dC = dA · dB`,

```
|ψ⟩ = (√ρ_AB ⊗ 1) |Ω⟩   on   (A ⊗ B) ⊗ C ,
```

whose `A ⊗ B` marginal is exactly `ρ_AB`.

## Reuse rather than reconstruction

The ket is the existing same-ancilla purification
`Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet`, not a second construction:
`A ⊗ B ⊗ C` with `dC = dA · dB` *is* the doubled space `(dA·dB) × (dA·dB)` that the same-ancilla
purification lives on, and `partialTraceB_sameAncillaPurificationKet` is the purification property.
All this file adds is the `PureTripartite` packaging, the normalization, and the marginal
identification.

## A canonical-purification dual-form quantity

`smoothMaxEntropyDual` is defined as minus the smooth min-entropy on the complementary register
of this particular purification:

```
smoothMaxEntropyDual ε ρ := − H_min^ε(A|C)_ρ .
```

This is a separate formal object from the fidelity-form conditional max-entropy in
`MaxEntropyFidelity.lean`. The source arXiv:1504.00233, `calculus.tex` defines
max-entropy in fidelity form and proves min–max and smooth duality (`lm:min-max/dual`,
`pr:smooth-dual`). This file does not formalize that identification.

The definition uses the canonical purification, not an existentially selected purification
witness. Independence from an arbitrary purification also remains to be proved. The conditioning-
isometry invariance theorem in `ConditioningIsometryInvariance.lean` is one ingredient; applying
it requires a proved inter-purification isometry or common extension and its dimension and
boundedness premises. None of those conclusions is implicit in the definition below.

## Main definitions

* `InfoTheory.SmoothMinEntropy.canonicalPurification`
* `InfoTheory.SmoothMinEntropy.smoothMaxEntropyDual`

## Main statements

* `InfoTheory.SmoothMinEntropy.canonicalPurification_marginalAB_toOp` — it purifies `ρ_AB`;
* `InfoTheory.SmoothMinEntropy.smoothMaxEntropyDual_zero_eq`,
  `InfoTheory.SmoothMinEntropy.smoothMaxEntropyDual_antitone_eps`.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Metrics.KitaevWatrousPurification
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **The canonical purification of `ρ_AB`.** The pure tripartite state on `A ⊗ B ⊗ C` with
`dC = dA · dB` whose ket is the same-ancilla purification `(√ρ_AB ⊗ 1)|Ω⟩`. This is an explicit
construction — no existential, no `Classical.choose` — and its `A ⊗ B` marginal recovers `ρ_AB`
(`canonicalPurification_marginalAB_toOp`). -/
def canonicalPurification {dA dB : ℕ} (ρ : DensityOp (dA * dB)) :
    PureTripartite dA dB (dA * dB) where
  ket := sameAncillaPurificationKet ρ
  normalized := by
    rw [sameAncillaPurificationKet,
      sameAncillaPurificationKetOfOp_norm ρ.toOp (posSemidefOp_implies_mathlib ρ.toPosSemidefOp),
      ρ.trace_one]

@[simp] lemma canonicalPurification_ket {dA dB : ℕ} (ρ : DensityOp (dA * dB)) :
    (canonicalPurification ρ).ket = sameAncillaPurificationKet ρ :=
  rfl

/-- **The canonical purification purifies `ρ_AB`:** its `A ⊗ B` marginal is `ρ_AB`. This is
`partialTraceB_sameAncillaPurificationKet` read through the `PureTripartite` packaging. -/
lemma canonicalPurification_marginalAB_toOp {dA dB : ℕ} (ρ : DensityOp (dA * dB)) :
    (canonicalPurification ρ).marginalAB.toOp = ρ.toOp :=
  partialTraceB_sameAncillaPurificationKet ρ

/-- **The canonical-purification dual-form quantity**

`smoothMaxEntropyDual ε ρ := − H_min^ε(A|C)_ρ` ,

where `H_min^ε(A|C)` is the smooth reference-optimized min-entropy
(`smoothBipartiteMinEntropyOptReal`) of the `A ⊗ C` marginal of the canonical purification of
`ρ_AB`.

This definition is not a proof of min–max duality or independence from the purification. Its
identification with the fidelity-form max-entropy API remains unproved. The instance
`NeZero (dA * (dA * dB))` is the nonvanishing of the
`A ⊗ C` register dimension, `C` being the canonical purifying system of dimension `dA · dB`. -/
def smoothMaxEntropyDual {dA dB : ℕ} [NeZero (dA * (dA * dB))]
    (ε : ℝ) (ρ : DensityOp (dA * dB)) : ℝ :=
  - smoothBipartiteMinEntropyOptReal ε
      (DensityOp.toSubDensityOp (canonicalPurification ρ).marginalAC)

/-- At `ε = 0` the dual max-entropy is minus the non-smooth guarded optimized min-entropy of the
`A ⊗ C` marginal: the `H_min^ε` side collapses (`smoothBipartiteMinEntropyOptReal_zero_eq`) and
the sign is inherited. -/
lemma smoothMaxEntropyDual_zero_eq {dA dB : ℕ} [NeZero (dA * (dA * dB))]
    (ρ : DensityOp (dA * dB)) :
    smoothMaxEntropyDual 0 ρ =
      - bipartiteMinEntropyOptReal
          (DensityOp.toSubDensityOp (canonicalPurification ρ).marginalAC) := by
  unfold smoothMaxEntropyDual
  rw [smoothBipartiteMinEntropyOptReal_zero_eq]

/-- **The dual max-entropy is antitone in the smoothing radius.** A larger smoothing ball can only
raise `H_min^ε(A|C)`, hence lower its negation. This is the sign flip of
`smoothBipartiteMinEntropyOptReal_monotone_eps`, and it carries the same `BddAbove` regularity
side-condition; `SmoothBipartiteRegularity.lean` discharges that hypothesis for `ε' < 1`. -/
lemma smoothMaxEntropyDual_antitone_eps {dA dB : ℕ} [NeZero (dA * (dA * dB))]
    {ε ε' : ℝ} (hε : 0 ≤ ε) (h : ε ≤ ε') (ρ : DensityOp (dA * dB))
    (hbdd : BddAbove (Set.ofPred (isInSmoothBipartiteMinSet ε'
      (DensityOp.toSubDensityOp (canonicalPurification ρ).marginalAC)))) :
    smoothMaxEntropyDual ε' ρ ≤ smoothMaxEntropyDual ε ρ :=
  neg_le_neg (smoothBipartiteMinEntropyOptReal_monotone_eps hε h _ hbdd)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
