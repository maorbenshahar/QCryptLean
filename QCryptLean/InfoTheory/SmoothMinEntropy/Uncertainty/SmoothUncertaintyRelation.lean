import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementTransport
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SmoothBipartiteRegularity

/-!
# The ε-smooth entropic uncertainty relation for two rank-one projective measurements

The ε-smooth form of the `ε = 0` relation of `MeasurementTransport.lean`:

```
H_min^ε(Z|Z′AB)_ρ  ≤  H_min^ε(X|B)_ρ − q ,        q = log₂(1/c) ,
```

between the ε-smooth guarded reference-optimized conditional min-entropies
(`smoothBipartiteMinEntropyOptReal`, `SmoothBipartite.lean`) of the `Z`-dilated state and the
`X`-measured marginal of `ρ_AB`, for two rank-one projective measurements of `ℂ^d` with overlap
`c = overlapConst P Q`.

## The argument

Each `Z`-side ball member `τ` is pushed through the measurement sub-channel
`Ξ = measConjTraceMap (U Vᴴ)`.  Two facts combine:

* **metric transport at the same radius** — `P(ρ_XB, Ξ τ) ≤ P(ρ_ZZ′AB, τ) ≤ ε`
  (`purifiedDistance_xMeasuredMarginal_measDilateTransport_le`), so `Ξ τ` is an `X`-side ball
  member at the *same* `ε`: the smoothing budget is not doubled by the transport; and
* **value transport** — `H_min(τ) + q ≤ H_min(Ξ τ)`
  (`bipartiteMinEntropyOptReal_measDilateTransport_ge`).

Taking the supremum over the `Z`-side ball gives the statement.  Because the repository's purified
distance is sub-density-native and the generalized-fidelity data-processing inequality applies
directly to `Ξ`, no purification and no Uhlmann ball-lift enters, and hence no purifying-register
dimension caveat.

## Hypotheses, and which of them are theorems

The general form `measDilation_smooth_core_of_regular` keeps exactly the two side-conditions that
are genuinely about the ℝ-valued encoding:

* `hbddX`, boundedness above of the `X`-side smooth optimization set. The unformalized endpoint
  argument in the documentation of `SmoothBipartiteRegularity.lean` explains the issue at `ε ≥ 1`.
* `hne`, nonvanishing of each `Z`-side ball member and of its image.  The image condition is not
  automatic: `W = U Vᴴ` annihilates the orthogonal complement of the range of the `Z`-dilation.

For a **normalized** `ρ_AB` and `0 ≤ ε < 1` both are theorems, and `measDilation_smooth_core`
carries
neither: ball members of a normalized centre have trace at least `1 − ε²`
(`ne_zero_of_purifiedDistance_of_normalized`), the dilation and the measured marginal preserve the
trace, and metric transport moves the normalization to the `X` side.  The overlap positivity
`0 < c` is `overlapConst_pos` throughout, never a hypothesis.

## Scope

As in `MeasurementTransport.lean`, this is the dual-form inequality
arXiv:1504.00233, `apps.tex:198`, `\label{eq:ucr-dual}` at `α = ∞`, smoothed; it is
**not** the tripartite relation `th:ur` (`apps.tex:183–192`), whose derivation additionally
consumes the min–max duality `pr:dual-new`.  The cited textbook states at `apps.tex:467` that
tripartite relations "in the spirit of" that section also hold for smooth min- and max-entropies,
citing Tomamichel–Renner (arXiv:1009.2015); the smooth
statement proved here is the dual form, obtained by the explicit operator algebra rather than from
that citation.

## Main statements

* `InfoTheory.SmoothMinEntropy.measDilation_smooth_core_of_regular`
* `InfoTheory.SmoothMinEntropy.measDilation_smooth_core`
-/

open Quantum.Operators Quantum.TensorProducts
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **The ε-smooth uncertainty relation, general form.**

`H_min^ε(Z|Z′AB)_ρ ≤ H_min^ε(X|B)_ρ − q` for an arbitrary sub-normalized `ρ_AB`, given the two
encoding side-conditions: the `X`-side smooth optimization set is bounded above (`hbddX`), and
every `Z`-side ball member and its measurement image are nonzero (`hne`). Both are discharged for
a normalized `ρ_AB` and `ε < 1` in `measDilation_smooth_core`. -/
theorem measDilation_smooth_core_of_regular {d dB : ℕ} [NeZero d] [NeZero dB]
    (P Q : RankOneProjectiveBasis d) (ρAB : SubDensityOp (d * dB)) {ε : ℝ} (hε : 0 ≤ ε)
    (hbddX : BddAbove (Set.ofPred (isInSmoothBipartiteMinSet ε (xMeasuredMarginal P ρAB))))
    (hne : ∀ τ : SubDensityOp (d * (d * d * dB)),
      purifiedDistance (zDilatedState Q ρAB) τ ≤ ε →
      τ.toOp ≠ 0 ∧ (measDilateTransport P Q τ).toOp ≠ 0) :
    smoothBipartiteMinEntropyOptReal ε (zDilatedState Q ρAB) ≤
      smoothBipartiteMinEntropyOptReal ε (xMeasuredMarginal P ρAB) - P.preparationQuality Q := by
  rw [show smoothBipartiteMinEntropyOptReal ε (zDilatedState Q ρAB)
        = sSup (Set.ofPred (isInSmoothBipartiteMinSet ε (zDilatedState Q ρAB))) from rfl]
  apply csSup_le (smoothBipartiteMinSet_nonempty hε (zDilatedState Q ρAB))
  rintro hZval ⟨τ, hdist, rfl⟩
  obtain ⟨hτ, hΞτ⟩ := hne τ hdist
  have hval := bipartiteMinEntropyOptReal_measDilateTransport_ge P Q τ hτ hΞτ
  have hmetric : purifiedDistance (xMeasuredMarginal P ρAB) (measDilateTransport P Q τ) ≤ ε :=
    le_trans (purifiedDistance_xMeasuredMarginal_measDilateTransport_le P Q ρAB τ) hdist
  have hballX : bipartiteMinEntropyOptReal (measDilateTransport P Q τ) ≤
      smoothBipartiteMinEntropyOptReal ε (xMeasuredMarginal P ρAB) :=
    smoothBipartiteMinEntropyOptReal_ge_of_mem_ball ε (xMeasuredMarginal P ρAB)
      (measDilateTransport P Q τ) hbddX hmetric
  linarith [hval, hballX]

/-- **The ε-smooth entropic uncertainty relation** for a normalized state and a smoothing radius
below one:

`H_min^ε(Z|Z′AB)_ρ ≤ H_min^ε(X|B)_ρ − q` ,   `q = log₂(1/c)` ,   `c = overlapConst P Q` .

No regularity hypothesis is carried. Boundedness of the `X`-side smooth optimization set follows
from `smoothBipartiteMinSet_bddAbove_of_normalized` (the `X`-measured marginal of a normalized
state is normalized, `xMeasuredMarginal_trace`), and the two nonvanishing conditions follow from
`ne_zero_of_purifiedDistance_of_normalized` on the `Z` side and, after metric transport, on the
`X` side.

The endpoint scaling argument in the documentation of `SmoothBipartiteRegularity.lean` explains
why the real-valued optimization ceases to represent the intended entropy at `ε ≥ 1`; that
argument is not a formalized endpoint theorem here. -/
theorem measDilation_smooth_core {d dB : ℕ} [NeZero d] [NeZero dB]
    (P Q : RankOneProjectiveBasis d) (ρAB : SubDensityOp (d * dB)) (hρ : ρAB.trace = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    smoothBipartiteMinEntropyOptReal ε (zDilatedState Q ρAB) ≤
      smoothBipartiteMinEntropyOptReal ε (xMeasuredMarginal P ρAB) - P.preparationQuality Q := by
  have hXnorm : (xMeasuredMarginal P ρAB).trace = 1 := by rw [xMeasuredMarginal_trace]; exact hρ
  have hZnorm : (zDilatedState Q ρAB).trace = 1 := by rw [zDilatedState_trace]; exact hρ
  refine measDilation_smooth_core_of_regular P Q ρAB hε
    (smoothBipartiteMinSet_bddAbove_of_normalized _ hXnorm hε hε1) (fun τ hdist => ⟨?_, ?_⟩)
  · exact ne_zero_of_purifiedDistance_of_normalized _ τ hZnorm hε hε1 hdist
  · exact ne_zero_of_purifiedDistance_of_normalized _ (measDilateTransport P Q τ) hXnorm hε hε1
      (le_trans (purifiedDistance_xMeasuredMarginal_measDilateTransport_le P Q ρAB τ) hdist)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
