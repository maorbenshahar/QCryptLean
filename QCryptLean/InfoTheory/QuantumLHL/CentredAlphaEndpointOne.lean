import QCryptLean.InfoTheory.QuantumLHL.SchattenAlpha
import QCryptLean.InfoTheory.QuantumLHL.UniformOutputBlock

/-!
# The `α = 1` endpoint of the Rényi-α leftover-hash moment inequality

The `α = 1` endpoint of the Rényi-α leftover-hash moment inequality, together with the
coefficient row-sum it rests on. These are the two objects
that the Riesz–Thorin interpolation consumes at the exponent `α = 1`;
the `α = 2` endpoint is the
`QuantumHashFamily.IsUniversal2Star.centred_second_moment`.

## The content

Write `c := 1/|Z|` and let the **centred bin operator** be
```
  W s m := (∑_{x : H.hash s x = m} V x) - c • (∑ x, V x).
```
`centred_bin_eq_sum_smul` is the observation that `W s m` is a linear combination of
the `V x` with the **real scalar** coefficients
```
  e s x m := (if H.hash s x = m then (1 : ℝ) else 0) - c,
```
which is exactly the `hWrw` step inside `centred_second_moment`; it is factored out
here so both endpoints share it, and it is what makes the σ-weighted form of the
inequality a corollary with no new content: the conjugation
`V ↦ σ^{-γ} V σ^{-γ}` commutes with a real-scalar linear combination, which is the
`hbin` step of `QuantumHashFamily.IsUniversal2Star.seedAvg_traceNorm_offDiag_le_genRef`.

`abs_coeff_row_sum` evaluates `∑_{s,m} |e s x m|`. For a fixed seed `s` exactly one
output `m` — namely `H.hash s x` — carries the coefficient `1 - c`, and the remaining
`|Z| - 1` carry `-c`, so the row sums to `(1 - c) + (|Z| - 1) c = 2 (1 - c)`. It uses
no collision property of the family, only `Finset.sum_ite_eq`.

`centred_traceNorm_sum_le` is then the `α = 1` endpoint: the trace-norm triangle
inequality `Quantum.Metrics.traceNorm_sum_le` applied per bin, followed by the row
sum. Its constant `2 (1 - 1/|Z|) |S|` is the `1 → 1` operator norm of the centring map
and is attained already at a single nonzero `V x` (with values
`12`, `56`, `240`, `992`, `4032` for the Toeplitz families of `|Z| = 4 … 64`).

Like the row sum, the endpoint holds for an arbitrary `QuantumHashFamily`: exactness
(`QuantumHashFamily.IsUniversal2Star`) is what the `α = 2` endpoint needs, not this one.

## Main declarations
- `centred_bin_eq_sum_smul` : `W s m = ∑ x, (e s x m) • V x`, for an arbitrary real `c`.
- `abs_coeff_row_sum` : `∑ s, ∑ m, |e s x m| = 2 (1 - 1/|Z|) |S|`.
- `centred_traceNorm_sum_le` : `∑ s, ∑ m, ‖W s m‖₁ ≤ 2 (1 - 1/|Z|) |S| ∑ x, ‖V x‖₁`.
-/

open Quantum.Operators Matrix

noncomputable section

namespace InfoTheory.QuantumLHL

/-!
## Step 0 — the centred bin operator as a real linear combination
-/

/-- **The centred bin operator is a real-coefficient linear combination of the `V x`.**
With `e s x m := (if H.hash s x = m then (1 : ℝ) else 0) - c`,
```
  (∑_{x : H.hash s x = m} V x) - c • (∑ x, V x) = ∑ x, (e s x m) • V x .
```
Pure algebra: no property of the hash family, and `c` is an arbitrary real. This is the
`hWrw` step inside `QuantumHashFamily.IsUniversal2Star.centred_second_moment`, factored
out so that the `α = 1` and `α = 2` endpoints of the Rényi-α moment inequality share it. -/
theorem centred_bin_eq_sum_smul {S X Z : Type*} [Fintype X] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S X Z) (V : X → Op n) (c : ℝ) (s : S) (m : Z) :
    (∑ x : X, if H.hash s x = m then V x else 0) - c • (∑ x : X, V x)
      = ∑ x : X, ((if H.hash s x = m then (1 : ℝ) else 0) - c) • V x := by
  have hpt : ∀ x : X, ((if H.hash s x = m then (1 : ℝ) else 0) - c) • V x
      = (if H.hash s x = m then V x else 0) - c • V x := by
    intro x
    by_cases hx : H.hash s x = m
    · simp [hx, sub_smul]
    · simp [hx]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, ← Finset.smul_sum]

/-!
## The coefficient row sum
-/

/-- **Row sum of the centred hash coefficients.** For every input `x`,
```
  ∑ s, ∑ m, |(if H.hash s x = m then (1 : ℝ) else 0) - 1/|Z||  =  2 (1 - 1/|Z|) |S| .
```
For a fixed seed the single output `m = H.hash s x` contributes `1 - 1/|Z|` and the other
`|Z| - 1` outputs contribute `1/|Z|` each, totalling `2 (1 - 1/|Z|)`; summing over seeds
multiplies by `|S|`. No collision property of the family is used.
-/
theorem abs_coeff_row_sum {S X Z : Type*} [Fintype S] [Fintype Z] [DecidableEq Z]
    (H : QuantumHashFamily S X Z) (x : X) :
    ∑ s : S, ∑ m : Z,
        |(if H.hash s x = m then (1 : ℝ) else 0) - 1 / (Fintype.card Z : ℝ)|
      = 2 * (1 - 1 / (Fintype.card Z : ℝ)) * (Fintype.card S : ℝ) := by
  haveI : Nonempty Z := H.outputNonempty
  set c : ℝ := 1 / (Fintype.card Z : ℝ) with hc_def
  have hZ_pos : 0 < (Fintype.card Z : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
  have hZ_ne : (Fintype.card Z : ℝ) ≠ 0 := ne_of_gt hZ_pos
  have hZ_one : (1 : ℝ) ≤ (Fintype.card Z : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
  have hc_nonneg : 0 ≤ c := by rw [hc_def]; positivity
  have hc_le_one : c ≤ 1 := by
    rw [hc_def, div_le_one hZ_pos]; exact hZ_one
  have hZc : (Fintype.card Z : ℝ) * c = 1 := by
    rw [hc_def]; field_simp
  -- Inner sum over the outputs: one hit at `1 - c`, the rest at `c`.
  have hinner : ∀ s : S,
      (∑ m : Z, |(if H.hash s x = m then (1 : ℝ) else 0) - c|) = 2 * (1 - c) := by
    intro s
    have hpt : ∀ m : Z, |(if H.hash s x = m then (1 : ℝ) else 0) - c|
        = (if H.hash s x = m then (1 : ℝ) - 2 * c else 0) + c := by
      intro m
      by_cases hm : H.hash s x = m
      · rw [if_pos hm, if_pos hm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - c)]; ring
      · rw [if_neg hm, if_neg hm, zero_sub, abs_neg, abs_of_nonneg hc_nonneg]; ring
    rw [Finset.sum_congr rfl (fun m _ => hpt m), Finset.sum_add_distrib,
      Finset.sum_ite_eq Finset.univ (H.hash s x) (fun _ => (1 : ℝ) - 2 * c)]
    rw [if_pos (Finset.mem_univ _), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hZc]
    ring
  rw [Finset.sum_congr rfl (fun s _ => hinner s), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-!
## Step 1 — the `α = 1` endpoint
-/

/-- **The `α = 1` endpoint of the Rényi-α leftover-hash moment inequality.** For an
arbitrary `QuantumHashFamily` and arbitrary complex matrix-valued `V : X → Op n`,
```
  ∑ s, ∑ m, ‖(∑_{x : H.hash s x = m} V x) - (1/|Z|) • (∑ x, V x)‖₁
    ≤ 2 (1 - 1/|Z|) |S| · ∑ x, ‖V x‖₁ .
```
The trace-norm triangle inequality on the real-coefficient expansion
`centred_bin_eq_sum_smul`, followed by `abs_coeff_row_sum`. The constant is the `1 → 1`
operator norm of the centring map and is sharp: a single nonzero `V x` turns every
inequality in the proof into an equality.

This is the `α = 1` input of the Riesz–Thorin interpolation, whose `α = 2` input is
`QuantumHashFamily.IsUniversal2Star.centred_second_moment`. -/
theorem centred_traceNorm_sum_le {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {n : ℕ} [NeZero n] (H : QuantumHashFamily S X Z) (V : X → Op n) :
    ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm
        ((∑ x : X, if H.hash s x = m then V x else 0)
          - (1 / (Fintype.card Z : ℝ)) • (∑ x : X, V x))
      ≤ 2 * (1 - 1 / (Fintype.card Z : ℝ)) * (Fintype.card S : ℝ)
          * ∑ x : X, Quantum.Metrics.traceNorm (V x) := by
  set c : ℝ := 1 / (Fintype.card Z : ℝ) with hc_def
  set e : S → X → Z → ℝ := fun s x m => (if H.hash s x = m then (1 : ℝ) else 0) - c
    with he_def
  -- Per bin: triangle inequality on the real-coefficient expansion.
  have hbin : ∀ (s : S) (m : Z),
      Quantum.Metrics.traceNorm ((∑ x : X, if H.hash s x = m then V x else 0)
          - c • (∑ x : X, V x))
        ≤ ∑ x : X, |e s x m| * Quantum.Metrics.traceNorm (V x) := by
    intro s m
    rw [centred_bin_eq_sum_smul H V c s m]
    calc Quantum.Metrics.traceNorm (∑ x : X, (e s x m) • V x)
        ≤ ∑ x : X, Quantum.Metrics.traceNorm ((e s x m) • V x) :=
          Quantum.Metrics.traceNorm_sum_le _ _
      _ = ∑ x : X, |e s x m| * Quantum.Metrics.traceNorm (V x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Complex.coe_smul, Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
          simp
  -- Reorder the triple sum so that `x` is outermost, then apply the row sum.
  have hswap : (∑ s : S, ∑ m : Z, ∑ x : X, |e s x m| * Quantum.Metrics.traceNorm (V x))
      = ∑ x : X, ∑ s : S, ∑ m : Z, |e s x m| * Quantum.Metrics.traceNorm (V x) := by
    rw [Finset.sum_congr rfl (fun s _ => Finset.sum_comm), Finset.sum_comm]
  calc ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm
          ((∑ x : X, if H.hash s x = m then V x else 0) - c • (∑ x : X, V x))
      ≤ ∑ s : S, ∑ m : Z, ∑ x : X, |e s x m| * Quantum.Metrics.traceNorm (V x) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun m _ => hbin s m
    _ = ∑ x : X, ∑ s : S, ∑ m : Z, |e s x m| * Quantum.Metrics.traceNorm (V x) := hswap
    _ = ∑ x : X, (∑ s : S, ∑ m : Z, |e s x m|) * Quantum.Metrics.traceNorm (V x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ x : X, (2 * (1 - c) * (Fintype.card S : ℝ))
          * Quantum.Metrics.traceNorm (V x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [he_def, hc_def, abs_coeff_row_sum H x]
    _ = 2 * (1 - c) * (Fintype.card S : ℝ)
          * ∑ x : X, Quantum.Metrics.traceNorm (V x) := (Finset.mul_sum _ _ _).symm

end InfoTheory.QuantumLHL

end -- noncomputable section
