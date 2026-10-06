import QCryptLean.InfoTheory.QuantumLHL.TwoUniversalExact
import QCryptLean.Quantum.Channels.CPTP.DiamondNorm
import QCryptLean.Quantum.Metrics.TraceNorm.Frobenius

/-!
# Off-diagonal (positivity-free) leftover-hash trace-norm bound

Lean form of Regula–Tomamichel arXiv:2603.04493 Lemma 12 (tightened leftover hash
lemma), Eqs (88)–(95): the seed-averaged trace-norm distance of a hashed cq block
operator from ideal, bounded via the **exact-collision second moment** — positivity
is *never* used; `2*`-universality of the hash family is what forces the centred
off-diagonal collision coefficient to vanish.

## Main declaration
- `QuantumHashFamily.IsUniversal2Star.seedAvg_traceNorm_offDiag_le`:
  ```
  (1/|S|) · ∑ s, ∑ m, ‖(∑_{x: hash s x = m} V x) − (1/|Z|) • Vtot‖₁
    ≤ √( dimE · |Z| · (1 − 1/|Z|) · ∑_x ‖V x‖²_F ).
  ```

## Proof outline
Three Cauchy–Schwarz applications, chained onto the centred second-moment
identity `centred_second_moment`:
1. `‖A‖₁ ≤ √dimE · ‖A‖_F` (`Quantum.Metrics.traceNorm_le_sqrt_dim_mul_sqrt_frobenius`);
2. `∑_{s,m} √‖W‖²_F ≤ √(|S||Z| · ∑_{s,m} ‖W‖²_F)` (Cauchy–Schwarz over bins);
3. `∑_{s,m} ‖W‖²_F = |S| · (1 − 1/|Z|) · ∑_x ‖V x‖²_F` (second moment).
Combining and cancelling `|S|` lands exactly on the stated bound.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

/-- **Cauchy–Schwarz sqrt bound.** For nonnegative `a : ι → ℝ`,
`∑ i, √(a i) ≤ √(|ι| · ∑ i, a i)`. -/
private lemma sum_sqrt_le {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, Real.sqrt (a i) ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, a i) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ))
    (fun i => Real.sqrt (a i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcs
  rw [Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (ha i))] at hcs
  have hnn : 0 ≤ ∑ i, Real.sqrt (a i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  calc ∑ i, Real.sqrt (a i)
      = Real.sqrt ((∑ i, Real.sqrt (a i)) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, a i) := Real.sqrt_le_sqrt hcs

/-- **Nested Cauchy–Schwarz sqrt bound** over a product index. -/
private lemma sum_sum_sqrt_le {α β : Type*} [Fintype α] [Fintype β]
    (a : α → β → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    ∑ i, ∑ j, Real.sqrt (a i j)
      ≤ Real.sqrt (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) * ∑ i, ∑ j, a i j) := by
  have h := sum_sqrt_le (ι := α × β) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.card_prod] at h
  push_cast at h
  exact h

/-- **Abstract seed-averaged trace-norm bound.** For an arbitrary bin operator
`W : S → Z → Op n`,
```
  ∑ s, ∑ m, ‖W s m‖₁ ≤ √( dimE · (|S|·|Z|) · ∑ s, ∑ m, ‖W s m‖²_F ).
```
Combines the sharp `√dimE` trace-norm/Frobenius bound (per bin) with a Cauchy–Schwarz over
the `|S|·|Z|` bins. -/
private lemma seedAvg_traceNorm_le_of_frob {S Z : Type*} [Fintype S] [Fintype Z]
    {n : ℕ} [NeZero n] (W : S → Z → Op n) :
    ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm (W s m)
      ≤ Real.sqrt ((n : ℝ) * ((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
          * ∑ s : S, ∑ m : Z, ((W s m)ᴴ * (W s m)).trace.re) := by
  have hfrob_nonneg : ∀ s m, 0 ≤ ((W s m)ᴴ * (W s m)).trace.re := by
    intro s m
    rw [Quantum.Channels.trace_conjTranspose_mul_self_re]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  -- Step 1: per-bin sharp `√n` trace-norm/Frobenius bound.
  have step1 : ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm (W s m)
      ≤ Real.sqrt n *
          ∑ s : S, ∑ m : Z, Real.sqrt (((W s m)ᴴ * (W s m)).trace.re) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun m _ =>
      Quantum.Metrics.traceNorm_le_sqrt_dim_mul_sqrt_frobenius (W s m)
  -- Step 2: Cauchy–Schwarz over the bins.
  have step2 : ∑ s : S, ∑ m : Z, Real.sqrt (((W s m)ᴴ * (W s m)).trace.re)
      ≤ Real.sqrt (((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
          * ∑ s : S, ∑ m : Z, ((W s m)ᴴ * (W s m)).trace.re) :=
    sum_sum_sqrt_le (fun s m => ((W s m)ᴴ * (W s m)).trace.re) hfrob_nonneg
  calc ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm (W s m)
      ≤ Real.sqrt n *
          ∑ s : S, ∑ m : Z, Real.sqrt (((W s m)ᴴ * (W s m)).trace.re) := step1
    _ ≤ Real.sqrt n *
          Real.sqrt (((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
            * ∑ s : S, ∑ m : Z, ((W s m)ᴴ * (W s m)).trace.re) := by
        exact mul_le_mul_of_nonneg_left step2 (Real.sqrt_nonneg _)
    _ = Real.sqrt ((n : ℝ) * ((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
          * ∑ s : S, ∑ m : Z, ((W s m)ᴴ * (W s m)).trace.re) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        ring

/-- Final algebraic cancellation: `(1/N)·√(nn·(N·Zc)·(N·(cc·Σ))) = √(nn·Zc·cc·Σ)`. -/
private lemma final_alg (N Zc cc sV nn : ℝ) (hN : 0 < N) :
    (1 / N) * Real.sqrt (nn * (N * Zc) * (N * (cc * sV)))
      = Real.sqrt (nn * Zc * cc * sV) := by
  have hval : nn * (N * Zc) * (N * (cc * sV)) = N ^ 2 * (nn * Zc * cc * sV) := by ring
  rw [hval, Real.sqrt_mul (by positivity), Real.sqrt_sq hN.le]
  field_simp

/-- **Off-diagonal (positivity-free) leftover-hash trace-norm bound**
(Regula–Tomamichel arXiv:2603.04493 Lemma 12, Eq. (85)). For an exact
(`2*`-universal) hash family `H` and *arbitrary* complex matrix-valued
`V : X → Op n` (`n = dimE`, `V x = R_{E,x}`),
```
  (1/|S|) · ∑ s, ∑ m, ‖(∑_{x: hash s x = m} V x) − (1/|Z|) • Vtot‖₁
    ≤ √( dimE · |Z| · (1 − 1/|Z|) · ∑_x ‖V x‖²_F ).
```
The reference measure `σ_E = 1_E/dimE` has full support, so no support/weighting
hypothesis is needed; `NeZero n` is the only dimension hypothesis. The `2*`-universality
`h2` is passed straight to `centred_second_moment`, replacing positivity. -/
theorem QuantumHashFamily.IsUniversal2Star.seedAvg_traceNorm_offDiag_le
    {S X Z : Type*} [Fintype S] [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} [NeZero n] {H : QuantumHashFamily S X Z} (h2 : H.IsUniversal2Star)
    (V : X → Op n) :
    (1 / (Fintype.card S : ℝ)) * ∑ s : S, ∑ m : Z,
        Quantum.Metrics.traceNorm ((∑ x : X, if H.hash s x = m then V x else 0)
          - (1 / (Fintype.card Z : ℝ)) • (∑ x : X, V x))
      ≤ Real.sqrt ((n : ℝ) * (Fintype.card Z : ℝ) * (1 - 1 / (Fintype.card Z : ℝ))
          * ∑ x : X, (((V x)ᴴ) * (V x)).trace.re) := by
  have : Nonempty Z := H.outputNonempty
  have : Nonempty S := H.seedNonempty
  have hS_pos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  have hZ_pos : 0 < (Fintype.card Z : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
  -- Abbreviate the bin operator.
  set W : S → Z → Op n := fun s m =>
    (∑ x : X, if H.hash s x = m then V x else 0)
      - (1 / (Fintype.card Z : ℝ)) • (∑ x : X, V x) with hW
  -- centred second-moment identity, packaged as the frobenius bin sum.
  have hsm := h2.centred_second_moment V
  have hF : ∑ s : S, ∑ m : Z, ((W s m)ᴴ * (W s m)).trace.re
      = (Fintype.card S : ℝ) * ((1 - 1 / (Fintype.card Z : ℝ))
          * ∑ x : X, (((V x)ᴴ) * (V x)).trace.re) := by
    have h1 : (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ m : Z, ((W s m)ᴴ * (W s m)).trace.re
        = (1 - 1 / (Fintype.card Z : ℝ)) *
            ∑ x : X, (((V x)ᴴ) * (V x)).trace.re := hsm
    have h2' : (Fintype.card S : ℝ) *
        ((1 / (Fintype.card S : ℝ))
          * ∑ s : S, ∑ m : Z, ((W s m)ᴴ * (W s m)).trace.re)
        = (Fintype.card S : ℝ) * ((1 - 1 / (Fintype.card Z : ℝ))
            * ∑ x : X, (((V x)ᴴ) * (V x)).trace.re) := by rw [h1]
    rwa [← mul_assoc, mul_one_div, div_self hS_ne, one_mul] at h2'
  -- Apply the abstract bound.
  have habs := seedAvg_traceNorm_le_of_frob W
  rw [hF] at habs
  -- Now habs : ∑∑ ‖W‖₁ ≤ √( n · (|S|·|Z|) · (|S| · ((1-1/|Z|)·Σ)) ).
  calc (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm (W s m)
      ≤ (1 / (Fintype.card S : ℝ)) *
          Real.sqrt ((n : ℝ) * ((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
            * ((Fintype.card S : ℝ) * ((1 - 1 / (Fintype.card Z : ℝ))
              * ∑ x : X, (((V x)ᴴ) * (V x)).trace.re))) := by
        exact mul_le_mul_of_nonneg_left habs (by positivity)
    _ = Real.sqrt ((n : ℝ) * (Fintype.card Z : ℝ) * (1 - 1 / (Fintype.card Z : ℝ))
          * ∑ x : X, (((V x)ᴴ) * (V x)).trace.re) :=
        final_alg (Fintype.card S : ℝ) (Fintype.card Z : ℝ)
          (1 - 1 / (Fintype.card Z : ℝ))
          (∑ x : X, (((V x)ᴴ) * (V x)).trace.re) (n : ℝ) hS_pos

end InfoTheory.QuantumLHL

end -- noncomputable section
