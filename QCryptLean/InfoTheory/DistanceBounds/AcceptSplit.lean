import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.Quantum.Metrics.RectangularPolar

/-!
# Accept-split bound for the generalized trace distance

The CKR de Finetti mixture-split (Christandl-König-Renner 2009, main.tex:268–:401 (\emph{Main
Result}: Theorem `\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328); Nahar,
Tupkary, Zhao, Lütkenhaus, Tan
2024, Eqs. B13-B15) writes the real and ideal privacy-amplification output states as an *accepting*
block plus a small *residual* block, and controls the generalized trace distance of the full states
by the distance of the accepting blocks plus twice the residual budget.

## Main statements
- `abs_trace_re_le_traceNorm`: `|(tr X).re| ≤ ‖X‖₁`.
- `traceDistanceGen_le_traceNorm_sub`: `D(ρ, σ) ≤ ‖ρ − σ‖₁`.
- `traceDistanceGen_le_acceptSplit`: the accept-split bound
  `D(ρReal, ρIdeal) ≤ D(ρReal_acc, ρIdeal_acc) + 2·s` from
  `½‖ρReal_resid‖₁ + ½‖ρIdeal_resid‖₁ ≤ s`.

References:
- Christandl-König-Renner (2009), arXiv:0809.3019, `\label{lem:extractpart}` (main.tex:319–:328):
accept-region split.
- Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), arXiv:2403.11851, Theorem 3, main.tex:1341–:1413
(Appendix B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}`
(main.tex:1356–:1362), the Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed
min-entropy bound `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting
step `\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413): accept
slack.
- Tomamichel (2016), §3.2, eq. (3.23): generalized trace distance for sub-normalized operators.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.CKRPostselection

/-- `|(tr X).re| ≤ ‖X‖₁`: the real part of the trace is bounded by the trace norm.

Trace pairing against the identity (an operator-norm contraction) bounds `‖(tr X)‖` by `‖X‖₁`
(`norm_trace_mul_le_traceNorm_of_opNorm_le_one`), and `|z.re| ≤ ‖z‖` for `z : ℂ`. -/
theorem abs_trace_re_le_traceNorm {d : ℕ} [NeZero d] (X : Op d) :
    |X.trace.re| ≤ traceNorm X := by
  have h1 : |X.trace.re| ≤ ‖X.trace‖ := Complex.abs_re_le_norm _
  have h2 :=
    Quantum.Metrics.RectangularPolar.norm_trace_mul_le_traceNorm_of_opNorm_le_one
      (1 : Op d) X Quantum.Metrics.RectangularPolar.l2_opNorm_one_le
  rw [one_mul] at h2
  exact le_trans h1 h2

/-- `D(ρ, σ) ≤ ‖ρ − σ‖₁`: the generalized trace distance is bounded by the bare trace norm of
the difference.  The trace-gap correction `½|(tr (ρ−σ)).re|` is itself bounded by `½‖ρ−σ‖₁`. -/
theorem traceDistanceGen_le_traceNorm_sub {d : ℕ} [NeZero d] (ρ σ : Op d) :
    traceDistanceGen ρ σ ≤ traceNorm (ρ - σ) := by
  unfold traceDistanceGen
  have h := abs_trace_re_le_traceNorm (ρ - σ)
  rw [Matrix.trace_sub] at h
  linarith

/-- **Data-processing monotonicity of the generalized trace distance under a CPTP map.**

For a CPTP map `Φ`, `D(Φ ρ, Φ σ) ≤ D(ρ, σ)`: the trace-norm part contracts under `Φ`
(`traceNorm_cptp_contractive_general`, using linearity to write `Φ ρ − Φ σ = Φ (ρ − σ)`), and the
trace-gap part is preserved because `Φ` is trace-preserving.  This is the general data-processing
inequality for the sub-normalized generalized trace distance (Tomamichel 2016, §3.2). -/
theorem traceDistanceGen_cptp_le {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n → Op m) (hΦ : Quantum.Channels.IsCPTP Φ) (ρ σ : Op n) :
    traceDistanceGen (Φ ρ) (Φ σ) ≤ traceDistanceGen ρ σ := by
  obtain ⟨hlin, _, htp⟩ := hΦ
  -- `Φ ρ − Φ σ = Φ (ρ − σ)` by linearity.
  have hsub : Φ ρ - Φ σ = Φ (ρ - σ) := by
    have := hlin.mk' Φ
    simp only [← hlin.mk'_apply, map_sub]
  -- Trace-norm part contracts.
  have hnorm : traceNorm (Φ ρ - Φ σ) ≤ traceNorm (ρ - σ) := by
    rw [hsub]
    exact traceNorm_cptp_contractive_general Φ ⟨hlin, ‹_›, htp⟩ (ρ - σ)
  -- Trace-gap part is preserved (trace preservation).
  have htrace : ((Φ ρ).trace - (Φ σ).trace).re = (ρ.trace - σ.trace).re := by
    rw [htp ρ, htp σ]
  exact traceDistanceGen_le_of_traceNorm_sub_le_of_trace_re_sub_eq hnorm htrace

/-- **Accept-split bound for the generalized trace distance (CKR `lem:extractpart` / Nahar et al.
B13-B15).**

If `ρReal = ρReal_acc + ρReal_resid` and `ρIdeal = ρIdeal_acc + ρIdeal_resid` with the residual
blocks small in combined half-trace-norm, `½‖ρReal_resid‖₁ + ½‖ρIdeal_resid‖₁ ≤ s`, then the
generalized trace distance of the full operators exceeds that of the accepting blocks by at most
`2·s`:
`D(ρReal, ρIdeal) ≤ D(ρReal_acc, ρIdeal_acc) + 2·s`.

Proof: two applications of the triangle inequality `traceDistanceGen_triangle` peel off the residual
distances `D(ρReal, ρReal_acc)` and `D(ρIdeal_acc, ρIdeal)`, each bounded by the corresponding
residual trace norm via `traceDistanceGen_le_traceNorm_sub`; the combined budget is `2·s`. -/
theorem traceDistanceGen_le_acceptSplit {d : ℕ} [NeZero d]
    (ρReal ρReal_acc ρReal_resid ρIdeal ρIdeal_acc ρIdeal_resid : Op d) (s : ℝ)
    (hReal : ρReal = ρReal_acc + ρReal_resid)
    (hIdeal : ρIdeal = ρIdeal_acc + ρIdeal_resid)
    (hs : (1 / 2) * traceNorm ρReal_resid + (1 / 2) * traceNorm ρIdeal_resid ≤ s) :
    traceDistanceGen ρReal ρIdeal ≤ traceDistanceGen ρReal_acc ρIdeal_acc + 2 * s := by
  have t1 := traceDistanceGen_triangle ρReal ρReal_acc ρIdeal
  have t2 := traceDistanceGen_triangle ρReal_acc ρIdeal_acc ρIdeal
  -- `D(ρReal, ρReal_acc) ≤ ‖ρReal_resid‖₁`.
  have b1 : traceDistanceGen ρReal ρReal_acc ≤ traceNorm ρReal_resid := by
    have h := traceDistanceGen_le_traceNorm_sub ρReal ρReal_acc
    have he : ρReal - ρReal_acc = ρReal_resid := by rw [hReal]; abel
    rwa [he] at h
  -- `D(ρIdeal_acc, ρIdeal) = D(ρIdeal, ρIdeal_acc) ≤ ‖ρIdeal_resid‖₁`.
  have b2 : traceDistanceGen ρIdeal_acc ρIdeal ≤ traceNorm ρIdeal_resid := by
    rw [traceDistanceGen_symm]
    have h := traceDistanceGen_le_traceNorm_sub ρIdeal ρIdeal_acc
    have he : ρIdeal - ρIdeal_acc = ρIdeal_resid := by rw [hIdeal]; abel
    rwa [he] at h
  linarith

/-- **Generalized trace distance is exactly invariant under conjugation by a rectangular
left-isometry.**

For `K` a rectangular left-isometry (`Kᴴ * K = 1`), the map `X ↦ K * X * Kᴴ` preserves both
constituents of the generalized trace distance: the trace-norm part by
`traceNorm_isometry_mul_left` (Tomamichel 2016, §3.2 data processing, here an exact equality
because `K` is an isometry onto its range), and the trace-gap part because `tr (K X Kᴴ) = tr X`
(`Kᴴ K = 1`).  Hence

`D(K ρ Kᴴ, K σ Kᴴ) = D(ρ, σ)`.

This is the floor-preservation step of the Nahar et al. 2024 (arXiv:2403.11851) main.tex:1411–:1413
(unlabeled; the closing bound of Theorem 3's proof) purification
identification `EⁿV = R`: the accept-block leftover-hashing distance computed on the smaller
purifying register `EⁿV` (dim `≤ g`) transports to the larger reference register `R` (dim `4^n`)
by the Uhlmann partial isometry **without** any dimension penalty — only the trace-distance number
crosses, never a `maxMixed(R)` dominator. -/
theorem traceDistanceGen_leftIsometryEmbed_eq
    {dSrc dTgt : ℕ} [NeZero dSrc] [NeZero dTgt]
    (K : Matrix (Fin dTgt) (Fin dSrc) ℂ)
    (hK : Kᴴ * K = (1 : Matrix (Fin dSrc) (Fin dSrc) ℂ))
    (ρ σ : Op dSrc) :
    traceDistanceGen (K * ρ * Kᴴ) (K * σ * Kᴴ) = traceDistanceGen ρ σ := by
  unfold traceDistanceGen
  have hsub : K * ρ * Kᴴ - K * σ * Kᴴ = K * (ρ - σ) * Kᴴ := by
    simp [Matrix.mul_sub, Matrix.sub_mul]
  have hnorm : traceNorm (K * ρ * Kᴴ - K * σ * Kᴴ) = traceNorm (ρ - σ) := by
    rw [hsub]
    exact Quantum.Metrics.TraceNormHoelder.traceNorm_isometry_mul_left K (ρ - σ) hK
  have htrρ : (K * ρ * Kᴴ).trace = ρ.trace := by
    rw [Matrix.trace_mul_cycle, hK, Matrix.one_mul]
  have htrσ : (K * σ * Kᴴ).trace = σ.trace := by
    rw [Matrix.trace_mul_cycle, hK, Matrix.one_mul]
  rw [hnorm, htrρ, htrσ]

end InfoTheory.CKRPostselection

end -- noncomputable section
