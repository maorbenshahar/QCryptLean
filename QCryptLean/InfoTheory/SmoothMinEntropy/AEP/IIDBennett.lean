import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSmoothRankBound
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.BennettScalar

/-!
# Bennett IID entropy floors

Bennett tail bounds control discarded mass in a spectral witness. Its feasible exponential
coefficient yields an extended per-copy smooth entropy rate, retaining signed real penalty
arithmetic.
-/

open Quantum.Operators
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The Bennett parameters -/

/-- **The Bernstein exponent budget** `a = 4·log 2·noiseFactor²`.

`a/2 = 2·log 2·noiseFactor²` is the natural-log exponent per copy that Renner's discarded-mass
budget `ε²/4` allows: `n·(a/2)/log 2 = 2·n·noiseFactor² = 2·log₂(1/ε) + 2`. -/
noncomputable def bennettExponentBudget (n_copies : ℕ) (ε : ℝ) : ℝ :=
  4 * Real.log 2 * noiseFactor n_copies ε ^ 2

/-- **The Bennett tilt width** `w = bennettFactor a`, the unique `w ≥ 0` with
`3w²/(6 + 2w) = a/2`.  Renner's clamped tilt sits at width `min(2·noiseFactor, log 2)`. -/
noncomputable def bennettTiltWidth (n_copies : ℕ) (ε : ℝ) : ℝ :=
  bennettFactor (bennettExponentBudget n_copies ε)

/-- **The Bennett regime** `a ≤ 3/4`, equivalently `w ≤ 1`, equivalently
`n_copies ≥ (16·log 2/3)·(log₂(1/ε) + 1)`.

This is exactly the admissibility gate `v⋆ = log(1 + w) ≤ log 2` of Renner's `lem:rtbound`.
Renner's own `iidAEPLargeBlockRegime` is `noiseFactor ≤ (2 − log 2)/2`, i.e.
`n_copies ≥ 2.3421…·(log₂(1/ε) + 1)`. -/
def iidAEPBennettRegime (n_copies : ℕ) (ε : ℝ) : Prop :=
  bennettExponentBudget n_copies ε ≤ 3 / 4

/-- **Renner's `δ` at the exact tilt**: `δ_Bennett = log₂ μ · bennettTiltWidth`,
`μ = iidAEPSpectralRadius ρ σ = rank + tr(ρ²σ⁻¹) + 2`.

The incumbent `δ_iidAEP_general` is `2·log₂ μ · noiseFactor`; the two differ only in the
width factor, `bennettTiltWidth` against `2·noiseFactor`. -/
noncomputable def δ_iidAEP_bennett
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) (ε : ℝ) : ℝ :=
  Real.logb 2 (iidAEPSpectralRadius ρ σ) * bennettTiltWidth n_copies ε

/-- **The exact Chernoff tilt** `τ⋆ = −log(1 + w)/log μ`.

Unclamped and with no `min`: on the Bennett regime `w ≤ 1` the magnitude `|τ⋆·log μ| =
log(1 + w)` is automatically at most `log 2`, so Renner's `lem:rtbound` gate holds without a
clamp. -/
noncomputable def iidAEPBennettTilt
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) (ε : ℝ) : ℝ :=
  -(Real.log (1 + bennettTiltWidth n_copies ε)
      / Real.log (iidAEPSpectralRadius ρ σ))

/-- **The Bennett discarded-mass tail bound** `2^(−n·(3w²/(6 + 2w))/log 2)`.

The incumbent `iidAEPRtErrorBound` is `2^(−n·δ²/(2·(log₂ μ)²)) = 2^(−n·w²/2)` at Renner's
width; here the Gaussian exponent `w²/2` is replaced by Bernstein's `3w²/(6 + 2w)/log 2`, which
is what the exact tilt actually delivers.  Independent of `ρ`, `σ` and the witness. -/
noncomputable def iidAEPBennettRtErrorBound (n_copies : ℕ) (ε : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(n_copies : ℝ)
    * (3 * bennettTiltWidth n_copies ε ^ 2 / (6 + 2 * bennettTiltWidth n_copies ε))
    / Real.log 2)

/-- Bit-normalized single-copy entropy floor at the Bennett correction. -/
noncomputable def iidAEPBitBennettEntropyFloor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) : ℝ :=
  iidAEPBitEntropyContribution ρ hρ_norm σ - δ_iidAEP_bennett ρ σ n_copies ε

/-- Block-length-scaled bit-normalized entropy floor at the Bennett correction. -/
noncomputable def iidAEPBitBennettBlockEntropyFloor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) : ℝ :=
  (n_copies : ℝ) * iidAEPBitBennettEntropyFloor ρ hρ_norm σ n_copies ε

/-- Scalar tilt conditions for the Bennett `r_t` estimate: the base `μ > 1` and the pin of the
witness tilt to `iidAEPBennettTilt`.  The analogue of `iidAEPRtParameters`. -/
def iidAEPBennettRtParameters
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies) : Prop :=
  1 < iidAEPSpectralRadius ρ σ ∧
    W.rtTilt = iidAEPBennettTilt ρ σ n_copies ε

/-! ## Elementary properties of the Bennett parameters -/

lemma bennettExponentBudget_nonneg (n_copies : ℕ) (ε : ℝ) :
    0 ≤ bennettExponentBudget n_copies ε := by
  unfold bennettExponentBudget
  have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  positivity

lemma bennettTiltWidth_nonneg (n_copies : ℕ) (ε : ℝ) :
    0 ≤ bennettTiltWidth n_copies ε :=
  bennettFactor_nonneg (bennettExponentBudget_nonneg n_copies ε)

/-- On the Bennett regime the tilt width is at most `1`, i.e. `v⋆ ≤ log 2`. -/
lemma bennettTiltWidth_le_one {n_copies : ℕ} {ε : ℝ}
    (hregime : iidAEPBennettRegime n_copies ε) :
    bennettTiltWidth n_copies ε ≤ 1 :=
  bennettFactor_le_one_of_le_three_quarters (bennettExponentBudget_nonneg n_copies ε) hregime

/-- Off the Bennett regime the tilt width is at least `1`. -/
lemma one_le_bennettTiltWidth {n_copies : ℕ} {ε : ℝ}
    (hsmall : ¬ iidAEPBennettRegime n_copies ε) :
    1 ≤ bennettTiltWidth n_copies ε := by
  unfold iidAEPBennettRegime at hsmall
  push_neg at hsmall
  exact one_le_bennettFactor_of_three_quarters_le hsmall.le

/-- **The Bennett correction dominates Renner's on the whole regime.**

`δ_iidAEP_bennett ρ σ n ε ≤ δ_iidAEP_general ρ σ n ε` whenever `bennettTiltWidth ≤ 1`.
Both sides are `log₂ μ` times a width; the widths compare by
`bennettFactor_le_two_mul_of_eq_four_mul_log_two_mul_sq`. -/
theorem δ_iidAEP_bennett_le_general
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) (ε : ℝ) (hregime : iidAEPBennettRegime n_copies ε) :
    δ_iidAEP_bennett ρ σ n_copies ε ≤ δ_iidAEP_general ρ σ n_copies ε := by
  have hμ2 : (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ :=
    two_le_iidAEPSpectralRadius ρ σ
  have hlogb : 0 ≤ Real.logb 2 (iidAEPSpectralRadius ρ σ) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hwidth : bennettTiltWidth n_copies ε ≤ 2 * noiseFactor n_copies ε :=
    bennettFactor_le_two_mul_of_eq_four_mul_log_two_mul_sq
      (Real.sqrt_nonneg _) rfl (bennettTiltWidth_le_one hregime)
  have hgen : δ_iidAEP_general ρ σ n_copies ε
      = Real.logb 2 (iidAEPSpectralRadius ρ σ) * (2 * noiseFactor n_copies ε) := by
    unfold δ_iidAEP_general
    have : (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2
        = iidAEPSpectralRadius ρ σ := rfl
    rw [this]; ring
  rw [δ_iidAEP_bennett, hgen]
  exact mul_le_mul_of_nonneg_left hwidth hlogb

/-- Renner's noise factor is strictly positive for `ε ∈ (0,1)` and `n_copies ≥ 1`: the radicand
`(log₂(1/ε) + 1)/n` is then strictly positive. -/
lemma noiseFactor_pos {n_copies : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε_lt_one : ε < 1) (hn : 1 ≤ (n_copies : ℝ)) :
    0 < noiseFactor n_copies ε := by
  have hlogb_nonneg : 0 ≤ Real.logb 2 ε⁻¹ :=
    Real.logb_nonneg (by norm_num)
      (by rw [le_inv_comm₀ (by norm_num) hε]; linarith)
  have hrad : (0 : ℝ) < (Real.logb 2 ε⁻¹ + 1) / (n_copies : ℝ) := by
    apply div_pos (by linarith) (by linarith)
  unfold noiseFactor
  exact Real.sqrt_pos.mpr hrad

/-- **The Bennett correction is strictly below Renner's on the whole regime.**

`δ_iidAEP_bennett ρ σ n ε < δ_iidAEP_general ρ σ n ε` for `ε ∈ (0,1)`, `n ≥ 1`, on the
Bennett regime.  Strictness comes from `log 2 < 3/4`
(`bennettFactor_lt_two_mul_of_eq_four_mul_log_two_mul_sq`) together with `log₂ μ ≥ 1`, which
holds because Renner's log-argument `μ = rank + tr + 2 ≥ 2`. -/
theorem δ_iidAEP_bennett_lt_general
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : DensityOp n)
    {n_copies : ℕ} {ε : ℝ} (hε : 0 < ε) (hε_lt_one : ε < 1) (hn : 1 ≤ (n_copies : ℝ))
    (hregime : iidAEPBennettRegime n_copies ε) :
    δ_iidAEP_bennett ρ σ n_copies ε < δ_iidAEP_general ρ σ n_copies ε := by
  have hμ2 : (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ :=
    two_le_iidAEPSpectralRadius ρ σ
  have hlogb : (1 : ℝ) ≤ Real.logb 2 (iidAEPSpectralRadius ρ σ) := by
    have h2 : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (iidAEPSpectralRadius ρ σ) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) hμ2
    have hone : Real.logb 2 (2 : ℝ) = 1 := by simp
    rwa [hone] at h2
  have hwidth : bennettTiltWidth n_copies ε < 2 * noiseFactor n_copies ε :=
    bennettFactor_lt_two_mul_of_eq_four_mul_log_two_mul_sq
      (noiseFactor_pos hε hε_lt_one hn) rfl (bennettTiltWidth_le_one hregime)
  have hgen : δ_iidAEP_general ρ σ n_copies ε
      = Real.logb 2 (iidAEPSpectralRadius ρ σ) * (2 * noiseFactor n_copies ε) := by
    unfold δ_iidAEP_general
    have : (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2
        = iidAEPSpectralRadius ρ σ := rfl
    rw [this]; ring
  rw [δ_iidAEP_bennett, hgen]
  exact mul_lt_mul_of_pos_left hwidth (by linarith)

lemma δ_iidAEP_bennett_nonneg
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) (ε : ℝ) :
    0 ≤ δ_iidAEP_bennett ρ σ n_copies ε := by
  have hμ2 : (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ :=
    two_le_iidAEPSpectralRadius ρ σ
  have hlogb : 0 ≤ Real.logb 2 (iidAEPSpectralRadius ρ σ) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  exact mul_nonneg hlogb (bennettTiltWidth_nonneg n_copies ε)

/-- The exact tilt is nonpositive: `log(1 + w) ≥ 0` and `log μ > 0`. -/
lemma iidAEPBennettTilt_nonpos
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) (ε : ℝ) :
    iidAEPBennettTilt ρ σ n_copies ε ≤ 0 := by
  have hμ2 : (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ :=
    two_le_iidAEPSpectralRadius ρ σ
  have hL : 0 < Real.log (iidAEPSpectralRadius ρ σ) := Real.log_pos (by linarith)
  have hw := bennettTiltWidth_nonneg n_copies ε
  have hlog : 0 ≤ Real.log (1 + bennettTiltWidth n_copies ε) :=
    Real.log_nonneg (by linarith)
  unfold iidAEPBennettTilt
  have : 0 ≤ Real.log (1 + bennettTiltWidth n_copies ε)
      / Real.log (iidAEPSpectralRadius ρ σ) := by positivity
  linarith

/-! ## The Chernoff/MGF smoothing budget at the Bennett exponent -/

/-- **The Bennett tail bound meets Renner's discarded-mass budget.**

`iidAEPBennettRtErrorBound n_copies ε ≤ ε²/2` for `ε ∈ (0,1)` and `n_copies ≥ 1`.

`bennettTiltWidth` is by construction the root of `3w²/(6 + 2w) = a/2` with
`a = 4·log 2·noiseFactor²`, so the exponent is `−n·(a/2)/log 2 = −2·n·noiseFactor² =
−2·log₂(1/ε) − 2` and the bound evaluates to `ε²/4`, exactly as the incumbent
`iidAEPBitRtExponentToSmoothingBudget` does.  The `n_copies`-dependence cancels, so no
finite-size regime hypothesis is needed. -/
theorem iidAEPBennettRtErrorBound_le_smoothingTraceBudget
    {n_copies : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε_lt_one : ε < 1) (hn : 1 ≤ (n_copies : ℝ)) :
    iidAEPBennettRtErrorBound n_copies ε ≤ iidAEPSmoothingTraceBudget ε := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn_pos : (0 : ℝ) < (n_copies : ℝ) := by linarith
  have hbern := three_mul_sq_div_bennettFactor (bennettExponentBudget_nonneg n_copies ε)
  -- `3w²/(6 + 2w) = a/2 = 2·log 2·noiseFactor²`
  have hbern' : 3 * bennettTiltWidth n_copies ε ^ 2 / (6 + 2 * bennettTiltWidth n_copies ε)
      = 2 * Real.log 2 * noiseFactor n_copies ε ^ 2 := by
    rw [bennettTiltWidth, hbern, bennettExponentBudget]; ring
  -- `noiseFactor² = (log₂(1/ε) + 1)/n`
  have hnf_sq : noiseFactor n_copies ε ^ 2 = (Real.logb 2 ε⁻¹ + 1) / (n_copies : ℝ) := by
    have hlogb_inv_nonneg : 0 ≤ Real.logb 2 ε⁻¹ :=
      Real.logb_nonneg (by norm_num)
        (by rw [le_inv_comm₀ (by norm_num) hε]; linarith)
    unfold noiseFactor
    rw [Real.sq_sqrt]; positivity
  have hexp_val : -(n_copies : ℝ)
        * (3 * bennettTiltWidth n_copies ε ^ 2 / (6 + 2 * bennettTiltWidth n_copies ε))
        / Real.log 2
      = -(2 * Real.logb 2 ε⁻¹) + -(2 : ℝ) := by
    rw [hbern', hnf_sq]
    field_simp
    ring
  unfold iidAEPBennettRtErrorBound iidAEPSmoothingTraceBudget
  rw [hexp_val, Real.rpow_add (by norm_num)]
  have hε_term : (2 : ℝ) ^ (-(2 * Real.logb 2 ε⁻¹)) = ε ^ 2 := by
    rw [Real.logb_inv, show -(2 * -Real.logb 2 ε) = Real.logb 2 ε * 2 by ring,
      Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hε,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hε_term]
  have htwopow_eq : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hε_sq_nonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
  calc ε ^ 2 * (2 : ℝ) ^ (-(2 : ℝ))
      = ε ^ 2 * (1 / 4) := by rw [htwopow_eq]
    _ ≤ ε ^ 2 * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left (by norm_num) hε_sq_nonneg
    _ = ε ^ 2 / 2 := by ring

/-! ## The single-copy envelope kept exact -/

/-- **Single-copy cumulant bound with `r_t` kept exact.**

`log₂ m(s) ≤ −s·H_bits + (e^{s·log μ} − s·log μ − 1)/log 2`

for `0 ≤ s` in Renner's `lem:rtbound` range `s·log μ ≤ log 2`.  This is
`singleCopy_rt_envelope` (the operator content, reused unchanged) followed by `log x ≤ x − 1`
and the `exp` form of `rt`, **without** the quadratic relaxation `rt ≤ κ·(s·log μ)²` that
`singleCopyMGF_logb_le` performs.

`hrange` is load-bearing for the same reason as in `singleCopy_rt_envelope`: it is the sole
source of the Jensen concavity gate `s ≤ 1/2` there. -/
theorem singleCopyMGF_logb_le_exact
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    {s : ℝ} (hs : 0 ≤ s)
    (hrange : s * Real.log (iidAEPSpectralRadius ρ σ) ≤ Real.log 2) :
    Real.logb 2 (iidAEPSingleCopyMGF ρ σ s)
      ≤ -s * iidAEPBitEntropyContribution ρ hρ_norm σ
        + (Real.exp (s * Real.log (iidAEPSpectralRadius ρ σ))
            - s * Real.log (iidAEPSpectralRadius ρ σ) - 1) / Real.log 2 := by
  classical
  set μ := iidAEPSpectralRadius ρ σ with hμ_def
  set m := iidAEPSingleCopyMGF ρ σ s with hm_def
  set H := iidAEPBitEntropyContribution ρ hρ_norm σ with hH_def
  have hm_pos : 0 < m := iidAEPSingleCopyMGF_pos ρ hρ_norm σ hfeas hs
  have hμ2 : (2 : ℝ) ≤ μ := hμ_def ▸ two_le_iidAEPSpectralRadius ρ σ
  have hμ_pos : (0 : ℝ) < μ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have henv := singleCopy_rt_envelope ρ hρ_norm σ hfeas hs hrange
  have hlog_le : Real.log m ≤ m - 1 := Real.log_le_sub_one_of_pos hm_pos
  have hrt_exp : InfoTheory.SmoothMinEntropy.rt s μ = Real.exp (s * Real.log μ) - s * Real.log μ - 1
      := by
    unfold InfoTheory.SmoothMinEntropy.rt
    rw [Real.rpow_def_of_pos hμ_pos, mul_comm (Real.log μ) s]
  rw [Real.logb, div_le_iff₀ hl2]
  rw [hrt_exp] at henv
  have hexpand : (-s * H
      + (Real.exp (s * Real.log μ) - s * Real.log μ - 1) / Real.log 2) * Real.log 2
      = -s * Real.log 2 * H + (Real.exp (s * Real.log μ) - s * Real.log μ - 1) := by
    field_simp
  rw [hexpand]
  linarith [hlog_le, henv]

/-! ## The Bennett scalar gate -/

/-- **The exact-tilt scalar gate.**  At `v = log(1 + w)`,

`φ(v) − v·w + 3w²/(6 + 2w) ≤ 0`,  `φ(v) = e^v − v − 1`,

for every `w ≥ 0`.  The first two terms sum to `−h(w)` **identically**
(`bennett_tilt_identity`), and `h(w) ≥ 3w²/(6 + 2w)` (`bennettH_ge_bernstein`).

The incumbent's analogue is `collisionMGF_scalar_gate`, which must instead balance the quadratic
envelope's `(1/log 2 − 1/2)·v²` against `w²/2` and therefore loses at both the envelope step
and the clamp. -/
private lemma bennettMGF_scalar_gate {w : ℝ} (hw : 0 ≤ w) :
    Real.exp (Real.log (1 + w)) - Real.log (1 + w) - 1 - Real.log (1 + w) * w
        + 3 * w ^ 2 / (6 + 2 * w) ≤ 0 := by
  rw [bennett_tilt_identity (by linarith : (-1 : ℝ) < w)]
  linarith [bennettH_ge_bernstein hw]

/-! ## The operator-collision MGF tail at the exact tilt -/

/-- **Operator-collision MGF tail bound at the exact tilt.**

`iidAEPCollisionTrace ρ σ N (−W.rtTilt)
  ≤ weightCapScale W ^ (−W.rtTilt) · iidAEPBennettRtErrorBound N ε`.

The analogue of `iidAEPCollisionTrace_le_rtErrorBound`, with three substitutions and no other
change: the single-copy input is `singleCopyMGF_logb_le_exact` (exact `rt`) rather than
`singleCopyMGF_logb_le` (quadratic envelope); the tilt is `iidAEPBennettTilt` rather than
the clamped `iidAEPOptimalTilt`; and the scalar endgame is `bennettMGF_scalar_gate` rather
than `collisionMGF_scalar_gate`.

`hregime` supplies `bennettTiltWidth ≤ 1`, hence `|s·log μ| = log(1 + w) ≤ log 2`, which is
Renner's `lem:rtbound` gate — so no clamp is needed.  `hcalib` calibrates the witness threshold
to `N·(H_bits − δ_Bennett)`, supplying the entropy cancellation; `hfeas` keeps `σ^{−s}` and the
collision moments finite. -/
theorem iidAEPCollisionTrace_le_bennettRtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hparams : iidAEPBennettRtParameters ρ σ n_copies ε W)
    (hregime : iidAEPBennettRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBennettBlockEntropyFloor ρ hρ_norm σ n_copies ε) :
    iidAEPCollisionTrace ρ σ n_copies (-W.rtTilt)
      ≤ weightCapScale W ^ (-W.rtTilt)
        * iidAEPBennettRtErrorBound n_copies ε := by
  classical
  have hμ2 : (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ := two_le_iidAEPSpectralRadius ρ σ
  have hLpos : 0 < Real.log (iidAEPSpectralRadius ρ σ) := Real.log_pos (by linarith)
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hw_nonneg : 0 ≤ bennettTiltWidth n_copies ε := bennettTiltWidth_nonneg n_copies ε
  have hw_le : bennettTiltWidth n_copies ε ≤ 1 := bennettTiltWidth_le_one hregime
  have hv_nonneg : 0 ≤ Real.log (1 + bennettTiltWidth n_copies ε) :=
    Real.log_nonneg (by linarith)
  have hv_le : Real.log (1 + bennettTiltWidth n_copies ε) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (by linarith)
  set s : ℝ := -W.rtTilt with hsdef
  have hs_eq : s = Real.log (1 + bennettTiltWidth n_copies ε)
      / Real.log (iidAEPSpectralRadius ρ σ) := by
    rw [hsdef, hparams.2, iidAEPBennettTilt, neg_neg]
  have hs_nonneg : (0 : ℝ) ≤ s := by rw [hs_eq]; positivity
  have hv_eq : s * Real.log (iidAEPSpectralRadius ρ σ)
      = Real.log (1 + bennettTiltWidth n_copies ε) := by
    rw [hs_eq, div_mul_cancel₀ _ (ne_of_gt hLpos)]
  have hrange : s * Real.log (iidAEPSpectralRadius ρ σ) ≤ Real.log 2 := by
    rw [hv_eq]; exact hv_le
  rw [iidAEPCollisionTrace_eq_singleCopyMGF_pow ρ σ n_copies s]
  have hbound := singleCopyMGF_logb_le_exact ρ hρ_norm σ hfeas hs_nonneg hrange
  have hm_nonneg := iidAEPSingleCopyMGF_nonneg ρ σ s
  set m := iidAEPSingleCopyMGF ρ σ s with hmdef
  set bnd := -s * iidAEPBitEntropyContribution ρ hρ_norm σ
      + (Real.exp (s * Real.log (iidAEPSpectralRadius ρ σ))
          - s * Real.log (iidAEPSpectralRadius ρ σ) - 1) / Real.log 2 with hbnddef
  have hm_le : m ≤ (2 : ℝ) ^ bnd := by
    rcases eq_or_lt_of_le hm_nonneg with hm0 | hmpos
    · rw [← hm0]; positivity
    · calc m = (2 : ℝ) ^ Real.logb 2 m :=
            (Real.rpow_logb (by norm_num) (by norm_num) hmpos).symm
        _ ≤ (2 : ℝ) ^ bnd := Real.rpow_le_rpow_of_exponent_le (by norm_num) hbound
  have hRHS : weightCapScale W ^ s * iidAEPBennettRtErrorBound n_copies ε
      = (2 : ℝ) ^ (-W.entropyThreshold * s
          + -(n_copies : ℝ)
              * (3 * bennettTiltWidth n_copies ε ^ 2
                  / (6 + 2 * bennettTiltWidth n_copies ε)) / Real.log 2) := by
    simp only [weightCapScale, iidAEPBennettRtErrorBound]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  have hcalib' : W.entropyThreshold
      = (n_copies : ℝ) * (iidAEPBitEntropyContribution ρ hρ_norm σ
          - δ_iidAEP_bennett ρ σ n_copies ε) := by
    rw [hcalib]
    simp only [iidAEPBitBennettBlockEntropyFloor, iidAEPBitBennettEntropyFloor]
  -- `δ_Bennett · s = log(1 + w)·w / log 2`: the `log μ` factors cancel exactly.
  have hds : δ_iidAEP_bennett ρ σ n_copies ε * s
      = Real.log (1 + bennettTiltWidth n_copies ε) * bennettTiltWidth n_copies ε
        / Real.log 2 := by
    rw [δ_iidAEP_bennett, Real.logb, hs_eq]
    field_simp
  -- the scalar endgame
  have hstep : (Real.exp (Real.log (1 + bennettTiltWidth n_copies ε))
          - Real.log (1 + bennettTiltWidth n_copies ε) - 1) / Real.log 2
        - δ_iidAEP_bennett ρ σ n_copies ε * s
        + (3 * bennettTiltWidth n_copies ε ^ 2
            / (6 + 2 * bennettTiltWidth n_copies ε)) / Real.log 2 ≤ 0 := by
    have hcollect : (Real.exp (Real.log (1 + bennettTiltWidth n_copies ε))
          - Real.log (1 + bennettTiltWidth n_copies ε) - 1) / Real.log 2
        - Real.log (1 + bennettTiltWidth n_copies ε) * bennettTiltWidth n_copies ε
          / Real.log 2
        + (3 * bennettTiltWidth n_copies ε ^ 2
            / (6 + 2 * bennettTiltWidth n_copies ε)) / Real.log 2
        = (Real.exp (Real.log (1 + bennettTiltWidth n_copies ε))
            - Real.log (1 + bennettTiltWidth n_copies ε) - 1
            - Real.log (1 + bennettTiltWidth n_copies ε) * bennettTiltWidth n_copies ε
            + 3 * bennettTiltWidth n_copies ε ^ 2
              / (6 + 2 * bennettTiltWidth n_copies ε)) / Real.log 2 := by
      ring
    rw [hds, hcollect]
    exact div_nonpos_of_nonpos_of_nonneg (bennettMGF_scalar_gate hw_nonneg) hl2.le
  have hle : bnd * (n_copies : ℝ)
      ≤ -W.entropyThreshold * s
        + -(n_copies : ℝ)
            * (3 * bennettTiltWidth n_copies ε ^ 2
                / (6 + 2 * bennettTiltWidth n_copies ε)) / Real.log 2 := by
    have hN : (0 : ℝ) ≤ (n_copies : ℝ) := Nat.cast_nonneg _
    have hmulnp : (n_copies : ℝ) *
        ((Real.exp (Real.log (1 + bennettTiltWidth n_copies ε))
              - Real.log (1 + bennettTiltWidth n_copies ε) - 1) / Real.log 2
            - δ_iidAEP_bennett ρ σ n_copies ε * s
            + (3 * bennettTiltWidth n_copies ε ^ 2
                / (6 + 2 * bennettTiltWidth n_copies ε)) / Real.log 2) ≤ 0 := by
      have := mul_le_mul_of_nonneg_left hstep hN
      simpa using this
    have hexpand : (-s * iidAEPBitEntropyContribution ρ hρ_norm σ
            + (Real.exp (Real.log (1 + bennettTiltWidth n_copies ε))
                - Real.log (1 + bennettTiltWidth n_copies ε) - 1) / Real.log 2)
            * (n_copies : ℝ)
          - (-((n_copies : ℝ) * (iidAEPBitEntropyContribution ρ hρ_norm σ
                - δ_iidAEP_bennett ρ σ n_copies ε)) * s
              + -(n_copies : ℝ)
                  * (3 * bennettTiltWidth n_copies ε ^ 2
                      / (6 + 2 * bennettTiltWidth n_copies ε)) / Real.log 2)
        = (n_copies : ℝ) *
            ((Real.exp (Real.log (1 + bennettTiltWidth n_copies ε))
                  - Real.log (1 + bennettTiltWidth n_copies ε) - 1) / Real.log 2
              - δ_iidAEP_bennett ρ σ n_copies ε * s
              + (3 * bennettTiltWidth n_copies ε ^ 2
                  / (6 + 2 * bennettTiltWidth n_copies ε)) / Real.log 2) := by
      ring
    rw [hbnddef, hcalib', hv_eq]
    linarith [hexpand, hmulnp]
  calc m ^ n_copies
      ≤ ((2 : ℝ) ^ bnd) ^ n_copies := pow_le_pow_left₀ hm_nonneg hm_le n_copies
    _ = (2 : ℝ) ^ (bnd * (n_copies : ℝ)) := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ bnd) n_copies,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ (2 : ℝ) ^ (-W.entropyThreshold * s
          + -(n_copies : ℝ)
              * (3 * bennettTiltWidth n_copies ε ^ 2
                  / (6 + 2 * bennettTiltWidth n_copies ε)) / Real.log 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    _ = weightCapScale W ^ s * iidAEPBennettRtErrorBound n_copies ε := hRHS.symm

/-! ## The Cramér–Chernoff chain at the exact tilt -/

/-- **Markov drop of the cap indicator, at any non-positive tilt.**

`iidAEPDiscardedSpectralMass ≤ iidAEPTiltedTailValue` whenever `W.rtTilt ≤ 0`.

The incumbent `iidAEPDiscardedSpectralMass_le_tiltedTailValue` states the same bound with
the tilt sign supplied by `iidAEPRtParameters` (through `iidAEPOptimalTilt_nonpos`);
this variant takes the sign directly, which is what the exact tilt needs.  The proof body is
identical: an `s ≥ 0` Markov drop over the nonnegative witness data, whose only nonelementary
input is the support fact `blockReferenceOverlap_eq_zero_of_referenceEigenvalue_eq_zero`, so
`hfeas` and `hreference` are load-bearing. -/
theorem iidAEPDiscardedSpectralMass_le_tiltedTailValue_of_tilt_nonpos
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (ht : W.rtTilt ≤ 0) :
    iidAEPDiscardedSpectralMass ρ n_copies W
      ≤ iidAEPTiltedTailValue ρ n_copies W := by
  classical
  have hq_nn : ∀ z : Fin (n ^ n_copies), 0 ≤ W.referenceEigenvalue z := hreference.1
  have hPidem := hreference.2.1.1
  have hPherm := hreference.2.1.2.1
  unfold iidAEPDiscardedSpectralMass iidAEPTiltedTailValue
    iidAEPTiltedMGFSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun xs _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun z _ => ?_)
  exact chernoff_termwise_bound
    (blockEigenvalue ρ n_copies xs x)
    (blockReferenceOverlap ρ n_copies W xs x z)
    (weightCapScale W)
    (W.referenceEigenvalue z)
    W.rtTilt
    (blockEigenvalue_nonneg ρ n_copies xs x)
    (blockReferenceOverlap_nonneg ρ n_copies W hPidem hPherm xs x z)
    (weightCapScale_pos W)
    (hq_nn z) ht
    (fun hp0 hq0 => blockReferenceOverlap_eq_zero_of_referenceEigenvalue_eq_zero
      ρ σ n_copies W hfeas hreference xs x z hp0 hq0)

/-- Renner's tilted MGF spectral sum at the exact tilt is bounded by
`λ^(−W.rtTilt) · iidAEPBennettRtErrorBound`.  The eigenbasis sum is rewritten to the
operator collision trace by `iidAEPTiltedMGFSum_eq_collisionTrace` (reused unchanged) and
the operator bound is `iidAEPCollisionTrace_le_bennettRtErrorBound`. -/
theorem iidAEPTiltedMGFSum_le_bennettRtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hparams : iidAEPBennettRtParameters ρ σ n_copies ε W)
    (hregime : iidAEPBennettRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBennettBlockEntropyFloor ρ hρ_norm σ n_copies ε) :
    iidAEPTiltedMGFSum ρ n_copies W (-W.rtTilt)
      ≤ weightCapScale W ^ (-W.rtTilt)
        * iidAEPBennettRtErrorBound n_copies ε := by
  rw [iidAEPTiltedMGFSum_eq_collisionTrace ρ σ n_copies W hreference]
  exact iidAEPCollisionTrace_le_bennettRtErrorBound
    ρ hρ_norm σ n_copies ε W hfeas hparams hregime hcalib

/-- The tilted tail value `λ^t · M(−t)` at the exact tilt is bounded by the Bennett error
term; the two powers of `λ` cancel. -/
theorem iidAEPTiltedTailValue_le_bennettRtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hparams : iidAEPBennettRtParameters ρ σ n_copies ε W)
    (hregime : iidAEPBennettRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBennettBlockEntropyFloor ρ hρ_norm σ n_copies ε) :
    iidAEPTiltedTailValue ρ n_copies W
      ≤ iidAEPBennettRtErrorBound n_copies ε := by
  have hmgf := iidAEPTiltedMGFSum_le_bennettRtErrorBound
    ρ hρ_norm σ n_copies ε W hfeas hreference hparams hregime hcalib
  have hpos : (0 : ℝ) < weightCapScale W := weightCapScale_pos W
  unfold iidAEPTiltedTailValue
  calc
    weightCapScale W ^ W.rtTilt * iidAEPTiltedMGFSum ρ n_copies W (-W.rtTilt)
        ≤ weightCapScale W ^ W.rtTilt
            * (weightCapScale W ^ (-W.rtTilt)
              * iidAEPBennettRtErrorBound n_copies ε) :=
          mul_le_mul_of_nonneg_left hmgf (Real.rpow_nonneg hpos.le _)
    _ = iidAEPBennettRtErrorBound n_copies ε := by
          rw [← mul_assoc, ← Real.rpow_add hpos]
          simp

/-- **Cramér–Chernoff tail at the exact tilt**: the discarded spectral mass is bounded by
`iidAEPBennettRtErrorBound`. -/
theorem iidAEPDiscardedSpectralMass_le_bennettRtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hparams : iidAEPBennettRtParameters ρ σ n_copies ε W)
    (hregime : iidAEPBennettRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBennettBlockEntropyFloor ρ hρ_norm σ n_copies ε) :
    iidAEPDiscardedSpectralMass ρ n_copies W
      ≤ iidAEPBennettRtErrorBound n_copies ε := by
  have ht : W.rtTilt ≤ 0 := by
    rw [hparams.2]; exact iidAEPBennettTilt_nonpos ρ σ n_copies ε
  calc
    iidAEPDiscardedSpectralMass ρ n_copies W
        ≤ iidAEPTiltedTailValue ρ n_copies W :=
          iidAEPDiscardedSpectralMass_le_tiltedTailValue_of_tilt_nonpos
            ρ σ n_copies W hfeas hreference ht
    _ ≤ iidAEPBennettRtErrorBound n_copies ε :=
          iidAEPTiltedTailValue_le_bennettRtErrorBound
            ρ hρ_norm σ n_copies ε W hfeas hreference hparams hregime hcalib

/-- **The weight-cap trace defect is bounded by the Bennett tail term.**

The analogue of `iidAEP_weightCapTraceDefect_le_rtErrorBound`.  `hpin` identifies the smoothed
state with the weight-cap state (so the trace defect *is* Renner's discarded mass), `hcalib`
pins the separation scale `λ = 2^(−T)` to the Bennett entropy floor, and `hfeas` is the support
gate that rules out the orthogonal-support counterexample (`ρ = P₀`, `σ = P₁`). -/
theorem iidAEP_weightCapTraceDefect_le_bennettRtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hpin : iidAEPIsWeightCapSmoothedState ρ n_copies W)
    (hparams : iidAEPBennettRtParameters ρ σ n_copies ε W)
    (hregime : iidAEPBennettRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBennettBlockEntropyFloor ρ hρ_norm σ n_copies ε) :
    iidAEPTraceDefect ρ n_copies W ≤ iidAEPBennettRtErrorBound n_copies ε := by
  rw [iidAEP_traceDefect_eq_discardedMass ρ n_copies W hpin]
  calc
    ∑ xs : Fin n_copies → X,
        ( ((iidAEPTensorState ρ n_copies).stateMap xs).trace
          - (weightCapBlockOp ρ n_copies W xs).trace.re )
      ≤ iidAEPDiscardedSpectralMass ρ n_copies W :=
        iidAEP_discardedOperatorMass_le_discardedSpectralMass
          ρ σ n_copies W hreference
    _ ≤ iidAEPBennettRtErrorBound n_copies ε :=
        iidAEPDiscardedSpectralMass_le_bennettRtErrorBound
          ρ hρ_norm σ n_copies ε W hfeas hreference hparams hregime hcalib

/-! ## The spectral witness at the Bennett threshold and tilt -/

/-- **Existence of Renner's weight-cap spectral witness calibrated to the Bennett floor.**

The witness construction is threshold- and tilt-parametric and is reused unchanged: the
reference-stage witness comes from the same five-stage chain as
`exists_iidAEPBitSpectralSetup`, `iidAEPRennerCutWitness` installs the crossing cut
and weight-cap state at the threshold `T = iidAEPBitBennettBlockEntropyFloor`, and
`iidAEPWitnessWithRtTilt` overwrites only the scalar tilt with
`iidAEPBennettTilt`. -/
theorem exists_iidAEPBitBennettSetup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (hε : 0 < ε) (hε_lt_one : ε < 1) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPReferenceSpectralDecomposition σ n_copies W ∧
        W.entropyThreshold
            = iidAEPBitBennettBlockEntropyFloor ρ hρ_norm σ n_copies ε ∧
        iidAEPNonnegativeThresholdCrossing W ∧
        iidAEPSpectralCutBlockDomination σ n_copies W ∧
        iidAEPIsWeightCapSmoothedState ρ n_copies W ∧
        iidAEPBennettRtParameters ρ σ n_copies ε W := by
  have hcore := exists_iidAEPWitnessProjectorSubstate ρ hρ_norm σ n_copies ε hε hε_lt_one
  have heigen := exists_iidAEPWitnessNonnegReferenceEigenvalues
    ρ hρ_norm σ n_copies ε hε hε_lt_one hcore
  have hincr := exists_iidAEPWitnessOrthogonalIncrements
    ρ hρ_norm σ n_copies ε hε hε_lt_one heigen
  have haction := exists_iidAEPWitnessReferenceSpectralAction
    ρ hρ_norm σ n_copies ε hε hε_lt_one hincr
  obtain ⟨W₀, hW₀⟩ := exists_iidAEPWitnessReferenceSpectralDecomposition
    ρ σ n_copies ε hε hε_lt_one haction
  set T : ℝ := iidAEPBitBennettBlockEntropyFloor ρ hρ_norm σ n_copies ε with hT
  refine ⟨iidAEPWitnessWithRtTilt
      (iidAEPRennerCutWitness ρ n_copies σ W₀ hW₀.2 T)
      (iidAEPBennettTilt ρ σ n_copies ε),
    iidAEPRennerCutWitness_reference ρ n_copies σ W₀ hW₀.2 T,
    rfl,
    iidAEPRennerCutWitness_crossing ρ n_copies σ W₀ hW₀.2 T,
    iidAEPRennerCutWitness_blockDomination ρ n_copies σ W₀ hW₀.2 T,
    iidAEPRennerCutWitness_isWeightCapSmoothedState ρ n_copies σ W₀ hW₀.2 T,
    iidAEPSpectralRadius_one_lt ρ σ, rfl⟩

/-! ## The AEP entropy-floor bound at the Bennett correction -/

/-! ## The i.i.d. smooth AEP at an explicit classical-rank cap -/

/-- **The Bennett `δ` under an explicit classical-rank cap, at the quantum-marginal reference.**

`δ_iidAEP_bennett ρ σ n ε ≤ log₂(r + 3)·bennettTiltWidth n ε` whenever
`ρ.classicalRank ≤ r` and `σ.toOp = ρ.quantumMarginalOp`.

The analogue of `δ_iidAEP_general_le_rankBound`, with the same two inputs: `rank(ρ_A) ≤ r` by
hypothesis and `tr(ρ_{AB}²(id ⊗ σ_B⁻¹)) ≤ 1` by
`CQState.sum_trace_sq_mul_rpowNegOne_re_le_one`, which needs the reference to be the quantum
marginal.  Together Renner's log-argument `rank + tr + 2` is at most `r + 3`. -/
theorem δ_iidAEP_bennett_le_rankBound
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (hσ_eq : σ.toOp = ρ.quantumMarginalOp)
    (n_copies : ℕ) (ε : ℝ) (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    δ_iidAEP_bennett ρ σ n_copies ε ≤
      Real.logb 2 ((r : ℝ) + 3) * bennettTiltWidth n_copies ε := by
  have h_rank1 : 1 ≤ ρ.classicalRank :=
    InfoTheory.SmoothMinEntropy.CQState.classicalRank_filter_pos ρ hρ_norm
  have h_tr_le : ρ.tracedSquareTimesInvFactor σ ≤ 1 :=
    InfoTheory.SmoothMinEntropy.CQState.sum_trace_sq_mul_rpowNegOne_re_le_one ρ hρ_norm σ hσ_eq
  have h_tr_nn : 0 ≤ ρ.tracedSquareTimesInvFactor σ :=
    InfoTheory.SmoothMinEntropy.CQState.sum_trace_sq_mul_rpowNegOne_re_nonneg ρ hρ_norm σ hσ_eq
  have h_rank1R : (1 : ℝ) ≤ (ρ.classicalRank : ℝ) := by exact_mod_cast h_rank1
  have h_rankR : (ρ.classicalRank : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrank
  have hμ_eq : iidAEPSpectralRadius ρ σ
      = (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2 := rfl
  have hpos : (0 : ℝ) < iidAEPSpectralRadius ρ σ := by rw [hμ_eq]; linarith
  have hle : iidAEPSpectralRadius ρ σ ≤ (r : ℝ) + 3 := by rw [hμ_eq]; linarith
  have hlog : Real.logb 2 (iidAEPSpectralRadius ρ σ) ≤ Real.logb 2 ((r : ℝ) + 3) :=
    Real.logb_le_logb_of_le (by norm_num) hpos hle
  exact mul_le_mul_of_nonneg_right hlog (bennettTiltWidth_nonneg n_copies ε)

/-- Outside the Bennett regime, the correction makes the feasible bit floor nonpositive. -/
theorem iidAEPBitBennettEntropyFloor_nonpos_of_not_bennettRegime
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hregime : ¬ iidAEPBennettRegime n_copies ε) :
    iidAEPBitBennettEntropyFloor ρ hρ_norm σ n_copies ε ≤ 0 := by
  have hH := iidAEPBitEntropyContribution_le_logb_classicalRank ρ hρ_norm σ hfeas
  have hrank : (1 : ℝ) ≤ (ρ.classicalRank : ℝ) := by
    exact_mod_cast ρ.classicalRank_filter_pos hρ_norm
  have htr := tracedSquareTimesInvFactor_nonneg ρ σ
  have hlog : Real.logb 2 (ρ.classicalRank : ℝ) ≤
      Real.logb 2 (iidAEPSpectralRadius ρ σ) := by
    apply Real.logb_le_logb_of_le (by norm_num) (by linarith)
    unfold iidAEPSpectralRadius
    linarith
  have hlog_nonneg : 0 ≤ Real.logb 2 (iidAEPSpectralRadius ρ σ) :=
    Real.logb_nonneg (by norm_num) (le_trans (by norm_num) (two_le_iidAEPSpectralRadius ρ σ))
  have hwidth := one_le_bennettTiltWidth hregime
  unfold iidAEPBitBennettEntropyFloor δ_iidAEP_bennett
  nlinarith

/-- The Bennett AEP floor bounds the extended rate for every positive smoothing radius. -/
theorem iidAEPBitBennettEntropyFloor_le_smoothRate_aep
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies]
    (ε : ℝ) (hε : 0 < ε)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ)) :
    ENNReal.ofReal (iidAEPBitBennettEntropyFloor ρ hρ_norm σ n_copies ε) ≤
      iidAEPSmoothRate ρ σ n_copies ε := by
  by_cases hε_lt_one : ε < 1
  swap
  · rw [iidAEPSmoothRate,
      smoothMinEntropy_eq_top_of_weight_le_eps_sq hε.le _ _ (by
        rw [CQState.tensorPower_sum_trace ρ hρ_norm]
        nlinarith), ENNReal.top_div_of_ne_top (by simp)]
    exact le_top
  by_cases hregime : iidAEPBennettRegime n_copies ε
  swap
  · rw [ENNReal.ofReal_eq_zero.mpr
      (iidAEPBitBennettEntropyFloor_nonpos_of_not_bennettRegime
        ρ hρ_norm σ n_copies ε hfeas hregime)]
    exact bot_le
  obtain ⟨W, href, hthr, _, hblock, hpin, hparams⟩ :=
    exists_iidAEPBitBennettSetup ρ hρ_norm σ n_copies ε hε hε_lt_one
  have hn : 1 ≤ (n_copies : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n_copies)
  have htrace := iidAEP_weightCapTraceDefect_le_bennettRtErrorBound
    ρ hρ_norm σ n_copies ε W hfeas href hpin hparams hregime hthr
  have hbudget := iidAEPBennettRtErrorBound_le_smoothingTraceBudget
    (n_copies := n_copies) hε hε_lt_one hn
  have htrace_budget := htrace.trans hbudget
  have hpd := iidAEP_weightCap_purifiedDistance_le_sqrt_two_mul_traceDefect
    ρ σ n_copies W href hpin
  have h_smooth :
      CQState.purifiedDistance (iidAEPTensorState ρ n_copies) W.smoothedState ≤ ε := by
    refine hpd.trans ?_
    rw [← iidAEP_sqrt_two_mul_smoothingTraceBudget hε.le]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htrace_budget (by norm_num))
  apply iidAEPSmoothRate_ge_of_blockFloor_le ρ σ n_copies ε _ W.smoothedState h_smooth
  have h_entropy := iidAEP_entropy_from_reference_domination σ n_copies W
    (iidAEP_spectral_cut_feasible_domination σ n_copies W hblock)
  rw [hthr] at h_entropy
  exact h_entropy

/-- The extended classical AEP rate at the Bennett correction and an explicit rank cap. -/
theorem iidAEPClassical_bit_normalized_rankBoundBennett
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (n_copies : ℕ) [NeZero n_copies]
    (ε : ℝ) (hε : 0 < ε)
    (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    ENNReal.ofReal
      (((vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)) / Real.log 2)
        - Real.logb 2 ((r : ℝ) + 3) * bennettTiltWidth n_copies ε) ≤
      iidAEPSmoothRate ρ (ρ.quantumMarginalDensityOp hρ_norm) n_copies ε := by
  let ρ_B := ρ.quantumMarginalDensityOp hρ_norm
  have hδ := δ_iidAEP_bennett_le_rankBound ρ hρ_norm ρ_B rfl n_copies ε r hrank
  have hAEP := iidAEPBitBennettEntropyFloor_le_smoothRate_aep
    ρ hρ_norm ρ_B n_copies ε hε
    (hasFeasibleLambda_quantumMarginalDensityOp ρ hρ_norm)
  refine (ENNReal.ofReal_le_ofReal ?_).trans hAEP
  unfold iidAEPBitBennettEntropyFloor iidAEPBitEntropyContribution
  rw [InfoTheory.RelativeEntropy.relativeEntropyReal_self]
  simp only [sub_zero]
  exact sub_le_sub_left hδ _

/-- The completed Bennett rank-capped block floor bounds extended smooth entropy. -/
theorem iid_smoothHmin_lower_bound_bit_normalized_rankBoundBennett
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (n_copies : ℕ) [NeZero n_copies]
    (ε : ℝ) (hε : 0 < ε)
    (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    ENNReal.ofReal ((n_copies : ℝ) *
      (((vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)) / Real.log 2)
        - Real.logb 2 ((r : ℝ) + 3) * bennettTiltWidth n_copies ε)) ≤
      smoothMinEntropy ε (CQState.tensorPower ρ n_copies)
        (SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hρ_norm)) n_copies) := by
  exact (ofReal_le_iidAEPSmoothRate_iff
    ρ (ρ.quantumMarginalDensityOp hρ_norm) n_copies ε _).mp
      (iidAEPClassical_bit_normalized_rankBoundBennett
        ρ hρ_norm n_copies ε hε r hrank)


/-- A smoothing witness with signed conditional entropy at least `n_copies * F` gives a signed
entropy rate of at least `F`. -/
theorem iidAEPSmoothRateReal_ge_of_blockFloor_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (F : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hbdd : BddAbove (setOf (isInSmoothedSetReal ε
      (iidAEPTensorState ρ n_copies)
      (iidAEPTensorReference σ n_copies))))
    (h_smooth :
      CQState.purifiedDistance (iidAEPTensorState ρ n_copies) W.smoothedState ≤ ε)
    (h_entropy : (n_copies : ℝ) * F ≤
      conditionalMinEntropyReal W.smoothedState (iidAEPTensorReference σ n_copies)) :
    F ≤ iidAEPSmoothRateReal ρ σ n_copies ε := by
  have h_candidate_le_smooth :
      conditionalMinEntropyReal W.smoothedState
          (iidAEPTensorReference σ n_copies) ≤
        smoothMinEntropyReal ε (iidAEPTensorState ρ n_copies)
          (iidAEPTensorReference σ n_copies) :=
    smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove ε
      (iidAEPTensorState ρ n_copies)
      (iidAEPTensorReference σ n_copies)
      (conditionalMinEntropyReal W.smoothedState
        (iidAEPTensorReference σ n_copies))
      W.smoothedState hbdd h_smooth le_rfl
  have hN_pos : (0 : ℝ) < (n_copies : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n_copies))
  have h_inv_nonneg : 0 ≤ (1 / (n_copies : ℝ)) := by positivity
  have h_floor_scaled : F ≤ (1 / (n_copies : ℝ)) *
      conditionalMinEntropyReal W.smoothedState
        (iidAEPTensorReference σ n_copies) := by
    have hmul := mul_le_mul_of_nonneg_left h_entropy h_inv_nonneg
    have hcancel : (1 / (n_copies : ℝ)) * ((n_copies : ℝ) * F) = F := by
      field_simp
    rwa [hcancel] at hmul
  have h_smooth_scaled :
      (1 / (n_copies : ℝ)) *
          conditionalMinEntropyReal W.smoothedState
            (iidAEPTensorReference σ n_copies) ≤
        iidAEPSmoothRateReal ρ σ n_copies ε := by
    have hmul := mul_le_mul_of_nonneg_left h_candidate_le_smooth h_inv_nonneg
    simpa [iidAEPSmoothRateReal, iidAEPTensorState,
      iidAEPTensorReference] using hmul
  exact le_trans h_floor_scaled h_smooth_scaled

/-- In the Bennett regime, the signed smooth entropy rate is at least
`iidAEPBitBennettEntropyFloor` against any feasible reference. -/
theorem iidAEPBitBennettEntropyFloor_le_smoothRate_aepReal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (hε : 0 < ε) (hε_lt_one : ε < 1)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hregime : iidAEPBennettRegime n_copies ε) :
    iidAEPBitBennettEntropyFloor ρ hρ_norm σ n_copies ε ≤
      iidAEPSmoothRateReal ρ σ n_copies ε := by
  obtain ⟨W, href, hthr, hcross, hblock, hpin, hparams⟩ :=
    exists_iidAEPBitBennettSetup ρ hρ_norm σ n_copies ε hε hε_lt_one
  have hn : 1 ≤ (n_copies : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n_copies)
  have htensor_norm := iidAEP_tensor_state_normalized ρ hρ_norm n_copies
  have hbdd := smoothMinEntropyReal_bddAbove ε hε_lt_one
      (iidAEPTensorState ρ n_copies)
      (iidAEP_tensor_state_normalized ρ hρ_norm n_copies)
      (iidAEPTensorReference σ n_copies)
  have htrace := iidAEP_weightCapTraceDefect_le_bennettRtErrorBound
    ρ hρ_norm σ n_copies ε W hfeas href hpin hparams hregime hthr
  have hbudget :=
    iidAEPBennettRtErrorBound_le_smoothingTraceBudget (n_copies := n_copies) hε hε_lt_one hn
  have htrace_budget : iidAEPTraceDefect ρ n_copies W ≤ iidAEPSmoothingTraceBudget ε :=
    le_trans htrace hbudget
  have htrace_lt : iidAEPTraceDefect ρ n_copies W < 1 := by
    have h1 := htrace_budget
    unfold iidAEPSmoothingTraceBudget at h1
    nlinarith [hε, hε_lt_one]
  have hweight_pos := iidAEP_smoothed_weight_pos_of_trace_defect_lt_total
    ρ n_copies W htensor_norm htrace_lt
  have hpd_route := iidAEP_weightCap_purifiedDistance_le_sqrt_two_mul_traceDefect
    ρ σ n_copies W href hpin
  have h_smooth :
      CQState.purifiedDistance (iidAEPTensorState ρ n_copies) W.smoothedState ≤ ε := by
    refine le_trans hpd_route ?_
    rw [← iidAEP_sqrt_two_mul_smoothingTraceBudget hε.le]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htrace_budget (by norm_num))
  have hdom := iidAEP_reference_domination_from_spectral_cut
    σ n_copies W hblock hweight_pos
  have hentropy := iidAEP_entropy_from_reference_dominationReal σ n_copies W hdom
  have h_entropy : (n_copies : ℝ) * iidAEPBitBennettEntropyFloor ρ hρ_norm σ n_copies ε ≤
      conditionalMinEntropyReal W.smoothedState (iidAEPTensorReference σ n_copies) := by
    rw [hthr] at hentropy
    exact hentropy
  exact iidAEPSmoothRateReal_ge_of_blockFloor_le ρ σ n_copies ε
    (iidAEPBitBennettEntropyFloor ρ hρ_norm σ n_copies ε) W hbdd h_smooth h_entropy

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
