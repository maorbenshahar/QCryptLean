import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBits.Setup

/-!
# Bit-normalized Renner `thm:Hmincondrep` — Chernoff/MGF budget and discarded-mass bridge

Two results for the bit-normalized (base-2) Renner branch:

* the Cramér–Chernoff smoothing-budget bound — Renner's discarded-mass tail bound
  `iidAEPRtErrorBound` lies below the smoothing budget `ε²/2` for every
  `ε ∈ (0,1)` and `n_copies ≥ 1`, because the optimal-tilt identity
  `δ = 2·log₂(μ)·noiseFactor` cancels the `n_copies`-dependence exactly;
* the weight-cap discarded-mass trace bridge — the CQ trace defect of Renner's
  weight-cap smoothed state `ρ̄` is bounded by `iidAEPRtErrorBound`.

These leaves are assembled into existence theorems that enrich a bit-normalized
spectral-witness setup with the smoothing budget and the trace bridge.
-/

open Quantum.Operators
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Key identity making Renner's optimal tilt cancel the noise factor:
`δ · log 2 / log μ = 2 · noiseFactor`, where `δ = δ_iidAEP_general` and
`μ = iidAEPSpectralRadius ρ σ`.  It follows from
`δ = 2 · logb 2 μ · noiseFactor` and `logb 2 μ = log μ / log 2`. -/
lemma iidAEP_delta_mul_log_two_div_log_spectralRadius_eq_two_mul_noiseFactor
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) :
    δ_iidAEP_general ρ σ n_copies ε * Real.log 2
        / Real.log (iidAEPSpectralRadius ρ σ)
      = 2 * noiseFactor n_copies ε := by
  have hμ2 : (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ :=
    InfoTheory.SmoothMinEntropy.two_le_iidAEPSpectralRadius ρ σ
  have hμpos : 0 < iidAEPSpectralRadius ρ σ := by linarith
  have hlogμ_pos : 0 < Real.log (iidAEPSpectralRadius ρ σ) :=
    Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hμ_eq :
      (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2
        = iidAEPSpectralRadius ρ σ := rfl
  unfold δ_iidAEP_general
  rw [hμ_eq, Real.logb]
  field_simp

/-- For `ε ∈ (0,1)` and `1 ≤ n_copies`, Renner's discarded-mass tail bound
`iidAEPRtErrorBound = 2 ^ (−n_copies·δ²/(2·(log₂ μ)²))` (main.tex:4962) lies
below the smoothing budget `ε²/2`. The optimal-tilt identity
`δ = 2·log₂(μ)·noiseFactor` makes the exponent equal `−2·log₂(1/ε) − 2`, so the
bound evaluates to `ε²/4 ≤ ε²/2`. The `n_copies`-dependence cancels exactly
(Renner's `+1`-inside-`/n` design), so no finite-size regime hypothesis is needed. -/
theorem iidAEPBitRtExponentToSmoothingBudget
    {X : Type*} [Fintype X]
    {n : ℕ}
    {ρ : CQState X n}
    {σ : DensityOp n} {n_copies : ℕ} {ε : ℝ}
    {W : IIDAEPSpectralWitness X n n_copies}
    (hε : 0 < ε) (hε_lt_one : ε < 1) (hn : 1 ≤ (n_copies : ℝ)) :
    iidAEPRtExponentToSmoothingBudget ρ σ n_copies ε W := by
  unfold iidAEPRtExponentToSmoothingBudget iidAEPRtErrorBound
    iidAEPSmoothingTraceBudget
  set μ : ℝ := iidAEPSpectralRadius ρ σ with hμ
  set δ : ℝ := δ_iidAEP_general ρ σ n_copies ε with hδ_def
  set nf : ℝ := noiseFactor n_copies ε with hnf_def
  have hμ2 : (2 : ℝ) ≤ μ := InfoTheory.SmoothMinEntropy.two_le_iidAEPSpectralRadius ρ σ
  have hn_pos : (0 : ℝ) < (n_copies : ℝ) := by linarith
  -- `log₂ μ > 0`, so its square is a nonzero denominator.
  have hlogbμ_pos : 0 < Real.logb 2 μ :=
    Real.logb_pos (by norm_num) (by linarith)
  have hlogbμ_sq_pos : 0 < Real.logb 2 μ ^ 2 := by positivity
  -- Renner's δ design: `δ = 2·log₂(μ)·nf`.
  have hδ_eq : δ = 2 * Real.logb 2 μ * nf := by
    rw [hδ_def, hnf_def, hμ]; rfl
  -- The exponent collapses to `−2·n·nf²`.
  have hexp_eq :
      -(n_copies : ℝ) * δ ^ 2 / (2 * Real.logb 2 μ ^ 2)
        = -(2 * (n_copies : ℝ) * nf ^ 2) := by
    rw [hδ_eq]
    field_simp
  rw [hexp_eq]
  -- `nf² = (log₂(1/ε)+1)/n`, so `2·n·nf² = 2·(log₂(1/ε)+1) = 2·log₂(1/ε) + 2`.
  have hlogb_inv_nonneg : 0 ≤ Real.logb 2 ε⁻¹ :=
    Real.logb_nonneg (by norm_num)
      (by rw [le_inv_comm₀ (by norm_num) hε]; linarith)
  have hnf_sq : nf ^ 2 = (Real.logb 2 ε⁻¹ + 1) / (n_copies : ℝ) := by
    rw [hnf_def]; unfold noiseFactor
    rw [Real.sq_sqrt]; positivity
  have hn_ne : (n_copies : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hexp_val :
      -(2 * (n_copies : ℝ) * nf ^ 2)
        = -(2 * Real.logb 2 ε⁻¹) + -(2 : ℝ) := by
    rw [hnf_sq]; field_simp; ring
  rw [hexp_val, Real.rpow_add (by norm_num)]
  -- `2 ^ (−2·log₂(1/ε)) = 2 ^ (2·log₂ ε) = (2 ^ log₂ ε)² = ε²`.
  have hε_term : (2 : ℝ) ^ (-(2 * Real.logb 2 ε⁻¹)) = ε ^ 2 := by
    rw [Real.logb_inv, show -(2 * -Real.logb 2 ε) = Real.logb 2 ε * 2 by ring,
      Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hε,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hε_term]
  -- `2 ^ (−2) = 1/4 ≤ 1/2`, then `ε² · (1/4) ≤ ε² · (1/2) = ε²/2`.
  have htwopow_eq : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hε_sq_nonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
  calc ε ^ 2 * (2 : ℝ) ^ (-(2 : ℝ))
      = ε ^ 2 * (1 / 4) := by rw [htwopow_eq]
    _ ≤ ε ^ 2 * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left (by norm_num) hε_sq_nonneg
    _ = ε ^ 2 / 2 := by ring

/-- Enriches a bit-normalized spectral setup with the nonnegative-branch Chernoff/MGF
smoothing budget: from `∃ W, iidAEPBitSpectralSetup …` it produces
`∃ W, iidAEPBitSpectralSetupWithRtBudget …`. The budget holds unconditionally
for `ε ∈ (0,1)` and `1 ≤ n_copies`. -/
theorem exists_iidAEPBitSpectralSetupWithRtBudget_of_setup
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1)
    (hsetup :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPBitSpectralSetupWithRtBudget ρ hρ_norm σ n_copies ε W := by
  obtain ⟨W, hW⟩ := hsetup
  have hn : 1 ≤ (n_copies : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n_copies)
  refine ⟨W, hW, ?_⟩
  intro hcross
  exact
    { crossing := hcross
      scalar_admissible := iidAEPBitSpectralSetup_rtParameters hW
      exponent_to_smoothing :=
        iidAEPBitRtExponentToSmoothingBudget _hε _hε_lt_one hn }

/-- For Renner's weight-cap smoothed state `ρ̄`, the CQ trace defect
`iidAEPTraceDefect ρ n_copies W = Σ_xs [tr(ρ^{⊗}_xs) − tr(ρ̄_xs)]` equals the
discarded mass `Σ_{(x,z): p_x > λ q_z} p_x |⟨z|x⟩|²` (main.tex:4665–4747); this
result bounds it by Renner's discarded-mass tail bound
`iidAEPRtErrorBound = 2 ^ (−n_copies·δ²/(2·(log₂ μ)²))` (main.tex:4962), the
relaxed Chernoff/MGF `r_t` estimate at the optimal tilt `τ* = −δ·log 2/(log μ)²`.

Load-bearing hypotheses:
* `hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ)` — some finite `λ` with
  `ρ_x ≤ λ·σ` for every `x`, i.e. `supp ρ_x ⊆ supp σ`. This support gate rules out a
  sub-threshold zero-eigenvalue reference block carrying positive discarded mass;
  without it the bound fails (orthogonal rank-one `ρ = P₀`, `σ = P₁`).
* `hpin : iidAEPIsWeightCapSmoothedState ρ n_copies W` — identifies each
  smoothed block with the explicit `weightCapBlockOp`, so the trace defect is the
  genuine discarded mass. Without it `smoothedState` is free (e.g. `0` gives trace
  defect `1`, exceeding the bound).
* hcut.1 (calibration) — pins the separation scale `λ = 2^(−W.entropyThreshold)`
  to the entropy floor by forcing
  `W.entropyThreshold = iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε`,
  matching the discarded mass to the Chernoff bound. Without it `λ` is free: an
  adversary takes `λ → 0`, discarding nearly all mass (e.g. `X = Unit`, `n = 2`,
  `n_copies = 4`, `ρ.stateMap () = 0.9·|0⟩⟨0|`, `σ = ½|0⟩⟨0| + ½|1⟩⟨1|`,
  `entropyThreshold = 10`: defect `≈ 0.8995` exceeds bound `≈ 0.563`). hcut.2 is
  the nonnegative threshold crossing.

This is the quantum-AEP / Cramér–Chernoff content: the per-copy MGF factorizes over
the `n_copies` tensor factors and cancels the per-block entropy contribution against
the Markov threshold factor. -/
theorem iidAEP_weightCapTraceDefect_le_rtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hblock : iidAEPSpectralCutBlockDomination σ n_copies W)
    (hpin : iidAEPIsWeightCapSmoothedState ρ n_copies W)
    (hparams : iidAEPRtParameters ρ σ ε W)
    (hregime : iidAEPLargeBlockRegime n_copies ε)
    (hcut : iidAEPBitSpectralCutCondition ρ hρ_norm σ n_copies ε W) :
    iidAEPTraceDefect ρ n_copies W ≤
      iidAEPRtErrorBound ρ σ n_copies ε W := by
  rw [iidAEP_traceDefect_eq_discardedMass ρ n_copies W hpin]
  exact iidAEP_discardedMass_le_rtErrorBound ρ hρ_norm σ n_copies ε W
    hfeas hreference hblock hparams hregime hcut.1 hcut.2

/-- Enriches a bit-normalized spectral setup carrying the Rt smoothing budget with the
weight-cap discarded-mass trace bridge: from
`∃ W, iidAEPBitSpectralSetupWithRtBudget …` it produces
`∃ W, iidAEPBitSpectralSetupWithRtTraceBridge …`. The support/feasibility
hypothesis `hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ)` (some finite
`λ` with `ρ_x ≤ λ·σ` for all `x`) is threaded into the Chernoff discarded-mass core;
it excludes the orthogonal-support counterexample (`ρ = P₀`, `σ = P₁`). -/
theorem exists_iidAEPBitSpectralSetupWithRtTraceBridge_of_setupWithRtBudget
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hregime : iidAEPLargeBlockRegime n_copies ε)
    (hsetup :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPBitSpectralSetupWithRtBudget ρ hρ_norm σ n_copies ε W) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPBitSpectralSetupWithRtTraceBridge
        ρ hρ_norm σ n_copies ε W := by
  obtain ⟨W, hW⟩ := hsetup
  refine ⟨W, hW, ?_⟩
  intro _hcross
  have hsetup' : iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W :=
    iidAEPBitSpectralSetupWithRtBudget_setup hW
  exact
    iidAEP_weightCapTraceDefect_le_rtErrorBound ρ hρ_norm σ n_copies ε W
      hfeas
      (iidAEPBitSpectralSetup_referenceSpectralDecomposition hsetup')
      (iidAEPBitSpectralSetup_blockDomination hsetup')
      (iidAEPBitSpectralSetup_isWeightCapSmoothedState hsetup')
      (iidAEPBitSpectralSetup_rtParameters hsetup')
      hregime
      (iidAEPBitSpectralSetup_spectralCutCondition hsetup')

/-- Existence of a bit-normalized spectral witness whose setup carries both the
nonnegative-branch Rt smoothing budget and the weight-cap discarded-mass trace
bridge, for `ε ∈ (0,1)`. The support/feasibility hypothesis `hfeas` is threaded into
the trace-bridge's Chernoff core. -/
theorem exists_iidAEPBitSpectralSetupWithRtTraceBridge
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    (ε : ℝ) (_hε : 0 < ε) (_hε_lt_one : ε < 1)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hregime : iidAEPLargeBlockRegime n_copies ε) :
    ∃ W : IIDAEPSpectralWitness X n n_copies,
      iidAEPBitSpectralSetupWithRtTraceBridge
        ρ hρ_norm σ n_copies ε W := by
  have hsetup :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPBitSpectralSetup ρ hρ_norm σ n_copies ε W :=
    exists_iidAEPBitSpectralSetup
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one
  have hbudget :
      ∃ W : IIDAEPSpectralWitness X n n_copies,
        iidAEPBitSpectralSetupWithRtBudget
          ρ hρ_norm σ n_copies ε W :=
    exists_iidAEPBitSpectralSetupWithRtBudget_of_setup
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one hsetup
  exact
    exists_iidAEPBitSpectralSetupWithRtTraceBridge_of_setupWithRtBudget
      ρ hρ_norm σ n_copies ε _hε _hε_lt_one hfeas hregime hbudget

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
