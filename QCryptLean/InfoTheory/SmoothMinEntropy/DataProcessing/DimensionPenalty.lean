import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Guessing.MinEntropyGuess
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth

/-!
# Signed reference and dimension penalties

Feasible coefficients control signed conditional min-entropy under changes of reference and
dimension. Real logarithmic arithmetic retains negative entropy values that the canonical
`ENNReal` entropy clips to zero.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder Pointwise

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Multiplying the maximally mixed sub-density reference by the dimension gives
the identity operator. -/
lemma maxMixed_dim_smul_toSubDensityOp_toOp_eq_one {d : ℕ} [NeZero d] :
    (Complex.ofReal (d : ℝ)) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp =
      (1 : Op d) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [DensityOp.toSubDensityOp, DensityOp.maxMixed, Matrix.smul_apply,
      Nat.cast_ne_zero.mpr (NeZero.ne d)]
  · simp [DensityOp.toSubDensityOp, DensityOp.maxMixed, Matrix.smul_apply, hij]

/-- Every sub-density operator is dominated by `d` times the maximally mixed
reference. -/
lemma SubDensityOp.opLe_dim_smul_maxMixed {d : ℕ} [NeZero d]
    (sigma : SubDensityOp d) :
    opLe sigma.toOp
      ((Complex.ofReal (d : ℝ)) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp) := by
  rw [maxMixed_dim_smul_toSubDensityOp_toOp_eq_one]
  exact sigma.opLe_one

/-- Feasibility against any sub-density reference transfers to the maximally
mixed reference with scalar cost `d`. -/
lemma isFeasible_maxMixed_of_isFeasible_subDensity
    {X : Type*} [Fintype X] {d : ℕ} [NeZero d]
    (rho : CQState X d) (sigma : SubDensityOp d) {t : ℝ}
    (ht : isFeasible rho sigma t) :
    isFeasible rho (DensityOp.toSubDensityOp (DensityOp.maxMixed d))
      ((d : ℝ) * t) := by
  rcases ht with ⟨ht_nonneg, ht_dom⟩
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  refine ⟨mul_nonneg hd_nonneg ht_nonneg, fun x => ?_⟩
  have h_sigma := sigma.opLe_dim_smul_maxMixed
  have h_scaled := opLe_smul_nonneg ht_nonneg h_sigma
  have h_chain := opLe_trans (ht_dom x) h_scaled
  simpa [smul_smul, Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
    using h_chain

/-- A single feasible scalar against any reference gives a dimension-scaled
upper bound for the maximally mixed feasible optimum. -/
lemma minFeasibleLambda_maxMixed_le_dim_mul_of_isFeasible
    {X : Type*} [Fintype X] {d : ℕ} [NeZero d]
    (rho : CQState X d) (sigma : SubDensityOp d) {t : ℝ}
    (ht : isFeasible rho sigma t) :
    minFeasibleLambda rho (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) ≤
      (d : ℝ) * t := by
  change sInf (Set.ofPred
      (isFeasible rho (DensityOp.toSubDensityOp (DensityOp.maxMixed d)))) ≤
    (d : ℝ) * t
  exact csInf_le
    (minFeasibleLambda_bddBelow rho
      (DensityOp.toSubDensityOp (DensityOp.maxMixed d)))
    (isFeasible_maxMixed_of_isFeasible_subDensity rho sigma ht)

/-- The quadratic form of the identity operator has nonnegative real part:
`0 ≤ Re ⟨v | 1 | v⟩` for every `v` (the identity is PSD). -/
lemma quadraticForm_one_re_nonneg {d : ℕ} (v : Fin d → ℂ) :
    0 ≤ (quadraticForm (1 : Op d) v).re := by
  have h01 : opLe (0 : Op d) (1 : Op d) :=
    opLe_of_posSemidef_sub (by simpa using (Matrix.PosSemidef.one : (1 : Op d).PosSemidef))
  have := h01 v
  simpa [quadraticForm, Matrix.zero_mulVec, dotProduct] using this

/-- **Fixed-maximally-mixed-reference feasible optimum is at most dimension times
the largest classical-outcome weight.**

For any CQ state `ρ` on Eve dimension `d` whose every classical marginal weight is
at most `T`, the feasible optimum against the *fixed* maximally mixed reference
`σ = maxMixed_d = I / d` satisfies `minFeasibleLambda ρ σ ≤ d · T`.

This is the load-bearing single-round step of the BB84 collective floor: against
the fixed `maxMixed_d`, the `−log₂ d` dimension penalty exactly cancels the `d`
factor here, reducing the conditional-min-entropy floor to the PSD trace bound
`λ_max(ρ_E^x) ≤ Tr(ρ_E^x) = classicalMarginal x ≤ T`.

`Nonempty X` is genuinely required: for an empty classical register the feasible
set contains `0`, so `minFeasibleLambda = 0`, and the claim `0 ≤ d · T` would fail
for `T < 0` (which `hT` cannot then exclude). The BB84 call site has
`X = Fin signalDim` (nonempty).

Proof: each block `ρ_E^x = (ρ.stateMap x).toOp` is PSD, hence dominated by
`Tr(ρ_E^x) · 1` (`psd_opLe_trace_re_smul_one`, Bhatia *Matrix Analysis* Ch. III:
`λ_max ≤ Tr` for PSD). Scaling the trace floor up to `T · 1` (since
`Tr = classicalMarginal x ≤ T`) and rewriting `T · 1 = (d·T) · maxMixed_d.toOp`
exhibits `d·T` as a feasible scalar.

References:
- Tomamichel 2016, *Quantum Information Processing with Finite Resources*, Def. 6.2
  (`minFeasibleLambda` SDP formulation `H_min = −log₂ λ*`).
- Bhatia, *Matrix Analysis*, Springer GTM 169, Ch. III (`λ_max(M) ≤ Tr M` for PSD `M`).
- Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024, arXiv:2403.11851, Theorem 3, `\label{eq:condLHL}`
(main.tex:462–:467) (collective floor against the fixed
  maximally-mixed Eve calibration).

This uses a fixed reference; the guessing-probability `Pg` bound is false in the window. -/
lemma minFeasibleLambda_maxMixed_le_dim_mul_maxClassicalWeight
    {X : Type*} [Fintype X] [Nonempty X] {d : ℕ} [NeZero d]
    (ρ : CQState X d) (T : ℝ) (hT : ∀ x : X, ρ.classicalMarginal x ≤ T) :
    minFeasibleLambda ρ (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) ≤
      (d : ℝ) * T := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hT_nonneg : 0 ≤ T := le_trans (ρ.classicalMarginal_nonneg x₀) (hT x₀)
  have hMM := maxMixed_dim_smul_toSubDensityOp_toOp_eq_one (d := d)
  have hfeas :
      isFeasible ρ (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) ((d : ℝ) * T) := by
    refine ⟨mul_nonneg (Nat.cast_nonneg d) hT_nonneg, fun x => ?_⟩
    have hPSD : (ρ.stateMap x).toOp.PosSemidef :=
      posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
    have hblock :
        opLe (ρ.stateMap x).toOp
          (Complex.ofReal (ρ.stateMap x).toOp.trace.re • (1 : Op d)) :=
      psd_opLe_trace_re_smul_one (ρ.stateMap x).toOp hPSD
    have htr_le : (ρ.stateMap x).toOp.trace.re ≤ T := hT x
    have hscale :
        opLe (Complex.ofReal (ρ.stateMap x).toOp.trace.re • (1 : Op d))
          (Complex.ofReal T • (1 : Op d)) := by
      intro v
      rw [quadraticForm_ofReal_smul, quadraticForm_ofReal_smul,
        Complex.mul_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_right htr_le (quadraticForm_one_re_nonneg v)
    have hchain : opLe (ρ.stateMap x).toOp (Complex.ofReal T • (1 : Op d)) :=
      opLe_trans hblock hscale
    have hrw : (Complex.ofReal ((d : ℝ) * T) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp : Op d) =
        Complex.ofReal T • (1 : Op d) := by
      rw [Complex.ofReal_mul, mul_comm, ← smul_eq_mul, smul_assoc, hMM]
    rw [hrw]; exact hchain
  exact minFeasibleLambda_le_of_isFeasible ρ
    (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) hfeas

/-- `d · (1/2) = 2^(−(1 − log₂ d))` for `d ≥ 1`: the dimension factor `d` from
`minFeasibleLambda ≤ d·(1/2)` rewrites exactly as the feasible exponential
`2^(−(1 − log₂ d))` consumed by
`conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k`. -/
lemma half_dim_eq_pow (d : ℕ) [NeZero d] :
    (d : ℝ) * (1 / 2) = (2 : ℝ) ^ (-(1 - Real.log (d : ℝ) / Real.log 2)) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hkey : (2 : ℝ) ^ (Real.log (d : ℝ) / Real.log 2) = d := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hlog2, mul_one, Real.exp_log hd]
  rw [Real.rpow_neg (by norm_num), Real.rpow_sub (by norm_num), Real.rpow_one, hkey]
  field_simp

/-- If every feasible scalar for one min-entropy SDP scales to a feasible
scalar for another, then the corresponding optima satisfy the same bound. -/
lemma minFeasibleLambda_le_mul_of_isFeasible_scaling
    {X Y : Type*} [Fintype X] [Fintype Y] {d e : ℕ}
    (rhoA : CQState X d) (sigmaA : SubDensityOp d)
    (rhoB : CQState Y e) (sigmaB : SubDensityOp e) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hfeasA : hasFeasibleLambda rhoA sigmaA)
    (hscale : ∀ {t : ℝ},
      isFeasible rhoA sigmaA t → isFeasible rhoB sigmaB (c * t)) :
    minFeasibleLambda rhoB sigmaB ≤
      c * minFeasibleLambda rhoA sigmaA := by
  have hsub :
      c • Set.ofPred (isFeasible rhoA sigmaA) ⊆
        Set.ofPred (isFeasible rhoB sigmaB) := by
    rintro _ ⟨t, ht, rfl⟩
    simpa [smul_eq_mul] using hscale ht
  have hscaled_nonempty :
      (c • Set.ofPred (isFeasible rhoA sigmaA) : Set ℝ).Nonempty := by
    obtain ⟨t, ht⟩ := hfeasA
    exact ⟨c • t, ⟨t, ht, rfl⟩⟩
  have hle_scaled :
      sInf (Set.ofPred (isFeasible rhoB sigmaB)) ≤
        sInf (c • Set.ofPred (isFeasible rhoA sigmaA) : Set ℝ) :=
    csInf_le_csInf (minFeasibleLambda_bddBelow rhoB sigmaB)
      hscaled_nonempty hsub
  have hscaled_inf :
      sInf (c • Set.ofPred (isFeasible rhoA sigmaA) : Set ℝ) =
        c * sInf (Set.ofPred (isFeasible rhoA sigmaA)) := by
    simpa [smul_eq_mul] using
      Real.sInf_smul_of_nonneg hc_nonneg (Set.ofPred (isFeasible rhoA sigmaA))
  calc
    minFeasibleLambda rhoB sigmaB
        = sInf (Set.ofPred (isFeasible rhoB sigmaB)) := rfl
    _ ≤ sInf (c • Set.ofPred (isFeasible rhoA sigmaA) : Set ℝ) := hle_scaled
    _ = c * sInf (Set.ofPred (isFeasible rhoA sigmaA)) := hscaled_inf
    _ = c * minFeasibleLambda rhoA sigmaA := rfl

/-- Feasibility scaling by a positive constant gives the corresponding
real-valued conditional min-entropy comparison.

The positive-lambda side conditions keep the statement on the nondegenerate
branch of `conditionalMinEntropyReal`, where it is exactly logarithmic
arithmetic applied to `minFeasibleLambda_le_mul_of_isFeasible_scaling`. -/
theorem conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling
    {X Y : Type*} [Fintype X] [Fintype Y] {d e : ℕ}
    (rhoA : CQState X d) (sigmaA : SubDensityOp d)
    (rhoB : CQState Y e) (sigmaB : SubDensityOp e) {c : ℝ}
    (hc_pos : 0 < c)
    (hfeasA : hasFeasibleLambda rhoA sigmaA)
    (hlamA_pos : 0 < minFeasibleLambda rhoA sigmaA)
    (hlamB_pos : 0 < minFeasibleLambda rhoB sigmaB)
    (hscale : ∀ {t : ℝ},
      isFeasible rhoA sigmaA t → isFeasible rhoB sigmaB (c * t)) :
    conditionalMinEntropyReal rhoA sigmaA - Real.log c / Real.log 2 ≤
      conditionalMinEntropyReal rhoB sigmaB := by
  let lamA : ℝ := minFeasibleLambda rhoA sigmaA
  let lamB : ℝ := minFeasibleLambda rhoB sigmaB
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hlam_le : lamB ≤ c * lamA := by
    simpa [lamA, lamB] using
      minFeasibleLambda_le_mul_of_isFeasible_scaling
        rhoA sigmaA rhoB sigmaB hc_nonneg hfeasA hscale
  have hlamA_pos' : 0 < lamA := by simpa [lamA] using hlamA_pos
  have hlamB_pos' : 0 < lamB := by simpa [lamB] using hlamB_pos
  have hlog_le : Real.log lamB ≤ Real.log (c * lamA) :=
    Real.log_le_log hlamB_pos' hlam_le
  have hlog_mul : Real.log (c * lamA) = Real.log c + Real.log lamA := by
    rw [Real.log_mul hc_pos.ne' hlamA_pos'.ne']
  have hlog_bound : Real.log lamB ≤ Real.log c + Real.log lamA := by
    simpa [hlog_mul] using hlog_le
  have hnum : -Real.log lamA - Real.log c ≤ -Real.log lamB := by
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hdiv :
      (-Real.log lamA - Real.log c) / Real.log 2 ≤
        -Real.log lamB / Real.log 2 :=
    div_le_div_of_nonneg_right hnum hlog2_pos.le
  have harith :
      (-Real.log lamA - Real.log c) / Real.log 2 =
        -Real.log lamA / Real.log 2 - Real.log c / Real.log 2 := by
    ring
  unfold conditionalMinEntropyReal
  change
    -Real.log lamA / Real.log 2 - Real.log c / Real.log 2 ≤
      -Real.log lamB / Real.log 2
  simpa [harith] using hdiv

/-- Same-state reference change by a feasibility scaling `c ≥ 1`, **without** the
positive-lambda side conditions: the degenerate `minFeasibleLambda = 0` branches
are absorbed by the sentinel value of `conditionalMinEntropyReal`.

For a single CQ state `rho` and two references `sigmaA`, `sigmaB`, if every scalar
feasible against `sigmaA` scales by `c` to a feasible scalar against `sigmaB`
(`hscale`) and the source feasible set is nonempty (`hfeasA`), then
`conditionalMinEntropyReal rho sigmaA − log c / log 2 ≤ conditionalMinEntropyReal rho sigmaB`.

The hypothesis `1 ≤ c` (rather than merely `0 < c`) is genuinely necessary in the
degenerate branch: when both optima vanish, both `conditionalMinEntropyReal`
values are the sentinel `0`, so the claim reduces to `−log c / log 2 ≤ 0`, i.e.
`log c ≥ 0`, which fails for `c < 1`.

The shared state `rho` is what makes the degenerate branches close cleanly:
a feasible scalar `0` against either reference means every block `ρ(x) ⪯ 0`, which
is reference-independent, so `minFeasibleLambda rho sigmaA = 0 ↔
minFeasibleLambda rho sigmaB = 0`.  The positive branch is the proved
`conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling`. -/
theorem conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling_sameState
    {X : Type*} [Fintype X] {d : ℕ}
    (rho : CQState X d) (sigmaA sigmaB : SubDensityOp d) {c : ℝ}
    (hc_one : 1 ≤ c)
    (hfeasA : hasFeasibleLambda rho sigmaA)
    (hscale : ∀ {t : ℝ},
      isFeasible rho sigmaA t → isFeasible rho sigmaB (c * t)) :
    conditionalMinEntropyReal rho sigmaA - Real.log c / Real.log 2 ≤
      conditionalMinEntropyReal rho sigmaB := by
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one hc_one
  have hpenalty_nonneg : 0 ≤ Real.log c / Real.log 2 :=
    div_nonneg (Real.log_nonneg hc_one) (Real.log_pos one_lt_two).le
  have hlamA_nonneg : 0 ≤ minFeasibleLambda rho sigmaA := minFeasibleLambda_nonneg rho sigmaA
  have hlamB_nonneg : 0 ≤ minFeasibleLambda rho sigmaB := minFeasibleLambda_nonneg rho sigmaB
  have hlamB_le :
      minFeasibleLambda rho sigmaB ≤ c * minFeasibleLambda rho sigmaA :=
    minFeasibleLambda_le_mul_of_isFeasible_scaling
      rho sigmaA rho sigmaB hc_pos.le hfeasA hscale
  -- A scalar `0` is feasible against one reference iff every block `⪯ 0`, which is
  -- reference-independent; hence `0`-feasibility transfers between the references.
  have hquad_zero_smul : ∀ (σ : SubDensityOp d) (v : Fin d → ℂ),
      (quadraticForm ((Complex.ofReal 0 : ℂ) • σ.toOp) v).re = 0 := by
    intro σ v
    rw [Complex.ofReal_zero, zero_smul]
    unfold quadraticForm
    simp [Matrix.zero_mulVec, dotProduct]
  have hzero_transfer :
      ∀ (σ σ' : SubDensityOp d), isFeasible rho σ 0 → isFeasible rho σ' 0 := by
    intro σ σ' h0
    refine ⟨le_refl 0, fun x v => ?_⟩
    have hx := h0.2 x v
    rw [hquad_zero_smul σ v] at hx
    rw [hquad_zero_smul σ' v]
    exact hx
  by_cases hlamA_pos : 0 < minFeasibleLambda rho sigmaA
  · by_cases hlamB_pos : 0 < minFeasibleLambda rho sigmaB
    · exact
        conditionalMinEntropyReal_sub_log_le_of_isFeasible_scaling
          rho sigmaA rho sigmaB hc_pos hfeasA hlamA_pos hlamB_pos hscale
    · -- `lamB = 0` ⟹ `isFeasible rho sigmaB 0` ⟹ `isFeasible rho sigmaA 0` ⟹
      -- `lamA = 0`, contradicting `0 < lamA`.  So this branch is impossible.
      exfalso
      push Not at hlamB_pos
      have hlamB_zero : minFeasibleLambda rho sigmaB = 0 :=
        le_antisymm hlamB_pos hlamB_nonneg
      have hfeasB : hasFeasibleLambda rho sigmaB :=
        ⟨c * minFeasibleLambda rho sigmaA,
          hscale (isFeasible_minFeasibleLambda_of_hasFeasibleLambda rho sigmaA hfeasA)⟩
      have h0B : isFeasible rho sigmaB 0 := by
        have := isFeasible_minFeasibleLambda_of_hasFeasibleLambda rho sigmaB hfeasB
        rwa [hlamB_zero] at this
      have h0A : isFeasible rho sigmaA 0 := hzero_transfer sigmaB sigmaA h0B
      have hlamA_le0 : minFeasibleLambda rho sigmaA ≤ 0 :=
        minFeasibleLambda_le_of_isFeasible rho sigmaA h0A
      linarith
  · -- `lamA = 0`: source entropy is the sentinel `0`; scaling forces `lamB = 0`.
    push Not at hlamA_pos
    have hlamA_zero : minFeasibleLambda rho sigmaA = 0 :=
      le_antisymm hlamA_pos hlamA_nonneg
    have hlamB_zero : minFeasibleLambda rho sigmaB = 0 :=
      le_antisymm (by simpa [hlamA_zero, mul_zero] using hlamB_le) hlamB_nonneg
    unfold conditionalMinEntropyReal
    rw [hlamA_zero, hlamB_zero, Real.log_zero, neg_zero, zero_div, zero_sub]
    linarith

/-- Replacing an arbitrary feasible reference by the maximally mixed reference
costs at most a factor equal to the Hilbert-space dimension. -/
theorem minFeasibleLambda_maxMixed_le_dim_mul
    {X : Type*} [Fintype X] {d : ℕ} [NeZero d]
    (rho : CQState X d) (sigma : SubDensityOp d)
    (hfeas : hasFeasibleLambda rho sigma) :
    minFeasibleLambda rho (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) ≤
      (d : ℝ) * minFeasibleLambda rho sigma := by
  let sigmaMM : SubDensityOp d := DensityOp.toSubDensityOp (DensityOp.maxMixed d)
  let c : ℝ := d
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact_mod_cast Nat.zero_le d
  have hscale : ∀ {t : ℝ},
      isFeasible rho sigma t → isFeasible rho sigmaMM (c * t) := by
    intro t ht
    have ht_mm :
        isFeasible rho (DensityOp.toSubDensityOp (DensityOp.maxMixed d))
          ((d : ℝ) * t) :=
      isFeasible_maxMixed_of_isFeasible_subDensity rho sigma ht
    simpa [sigmaMM, c] using ht_mm
  simpa [sigmaMM, c] using
    minFeasibleLambda_le_mul_of_isFeasible_scaling
      rho sigma rho sigmaMM hc_nonneg hfeas hscale

/-- A lambda upper bound against any feasible reference transfers to the
maximally mixed reference with dimension factor. -/
lemma minFeasibleLambda_maxMixed_le_dim_mul_of_le
    {X : Type*} [Fintype X] {d : ℕ} [NeZero d]
    (rho : CQState X d) (sigma : SubDensityOp d) {B : ℝ}
    (hfeas : hasFeasibleLambda rho sigma)
    (hbound : minFeasibleLambda rho sigma ≤ B) :
    minFeasibleLambda rho (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) ≤
      (d : ℝ) * B :=
  (minFeasibleLambda_maxMixed_le_dim_mul rho sigma hfeas).trans
    (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg d))

/-- The maximally mixed feasible optimum is bounded by dimension times the
operational guessing probability. -/
lemma minFeasibleLambda_maxMixed_le_dim_mul_povmGuessingProb
    {X : Type*} [Fintype X] {d : ℕ} [NeZero d]
    (rho : CQState X d) (hp : 0 < povmGuessingProb rho) :
    minFeasibleLambda rho (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) ≤
      (d : ℝ) * povmGuessingProb rho := by
  classical
  have : Nonempty X := nonempty_of_povmGuessingProb_pos hp
  obtain ⟨M, hM_pos, hM_sum, hp_eq⟩ := exists_optimal_povm rho
  obtain ⟨sigma, hsigma_feas⟩ :=
    pgm_sigma_feasible rho M hM_pos hM_sum hp hp_eq.symm
  exact minFeasibleLambda_maxMixed_le_dim_mul_of_isFeasible rho sigma hsigma_feas

private lemma maxMixed_reference_posDef {d : ℕ} [NeZero d] :
    (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp.PosDef := by
  simpa [DensityOp.toSubDensityOp, DensityOp.maxMixed] using
    ((Matrix.PosDef.one : (1 : Op d).PosDef).smul
      (a := (1 / (d : ℂ))) (by
        exact_mod_cast (one_div_pos.mpr
          (Nat.cast_pos.mpr (Nat.pos_of_neZero d)))))

/-- A positive feasible-lambda upper bound of the form `exp (-k log 2)`
gives the corresponding real conditional min-entropy lower bound. -/
lemma conditionalMinEntropyReal_ge_of_minFeasibleLambda_le_exp_neg_mul_log_two
    {X : Type*} [Fintype X] {d : ℕ}
    (rho : CQState X d) (sigma : SubDensityOp d) (k : ℝ)
    (hpos : 0 < minFeasibleLambda rho sigma)
    (hle : minFeasibleLambda rho sigma ≤ Real.exp (-k * Real.log 2)) :
    k ≤ conditionalMinEntropyReal rho sigma := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log (minFeasibleLambda rho sigma) ≤ -k * Real.log 2 :=
    (Real.log_le_iff_le_exp hpos).mpr hle
  have hk_log_le : k * Real.log 2 ≤ -Real.log (minFeasibleLambda rho sigma) := by
    linarith
  unfold conditionalMinEntropyReal
  exact (le_div_iff₀ hlog2).mpr hk_log_le

/-- An optimized min-entropy lower bound is equivalently an exponential upper
bound on the CQ guessing probability. -/
lemma povmGuessingProb_le_exp_neg_mul_log_two_of_conditionalMinEntropyOptReal_ge
    {X : Type*} [Fintype X] {d : ℕ} [NeZero d]
    (rho : CQState X d) (k : ℝ)
    (hp : 0 < povmGuessingProb rho)
    (hk : k ≤ conditionalMinEntropyOptReal rho) :
    povmGuessingProb rho ≤ Real.exp (-k * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk_neglog :
      k ≤ -Real.log (povmGuessingProb rho) / Real.log 2 := by
    simpa [conditionalMinEntropyReal_cq_guess_eq rho] using hk
  have hk_log : k * Real.log 2 ≤ -Real.log (povmGuessingProb rho) :=
    (le_div_iff₀ hlog2).mp hk_neglog
  have hlog_le : Real.log (povmGuessingProb rho) ≤ -k * Real.log 2 := by
    linarith
  exact (Real.log_le_iff_le_exp hp).mp hlog_le

/-- Multiplying `exp (-R log 2)` by a positive factor subtracts
`log₂` of that factor from the exponent's rate. -/
lemma real_mul_exp_neg_mul_log_two_eq_exp_sub_log_div_log_two
    {a R : ℝ} (ha : 0 < a) :
    a * Real.exp (-R * Real.log 2) =
      Real.exp (-(R - Real.log a / Real.log 2) * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    a * Real.exp (-R * Real.log 2)
        = Real.exp (Real.log a) * Real.exp (-R * Real.log 2) := by
            rw [Real.exp_log ha]
    _ = Real.exp (Real.log a + (-R * Real.log 2)) := by
            rw [← Real.exp_add]
    _ = Real.exp (-(R - Real.log a / Real.log 2) * Real.log 2) := by
            congr 1
            field_simp [hlog2.ne']
            ring

/-- For a normalized CQ state, any positive-definite reference has strictly
positive feasible-lambda optimum. -/
lemma minFeasibleLambda_pos_of_normalized_of_posDef
    {X : Type*} [Fintype X] {d : ℕ}
    (rho : NormalizedCQState X d) (sigma : SubDensityOp d)
    (hsigma : sigma.toOp.PosDef) :
    0 < minFeasibleLambda (rho : CQState X d) sigma := by
  have hweight_pos : 0 < ∑ x : X, ((rho : CQState X d).stateMap x).trace := by
    rw [rho.weight_eq_one]
    norm_num
  exact minFeasibleLambda_pos_of_posDef_of_weight_pos
    (rho : CQState X d) sigma hsigma hweight_pos

/- **Why this `maxMixed(d)` floor cannot be sharpened to a `polyDim`-only penalty**
For a permutation-covariant attack Eve's register has `d = eveDim ~ 2^n ≫
polyDim`.  The floor below is `optReal(ρ) − log₂ d`, and `optReal(ρ) ≤ log₂ d`, so its
right-hand side is capped at `optReal(ρ) ≤ log₂(eveDim)`: a `polyDim`-only lead term
`Θ(n)` is unreachable through the full-register `maxMixed(d)` reference.  The correct
reference is the maximally mixed state on the symmetric isotypic component, whose
dimension is `Tr P_R ≤ polyDim`, paid once. Its representation-theory core
(`FinitePermUnitaryRep`, the group-average projector `P_R`) is in
`Quantum/Symmetry/PermRepProjector`. The transport below uses the full-register
`maxMixed(d)` reference. -/
/-- Optimized real min-entropy transfers to the fixed maximally mixed reference
with the unavoidable finite-dimensional loss `log₂ d`. -/
theorem conditionalMinEntropyReal_maxMixed_ge_optReal_sub_log_dim
    {X : Type*} [Fintype X] [Nonempty X] {d : ℕ} [NeZero d]
    (rhoN : NormalizedCQState X d) (R : ℝ)
    (hopt : R ≤ conditionalMinEntropyOptReal (rhoN : CQState X d)) :
    R - Real.log (d : ℝ) / Real.log 2 ≤
      conditionalMinEntropyReal (rhoN : CQState X d)
        (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) := by
  let rho : CQState X d := (rhoN : CQState X d)
  let sigmaMM : SubDensityOp d := DensityOp.toSubDensityOp (DensityOp.maxMixed d)
  let p : ℝ := povmGuessingProb rho
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_neZero d
  have hd_nonneg : 0 ≤ (d : ℝ) := le_of_lt hd_pos
  have hp : 0 < p := by
    simpa [rho, p] using povmGuessingProb_pos_of_normalizedCQState rhoN
  have hp_exp : p ≤ Real.exp (-R * Real.log 2) :=
    povmGuessingProb_le_exp_neg_mul_log_two_of_conditionalMinEntropyOptReal_ge
      rho R hp (by simpa [rho] using hopt)
  have hdim_exp :
      (d : ℝ) * Real.exp (-R * Real.log 2) =
        Real.exp (-(R - Real.log (d : ℝ) / Real.log 2) * Real.log 2) := by
    exact real_mul_exp_neg_mul_log_two_eq_exp_sub_log_div_log_two hd_pos
  have hlam_le :
      minFeasibleLambda rho sigmaMM ≤
        Real.exp (-(R - Real.log (d : ℝ) / Real.log 2) * Real.log 2) := by
    calc
      minFeasibleLambda rho sigmaMM
          ≤ (d : ℝ) * p := by
              simpa [sigmaMM, p] using
                minFeasibleLambda_maxMixed_le_dim_mul_povmGuessingProb rho hp
      _ ≤ (d : ℝ) * Real.exp (-R * Real.log 2) :=
              mul_le_mul_of_nonneg_left hp_exp hd_nonneg
      _ = Real.exp (-(R - Real.log (d : ℝ) / Real.log 2) * Real.log 2) := hdim_exp
  have hlam_pos : 0 < minFeasibleLambda rho sigmaMM :=
    by
      simpa [rho, sigmaMM] using
        minFeasibleLambda_pos_of_normalized_of_posDef rhoN sigmaMM
          (by simpa [sigmaMM] using maxMixed_reference_posDef (d := d))
  simpa [rho, sigmaMM] using
    conditionalMinEntropyReal_ge_of_minFeasibleLambda_le_exp_neg_mul_log_two
      rho sigmaMM (R - Real.log (d : ℝ) / Real.log 2) hlam_pos hlam_le

/-- Feasibility against a scaled reference is the scaled feasibility predicate:
for `0 < c`, `t` is feasible against `c • σ` iff `c * t` is feasible against `σ`. -/
lemma isFeasible_smul_sigma_iff {X : Type*} [Fintype X] {d : ℕ}
    (ρ : CQState X d) (σ : SubDensityOp d) {c : ℝ} (hc : 0 < c) (hc_le : c ≤ 1) {t : ℝ} :
    isFeasible ρ (σ.smul c hc.le hc_le) t ↔ isFeasible ρ σ (c * t) := by
  unfold isFeasible
  constructor
  · rintro ⟨ht_nn, hdom⟩
    refine ⟨mul_nonneg hc.le ht_nn, fun x v => ?_⟩
    have h := hdom x v
    have hcast : (Complex.ofReal t • (σ.smul c hc.le hc_le).toOp : Op d) =
        Complex.ofReal (c * t) • σ.toOp := by
      change (Complex.ofReal t • ((c : ℂ) • σ.toOp) : Op d) =
        Complex.ofReal (c * t) • σ.toOp
      rw [smul_smul, Complex.ofReal_mul]
      congr 1
      ring
    rw [hcast] at h
    exact h
  · rintro ⟨h_ct_nn, hdom⟩
    have ht_nn : 0 ≤ t := by
      by_contra ht_lt
      push Not at ht_lt
      have : c * t < 0 := mul_neg_of_pos_of_neg hc ht_lt
      linarith
    refine ⟨ht_nn, fun x v => ?_⟩
    have h := hdom x v
    have hcast : (Complex.ofReal t • (σ.smul c hc.le hc_le).toOp : Op d) =
        Complex.ofReal (c * t) • σ.toOp := by
      change (Complex.ofReal t • ((c : ℂ) • σ.toOp) : Op d) =
        Complex.ofReal (c * t) • σ.toOp
      rw [smul_smul, Complex.ofReal_mul]
      congr 1
      ring
    rw [hcast]
    exact h

/-- The feasibility set for a scaled reference is `(1/c)` times the original
feasibility set. -/
lemma setOf_isFeasible_smul_sigma {X : Type*} [Fintype X] {d : ℕ}
    (ρ : CQState X d) (σ : SubDensityOp d) {c : ℝ} (hc : 0 < c) (hc_le : c ≤ 1) :
    Set.ofPred (isFeasible ρ (σ.smul c hc.le hc_le)) =
      (c⁻¹) • Set.ofPred (isFeasible ρ σ) := by
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_smul_set]
  rw [isFeasible_smul_sigma_iff ρ σ hc hc_le]
  constructor
  · intro h
    refine ⟨c * t, h, ?_⟩
    rw [smul_eq_mul]
    field_simp
  · rintro ⟨s, hs, rfl⟩
    rw [smul_eq_mul]
    have : c * (c⁻¹ * s) = s := by field_simp
    rw [this]
    exact hs

/-- The min-feasible-λ optimum scales inversely with the reference: for `0 < c`,
`minFeasibleLambda ρ (c • σ) = (1/c) · minFeasibleLambda ρ σ`. -/
lemma minFeasibleLambda_smul_sigma {X : Type*} [Fintype X] {d : ℕ}
    (ρ : CQState X d) (σ : SubDensityOp d) {c : ℝ} (hc : 0 < c) (hc_le : c ≤ 1) :
    minFeasibleLambda ρ (σ.smul c hc.le hc_le) = c⁻¹ * minFeasibleLambda ρ σ := by
  unfold minFeasibleLambda
  rw [setOf_isFeasible_smul_sigma ρ σ hc hc_le]
  have hinv_nn : 0 ≤ c⁻¹ := le_of_lt (inv_pos.mpr hc)
  have := Real.sInf_smul_of_nonneg hinv_nn (Set.ofPred (isFeasible ρ σ))
  simpa [smul_eq_mul] using this

/-- Pointwise: for `0 < c ≤ 1` and any CQ state `ρ'`, the conditional real
min-entropy under the scaled reference is at least the original minus
`log(1/c) / log 2 = -log(c)/log 2`, i.e. shifted by `log(c)/log 2`. -/
lemma conditionalMinEntropyReal_smul_sigma_ge
    {X : Type*} [Fintype X] {d : ℕ}
    (ρ : CQState X d) (σ : SubDensityOp d) {c : ℝ} (hc : 0 < c) (hc_le : c ≤ 1) :
    conditionalMinEntropyReal ρ σ + Real.log c / Real.log 2 ≤
      conditionalMinEntropyReal ρ (σ.smul c hc.le hc_le) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogc_nonpos : Real.log c ≤ 0 := Real.log_nonpos hc.le hc_le
  have hd_nonpos : Real.log c / Real.log 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlogc_nonpos hlog2.le
  have hlam_eq : minFeasibleLambda ρ (σ.smul c hc.le hc_le) =
      c⁻¹ * minFeasibleLambda ρ σ :=
    minFeasibleLambda_smul_sigma ρ σ hc hc_le
  set lamA := minFeasibleLambda ρ σ with hlamA
  have hlamA_nn : 0 ≤ lamA := minFeasibleLambda_nonneg ρ σ
  unfold conditionalMinEntropyReal
  rw [hlam_eq, ← hlamA]
  by_cases hlamA_pos : 0 < lamA
  · have hcinv_pos : 0 < c⁻¹ := inv_pos.mpr hc
    have hprod_pos : 0 < c⁻¹ * lamA := mul_pos hcinv_pos hlamA_pos
    rw [Real.log_mul hcinv_pos.ne' hlamA_pos.ne', Real.log_inv]
    -- Goal: -log lamA / log 2 + log c / log 2 ≤ -(-log c + log lamA) / log 2
    have : -Real.log lamA / Real.log 2 + Real.log c / Real.log 2 =
        -(-Real.log c + Real.log lamA) / Real.log 2 := by
      field_simp
      ring
    linarith [this]
  · -- lamA = 0 case: cond entropy values both 0 (junk).
    have hlamA_zero : lamA = 0 := le_antisymm (not_lt.mp hlamA_pos) hlamA_nn
    rw [hlamA_zero, mul_zero, Real.log_zero, neg_zero, zero_div, zero_add]
    -- Goal: log c / log 2 ≤ 0
    exact hd_nonpos


/-- Scaling the reference by `0 < c ≤ 1` decreases signed smooth min-entropy by at most `-log c
/ log 2`, including negative target values. -/
theorem smoothMinEntropyReal_smul_sigma_sub_log
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε_nn : 0 ≤ ε) (ρ : CQState X n) (σ : SubDensityOp n)
    (c : ℝ) (hc : 0 < c) (hc_le : c ≤ 1) :
    smoothMinEntropyReal ε ρ σ + Real.log c / Real.log 2 ≤
      smoothMinEntropyReal ε ρ (σ.smul c hc.le hc_le) := by
  -- The shift `d = log c / log 2 ≤ 0` is nonpositive.
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogc_nonpos : Real.log c ≤ 0 := Real.log_nonpos hc.le hc_le
  have hd_nonpos : Real.log c / Real.log 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlogc_nonpos hlog2.le
  -- The pointwise inequality (over each ρ' in the smoothing ball).
  have hpw : ∀ ρ' : CQState X n,
      conditionalMinEntropyReal ρ' σ + Real.log c / Real.log 2 ≤
        conditionalMinEntropyReal ρ' (σ.smul c hc.le hc_le) := fun ρ' =>
    conditionalMinEntropyReal_smul_sigma_ge ρ' σ hc hc_le
  -- Set abbreviations.
  set A := Set.ofPred (isInSmoothedSetReal ε ρ σ) with hA
  set B := Set.ofPred (isInSmoothedSetReal ε ρ (σ.smul c hc.le hc_le)) with hB
  have hA_ne : A.Nonempty := ⟨conditionalMinEntropyReal ρ σ, ρ, rfl, by
    rw [CQState.purifiedDistance_self_zero]; exact hε_nn⟩
  have hB_ne : B.Nonempty := ⟨conditionalMinEntropyReal ρ (σ.smul c hc.le hc_le), ρ, rfl, by
    rw [CQState.purifiedDistance_self_zero]; exact hε_nn⟩
  -- Each element of A corresponds (via the same ρ') to an element of B.
  have h_AB : ∀ a ∈ A, ∃ b ∈ B,
      a + Real.log c / Real.log 2 ≤ b := by
    rintro a ⟨ρ', rfl, hd⟩
    exact ⟨conditionalMinEntropyReal ρ' (σ.smul c hc.le hc_le), ⟨ρ', rfl, hd⟩, hpw ρ'⟩
  -- The reverse: each b ∈ B has a corresponding a ∈ A with a + d = b
  -- when λ > 0, else b = 0. We use this to show bddAbove S → bddAbove T.
  have h_BA : ∀ b ∈ B, ∃ a ∈ A,
      b ≤ a + Real.log c / Real.log 2 ∨ b ≤ 0 := by
    rintro b ⟨ρ', rfl, hd⟩
    refine ⟨conditionalMinEntropyReal ρ' σ, ⟨ρ', rfl, hd⟩, ?_⟩
    -- Use the explicit formula via minFeasibleLambda_smul_sigma.
    have hlam_eq : minFeasibleLambda ρ' (σ.smul c hc.le hc_le) =
        c⁻¹ * minFeasibleLambda ρ' σ :=
      minFeasibleLambda_smul_sigma ρ' σ hc hc_le
    set lamA := minFeasibleLambda ρ' σ with hlamA
    have hlamA_nn : 0 ≤ lamA := minFeasibleLambda_nonneg ρ' σ
    by_cases hlamA_pos : 0 < lamA
    · left
      have hcinv_pos : 0 < c⁻¹ := inv_pos.mpr hc
      change conditionalMinEntropyReal ρ' (σ.smul c hc.le hc_le) ≤
        conditionalMinEntropyReal ρ' σ + Real.log c / Real.log 2
      unfold conditionalMinEntropyReal
      rw [hlam_eq, ← hlamA, Real.log_mul hcinv_pos.ne' hlamA_pos.ne', Real.log_inv]
      have hkey : -Real.log lamA / Real.log 2 + Real.log c / Real.log 2 =
          -(-Real.log c + Real.log lamA) / Real.log 2 := by
        field_simp
        ring
      linarith [hkey]
    · right
      have hlamA_zero : lamA = 0 := le_antisymm (not_lt.mp hlamA_pos) hlamA_nn
      change conditionalMinEntropyReal ρ' (σ.smul c hc.le hc_le) ≤ 0
      unfold conditionalMinEntropyReal
      rw [hlam_eq, hlamA_zero, mul_zero, Real.log_zero, neg_zero, zero_div]
  change sSup A + Real.log c / Real.log 2 ≤ sSup B
  -- Case split on `BddAbove B`.
  by_cases hBddB : BddAbove B
  · -- Case 1: B bounded above. sSup B finite.
    rw [← le_sub_iff_add_le]
    apply csSup_le hA_ne
    intro a ha
    obtain ⟨b, hb_mem, hab⟩ := h_AB a ha
    have hb_le : b ≤ sSup B := le_csSup hBddB hb_mem
    linarith
  · -- Case 2: B not bounded above. sSup B = 0.
    rw [Real.sSup_of_not_bddAbove hBddB]
    -- Need sSup A + d ≤ 0.
    by_cases hBddA : BddAbove A
    · -- 2a: A bounded above. We derive contradiction by showing B is bounded.
      exfalso
      apply hBddB
      -- Show B is bounded by `max (sSup A + d) 0`.
      refine ⟨max (sSup A + Real.log c / Real.log 2) 0, ?_⟩
      intro b hb
      obtain ⟨a, ha_mem, ha_cases⟩ := h_BA b hb
      rcases ha_cases with hle | hle
      · -- b ≤ a + d ≤ sSup A + d ≤ max ...
        have ha_le : a ≤ sSup A := le_csSup hBddA ha_mem
        have : b ≤ sSup A + Real.log c / Real.log 2 := by linarith
        exact le_trans this (le_max_left _ _)
      · -- b ≤ 0 ≤ max ...
        exact le_trans hle (le_max_right _ _)
    · -- 2b: A not bounded above. sSup A = 0. Need 0 + d ≤ 0, d ≤ 0.
      rw [Real.sSup_of_not_bddAbove hBddA]
      linarith


/-- Domination of `c` times the source reference transfers signed smooth min-entropy with the
additive term `log c / log 2`, for `0 < c ≤ 1`. -/
theorem smoothMinEntropyReal_ge_of_smul_opLe
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {d : ℕ} [NeZero d]
    (ε : ℝ) (hε_nn : 0 ≤ ε) (ρ : CQState X d) (σ σ' : SubDensityOp d)
    (c : ℝ) (hc : 0 < c) (hc_le : c ≤ 1)
    (hdom : ∀ v : Fin d → ℂ,
      (quadraticForm ((c : ℂ) • σ.toOp) v).re ≤ (quadraticForm σ'.toOp v).re)
    (hfeas : ∀ ρ' : CQState X d, CQState.purifiedDistance ρ ρ' ≤ ε →
        hasFeasibleLambda ρ' (σ.smul c hc.le hc_le))
    (hpos_sigma_prime : ∀ ρ' : CQState X d, CQState.purifiedDistance ρ ρ' ≤ ε →
        0 < minFeasibleLambda ρ' σ')
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ σ'))) :
    smoothMinEntropyReal ε ρ σ + Real.log c / Real.log 2 ≤ smoothMinEntropyReal ε ρ σ' := by
  have hscale :
      smoothMinEntropyReal ε ρ σ + Real.log c / Real.log 2 ≤
        smoothMinEntropyReal ε ρ (σ.smul c hc.le hc_le) :=
    smoothMinEntropyReal_smul_sigma_sub_log ε hε_nn ρ σ c hc hc_le
  have hdom' : ∀ v : Fin d → ℂ,
      (quadraticForm (σ.smul c hc.le hc_le).toOp v).re ≤ (quadraticForm σ'.toOp v).re := by
    intro v
    have hsmul_toOp : (σ.smul c hc.le hc_le).toOp = (c : ℂ) • σ.toOp := rfl
    rw [hsmul_toOp]; exact hdom v
  have hmono :
      smoothMinEntropyReal ε ρ (σ.smul c hc.le hc_le) ≤ smoothMinEntropyReal ε ρ σ' :=
    smoothMinEntropyReal_mono_sigma_of_bddAbove ε hε_nn ρ (σ.smul c hc.le hc_le) σ'
      hdom' hfeas hpos_sigma_prime hbdd
  exact hscale.trans hmono

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
