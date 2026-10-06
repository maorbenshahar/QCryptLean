import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy

/-!
# Rank-one blocks pin a PSD sub-operator to a rescaling — the `minFeasibleLambda` floor

A **PSD sub-operator witness** for a CQ state `ρ` is a second CQ state `R` with
`opLe (R.stateMap x).toOp (ρ.stateMap x).toOp` for every classical outcome `x`; positivity
`0 ⪯ R_x` is carried by the `SubDensityOp` type itself. This is the smoothing class the
library actually optimises over: `InfoTheory.SmoothMinEntropy.isInSmoothedSetReal` ranges over
`rho2 : CQState X n`, whose blocks are `SubDensityOp`, so a *Hermitian but indefinite* witness
is not even expressible.

**When `ρ`'s blocks have rank ≤ 1, that class buys nothing beyond the trace it throws away.**

* `exists_smul_of_opLe_vecMulVec_star` is the rigidity: for `ρ_x = |φ⟩⟨φ|`, the constraints
  `0 ⪯ R_x` and `R_x ⪯ ρ_x` force `R_x = c_x • ρ_x` with `c_x ∈ [0,1]`. For `w` with
  `⟨w, φ⟩ = 0` one has `⟨w|R_x|w⟩ ≤ ⟨w|ρ_x|w⟩ = 0`, so `R_x w = 0`; a PSD operator killing
  the whole orthogonal complement of `φ` is a multiple of `|φ⟩⟨φ|`. The witness cannot
  rotate — only rescale.
* `minFeasibleLambda_ge_of_rankOne_blocks` turns the rigidity into the floor
  `c · λ*(ρ|σ) ≤ λ*(R|σ)` as soon as every block keeps at least a `c`-fraction of its weight.
* `minFeasibleLambda_ge_of_rankOne_blocks_of_blockWeight_floor` restates it in the ε-ball
  idiom: discarding at most `ε` of trace from blocks each of weight at least `θ` costs at
  most the factor `1 - ε/θ`. So `λ*` (hence the leftover-hash budget) only moves once `ε`
  is comparable to the *smallest* block weight, never merely to the total.
* `not_minFeasibleLambda_ge_globalTraceRatio` records the sharp edge of the result: the
  *global* form `(Tr R / Tr ρ) · λ*(ρ) ≤ λ*(R)` — the shape one first writes down — is
  **false**, by a compiled `dim = 2`, `|X| = 2` witness. The charge is per block, not global.

## Scope of PSD smoothing

The rank-one rigidity limits PSD sub-operator witnesses for
bb84SiftedPEAnnounceEveVisible_agreeBlock_ckrTensorTraceNorm_le_lhlOutput_of_goodBranch_anyRef.
Weakening the blockwise constraint to the marginal constraint `R_E ⪯ ρ_E` does not in general
supply the required entropy floor. Regula–Tomamichel's Corollary 15 uses an `R` that need not be
PSD; the gap from the PSD class can be unbounded as the reference's small eigenvalue tends to zero.

* **Regula–Tomamichel smooth `R` is Hermitian, not PSD.** In arXiv:2603.04493, equations (38)
  and (40), the smoothing set is `{R | R = R†, ‖ρ − R‖₊ ≤ ε, R ≤ ρ}`. Theorem 14 uses it;
  the proof of equation (100) requires only a Hermitian `R_XE` satisfying `R_E ≤ ρ_E`.
  The remark after Theorem 14 states that this smoothing implies the marginal constraint of
  partial smoothing. The PSD/partially-smoothed class is weaker. Such an `R` need not supply
  the `0 ⪯ R ⪯ ρ` witness required by `opLe` and `SubDensityOp`.
* **The `+ 2 * ε` in `InfoTheory.QuantumLHL.quantum_seedKey_LHL_smooth_of_refOptimisedFloor`
  reflects the PSD smoothing geometry.** The ε of discarded trace is constrained by the
  per-block floor proved here.
* **The Hermitian accept-probability split** in arXiv:2603.04493, equation (100), is
  `Tr(ρ_ZE^f − 1_Z/|Z| ⊗ ρ_E)₊ ≤ ‖ρ_XE − R_XE‖₊ + ‖R_ZE^f − 1_Z/|Z| ⊗ R_E‖₊`.
  It uses the positive-part norm `‖X‖₊ = Tr X₊` for Hermitian `R`, together with the
  σ-weighted geometry `J_σ(X) = ½(σX + Xσ)`, `‖X‖_σ = √(Tr X J_σ⁻¹(X))`, and
  Kadison-type operator monotonicity. These objects are outside this module's PSD framework.
  `Quantum.Metrics.traceDistanceGen` is Tomamichel's symmetrised
  `½‖ρ−σ‖₁ + ½|Tr ρ − Tr σ|`, which is a different functional.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

private lemma op_ext_of_mulVec {n : ℕ} {A B : Op n} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have hj := congrFun (h (Pi.single j 1)) i
  simpa using hj

private lemma vec_ext_of_star_dotProduct {n : ℕ} {a b : Fin n → ℂ}
    (h : ∀ u : Fin n → ℂ, star u ⬝ᵥ a = star u ⬝ᵥ b) : a = b := by
  funext i
  have hi := h (Pi.single i 1)
  simpa using hi

private lemma vecMulVec_star_mulVec {n : ℕ} (φ v : Fin n → ℂ) :
    (Matrix.vecMulVec φ (star φ)) *ᵥ v = (star φ ⬝ᵥ v) • φ := by
  funext i
  simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm]

private lemma star_dotProduct_self {n : ℕ} (φ : Fin n → ℂ) :
    star φ ⬝ᵥ φ = ((∑ i, Complex.normSq (φ i) : ℝ) : ℂ) := by
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

private lemma star_dotProduct_comm {n : ℕ} (u v : Fin n → ℂ) :
    (starRingEnd ℂ) (star u ⬝ᵥ v) = star v ⬝ᵥ u := by
  simp [dotProduct, map_sum, mul_comm]

private lemma star_mulVec_dotProduct {n : ℕ} {R : Op n} (hR : R.IsHermitian)
    (w z : Fin n → ℂ) : star w ⬝ᵥ (R *ᵥ z) = star (R *ᵥ w) ⬝ᵥ z := by
  rw [Matrix.star_mulVec, hR.eq, ← Matrix.dotProduct_mulVec]

/-- **Rank-one rigidity of PSD sub-operators.**

If `R` is positive semidefinite and dominated in the Löwner order by the rank-one operator
`|φ⟩⟨φ| = vecMulVec φ (star φ)`, then `R` is a *rescaling* of it: `R = c • |φ⟩⟨φ|` for a
single `c ∈ [0,1]`.

Over rank-one blocks the PSD
sub-operator smoothing class has no directional freedom whatsoever — every witness in it is
determined by one scalar per block. The proof is elementary: for `w` orthogonal to `φ`,
`0 ≤ ⟨w|R|w⟩ ≤ ⟨w| |φ⟩⟨φ| |w⟩ = 0`, so `R` annihilates `φ`'s orthogonal complement
(`opLe_mulVec_eq_zero_of_psd`); Hermiticity then forces `R φ ∈ span φ`, and the two facts
together determine `R` on every vector. -/
theorem exists_smul_of_opLe_vecMulVec_star {n : ℕ} {R : Op n} (φ : Fin n → ℂ)
    (hR : R.PosSemidef) (hRP : opLe R (Matrix.vecMulVec φ (star φ))) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ R = (c : ℂ) • Matrix.vecMulVec φ (star φ) := by
  have hker : ∀ w : Fin n → ℂ, star φ ⬝ᵥ w = 0 → R *ᵥ w = 0 := by
    intro w hw
    refine opLe_mulVec_eq_zero_of_psd hR hRP ?_
    rw [vecMulVec_star_mulVec, hw, zero_smul]
  by_cases hφ : φ = 0
  · refine ⟨0, le_refl 0, zero_le_one, ?_⟩
    subst hφ
    have hz : R = 0 := op_ext_of_mulVec (fun v => by rw [hker v (by simp), Matrix.zero_mulVec])
    simp [hz]
  · obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hφ
    set q : ℝ := ∑ i, Complex.normSq (φ i) with hqdef
    have hsq : star φ ⬝ᵥ φ = (q : ℂ) := star_dotProduct_self φ
    have hqpos : 0 < q := by
      refine Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
        ⟨i0, Finset.mem_univ i0, ?_⟩
      simpa using hi0
    have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hqpos
    set μ : ℂ := star φ ⬝ᵥ (R *ᵥ φ) with hμdef
    have hμre : 0 ≤ μ.re := posSemidef_re_quadraticForm_nonneg hR φ
    have hμim : μ.im = 0 := quadraticForm_im_of_isHermitian R hR.isHermitian φ
    have hμcast : ((μ.re : ℝ) : ℂ) = μ := by
      apply Complex.ext <;> simp [hμim]
    -- `R` maps `φ` into the line spanned by `φ`.
    have hRφ : R *ᵥ φ = (μ / (q : ℂ)) • φ := by
      refine vec_ext_of_star_dotProduct (fun u => ?_)
      have hw : star φ ⬝ᵥ ((q : ℂ) • u - (star φ ⬝ᵥ u) • φ) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, hsq]
        simp only [smul_eq_mul]
        ring
      have hswap := star_mulVec_dotProduct hR.isHermitian
        ((q : ℂ) • u - (star φ ⬝ᵥ u) • φ) φ
      rw [hker _ hw] at hswap
      simp only [star_sub, star_smul, star_dotProduct_comm, star_zero,
        zero_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul,
        Complex.star_def, Complex.conj_ofReal] at hswap
      rw [← hμdef] at hswap
      rw [dotProduct_smul, smul_eq_mul]
      field_simp at hswap ⊢
      linear_combination hswap
    refine ⟨μ.re / q ^ 2, ?_, ?_, ?_⟩
    · positivity
    · rw [div_le_one (by positivity)]
      have hPq : quadraticForm (Matrix.vecMulVec φ (star φ)) φ = (q : ℂ) ^ 2 := by
        change star φ ⬝ᵥ ((Matrix.vecMulVec φ (star φ)) *ᵥ φ) = _
        rw [vecMulVec_star_mulVec, dotProduct_smul, smul_eq_mul, hsq]; ring
      have hle := hRP φ
      rw [hPq, ← Complex.ofReal_pow, Complex.ofReal_re] at hle
      exact hle
    · refine op_ext_of_mulVec (fun v => ?_)
      have hw : star φ ⬝ᵥ (v - ((star φ ⬝ᵥ v) / (q : ℂ)) • φ) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hsq]
        field_simp
        ring
      have hRw := hker _ hw
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hRφ, sub_eq_zero] at hRw
      rw [hRw, Matrix.smul_mulVec, vecMulVec_star_mulVec]
      rw [Complex.ofReal_div, Complex.ofReal_pow, hμcast]
      rw [smul_smul, smul_smul]
      congr 1
      field_simp

/-- A PSD sub-operator of a **rank-one** block that retains a `c`-fraction of the block's
trace dominates `c` times the block: `c • ρ ⪯ R`.

By `exists_smul_of_opLe_vecMulVec_star` the sub-operator is `R = c' • ρ`, and the trace
constraint `c · Tr ρ ≤ Tr R = c' · Tr ρ` pins `c ≤ c'` whenever `Tr ρ > 0`; a zero-weight
rank-one block is the zero operator, where the claim is vacuous. No sign hypothesis on `c`
is needed. -/
theorem opLe_smul_of_rankOne_of_trace_le {n : ℕ} {ρ R : SubDensityOp n} {c : ℝ}
    (φ : Fin n → ℂ) (hρ : ρ.toOp = Matrix.vecMulVec φ (star φ))
    (hsub : opLe R.toOp ρ.toOp)
    (hkeep : c * ρ.trace ≤ R.trace) :
    opLe ((c : ℂ) • ρ.toOp) R.toOp := by
  have hRpsd : R.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib R.toPosSemidefOp
  obtain ⟨c', hc'0, -, hRc⟩ :=
    exists_smul_of_opLe_vecMulVec_star φ hRpsd (hρ ▸ hsub)
  rw [← hρ] at hRc
  have htr : R.trace = c' * ρ.trace := by
    rw [SubDensityOp.trace, SubDensityOp.trace, hRc, Matrix.trace_smul, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rcases eq_or_lt_of_le ρ.trace_nonneg with htr0 | htrpos
  · -- A zero-weight rank-one block is the zero operator: both sides vanish.
    have hφ0 : φ = 0 := by
      have hq : (∑ i, Complex.normSq (φ i)) = 0 := by
        have : ρ.trace = (∑ i, Complex.normSq (φ i)) := by
          rw [SubDensityOp.trace, hρ]
          simp [Matrix.trace, Matrix.vecMulVec_apply, Complex.re_sum, Complex.normSq_apply]
        rw [← this, ← htr0]
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Complex.normSq_nonneg (φ j))).mp hq i (Finset.mem_univ i)
      simpa using Complex.normSq_eq_zero.mp this
    intro v
    rw [hρ, hφ0]
    simpa [quadraticForm] using hRpsd.dotProduct_mulVec_nonneg v |>.1
  · have hcc' : c ≤ c' := le_of_mul_le_mul_right (by linarith [hkeep, htr]) htrpos
    intro v
    rw [hRc]
    rw [show ((c : ℂ) • ρ.toOp) = (Complex.ofReal c) • ρ.toOp from rfl,
      show ((c' : ℂ) • ρ.toOp) = (Complex.ofReal c') • ρ.toOp from rfl,
      quadraticForm_ofReal_smul, quadraticForm_ofReal_smul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_right hcc'
      (Quantum.Operators.posSemidef_re_quadraticForm_nonneg
        (Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp) v)

/-- **Sub-operator smoothing over rank-one blocks lowers `minFeasibleLambda` by no more than
the per-block trace it discards.**

If every block of `ρ` has rank at most one, `R` is a blockwise PSD sub-operator of `ρ`, and
every block of `R` keeps at least a `c`-fraction of the corresponding block's weight, then

  `c · λ*(ρ|σ) ≤ λ*(R|σ)`,

for **every** reference `σ` — no positive-definiteness, no support condition, no
normalisation beyond `SubDensityOp`. Since `H_min = −log₂ λ*`, the smoothing can buy at most
`log₂(1/c)` bits.

The retention hypothesis is genuinely per block: the global form
`(Tr R / Tr ρ) · λ*(ρ|σ) ≤ λ*(R|σ)` is FALSE, see `not_minFeasibleLambda_ge_globalTraceRatio`. -/
theorem minFeasibleLambda_ge_of_rankOne_blocks
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ R : CQState X n) (σ : SubDensityOp n) {c : ℝ}
    (hrank : ∀ x, ∃ φ : Fin n → ℂ, (ρ.stateMap x).toOp = Matrix.vecMulVec φ (star φ))
    (hsub : ∀ x, opLe (R.stateMap x).toOp (ρ.stateMap x).toOp)
    (hc : 0 ≤ c)
    (hkeep : ∀ x, c * (ρ.stateMap x).trace ≤ (R.stateMap x).trace) :
    c * minFeasibleLambda ρ σ ≤ minFeasibleLambda R σ := by
  have hdom : ∀ x, opLe ((c : ℂ) • (ρ.stateMap x).toOp) (R.stateMap x).toOp := by
    intro x
    obtain ⟨φ, hφ⟩ := hrank x
    exact opLe_smul_of_rankOne_of_trace_le φ hφ (hsub x) (hkeep x)
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0, zero_mul]
    exact minFeasibleLambda_nonneg R σ
  · by_cases hfeas : hasFeasibleLambda R σ
    · refine le_csInf hfeas ?_
      intro t ht
      have hfρ : isFeasible ρ σ (t / c) := by
        refine ⟨div_nonneg ht.1 hcpos.le, fun x => ?_⟩
        have hchain : opLe ((c : ℂ) • (ρ.stateMap x).toOp)
            (Complex.ofReal t • σ.toOp) := opLe_trans (hdom x) (ht.2 x)
        have hscaled := opLe_smul_nonneg (t := 1 / c) (by positivity) hchain
        have hL : (Complex.ofReal (1 / c)) • ((c : ℂ) • (ρ.stateMap x).toOp)
            = (ρ.stateMap x).toOp := by
          rw [smul_smul, ← Complex.ofReal_mul, one_div_mul_cancel (ne_of_gt hcpos),
            Complex.ofReal_one, one_smul]
        have hRt : (Complex.ofReal (1 / c)) • (Complex.ofReal t • σ.toOp)
            = Complex.ofReal (t / c) • σ.toOp := by
          rw [smul_smul, ← Complex.ofReal_mul]
          ring_nf
        rw [hL, hRt] at hscaled
        exact hscaled
      have hle := minFeasibleLambda_le_of_isFeasible ρ σ hfρ
      have : c * minFeasibleLambda ρ σ ≤ c * (t / c) :=
        mul_le_mul_of_nonneg_left hle hcpos.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hcpos)] at this
    · have hempty : ∀ t, ¬ isFeasible ρ σ t := by
        intro t ht
        exact hfeas ⟨t, ht.1, fun x => opLe_trans (hsub x) (ht.2 x)⟩
      have hsetρ : Set.ofPred (isFeasible ρ σ) = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr hempty
      have hsetR : Set.ofPred (isFeasible R σ) = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun t ht => hfeas ⟨t, ht⟩)
      have hρ0 : minFeasibleLambda ρ σ = 0 := by
        rw [minFeasibleLambda, hsetρ, Real.sInf_empty]
      have hR0 : minFeasibleLambda R σ = 0 := by
        rw [minFeasibleLambda, hsetR, Real.sInf_empty]
      rw [hρ0, hR0, mul_zero]

/-- The ε-ball form of `minFeasibleLambda_ge_of_rankOne_blocks`: discarding at most `ε` of
trace from rank-one blocks each of weight at least `θ` costs at most the factor `1 - ε/θ`
in `λ*`, i.e. at most `log₂(1/(1 - ε/θ))` bits of min-entropy.

This is the quantitative form of the foreclosure. A smoothing radius `ε` only moves the
budget once it is comparable to the *smallest* block weight `θ`; being small compared to the
total weight is worth nothing. -/
theorem minFeasibleLambda_ge_of_rankOne_blocks_of_blockWeight_floor
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ R : CQState X n) (σ : SubDensityOp n) {ε θ : ℝ}
    (hrank : ∀ x, ∃ φ : Fin n → ℂ, (ρ.stateMap x).toOp = Matrix.vecMulVec φ (star φ))
    (hsub : ∀ x, opLe (R.stateMap x).toOp (ρ.stateMap x).toOp)
    (hε : 0 ≤ ε) (hθ : 0 < θ) (hεθ : ε ≤ θ)
    (hfloor : ∀ x, θ ≤ (ρ.stateMap x).trace)
    (hdiscard : ∀ x, (ρ.stateMap x).trace - (R.stateMap x).trace ≤ ε) :
    (1 - ε / θ) * minFeasibleLambda ρ σ ≤ minFeasibleLambda R σ := by
  refine minFeasibleLambda_ge_of_rankOne_blocks ρ R σ hrank hsub ?_ ?_
  · have : ε / θ ≤ 1 := (div_le_one hθ).mpr hεθ
    linarith
  · intro x
    have hkey : ε ≤ ε / θ * (ρ.stateMap x).trace :=
      calc ε = ε / θ * θ := by field_simp
        _ ≤ ε / θ * (ρ.stateMap x).trace :=
            mul_le_mul_of_nonneg_left (hfloor x) (div_nonneg hε hθ.le)
    have hd := hdiscard x
    nlinarith [hd, hkey]

/-! ### The *global* trace-ratio form is false

`minFeasibleLambda_ge_of_rankOne_blocks` charges the retained fraction **per block**. The
superficially natural *global* form — "`λ*` drops by no more than the total trace discarded",
i.e. `(Tr R / Tr ρ) · λ*(ρ|σ) ≤ λ*(R|σ)` — is **false**, even for rank-one blocks and a
positive-definite reference, already at `|X| = 2`, `dim = 2`.

The witness compiled below is `ρ = ¼|0⟩⟨0| ⊕ ¼|1⟩⟨1|`, `R = 0 ⊕ ¼|1⟩⟨1|`, with the
positive-definite reference `σ = diag(¼, ¾)`. The compiled bounds are `1 ≤ λ*(ρ|σ)`
(`cexRho_lambda_ge`, from `⟨0|ρ₀|0⟩ = ¼` against `⟨0|tσ|0⟩ = t/4`) and `λ*(R|σ) ≤ ⅓`
(`cexR_lambda_le`, exhibiting `t = ⅓` as feasible) — in fact both are equalities. Since
`Tr R / Tr ρ = ½`, the global bound would demand `½ ≤ ⅓`. The mechanism is exactly the one
the per-block statement rules out: the discarded block is the one that *attains* `λ*`, so
half the trace buys a factor `3`.
-/

private def diag2 (a b : ℝ) : Op 2 := Matrix.diagonal ![(a : ℂ), (b : ℂ)]

private lemma quadraticForm_diag2 (a b : ℝ) (v : Fin 2 → ℂ) :
    quadraticForm (diag2 a b) v
      = ((a * Complex.normSq (v 0) + b * Complex.normSq (v 1) : ℝ) : ℂ) := by
  simp [diag2, quadraticForm, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two,
    Complex.normSq_eq_conj_mul_self]
  ring

private lemma trace_diag2 (a b : ℝ) : (diag2 a b).trace = ((a + b : ℝ) : ℂ) := by
  simp [diag2, Matrix.trace, Fin.sum_univ_two]

private lemma isHermitian_diag2 (a b : ℝ) : (diag2 a b).IsHermitian := by
  simp [diag2, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]

/-- A nonnegative diagonal `2 × 2` operator of trace at most one, as a `SubDensityOp`. -/
private def sub2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) : SubDensityOp 2 where
  toOp := diag2 a b
  isHermitian := isHermitian_diag2 a b
  pos_semidef := by
    intro v
    rw [quadraticForm_diag2, Complex.ofReal_re]
    exact add_nonneg (mul_nonneg ha (Complex.normSq_nonneg _))
      (mul_nonneg hb (Complex.normSq_nonneg _))
  trace_le_one := by
    rw [trace_diag2, Complex.ofReal_re]
    exact hab

private lemma sub2_trace (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (sub2 a b ha hb hab).trace = a + b := by
  rw [SubDensityOp.trace]
  change (diag2 a b).trace.re = _
  rw [trace_diag2, Complex.ofReal_re]

private lemma opLe_diag2 {a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    opLe (diag2 a b) (diag2 a' b') := by
  intro v
  rw [quadraticForm_diag2, quadraticForm_diag2, Complex.ofReal_re, Complex.ofReal_re]
  have h0 := Complex.normSq_nonneg (v 0)
  have h1 := Complex.normSq_nonneg (v 1)
  nlinarith

private lemma smul_diag2 (t a b : ℝ) :
    (Complex.ofReal t) • diag2 a b = diag2 (t * a) (t * b) := by
  ext i j
  simp only [diag2, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_zero]
  by_cases h : i = j
  · subst h
    fin_cases i <;> simp
  · simp [h]

private def cexSigma : SubDensityOp 2 :=
  sub2 (1 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num)

private def cexRho : CQState (Fin 2) 2 where
  stateMap := ![sub2 (1 / 4) 0 (by norm_num) le_rfl (by norm_num),
                sub2 0 (1 / 4) le_rfl (by norm_num) (by norm_num)]
  weight_le_one := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub2_trace]
    norm_num

private def cexR : CQState (Fin 2) 2 where
  stateMap := ![sub2 0 0 le_rfl le_rfl (by norm_num),
                sub2 0 (1 / 4) le_rfl (by norm_num) (by norm_num)]
  weight_le_one := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub2_trace]
    norm_num

private lemma cexRho_weight : (∑ x, (cexRho.stateMap x).trace) = 1 / 2 := by
  rw [Fin.sum_univ_two]
  simp only [cexRho, Matrix.cons_val_zero, Matrix.cons_val_one, sub2_trace]
  norm_num

private lemma cexR_weight : (∑ x, (cexR.stateMap x).trace) = 1 / 4 := by
  rw [Fin.sum_univ_two]
  simp only [cexR, Matrix.cons_val_zero, Matrix.cons_val_one, sub2_trace]
  norm_num

private lemma cexRho_rankOne :
    ∀ x, ∃ φ : Fin 2 → ℂ, (cexRho.stateMap x).toOp = Matrix.vecMulVec φ (star φ) := by
  intro x
  fin_cases x
  · refine ⟨![1 / 2, 0], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cexRho, sub2, diag2, Matrix.vecMulVec_apply]
    norm_num
  · refine ⟨![0, 1 / 2], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cexRho, sub2, diag2, Matrix.vecMulVec_apply]
    norm_num

private lemma cexR_opLe_cexRho :
    ∀ x, opLe (cexR.stateMap x).toOp (cexRho.stateMap x).toOp := by
  intro x
  fin_cases x
  · exact opLe_diag2 (by norm_num) le_rfl
  · exact opLe_diag2 le_rfl le_rfl

private lemma cexR_lambda_le : minFeasibleLambda cexR cexSigma ≤ 1 / 3 := by
  have hf : isFeasible cexR cexSigma (1 / 3) := by
    refine ⟨by norm_num, fun x => ?_⟩
    have hsm : (Complex.ofReal (1 / 3 : ℝ)) • cexSigma.toOp = diag2 (1 / 12) (1 / 4) := by
      change (Complex.ofReal (1 / 3 : ℝ)) • diag2 (1 / 4) (3 / 4) = _
      rw [smul_diag2]; norm_num
    rw [hsm]
    fin_cases x
    · exact opLe_diag2 (by norm_num) (by norm_num)
    · exact opLe_diag2 (by norm_num) le_rfl
  exact minFeasibleLambda_le_of_isFeasible cexR cexSigma hf

private lemma cexRho_lambda_ge : (1 : ℝ) ≤ minFeasibleLambda cexRho cexSigma := by
  refine le_csInf ⟨1, ?_⟩ ?_
  · refine ⟨zero_le_one, fun x => ?_⟩
    have hsm : (Complex.ofReal (1 : ℝ)) • cexSigma.toOp = diag2 (1 / 4) (3 / 4) := by
      change (Complex.ofReal (1 : ℝ)) • diag2 (1 / 4) (3 / 4) = _
      rw [smul_diag2]; norm_num
    rw [hsm]
    fin_cases x
    · exact opLe_diag2 le_rfl (by norm_num)
    · exact opLe_diag2 (by norm_num) (by norm_num)
  · intro t ht
    have h0 := ht.2 0
    have hsm : (Complex.ofReal t) • cexSigma.toOp = diag2 (t * (1 / 4)) (t * (3 / 4)) := by
      change (Complex.ofReal t) • diag2 (1 / 4) (3 / 4) = _
      rw [smul_diag2]
    rw [hsm, show (cexRho.stateMap 0).toOp = diag2 (1 / 4) 0 from rfl] at h0
    have hv := h0 ![1, 0]
    rw [quadraticForm_diag2, quadraticForm_diag2, Complex.ofReal_re, Complex.ofReal_re] at hv
    norm_num at hv
    linarith

/-- **The global trace-ratio floor is FALSE for rank-one blocks.**

There is no theorem of the shape "`λ*` falls by at most the globally discarded trace":
even with every `ρ` block of rank one, with a positive-definite reference, and with `R`
a genuine PSD sub-operator of `ρ` blockwise, `minFeasibleLambda R σ` can sit strictly
below `(Tr R / Tr ρ) · minFeasibleLambda ρ σ`.  Only the *per-block* retention
of `minFeasibleLambda_ge_of_rankOne_blocks` is available. -/
theorem not_minFeasibleLambda_ge_globalTraceRatio :
    ¬ ∀ (ρ R : CQState (Fin 2) 2) (σ : SubDensityOp 2),
        (∀ x, ∃ φ : Fin 2 → ℂ, (ρ.stateMap x).toOp = Matrix.vecMulVec φ (star φ)) →
        (∀ x, opLe (R.stateMap x).toOp (ρ.stateMap x).toOp) →
        ((∑ x, (R.stateMap x).trace) / (∑ x, (ρ.stateMap x).trace)) *
            minFeasibleLambda ρ σ ≤ minFeasibleLambda R σ := by
  intro h
  have hmain := h cexRho cexR cexSigma cexRho_rankOne cexR_opLe_cexRho
  rw [cexR_weight, cexRho_weight] at hmain
  norm_num at hmain
  linarith [cexR_lambda_le, cexRho_lambda_ge, hmain]

end InfoTheory.SmoothMinEntropy
