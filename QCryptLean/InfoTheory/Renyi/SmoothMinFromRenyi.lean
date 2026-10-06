import QCryptLean.InfoTheory.Renyi.PetzConditional
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett

/-!
# Smooth min-entropy from Petz Rényi entropy

Renner weight-cap witnesses calibrated to a Petz Rényi threshold give a smooth min-entropy floor
for tensor powers. The signed Rényi rate and smoothing penalty are evaluated in real arithmetic;
the completed floor is converted with `ENNReal.ofReal`. The reference is fixed throughout.
-/

open Quantum.Operators Matrix InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

/-!
## Blockwise evaluation of the Petz trace
-/

/-- Polynomial application is blockwise on a block-diagonal matrix: `blockDiagonal` is a unital
algebra map, so it commutes with `Polynomial.aeval`. -/
private lemma aeval_blockDiagonal {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (M : X → Op N) (q : Polynomial ℝ) :
    (Polynomial.aeval (Matrix.blockDiagonal M)) q
      = Matrix.blockDiagonal (fun x => (Polynomial.aeval (M x)) q) := by
  classical
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [map_add, hp, hr, ← Matrix.blockDiagonal_add]
      exact congrArg _ (funext fun x => (map_add (Polynomial.aeval (M x)) p r).symm)
  | monomial k c =>
      have hR : (fun x => (Polynomial.aeval (M x)) (Polynomial.monomial k c))
          = fun x => (c : ℝ) • (M x) ^ k := by
        funext x
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      rw [hR, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul, ← Matrix.blockDiagonal_pow, ← Matrix.blockDiagonal_smul]
      rfl

/-- The continuous functional calculus is blockwise on block-diagonal matrices.

Proof by Lagrange interpolation on the union of the real spectra of `blockDiagonal M` and of
all the blocks `M x` — a finite set, since matrix spectra are finite. On that union the
interpolating polynomial agrees with `f`, so `cfc f` equals `aeval q` simultaneously at
`blockDiagonal M` and at every block, and `aeval` is blockwise. -/
private lemma cfc_blockDiagonal {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (M : X → Op N) (hM : ∀ x, IsSelfAdjoint (M x)) (f : ℝ → ℝ) :
    cfc f (Matrix.blockDiagonal M) = Matrix.blockDiagonal (fun x => cfc f (M x)) := by
  classical
  have hBD : IsSelfAdjoint (Matrix.blockDiagonal M) := by
    change (Matrix.blockDiagonal M)ᴴ = Matrix.blockDiagonal M
    rw [Matrix.blockDiagonal_conjTranspose]
    exact congrArg _ (funext fun x => hM x)
  set s : Finset ℝ :=
    (Matrix.finite_real_spectrum (A := Matrix.blockDiagonal M)).toFinset ∪
      Finset.univ.biUnion (fun x : X => (Matrix.finite_real_spectrum (A := M x)).toFinset)
    with hs
  set q : Polynomial ℝ := Lagrange.interpolate s id f with hq
  have hval : ∀ μ ∈ s, Polynomial.eval μ q = f μ := by
    intro μ hμ
    exact Lagrange.eval_interpolate_at_node (s := s) (v := (id : ℝ → ℝ)) f (Set.injOn_id _) hμ
  have hmain : cfc f (Matrix.blockDiagonal M)
      = (Polynomial.aeval (Matrix.blockDiagonal M)) q := by
    rw [← cfc_polynomial (R := ℝ) q (Matrix.blockDiagonal M)]
    refine cfc_congr fun μ hμ => (hval μ ?_).symm
    exact Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact hμ)
  have hblk : ∀ x, cfc f (M x) = (Polynomial.aeval (M x)) q := by
    intro x
    rw [← cfc_polynomial (R := ℝ) q (M x)]
    refine cfc_congr fun μ hμ => (hval μ ?_).symm
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x,
        by rw [Set.Finite.mem_toFinset]; exact hμ⟩)
  rw [hmain, aeval_blockDiagonal]
  exact congrArg _ (funext fun x => (hblk x).symm)

/-- The `CFC.rpow` real power is blockwise on block-diagonal PSD matrices. -/
private lemma rpow_blockDiagonal {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (M : X → Op N) (hM : ∀ x, (0 : Op N) ≤ M x) (y : ℝ) :
    (Matrix.blockDiagonal M) ^ y = Matrix.blockDiagonal (fun x => (M x) ^ y) := by
  have hBD : (0 : Matrix (Fin N × X) (Fin N × X) ℂ) ≤ Matrix.blockDiagonal M := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.posSemidef_blockDiagonal fun x => Matrix.nonneg_iff_posSemidef.mp (hM x)
  rw [CFC.rpow_eq_cfc_real hBD,
    cfc_blockDiagonal M (fun x => (Matrix.nonneg_iff_posSemidef.mp (hM x)).isHermitian)
      (fun t : ℝ => t ^ y)]
  exact congrArg _ (funext fun x => (CFC.rpow_eq_cfc_real (hM x)).symm)

/-- **Blockwise evaluation of the Petz trace.** On a block-diagonal layout the Petz trace is
the sum of the per-block Petz traces. -/
private lemma petzTrace_blockDiagonal {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (α : ℝ) (M R : X → Op N) (hM : ∀ x, (0 : Op N) ≤ M x) (hR : ∀ x, (0 : Op N) ≤ R x) :
    petzTrace α (Matrix.blockDiagonal M) (Matrix.blockDiagonal R)
      = ∑ x : X, petzTrace α (M x) (R x) := by
  unfold petzTrace
  rw [rpow_blockDiagonal M hM, rpow_blockDiagonal R hR, ← Matrix.blockDiagonal_mul,
    Matrix.trace_blockDiagonal, Complex.re_sum]

/-!
## L1 — the pinned-reference Petz trace is Renner's single-copy tilted MGF
-/

/-- **The Petz trace at the pinned reference is Renner's single-copy tilted MGF at tilt
`s = α − 1`.**

`Tr[ρ_XB^α (1_X ⊗ ρ_B)^{1−α}] = Σ_x tr[ρ_x^{1+(α−1)} ρ_B^{−(α−1)}]`.

Left side: Dupuis–Fawzi `\label{def:petz-renyi-divergence}`,
arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex:294`, at the DOWN reference of
`:254`. Right side: Renner's per-copy tilted MGF,
arXiv:quant-ph/0512258v2, `main.tex:4865`–`:4920`.

The identity is basis-free algebra: `ρ.toJointOp` and the pinned reference are block-diagonal
on the same layout, the CFC real powers are blockwise, and `Matrix.trace_blockDiagonal` sums
the blocks. `hnorm` is used only to form `quantumMarginalDensityOp`. There is no
positive-definiteness and no support hypothesis: at the negative exponent both sides use the
same `CFC.rpow` support pseudo-inverse power. -/
theorem petzTrace_toJointOp_eq_singleCopyMGF
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} [NeZero n]
    (α : ℝ) (ρ : InfoTheory.SmoothMinEntropy.CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    InfoTheory.Renyi.petzTrace α ρ.toJointOp
        (Matrix.blockDiagonal (fun _ : X => ρ.quantumMarginalOp))
      = InfoTheory.SmoothMinEntropy.iidAEPSingleCopyMGF ρ
          (ρ.quantumMarginalDensityOp hnorm) (α - 1) := by
  classical
  have hM : ∀ x : X, (0 : Op n) ≤ (ρ.stateMap x).toOp := fun x =>
    Matrix.nonneg_iff_posSemidef.mpr
      (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)
  have hR : ∀ _ : X, (0 : Op n) ≤ ρ.quantumMarginalOp := fun _ => by
    rw [CQState.quantumMarginalOp]
    exact Finset.sum_nonneg fun y _ => hM y
  have hE1 : (1 : ℝ) + (α - 1) = α := by ring
  have hE2 : -(α - 1) = 1 - α := by ring
  rw [CQState.toJointOp, petzTrace_blockDiagonal α _ _ hM hR]
  unfold InfoTheory.SmoothMinEntropy.iidAEPSingleCopyMGF
  rw [Complex.re_sum, hE1, hE2]
  rfl

/-!
## The Rényi calibration of Renner's weight-cap threshold
-/

/-- The block-length-scaled Rényi entropy floor at smoothing radius `ε`:

`T = m · H'_α(X|B)_ρ − log₂(2/ε²)/(α−1)`.

Direct analogue of `InfoTheory.SmoothMinEntropy.iidAEPBitBennettBlockEntropyFloor` with the Bennett
correction
replaced by the Rényi one of arXiv:1504.00233, `calculus.tex:1082`
(`\label{eq:min-renyi-bound-untight}`). Setting Renner's weight-cap threshold to this value and
the Chernoff tilt to `−(α−1)` is the entire content of this rung. -/
noncomputable def renyiBlockEntropyFloor
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (α ε : ℝ) (ρ : InfoTheory.SmoothMinEntropy.CQState X n) (m : ℕ) : ℝ :=
  (m : ℝ) * InfoTheory.Renyi.condPetzRenyiDown α ρ
    - Real.logb 2 (2 / ε ^ 2) / (α - 1)

/-- Inversion of `condPetzRenyiDown` through L1: the single-copy tilted MGF at `s = α − 1` is
`2^{−(α−1)·H'_α(X|B)_ρ}`.

This is the definition `H'_α = −(1/(α−1))·log₂ Tr[ρ^α σ^{1−α}]`
(arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex:294`) read backwards, with the
Petz trace replaced by the MGF via `petzTrace_toJointOp_eq_singleCopyMGF`. -/
private theorem singleCopyMGF_eq_rpow_condPetzRenyiDown
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} [NeZero n]
    (α : ℝ) (hα1 : 1 < α) (ρ : InfoTheory.SmoothMinEntropy.CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (hpos : 0 < InfoTheory.SmoothMinEntropy.iidAEPSingleCopyMGF ρ
      (ρ.quantumMarginalDensityOp hnorm) (α - 1)) :
    InfoTheory.SmoothMinEntropy.iidAEPSingleCopyMGF ρ
        (ρ.quantumMarginalDensityOp hnorm) (α - 1)
      = (2 : ℝ) ^ (-(α - 1) * InfoTheory.Renyi.condPetzRenyiDown α ρ) := by
  have hβ : α - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hα1)
  have hexp : -(α - 1) * InfoTheory.Renyi.condPetzRenyiDown α ρ
      = Real.logb 2 (InfoTheory.SmoothMinEntropy.iidAEPSingleCopyMGF ρ
          (ρ.quantumMarginalDensityOp hnorm) (α - 1)) := by
    rw [condPetzRenyiDown, petzRenyiDivergence, petzTrace_toJointOp_eq_singleCopyMGF α ρ hnorm]
    field_simp
  rw [hexp, Real.rpow_logb (by norm_num) (by norm_num) hpos]

/-!
## L2 — the calibration: the tilted tail value is exactly `ε²/2`
-/

/-- **At the Rényi threshold and the tilt `−(α−1)`, Renner's tilted tail value is exactly
`ε²/2`.**

This is the whole mathematical content of the rung, and it is an equality, not an inequality.
The chain is: the tail value is `λ^{W.rtTilt} · M(−W.rtTilt)` with `λ = 2^{−T}`
(arXiv:quant-ph/0512258v2, `main.tex:4586`, `:4965`); the Nussbaum–Szkoła identity
`InfoTheory.SmoothMinEntropy.iidAEPTiltedMGFSum_eq_collisionTrace` (`main.tex:4865`–`:4920`) turns
the
eigenbasis-pair sum into the operator collision trace; `M(s) = m(s)^m` factorises it; and L1
plus the definition of `H'_α` evaluate `m(α−1) = 2^{−(α−1)·H'_α}`. The exponents then collapse
to `−log₂(2/ε²)`, which is exactly the Markov budget the smoothing step needs
(arXiv:1504.00233, `calculus.tex:1082`, `\label{eq:min-renyi-bound-untight}`).

`hfeas` is the support gate that keeps `m(α−1)` from vanishing; `hreference` pins the witness's
cumulative projectors to a genuine spectral resolution of `σ^{⊗m}` and is what the
Nussbaum–Szkoła identity consumes. No upper bound on `α` is needed. -/
theorem tiltedTailValue_eq_half_eps_sq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (α : ℝ) (hα1 : 1 < α) (ε : ℝ) (hε : 0 < ε)
    (ρ : InfoTheory.SmoothMinEntropy.CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (hfeas : InfoTheory.SmoothMinEntropy.hasFeasibleLambda ρ
      (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hnorm)))
    (m : ℕ) [NeZero (n ^ m)]
    (W : InfoTheory.SmoothMinEntropy.IIDAEPSpectralWitness X n m)
    (hreference : InfoTheory.SmoothMinEntropy.iidAEPReferenceSpectralDecomposition
      (ρ.quantumMarginalDensityOp hnorm) m W)
    (hcalib : W.entropyThreshold = renyiBlockEntropyFloor α ε ρ m)
    (htilt : W.rtTilt = -(α - 1)) :
    InfoTheory.SmoothMinEntropy.iidAEPTiltedTailValue ρ m W = ε ^ 2 / 2 := by
  classical
  have hβpos : (0 : ℝ) < α - 1 := sub_pos.mpr hα1
  have hβne : α - 1 ≠ 0 := ne_of_gt hβpos
  have hQpos : 0 < InfoTheory.SmoothMinEntropy.iidAEPSingleCopyMGF ρ
      (ρ.quantumMarginalDensityOp hnorm) (α - 1) :=
    InfoTheory.SmoothMinEntropy.iidAEPSingleCopyMGF_pos ρ hnorm
      (ρ.quantumMarginalDensityOp hnorm) hfeas hβpos.le
  have hQ := singleCopyMGF_eq_rpow_condPetzRenyiDown α hα1 ρ hnorm hQpos
  have htiltneg : -W.rtTilt = α - 1 := by rw [htilt]; ring
  -- the tail value in closed form: `λ^{rtTilt} · m(α−1)^m`
  have hstep : InfoTheory.SmoothMinEntropy.iidAEPTiltedTailValue ρ m W
      = InfoTheory.SmoothMinEntropy.weightCapScale W ^ W.rtTilt
        * InfoTheory.SmoothMinEntropy.iidAEPSingleCopyMGF ρ
            (ρ.quantumMarginalDensityOp hnorm) (α - 1) ^ m := by
    unfold InfoTheory.SmoothMinEntropy.iidAEPTiltedTailValue
    rw [InfoTheory.SmoothMinEntropy.iidAEPTiltedMGFSum_eq_collisionTrace ρ
        (ρ.quantumMarginalDensityOp hnorm) m W hreference (-W.rtTilt),
      InfoTheory.SmoothMinEntropy.iidAEPCollisionTrace_eq_singleCopyMGF_pow ρ
        (ρ.quantumMarginalDensityOp hnorm) m (-W.rtTilt), htiltneg]
  have hscale : InfoTheory.SmoothMinEntropy.weightCapScale W
      = (2 : ℝ) ^ (-renyiBlockEntropyFloor α ε ρ m) := by
    unfold InfoTheory.SmoothMinEntropy.weightCapScale
    rw [hcalib]
  rw [hstep, hscale, hQ, htilt,
    ← Real.rpow_natCast ((2 : ℝ) ^ (-(α - 1) * InfoTheory.Renyi.condPetzRenyiDown α ρ)) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hexp : -renyiBlockEntropyFloor α ε ρ m * -(α - 1)
      + -(α - 1) * InfoTheory.Renyi.condPetzRenyiDown α ρ * (m : ℝ)
      = -Real.logb 2 (2 / ε ^ 2) := by
    unfold renyiBlockEntropyFloor
    field_simp
    ring
  rw [hexp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity), inv_div]

/-!
## L3 — smoothing control
-/

/-- **The weight-cap witness at the Rényi threshold is `ε`-close in purified distance.**

`traceDefect ≤ ε²/2` and `P(ρ^{⊗m}, ρ̄) ≤ ε`.

Renner's discarded-mass chain (arXiv:quant-ph/0512258v2, `main.tex:4707`–`:4757`,
`\label{eq:tracelowbound}`, then the Markov drop at `:4965`) bounds the trace defect by the
tilted tail value, which L2 evaluates to `ε²/2`; the fidelity route of `main.tex:4671`–`:4706`
gives `P ≤ √(2·traceDefect)`. This is the library's upward relaxation of Tomamichel's
`P ≤ √(2 tr Σ − (tr Σ)²)` (arXiv:1504.00233, `calculus.tex:1008`,
`\label{lm:aep/smooth-bound}`).

`hpin` and `hreference` are both load-bearing (documented at the lemmas: without `hpin`
the free `smoothedState` field admits `0`; without `hreference` a non-idempotent `B_z` gives
zero trace defect and purified distance `1`). `ε < 1` is not needed here. -/
theorem purifiedDistance_smoothedState_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (α : ℝ) (hα1 : 1 < α) (ε : ℝ) (hε : 0 < ε)
    (ρ : InfoTheory.SmoothMinEntropy.CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (hfeas : InfoTheory.SmoothMinEntropy.hasFeasibleLambda ρ
      (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hnorm)))
    (m : ℕ) [NeZero m] [NeZero (n ^ m)] [Nonempty (Fin m → X)]
    (W : InfoTheory.SmoothMinEntropy.IIDAEPSpectralWitness X n m)
    (hreference : InfoTheory.SmoothMinEntropy.iidAEPReferenceSpectralDecomposition
      (ρ.quantumMarginalDensityOp hnorm) m W)
    (hpin : InfoTheory.SmoothMinEntropy.iidAEPIsWeightCapSmoothedState ρ m W)
    (hcalib : W.entropyThreshold = renyiBlockEntropyFloor α ε ρ m)
    (htilt : W.rtTilt = -(α - 1)) :
    InfoTheory.SmoothMinEntropy.iidAEPTraceDefect ρ m W ≤ ε ^ 2 / 2 ∧
      InfoTheory.SmoothMinEntropy.CQState.purifiedDistance
        (InfoTheory.SmoothMinEntropy.iidAEPTensorState ρ m) W.smoothedState ≤ ε := by
  have htail := tiltedTailValue_eq_half_eps_sq α hα1 ε hε ρ hnorm hfeas m W hreference
    hcalib htilt
  have h1 :=
    InfoTheory.SmoothMinEntropy.iidAEP_traceDefect_eq_discardedMass ρ m W hpin
  have h2 :=
    InfoTheory.SmoothMinEntropy.iidAEP_discardedOperatorMass_le_discardedSpectralMass
      ρ (ρ.quantumMarginalDensityOp hnorm) m W hreference
  have h3 :=
    InfoTheory.SmoothMinEntropy.iidAEPDiscardedSpectralMass_le_tiltedTailValue_of_tilt_nonpos
      ρ (ρ.quantumMarginalDensityOp hnorm) m W hfeas hreference (by rw [htilt]; linarith)
  have hdef : InfoTheory.SmoothMinEntropy.iidAEPTraceDefect ρ m W ≤ ε ^ 2 / 2 := by
    rw [h1, ← htail]
    exact le_trans h2 h3
  refine ⟨hdef, ?_⟩
  refine le_trans
    (InfoTheory.SmoothMinEntropy.iidAEP_weightCap_purifiedDistance_le_sqrt_two_mul_traceDefect
      ρ (ρ.quantumMarginalDensityOp hnorm) m W hreference hpin) ?_
  refine le_trans (Real.sqrt_le_sqrt (by linarith : 2 * _ ≤ 2 * (ε ^ 2 / 2))) ?_
  rw [show (2 : ℝ) * (ε ^ 2 / 2) = ε ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hε.le]

/-!
## L4 — the entropy floor at the witness
-/

/-!
## L5 — the endpoint
-/

/-- Renner's weight-cap spectral witness, calibrated to the Rényi threshold
`renyiBlockEntropyFloor α ε ρ m` and the Chernoff tilt `−(α−1)`.

The construction is threshold- and tilt-parametric and is reused unchanged from
`InfoTheory.SmoothMinEntropy.exists_iidAEPBitBennettSetup`: the five-stage reference chain of
`Renner/IIDAEP/SpectralSetup.lean`, then `InfoTheory.SmoothMinEntropy.iidAEPRennerCutWitness` at the
threshold, then `InfoTheory.SmoothMinEntropy.iidAEPWitnessWithRtTilt`, which overwrites only the
scalar tilt. -/
private theorem exists_renyiSmoothingWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (α ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (ρ : InfoTheory.SmoothMinEntropy.CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (m : ℕ) [NeZero m] [NeZero (n ^ m)] [Nonempty (Fin m → X)] :
    ∃ W : InfoTheory.SmoothMinEntropy.IIDAEPSpectralWitness X n m,
      InfoTheory.SmoothMinEntropy.iidAEPReferenceSpectralDecomposition
          (ρ.quantumMarginalDensityOp hnorm) m W ∧
        W.entropyThreshold = renyiBlockEntropyFloor α ε ρ m ∧
        InfoTheory.SmoothMinEntropy.iidAEPIsWeightCapSmoothedState ρ m W ∧
        InfoTheory.SmoothMinEntropy.iidAEPSpectralCutBlockDomination
          (ρ.quantumMarginalDensityOp hnorm) m W ∧
        W.rtTilt = -(α - 1) := by
  have hcore := InfoTheory.SmoothMinEntropy.exists_iidAEPWitnessProjectorSubstate
    ρ hnorm (ρ.quantumMarginalDensityOp hnorm) m ε hε hε1
  have heigen :=
    InfoTheory.SmoothMinEntropy.exists_iidAEPWitnessNonnegReferenceEigenvalues
      ρ hnorm (ρ.quantumMarginalDensityOp hnorm) m ε hε hε1 hcore
  have hincr := InfoTheory.SmoothMinEntropy.exists_iidAEPWitnessOrthogonalIncrements
    ρ hnorm (ρ.quantumMarginalDensityOp hnorm) m ε hε hε1 heigen
  have haction :=
    InfoTheory.SmoothMinEntropy.exists_iidAEPWitnessReferenceSpectralAction
      ρ hnorm (ρ.quantumMarginalDensityOp hnorm) m ε hε hε1 hincr
  obtain ⟨W₀, hW₀⟩ :=
    InfoTheory.SmoothMinEntropy.exists_iidAEPWitnessReferenceSpectralDecomposition
      ρ (ρ.quantumMarginalDensityOp hnorm) m ε hε hε1 haction
  exact ⟨InfoTheory.SmoothMinEntropy.iidAEPWitnessWithRtTilt
      (InfoTheory.SmoothMinEntropy.iidAEPRennerCutWitness ρ m
        (ρ.quantumMarginalDensityOp hnorm) W₀ hW₀.2 (renyiBlockEntropyFloor α ε ρ m))
      (-(α - 1)),
    InfoTheory.SmoothMinEntropy.iidAEPRennerCutWitness_reference ρ m
      (ρ.quantumMarginalDensityOp hnorm) W₀ hW₀.2 (renyiBlockEntropyFloor α ε ρ m),
    rfl,
    InfoTheory.SmoothMinEntropy.iidAEPRennerCutWitness_isWeightCapSmoothedState ρ m
      (ρ.quantumMarginalDensityOp hnorm) W₀ hW₀.2 (renyiBlockEntropyFloor α ε ρ m),
    InfoTheory.SmoothMinEntropy.iidAEPRennerCutWitness_blockDomination ρ m
      (ρ.quantumMarginalDensityOp hnorm) W₀ hW₀.2 (renyiBlockEntropyFloor α ε ρ m),
    rfl⟩

/-- Spectral domination gives the completed Rényi floor in extended conditional entropy.
No retained-weight or tail-bound hypotheses are needed for this operator implication. -/
theorem renyiBlockEntropyFloor_le_conditionalMinEntropy
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} [NeZero n]
    (α ε : ℝ) (ρ : InfoTheory.SmoothMinEntropy.CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) (m : ℕ)
    (W : InfoTheory.SmoothMinEntropy.IIDAEPSpectralWitness X n m)
    (hblock : InfoTheory.SmoothMinEntropy.iidAEPSpectralCutBlockDomination
      (ρ.quantumMarginalDensityOp hnorm) m W)
    (hcalib : W.entropyThreshold = renyiBlockEntropyFloor α ε ρ m) :
    ENNReal.ofReal (renyiBlockEntropyFloor α ε ρ m) ≤
      InfoTheory.SmoothMinEntropy.conditionalMinEntropy W.smoothedState
        (InfoTheory.SmoothMinEntropy.iidAEPTensorReference
          (ρ.quantumMarginalDensityOp hnorm) m) := by
  rw [← hcalib]
  exact InfoTheory.SmoothMinEntropy.iidAEP_entropy_from_reference_domination
    (ρ.quantumMarginalDensityOp hnorm) m W
    (InfoTheory.SmoothMinEntropy.iidAEP_spectral_cut_feasible_domination
      (ρ.quantumMarginalDensityOp hnorm) m W hblock)

/-- The Petz Rényi block floor bounds extended smooth entropy for every positive radius.
At radius at least one the normalized tensor power has the zero state in its smoothing ball. -/
theorem smoothMinEntropy_tensorPower_ge_condPetzRenyiDown_sub
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (α : ℝ) (hα1 : 1 < α) (ε : ℝ) (hε : 0 < ε)
    (ρ : InfoTheory.SmoothMinEntropy.CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (m : ℕ) [NeZero m] :
    ENNReal.ofReal ((m : ℝ) * condPetzRenyiDown α ρ
      - Real.logb 2 (2 / ε ^ 2) / (α - 1)) ≤
      InfoTheory.SmoothMinEntropy.smoothMinEntropy ε
        (InfoTheory.SmoothMinEntropy.CQState.tensorPower ρ m)
        (InfoTheory.SmoothMinEntropy.SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hnorm)) m) := by
  by_cases hε1 : ε < 1
  · have hfeas :=
      InfoTheory.SmoothMinEntropy.hasFeasibleLambda_quantumMarginalDensityOp ρ hnorm
    obtain ⟨W, href, hthr, hpin, hblock, htilt⟩ :=
      exists_renyiSmoothingWitness α ε hε hε1 ρ hnorm m
    have hpd := purifiedDistance_smoothedState_le α hα1 ε hε ρ hnorm hfeas m W
      href hpin hthr htilt
    exact InfoTheory.SmoothMinEntropy.smoothMinEntropy_ge_of_hmin_approx
      (InfoTheory.SmoothMinEntropy.iidAEPTensorState ρ m) W.smoothedState
      (InfoTheory.SmoothMinEntropy.iidAEPTensorReference
        (ρ.quantumMarginalDensityOp hnorm) m)
      (renyiBlockEntropyFloor α ε ρ m) hpd.2
      (renyiBlockEntropyFloor_le_conditionalMinEntropy α ε ρ hnorm m W hblock hthr)
  · rw [InfoTheory.SmoothMinEntropy.smoothMinEntropy_eq_top_of_weight_le_eps_sq
      hε.le _ _ (by
        have hn := InfoTheory.SmoothMinEntropy.iidAEP_tensor_state_normalized ρ hnorm m
        change ∑ xs, ((InfoTheory.SmoothMinEntropy.iidAEPTensorState ρ m).stateMap xs).trace
          ≤ ε ^ 2
        rw [hn]
        nlinarith)]
    exact le_top

/-- The tensor-power Rényi form of the extended smooth-entropy lower bound. -/
theorem smoothMinEntropy_tensorPower_ge_condPetzRenyiDown_tensorPower_sub
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (α : ℝ) (hα1 : 1 < α) (ε : ℝ) (hε : 0 < ε)
    (ρ : InfoTheory.SmoothMinEntropy.CQState X n)
    (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (m : ℕ) [NeZero m] :
    ENNReal.ofReal (condPetzRenyiDown α (InfoTheory.SmoothMinEntropy.CQState.tensorPower ρ m)
      - Real.logb 2 (2 / ε ^ 2) / (α - 1)) ≤
      InfoTheory.SmoothMinEntropy.smoothMinEntropy ε
        (InfoTheory.SmoothMinEntropy.CQState.tensorPower ρ m)
        (InfoTheory.SmoothMinEntropy.SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hnorm)) m) := by
  rw [renyiCondEntropy_down_tensorPower α ρ m]
  exact smoothMinEntropy_tensorPower_ge_condPetzRenyiDown_sub α hα1 ε hε ρ hnorm m

end InfoTheory.Renyi

end
