import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCap
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCapVectorFamily
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBitsBlockDomination
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDDiscardedMass
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSingleCopyEnvelope
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CfcSpectral

/-!
# Renner Cramér–Chernoff discarded-mass tail for `thm:Hmincondrep` (bit track)

The quantum-AEP / Cramér–Chernoff bound on the operator discarded mass of the
weight-cap blocks (Renner, main.tex:4759–4979). The top result
`iidAEP_discardedMass_le_rtErrorBound` shows
`Σ_xs [tr(ρ^{⊗}_xs) − tr(ρ̄_xs)] ≤ iidAEPRtErrorBound`, where
`iidAEPRtErrorBound = 2^(−n·δ²/(2(log₂ μ)²))` and `μ = γ + 2`.

It composes the operator-vs-spectral comparison
`iidAEP_discardedOperatorMass_le_discardedSpectralMass`
with `iidAEPDiscardedSpectralMass_le_rtErrorBound`,
which combines the Markov drop of the cap indicator at the optimal tilt
`s = −W.rtTilt ≥ 0` with the operator-collision MGF bound.
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.VonNeumannEntropy
open InfoTheory.SmoothMinEntropy.IIDAEPCumulative
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The Cramér–Chernoff / quantum-AEP tail `D ≤ rtErrorBound` (Renner main.tex:4759–4979)

The discarded spectral mass `D` is bounded by the relaxed MGF tail in two steps.
The decomposition routes through the operator collision trace rather than a naive
eigenvalue-product tensorization, which is unavailable because the witness index
`Fin (n^n_copies)` is a sorted index, not a product index:

1. Markov drop of the cap indicator: for `s = −W.rtTilt ≥ 0` the indicator
   `λ q_z < p_x` is dominated by the tilted ratio `(p_x/(λ q_z))^s ≥ 1`, giving
   `D ≤ λ^(−s)·M(s)` with `M(s) = iidAEPTiltedMGFSum`. Its only nonelementary
   input is the support fact (positive-overlap blocks have positive reference
   eigenvalue), carried by `hfeas`/`hreference`.
2. `λ^(−s)·M(s) ≤ rtErrorBound`: `M(s)` is the collision trace `tr[R^{1+s} τ^{−s}]`,
   which factorizes as the `N`-th power of the single-copy collision trace; the
   single-copy trace is bounded by the `r_t`/collision envelope with `μ = γ + 2`,
   and the quadratic relaxation `rt(t, μ) ≤ ½ t² (log μ)²` lands on
   `iidAEPRtErrorBound`. -/

/-- **Renner's tilted MGF sum `M(s)`** (main.tex:4865–4960): the Cramér–Chernoff
moment-generating quantity over the witness eigenbasis data,
`M(s) = Σ_{xs} Σ_x Σ_z p_x(xs)^(1+s) · q_z^(−s) · |⟨z|x⟩|²`,
with block eigenvalues `p_x = blockEigenvalue`, reference eigenvalues
`q_z = W.referenceEigenvalue`, and squared overlaps
`|⟨z|x⟩|² = blockReferenceOverlap`. Powers are `Real.rpow`. This is the
spectral-sum form of the operator collision trace `tr[R^{1+s} τ^{−s}]`. -/
def iidAEPTiltedMGFSum
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) (s : ℝ) : ℝ :=
  ∑ xs : Fin n_copies → X, ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies),
    blockEigenvalue ρ n_copies xs x ^ (1 + s)
      * W.referenceEigenvalue z ^ (-s)
      * blockReferenceOverlap ρ n_copies W xs x z

/-- **Renner's optimal-tilt MGF tail value** `λ^(−s) · M(s)` at the witness tilt
`s = −W.rtTilt`, with `λ = weightCapScale W = 2^(−T)` the separation scale. At the
optimal tilt `W.rtTilt = iidAEPOptimalTilt ρ σ n_copies ε ≤ 0` the exponent
`s = −W.rtTilt ≥ 0`, so the Markov drop is valid (main.tex:4965). -/
def iidAEPTiltedTailValue
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  weightCapScale W ^ W.rtTilt
    * iidAEPTiltedMGFSum ρ n_copies W (-W.rtTilt)

/-! ### Scalar sign facts for the optimal tilt

Pure scalar facts about the spectral radius `μ`, the bit penalty `δ`, and the
optimal tilt `τ*` that certify the Markov exponent `s = −W.rtTilt ≥ 0` used by the
Cramér–Chernoff drop. -/

/-- The Renner spectral radius is strictly greater than `1` (in fact `≥ 2`):
it is `(classicalRank : ℝ) + tracedSquareTimesInvFactor + 2` with both leading
terms nonnegative. -/
lemma iidAEPSpectralRadius_one_lt
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) :
    1 < iidAEPSpectralRadius ρ σ := by
  unfold iidAEPSpectralRadius
  have h1 : (0 : ℝ) ≤ (ρ.classicalRank : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ ρ.tracedSquareTimesInvFactor σ :=
    InfoTheory.SmoothMinEntropy.tracedSquareTimesInvFactor_nonneg ρ σ
  linarith

/-- The Renner penalty `δ_iidAEP_general` is non-negative: it is twice a
non-negative base-two logarithm (`logb 2 μ ≥ 0` since the spectral radius
`μ ≥ 2`) scaled by the non-negative noise factor. -/
lemma δ_iidAEP_general_nonneg
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) :
    0 ≤ δ_iidAEP_general ρ σ n_copies ε := by
  unfold δ_iidAEP_general
  have hμ2 : (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ :=
    InfoTheory.SmoothMinEntropy.two_le_iidAEPSpectralRadius ρ σ
  have hlogb : 0 ≤ Real.logb 2 (iidAEPSpectralRadius ρ σ) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hnf : 0 ≤ noiseFactor n_copies ε := Real.sqrt_nonneg _
  have hμ_eq :
      (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2
        = iidAEPSpectralRadius ρ σ := rfl
  rw [hμ_eq]
  positivity

/-- The clamped optimal tilt is non-positive: both arguments of the `min` are
nonnegative (`δ ≥ 0`, `log 2 > 0`, `log μ > 0` since `μ ≥ 2`), so their minimum
is nonnegative and its negation is `≤ 0`. -/
lemma iidAEPOptimalTilt_nonpos
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (n_copies : ℕ) (ε : ℝ) :
    iidAEPOptimalTilt ρ σ n_copies ε ≤ 0 := by
  unfold iidAEPOptimalTilt
  have hδ : 0 ≤ δ_iidAEP_general ρ σ n_copies ε :=
    δ_iidAEP_general_nonneg ρ σ n_copies ε
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hμ2 : (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ :=
    InfoTheory.SmoothMinEntropy.two_le_iidAEPSpectralRadius ρ σ
  have hlogμ : 0 < Real.log (iidAEPSpectralRadius ρ σ) :=
    Real.log_pos (by linarith)
  have ha : 0 ≤ δ_iidAEP_general ρ σ n_copies ε * Real.log 2
      / (Real.log (iidAEPSpectralRadius ρ σ)) ^ 2 := by positivity
  have hb : 0 ≤ Real.log 2 / Real.log (iidAEPSpectralRadius ρ σ) := by
    positivity
  have : 0 ≤ min (δ_iidAEP_general ρ σ n_copies ε * Real.log 2
            / (Real.log (iidAEPSpectralRadius ρ σ)) ^ 2)
        (Real.log 2 / Real.log (iidAEPSpectralRadius ρ σ)) := le_min ha hb
  linarith

/-- **Cramér–Chernoff per-term Markov bound.** For a nonpositive tilt `t ≤ 0` (so
`s = −t ≥ 0`), the over-threshold cap-indicator term `p · o` (active only on the
event `λ q < p`) is dominated by the tilted MGF term
`λ^t · (p^(1+(−t)) · q^(−(−t)) · o)`. On the cap event with `q > 0` this is
`1 ≤ (p/(λ q))^{−t}`. When `q = 0` the support hypothesis `hsupp` forces the
overlap `o` to vanish. `hsupp` is required only on the cap event, where `0 < p` is
forced (`0 ≤ λ q < p`); a zero block eigenvalue is genuinely possible in the
reference kernel, so the positivity guard is essential. -/
lemma chernoff_termwise_bound
    (p o lam q t : ℝ)
    (hp : 0 ≤ p) (ho : 0 ≤ o) (hlam : 0 < lam) (hq : 0 ≤ q)
    (ht : t ≤ 0) (hsupp : 0 < p → q = 0 → o = 0) :
    (if lam * q < p then p * o else 0)
      ≤ lam ^ t * (p ^ (1 + -t) * q ^ (-(-t)) * o) := by
  have hs : 0 ≤ -t := by linarith
  have hrhs_nn : 0 ≤ lam ^ t * (p ^ (1 + -t) * q ^ (-(-t)) * o) := by
    have h1 := Real.rpow_nonneg hlam.le t
    have h2 := Real.rpow_nonneg hp (1 + -t)
    have h3 := Real.rpow_nonneg hq (-(-t))
    positivity
  split_ifs with hcap
  · -- cap event `λ q < p`
    rcases eq_or_lt_of_le hq with hq0 | hqpos
    · -- reference kernel `q = 0`: `0 < p` is forced, so the support fact applies
      have hppos : 0 < p := lt_of_le_of_lt (mul_nonneg hlam.le hq) hcap
      rw [hsupp hppos hq0.symm]; simp
    · -- bulk `q > 0`
      have hlamq_pos : 0 < lam * q := mul_pos hlam hqpos
      have hppos : 0 < p := lt_trans hlamq_pos hcap
      have hpsplit : p ^ (1 + -t) = p * p ^ (-t) := by
        rw [Real.rpow_add hppos, Real.rpow_one]
      -- the tilted factor exceeds one
      have h1 : p ^ t ≤ lam ^ t * q ^ t := by
        have := Real.rpow_le_rpow_of_nonpos hlamq_pos (le_of_lt hcap) ht
        rwa [Real.mul_rpow hlam.le hq] at this
      have h2 : p ^ t * p ^ (-t) ≤ lam ^ t * q ^ t * p ^ (-t) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp _)
      have h3 : p ^ t * p ^ (-t) = 1 := by
        rw [← Real.rpow_add hppos]; simp
      have key : (1 : ℝ) ≤ lam ^ t * p ^ (-t) * q ^ t := by
        have h2' : (1 : ℝ) ≤ lam ^ t * q ^ t * p ^ (-t) := h3 ▸ h2
        exact le_of_le_of_eq h2' (by ring)
      calc p * o = (p * o) * 1 := (mul_one _).symm
        _ ≤ (p * o) * (lam ^ t * p ^ (-t) * q ^ t) :=
              mul_le_mul_of_nonneg_left key (mul_nonneg hp ho)
        _ = lam ^ t * (p ^ (1 + -t) * q ^ (-(-t)) * o) := by
              rw [hpsplit, neg_neg]; ring
  · exact hrhs_nn

/-- **Support fact for the Cramér–Chernoff drop** (main.tex:4865–4920). If a sorted
reference eigenvector `|z⟩` (`W.spectralProjector z`) lies in the kernel of the
tensor-power reference `(id⊗σ)^{⊗N}` — i.e. `q_z = W.referenceEigenvalue z = 0` —
then it is orthogonal to every block eigenvector `|x⟩` of `ρ^{⊗N}` with positive
eigenvalue `p_x > 0`, so `|⟨z|x⟩|² = blockReferenceOverlap` vanishes. This is the
content of `hfeas` (single-copy support gate `supp ρ_x ⊆ supp σ`, lifted to the
tensor power) combined with the reference geometry `hreference`; it rules out the
orthogonal-support counterexample (`ρ = P₀`, `σ = P₁`).

The positivity hypothesis `hp : 0 < blockEigenvalue ρ n_copies xs x` is essential:
only positive-eigenvalue eigenvectors lie in `supp ρ^{⊗N}_xs`. Without it the
statement is false — a zero-eigenvalue eigenvector may itself be a reference-kernel
vector and overlap `|z⟩`.

Proof via the support chain: Löwner domination `ρ_x ≼ λ₀ σ` tensors to
`T = ρ^{⊗N}_xs ≼ c • τ`, giving `ker τ ⊆ ker T`; at `q_z = 0` the projector `P_z`
lands in `ker τ`, so `T·P_z = 0`, whence `P_z·M = 0` for the eigenprojector
`M = |x⟩⟨x|` and the overlap trace vanishes. -/
lemma blockReferenceOverlap_eq_zero_of_referenceEigenvalue_eq_zero
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (xs : Fin n_copies → X) (x z : Fin (n ^ n_copies))
    (hp : 0 < blockEigenvalue ρ n_copies xs x)
    (hq : W.referenceEigenvalue z = 0) :
    blockReferenceOverlap ρ n_copies W xs x z = 0 := by
  -- Notation: `T` the block operator `ρ^{⊗}_xs`, `τ` the reference, `Pz`, `M` the
  -- rank-one increment/eigenprojectors `|z⟩⟨z|`, `|x⟩⟨x|`.
  -- Tensor-power Löwner domination `T ≼ c • τ` (the operator content of `hfeas`).
  obtain ⟨c, hle⟩ :=
    iidAEPBlockOp_opLe_smul_tensorReference ρ σ n_copies hfeas xs
  -- Hermitian / PSD facts.
  have hT_psd : ((iidAEPTensorState ρ n_copies).stateMap xs).toOp.PosSemidef :=
    posSemidefOp_implies_mathlib
      ((iidAEPTensorState ρ n_copies).stateMap xs).toPosSemidefOp
  have hT_herm : ((iidAEPTensorState ρ n_copies).stateMap xs).toOp.IsHermitian :=
    hT_psd.isHermitian
  have hτ_herm : (iidAEPTensorReference σ n_copies).toOp.IsHermitian :=
    (iidAEPTensorReference σ n_copies).isHermitian
  have hPz_herm : (W.spectralProjector z).IsHermitian := (hreference.2.1).2.1 z
  -- Reference kernel: `τ * Pz = 0` (spectral action at `q_z = 0`).
  have hτPz : (iidAEPTensorReference σ n_copies).toOp * W.spectralProjector z = 0 := by
    have h := ((hreference.2.2.1).2 z).1
    rw [hq] at h
    simpa using h
  -- Domination + kernel ⟹ `T * Pz = 0` (kernel inclusion).
  have hTPz : ((iidAEPTensorState ρ n_copies).stateMap xs).toOp *
      W.spectralProjector z = 0 :=
    mul_eq_zero_of_opLe_smul hT_psd hτ_herm hPz_herm hle hτPz
  -- Adjoint: `Pz * T = 0`.
  have hPzT : W.spectralProjector z *
      ((iidAEPTensorState ρ n_copies).stateMap xs).toOp = 0 := by
    have h := congrArg Matrix.conjTranspose hTPz
    rwa [Matrix.conjTranspose_mul, hT_herm, hPz_herm, Matrix.conjTranspose_zero] at h
  -- Eigenprojector relation `T * M = p_x • M`.
  have hTM := blockOp_mul_blockSpectralProjector ρ n_copies xs x
  -- `Pz * M = 0`.
  have hpne : (blockEigenvalue ρ n_copies xs x : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne'
  have hMfac : blockSpectralProjector ρ n_copies xs x =
      ((blockEigenvalue ρ n_copies xs x : ℂ)⁻¹) •
        (((iidAEPTensorState ρ n_copies).stateMap xs).toOp *
          blockSpectralProjector ρ n_copies xs x) := by
    rw [hTM, smul_smul, inv_mul_cancel₀ hpne, one_smul]
  have hPzM : W.spectralProjector z * blockSpectralProjector ρ n_copies xs x = 0 := by
    rw [hMfac, mul_smul_comm, ← mul_assoc, hPzT, Matrix.zero_mul, smul_zero]
  unfold blockReferenceOverlap
  rw [hPzM, Matrix.trace_zero, Complex.zero_re]

/-- **Cramér–Chernoff / Markov drop of the cap indicator** (main.tex:4865–4920). For
the tilt `s = −W.rtTilt ≥ 0`, dropping the over-threshold indicator of `D` against
the tilted ratio gives `D = iidAEPDiscardedSpectralMass ≤
iidAEPTiltedTailValue`. Elementary `s ≥ 0` Markov over the nonnegative witness
data; the only nonelementary input is the support fact
(`blockReferenceOverlap_eq_zero_of_referenceEigenvalue_eq_zero`), so `hfeas` and
`hreference` are load-bearing. `hparams` certifies `s = −W.rtTilt ≥ 0`. -/
theorem iidAEPDiscardedSpectralMass_le_tiltedTailValue
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hparams : iidAEPRtParameters ρ σ ε W) :
    iidAEPDiscardedSpectralMass ρ n_copies W
      ≤ iidAEPTiltedTailValue ρ n_copies W := by
  classical
  -- the optimal tilt is nonpositive, so the Markov exponent `s = −W.rtTilt ≥ 0`
  have ht : W.rtTilt ≤ 0 := by
    rw [hparams.2]; exact iidAEPOptimalTilt_nonpos ρ σ n_copies ε
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

/-- **Collision-trace identity** (main.tex:4865–4920). Renner's tilted MGF spectral
sum equals the operator collision trace:
`iidAEPTiltedMGFSum ρ n_copies W s = iidAEPCollisionTrace ρ σ n_copies s`.
Per `xs`, the inner double sum is the spectral expansion of `tr[R_xs^{1+s} τ^{−s}]`:
`Σ_x p_x^{1+s}|x⟩⟨x| = R_xs^{1+s}` and `Σ_z q_z^{−s}|z⟩⟨z| = τ^{−s}` (the reference
resolution carried by `hreference`, hence load-bearing), with the overlaps
assembling the trace of the product. -/
theorem iidAEPTiltedMGFSum_eq_collisionTrace
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (s : ℝ) :
    iidAEPTiltedMGFSum ρ n_copies W s
      = iidAEPCollisionTrace ρ σ n_copies s := by
  classical
  -- Unpack the reference spectral resolution data.
  obtain ⟨_hq_nn, hincr, haction, _hcum⟩ := hreference
  obtain ⟨hPidem, hPherm, _hPne, hPorth, hPsum⟩ := hincr
  obtain ⟨hτ_resolve, _⟩ := haction
  unfold iidAEPTiltedMGFSum iidAEPCollisionTrace
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  -- Mathlib eigenbasis resolution properties of the block operator `R`
  -- (`P_x = blockSpectralProjector` is defeq to the `vecMulVec` rank-one projector).
  have hincrR := isHermitian_eigenvectorBasis_rankOneProjectors_increments
    ((iidAEPTensorState ρ n_copies).stateMap
      xs).toPosSemidefOp.toHermitianOp.isHermitian
  have hconv : ∀ x, blockSpectralProjector ρ n_copies xs x
      = Matrix.vecMulVec
          (((((iidAEPTensorState ρ n_copies).stateMap
            xs).toPosSemidefOp.toHermitianOp.isHermitian).eigenvectorBasis x).ofLp)
          (star ((((iidAEPTensorState ρ n_copies).stateMap
            xs).toPosSemidefOp.toHermitianOp.isHermitian).eigenvectorBasis x).ofLp) :=
    fun x => rfl
  have hPx_idem : ∀ x, blockSpectralProjector ρ n_copies xs x
      * blockSpectralProjector ρ n_copies xs x = blockSpectralProjector ρ n_copies xs x := by
    intro x; rw [hconv]; exact hincrR.1 x
  have hPx_herm : ∀ x, (blockSpectralProjector ρ n_copies xs x).IsHermitian := by
    intro x; rw [Matrix.IsHermitian, hconv]; exact hincrR.2.1 x
  have hPx_orth : ∀ x x', x ≠ x' →
      blockSpectralProjector ρ n_copies xs x * blockSpectralProjector ρ n_copies xs x' = 0 := by
    intro x x' hxx'; rw [hconv, hconv]; exact hincrR.2.2.2.1 x x' hxx'
  have hPx_sum : ∑ x, blockSpectralProjector ρ n_copies xs x = 1 := by
    rw [Finset.sum_congr rfl (fun x _ => hconv x)]; exact hincrR.2.2.2.2
  -- The two tilted CFC real powers expand coefficientwise (lemma (b)). Rewriting with
  -- the resolution lemmas directly avoids re-synthesizing the `Op^ℝ` CFC-power instance.
  rw [CfcSpectral.rpow_of_orthogonalResolution _ (blockEigenvalue ρ n_copies xs)
      (blockSpectralProjector ρ n_copies xs)
      (Matrix.nonneg_iff_posSemidef.mpr
        (posSemidefOp_implies_mathlib
          ((iidAEPTensorState ρ n_copies).stateMap xs).toPosSemidefOp))
      hPx_herm hPx_idem hPx_orth hPx_sum (blockSpectralDecomposition ρ n_copies xs) (1 + s),
    CfcSpectral.rpow_of_orthogonalResolution _ (W.referenceEigenvalue) (W.spectralProjector)
      (Matrix.nonneg_iff_posSemidef.mpr
        (posSemidefOp_implies_mathlib (iidAEPTensorReference σ n_copies).toPosSemidefOp))
      hPherm hPidem hPorth hPsum hτ_resolve (-s),
    Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  -- Per `(x, z)`: pull out the real scalars and rewrite the projector overlap.
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_smul,
    smul_eq_mul,
    show ((blockEigenvalue ρ n_copies xs x ^ (1 + s) : ℝ) : ℂ)
          * ((W.referenceEigenvalue z ^ (-s) : ℝ) : ℂ)
        = (((blockEigenvalue ρ n_copies xs x ^ (1 + s))
            * (W.referenceEigenvalue z ^ (-s)) : ℝ) : ℂ) from by push_cast; ring,
    Complex.re_ofReal_mul,
    show (blockSpectralProjector ρ n_copies xs x * W.spectralProjector z).trace
        = (W.spectralProjector z * blockSpectralProjector ρ n_copies xs x).trace
        from Matrix.trace_mul_comm _ _,
    blockReferenceOverlap]

/-- **Operator-collision MGF tail bound** (main.tex:4920–4979). At the optimal tilt
`s = −W.rtTilt`, Renner's tilted MGF sum is bounded by
`λ^(−s) · iidAEPRtErrorBound`, with `λ = weightCapScale W = 2^(−T)`:
`M(−W.rtTilt) ≤ λ^(−W.rtTilt) · iidAEPRtErrorBound`.
The right-hand side is Renner's relaxed envelope `2^(−n·δ²/(2(log₂ μ)²))`. The
proof rewrites the eigenbasis spectral sum as the operator collision trace via
`iidAEPTiltedMGFSum_eq_collisionTrace` and applies
`iidAEPCollisionTrace_le_rtErrorBound`.

`hfeas` keeps `σ^{−s}` and the `s = 1` collision moment finite; `hparams` pins the
optimal tilt, `hregime` the large-block regime, and `hcalib` the entropy threshold. -/
theorem iidAEPTiltedMGFSum_le_rtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (_hblock : iidAEPSpectralCutBlockDomination σ n_copies W)
    (hparams : iidAEPRtParameters ρ σ ε W)
    (hregime : iidAEPLargeBlockRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε)
    (_hcross : iidAEPNonnegativeThresholdCrossing W) :
    iidAEPTiltedMGFSum ρ n_copies W (-W.rtTilt)
      ≤ weightCapScale W ^ (-W.rtTilt)
        * iidAEPRtErrorBound ρ σ n_copies ε W := by
  -- Bridge the eigenbasis spectral sum to the operator collision trace, …
  rw [iidAEPTiltedMGFSum_eq_collisionTrace ρ σ n_copies W hreference]
  -- … then apply the operator-collision MGF tail bound.
  exact iidAEPCollisionTrace_le_rtErrorBound
    ρ hρ_norm σ n_copies ε W hfeas hparams hregime hcalib

/-- **Optimal-tilt MGF tail bound** (main.tex:4920–4979). The tail value
`iidAEPTiltedTailValue = λ^t · M(−t)` (`t = W.rtTilt`) is bounded by Renner's
relaxed error term `iidAEPRtErrorBound = 2^(−n·δ²/(2(log₂ μ)²))`,
`μ = iidAEPSpectralRadius ρ σ = γ + 2`. The operator core bounds
`M(−t) ≤ λ^{−t}·rtErrorBound`, and `λ^t · λ^{−t} = 1` (`Real.rpow_add`) cancels the
scale. -/
theorem iidAEPTiltedTailValue_le_rtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hblock : iidAEPSpectralCutBlockDomination σ n_copies W)
    (hparams : iidAEPRtParameters ρ σ ε W)
    (hregime : iidAEPLargeBlockRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε)
    (hcross : iidAEPNonnegativeThresholdCrossing W) :
    iidAEPTiltedTailValue ρ n_copies W
      ≤ iidAEPRtErrorBound ρ σ n_copies ε W := by
  have hmgf := iidAEPTiltedMGFSum_le_rtErrorBound
    ρ hρ_norm σ n_copies ε W hfeas hreference hblock hparams hregime hcalib hcross
  have hpos : (0 : ℝ) < weightCapScale W := weightCapScale_pos W
  unfold iidAEPTiltedTailValue
  calc
    weightCapScale W ^ W.rtTilt * iidAEPTiltedMGFSum ρ n_copies W (-W.rtTilt)
        ≤ weightCapScale W ^ W.rtTilt
            * (weightCapScale W ^ (-W.rtTilt)
              * iidAEPRtErrorBound ρ σ n_copies ε W) :=
          mul_le_mul_of_nonneg_left hmgf (Real.rpow_nonneg hpos.le _)
    _ = iidAEPRtErrorBound ρ σ n_copies ε W := by
          rw [← mul_assoc, ← Real.rpow_add hpos]
          simp

/-- **Cramér–Chernoff tail** `D ≤ rtErrorBound`. The discarded spectral mass
`D = iidAEPDiscardedSpectralMass` is bounded by Renner's relaxed error term
`iidAEPRtErrorBound = 2^(−n·δ²/(2(log₂ μ)²))`, `μ = γ + 2`, by chaining the
Markov drop (`iidAEPDiscardedSpectralMass_le_tiltedTailValue`) with the
operator-collision MGF tail (`iidAEPTiltedTailValue_le_rtErrorBound`) through
`iidAEPTiltedTailValue`.

* `hfeas` — single-copy support gate ruling out the orthogonal-support
  counterexample (`ρ = P₀`, `σ = P₁`);
* `hreference` — the sorted cumulative reference resolution;
* `hparams` — `μ = γ + 2 > 1` and the optimal tilt;
* `hregime`, `hcalib`, `hcross` — large-block regime, calibration of
  W.entropyThreshold to the bit block entropy floor, and the nonnegative
  threshold crossing.

(Note: `hblock` is not consumed by the proof; remove it from the signature.) -/
theorem iidAEPDiscardedSpectralMass_le_rtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hblock : iidAEPSpectralCutBlockDomination σ n_copies W)
    (hparams : iidAEPRtParameters ρ σ ε W)
    (hregime : iidAEPLargeBlockRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε)
    (hcross : iidAEPNonnegativeThresholdCrossing W) :
    iidAEPDiscardedSpectralMass ρ n_copies W
      ≤ iidAEPRtErrorBound ρ σ n_copies ε W := by
  calc
    iidAEPDiscardedSpectralMass ρ n_copies W
        ≤ iidAEPTiltedTailValue ρ n_copies W :=
          iidAEPDiscardedSpectralMass_le_tiltedTailValue
            ρ σ n_copies ε W hfeas hreference hparams
    _ ≤ iidAEPRtErrorBound ρ σ n_copies ε W :=
          iidAEPTiltedTailValue_le_rtErrorBound
            ρ hρ_norm σ n_copies ε W hfeas hreference hblock hparams hregime
            hcalib hcross

/-- **Renner Cramér–Chernoff discarded-mass tail.** The total operator discarded mass
`Σ_xs [tr(ρ^{⊗}_xs) − tr(ρ̄_xs)]` of the weight-cap blocks is bounded by Renner's
relaxed error term `iidAEPRtErrorBound = 2^(−n·δ²/(2(log₂ μ)²))`, `μ = γ + 2`
(main.tex:4962). Stated purely about `weightCapBlockOp` (no weight-cap pin). It
composes the operator-vs-spectral comparison
`iidAEP_discardedOperatorMass_le_discardedSpectralMass` with the
Cramér–Chernoff tail `iidAEPDiscardedSpectralMass_le_rtErrorBound`.

* `hfeas` — single-copy support gate ruling out the orthogonal-support
  counterexample (`ρ = P₀`, `σ = P₁`);
* `hreference` — the sorted cumulative reference resolution;
* `hparams` — `μ = γ + 2 > 1` and the optimal tilt;
* `hregime`, `hcalib`, `hcross` — large-block regime, calibration of
  W.entropyThreshold, and the nonnegative threshold crossing.

(Note: `hblock` is not consumed by the proof; remove it from the signature.) -/
theorem iidAEP_discardedMass_le_rtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hblock : iidAEPSpectralCutBlockDomination σ n_copies W)
    (hparams : iidAEPRtParameters ρ σ ε W)
    (hregime : iidAEPLargeBlockRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε)
    (hcross : iidAEPNonnegativeThresholdCrossing W) :
    ∑ xs : Fin n_copies → X,
        ( ((iidAEPTensorState ρ n_copies).stateMap xs).trace
          - (weightCapBlockOp ρ n_copies W xs).trace.re )
      ≤ iidAEPRtErrorBound ρ σ n_copies ε W := by
  calc
    ∑ xs : Fin n_copies → X,
        ( ((iidAEPTensorState ρ n_copies).stateMap xs).trace
          - (weightCapBlockOp ρ n_copies W xs).trace.re )
      ≤ iidAEPDiscardedSpectralMass ρ n_copies W :=
        iidAEP_discardedOperatorMass_le_discardedSpectralMass
          ρ σ n_copies W hreference
    _ ≤ iidAEPRtErrorBound ρ σ n_copies ε W :=
        iidAEPDiscardedSpectralMass_le_rtErrorBound
          ρ hρ_norm σ n_copies ε W hfeas hreference hblock hparams hregime
          hcalib hcross

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
