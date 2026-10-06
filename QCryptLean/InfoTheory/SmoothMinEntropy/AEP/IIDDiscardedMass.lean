import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCap
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCapVectorFamily
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBitsBlockDomination
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CfcSpectral

/-!
# Renner discarded-mass operator-vs-spectral bound (`thm:Hmincondrep`)

For Renner's Cramér–Chernoff discarded-mass argument (main.tex:4707–4757), this
module relates the trace defect of a weight-cap smoothed witness to the discarded
*spectral* mass over the witness eigenbasis.

## Main definitions
- `blockReferenceOverlap`: the squared overlap `|⟨z|x⟩|²` between the `z`-th
  reference eigenvector and the `x`-th block eigenvector.
- `iidAEPDiscardedSpectralMass`: Renner's discarded spectral mass `D`
  (`eq:tracelowbound`), the over-threshold spectral mass weighted by the overlaps.

## Main results
- `iidAEP_traceDefect_eq_discardedMass`: the CQ trace defect equals the total
  operator discarded mass `Σ_xs [tr(ρ^{⊗}_xs) − tr(ρ̄_xs)]`.
- `iidAEP_discardedOperatorMass_le_discardedSpectralMass`: the operator
  discarded mass is bounded by `D`.

## References
Renner, main.tex:4707–4757 (`eq:tracelowbound`).
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.VonNeumannEntropy
open InfoTheory.SmoothMinEntropy.IIDAEPCumulative
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The CQ trace defect of a weight-cap smoothed witness equals the total operator
discarded mass, summed block by block:
`Σ_xs [tr(ρ^{⊗}_xs) − tr(ρ̄_xs)]`, where `ρ̄_xs = weightCapBlockOp ρ n_copies W xs`.

The weight-cap pin `hpin` is required: it identifies each smoothed block operator
`(W.smoothedState.stateMap xs).toOp` with the explicit weight-cap block
`weightCapBlockOp ρ n_copies W xs`, so that the smoothed-block trace
(`SubDensityOp.trace = (·).toOp.trace.re`) becomes `(weightCapBlockOp …).trace.re`. -/
lemma iidAEP_traceDefect_eq_discardedMass
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hpin : iidAEPIsWeightCapSmoothedState ρ n_copies W) :
    iidAEPTraceDefect ρ n_copies W =
      ∑ xs : Fin n_copies → X,
        ( ((iidAEPTensorState ρ n_copies).stateMap xs).trace
          - (weightCapBlockOp ρ n_copies W xs).trace.re ) := by
  unfold iidAEPTraceDefect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro xs _
  congr 1
  change (W.smoothedState.stateMap xs).toOp.trace.re
      = (weightCapBlockOp ρ n_copies W xs).trace.re
  rw [hpin xs]

/-! ## Discarded operator mass ≤ discarded spectral mass `D`

Renner's discarded-mass lower bound `eq:tracelowbound` (main.tex:4707–4757). The
weight-cap block trace loses *exactly* the over-threshold spectral mass: for each
classical label `xs`, block eigenvalue index `x`, and sorted reference index `z`
for which the separation cap binds (`p_x(xs) > λ q_z`), the discarded part is
`p_x(xs) · |⟨z|x⟩|²`. -/

/-- The squared overlap `|⟨z|x⟩|²` between the `z`-th sorted reference eigenvector
`|z⟩` — i.e. the rank-one increment projector `P_z = W.spectralProjector z` — and
the `x`-th block eigenvector `|x⟩` (`blockSpectralProjector`), read off as
`tr(P_z |x⟩⟨x|).re`. For the rank-one projectors `P_z = |z⟩⟨z|` and
`|x⟩⟨x|` this equals `|⟨z|x⟩|²` and lies in `[0,1]`. -/
def blockReferenceOverlap
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x z : Fin (n ^ n_copies)) : ℝ :=
  (W.spectralProjector z * blockSpectralProjector ρ n_copies xs x).trace.re

/-- **Renner's discarded spectral mass `D`** (main.tex:4707–4757). Summing over
classical labels `xs`, block eigenvalues `p_x(xs) = blockEigenvalue ρ n_copies xs x`,
and sorted reference indices `z`, the spectral mass exceeding the separation cap
`λ q_z = weightCapScale W · W.referenceEigenvalue z`, weighted by the squared
overlap `|⟨z|x⟩|²` (`blockReferenceOverlap`):

  `D = Σ_{xs} Σ_x Σ_{z : λ q_z < p_x(xs)} p_x(xs) · |⟨z|x⟩|²`. -/
def iidAEPDiscardedSpectralMass
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies) : ℝ :=
  ∑ xs : Fin n_copies → X, ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies),
    (if weightCapScale W * W.referenceEigenvalue z < blockEigenvalue ρ n_copies xs x then
        blockEigenvalue ρ n_copies xs x * blockReferenceOverlap ρ n_copies W xs x z
      else 0)

/-! ### Helper lemmas -/

/-- **Trace expansion of the weight-cap block.** The real trace of
`ρ̄_xs = Σ_x Σ_z p_{x,z}(xs)·B_z|x⟩⟨x|B_z` is the double sum of the split
coefficients weighted by the real trace of the cumulative sandwiches. -/
lemma weightCapBlockOp_trace_re_eq
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) :
    (weightCapBlockOp ρ n_copies W xs).trace.re
      = ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies),
          splitCoefficient ρ n_copies W xs x z *
            (W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
              W.cumulativeProjector z).trace.re := by
  unfold weightCapBlockOp
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- **Completeness of the reference overlaps.** Since `Σ_z P_z = 1` and each block
eigenprojector has unit trace, the squared overlaps sum to one:
`Σ_z |⟨z|x⟩|² = tr(|x⟩⟨x|) = 1`. -/
lemma sum_blockReferenceOverlap_eq_one
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hsum : ∑ z : Fin (n ^ n_copies), W.spectralProjector z = 1)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    ∑ z : Fin (n ^ n_copies), blockReferenceOverlap ρ n_copies W xs x z = 1 := by
  unfold blockReferenceOverlap
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hsum, one_mul,
    blockSpectralProjector_trace]
  simp

/-- **Nonnegativity of the reference overlap** `|⟨z|x⟩|² ≥ 0`. For the Hermitian
idempotent increment projector `P_z` and the PSD block eigenprojector
`M = |x⟩⟨x|`, the trace `tr(P_z M).re = tr(P_z M P_z).re ≥ 0`. -/
lemma blockReferenceOverlap_nonneg
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hPidem : ∀ z : Fin (n ^ n_copies),
      W.spectralProjector z * W.spectralProjector z = W.spectralProjector z)
    (hPherm : ∀ z : Fin (n ^ n_copies),
      (W.spectralProjector z)† = W.spectralProjector z)
    (xs : Fin n_copies → X) (x z : Fin (n ^ n_copies)) :
    0 ≤ blockReferenceOverlap ρ n_copies W xs x z := by
  unfold blockReferenceOverlap
  set P := W.spectralProjector z with hP
  set M := blockSpectralProjector ρ n_copies xs x with hM
  have hM_psd : M.PosSemidef := by
    simpa [hM, blockSpectralProjector] using
      Matrix.posSemidef_vecMulVec_self_star
        (((iidAEPTensorState ρ n_copies).stateMap
          xs).toPosSemidefOp.toHermitianOp.isHermitian.eigenvectorBasis x).ofLp
  have hsand : (P * M * P).PosSemidef := by
    have := hM_psd.mul_mul_conjTranspose_same P
    rwa [hPherm z] at this
  have hPP : P * P = P := hPidem z
  have hcyc : (P * M).trace = (P * M * P).trace := by
    rw [Matrix.trace_mul_comm (P * M) P, ← mul_assoc, hPP]
  rw [hcyc]
  exact (Complex.nonneg_iff.mp hsand.trace_nonneg).1

/-- The cumulative sandwich trace equals the partial sum of increment overlaps:
`tr(B_z|x⟩⟨x|B_z).re = Σ_{z' : z ≤ z'} |⟨z'|x⟩|²`, where `B_z = Σ_{z ≤ z'} P_{z'}`
is the idempotent cumulative projector. -/
lemma cumulativeProjector_sandwich_trace_re_eq
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hBdef : ∀ z : Fin (n ^ n_copies), W.cumulativeProjector z =
      (Finset.univ.filter (fun z' : Fin (n ^ n_copies) => z ≤ z')).sum
        (fun z' => W.spectralProjector z'))
    (hBidem : ∀ z : Fin (n ^ n_copies),
      W.cumulativeProjector z * W.cumulativeProjector z = W.cumulativeProjector z)
    (xs : Fin n_copies → X) (x z : Fin (n ^ n_copies)) :
    (W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
        W.cumulativeProjector z).trace.re
      = ∑ z' ∈ Finset.univ.filter (fun z' : Fin (n ^ n_copies) => z ≤ z'),
          blockReferenceOverlap ρ n_copies W xs x z' := by
  set M := blockSpectralProjector ρ n_copies xs x with hM
  have hcyc : (W.cumulativeProjector z * M * W.cumulativeProjector z).trace
      = (W.cumulativeProjector z * M).trace := by
    rw [Matrix.trace_mul_comm, ← mul_assoc, hBidem]
  rw [hcyc, hBdef z, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  rfl

/-- **Renner's telescoping cap.** The partial sum of split coefficients along the
sorted reference order recovers the capped cumulative mass
`Σ_{z : z ≤ z'} p_{x,z}(xs) = min(p_x(xs), λ q_{z'})`. -/
lemma partialSum_splitCoefficient_eq_min
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x z' : Fin (n ^ n_copies)) :
    (Finset.univ.filter (fun z : Fin (n ^ n_copies) => z ≤ z')).sum
        (fun z => splitCoefficient ρ n_copies W xs x z)
      = min (blockEigenvalue ρ n_copies xs x)
          (weightCapScale W * W.referenceEigenvalue z') := by
  have hbeta : ∀ z : Fin (n ^ n_copies),
      splitCoefficient ρ n_copies W xs x z
        = betaIncr (fun w => min (blockEigenvalue ρ n_copies xs x)
            (weightCapScale W * W.referenceEigenvalue w)) z := fun z => rfl
  rw [Finset.sum_congr rfl (fun z _ => hbeta z)]
  exact sum_filter_le_betaIncr _ z'

/-- **Per-block (per-`(xs, x)`) discarded-mass bound** (Renner
`eq:tracelowbound`). The operator defect of one block eigenvalue is at most the
over-threshold spectral mass:
`p_x − Σ_z p_{x,z}·tr(B_z|x⟩⟨x|B_z).re ≤ Σ_{z : λ q_z < p_x} p_x·|⟨z|x⟩|²`. -/
lemma blockDiscarded_le_overThreshold
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hsum : ∑ z : Fin (n ^ n_copies), W.spectralProjector z = 1)
    (hBdef : ∀ z : Fin (n ^ n_copies), W.cumulativeProjector z =
      (Finset.univ.filter (fun z' : Fin (n ^ n_copies) => z ≤ z')).sum
        (fun z' => W.spectralProjector z'))
    (hBidem : ∀ z : Fin (n ^ n_copies),
      W.cumulativeProjector z * W.cumulativeProjector z = W.cumulativeProjector z)
    (hPidem : ∀ z : Fin (n ^ n_copies),
      W.spectralProjector z * W.spectralProjector z = W.spectralProjector z)
    (hPherm : ∀ z : Fin (n ^ n_copies),
      (W.spectralProjector z)† = W.spectralProjector z)
    (hq_nn : ∀ z : Fin (n ^ n_copies), 0 ≤ W.referenceEigenvalue z)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    blockEigenvalue ρ n_copies xs x
        - ∑ z : Fin (n ^ n_copies), splitCoefficient ρ n_copies W xs x z *
            (W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
              W.cumulativeProjector z).trace.re
      ≤ ∑ z : Fin (n ^ n_copies),
          (if weightCapScale W * W.referenceEigenvalue z
              < blockEigenvalue ρ n_copies xs x then
              blockEigenvalue ρ n_copies xs x
                * blockReferenceOverlap ρ n_copies W xs x z
            else 0) := by
  classical
  set p := blockEigenvalue ρ n_copies xs x with hp
  set lam := weightCapScale W with hlam
  set q := fun z => W.referenceEigenvalue z with hq
  set o := fun z => blockReferenceOverlap ρ n_copies W xs x z with ho
  have ho_nn : ∀ z, 0 ≤ o z := fun z =>
    blockReferenceOverlap_nonneg ρ n_copies W hPidem hPherm xs x z
  -- Rewrite the retained mass as `Σ_{z'} min(p, λ q_{z'}) · o_{z'}`.
  have key : (∑ z : Fin (n ^ n_copies), splitCoefficient ρ n_copies W xs x z *
        (W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
          W.cumulativeProjector z).trace.re)
      = ∑ z' : Fin (n ^ n_copies), min p (lam * q z') * o z' := by
    have e1 : ∀ z : Fin (n ^ n_copies),
        splitCoefficient ρ n_copies W xs x z *
          (W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
            W.cumulativeProjector z).trace.re
          = ∑ z' ∈ Finset.univ.filter (fun z' : Fin (n ^ n_copies) => z ≤ z'),
              splitCoefficient ρ n_copies W xs x z * o z' := by
      intro z
      rw [cumulativeProjector_sandwich_trace_re_eq ρ n_copies W hBdef hBidem xs x z,
        Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun z _ => e1 z)]
    have swap : (∑ z : Fin (n ^ n_copies),
          ∑ z' ∈ Finset.univ.filter (fun z' : Fin (n ^ n_copies) => z ≤ z'),
            splitCoefficient ρ n_copies W xs x z * o z')
        = ∑ z' : Fin (n ^ n_copies),
            ∑ z ∈ Finset.univ.filter (fun z : Fin (n ^ n_copies) => z ≤ z'),
              splitCoefficient ρ n_copies W xs x z * o z' := by
      apply Finset.sum_comm'
      intro z z'
      simp [Finset.mem_filter]
    rw [swap]
    refine Finset.sum_congr rfl (fun z' _ => ?_)
    rw [← Finset.sum_mul, partialSum_splitCoefficient_eq_min ρ n_copies W xs x z']
  -- Completeness gives `p = Σ_{z'} p · o_{z'}`.
  have hp_eq : p = ∑ z' : Fin (n ^ n_copies), p * o z' := by
    rw [← Finset.mul_sum, sum_blockReferenceOverlap_eq_one ρ n_copies W hsum xs x, mul_one]
  -- Combine into a single sum and compare term by term.
  have hsub : p - (∑ z : Fin (n ^ n_copies), splitCoefficient ρ n_copies W xs x z *
        (W.cumulativeProjector z * blockSpectralProjector ρ n_copies xs x *
          W.cumulativeProjector z).trace.re)
      = ∑ z' : Fin (n ^ n_copies), (p - min p (lam * q z')) * o z' := by
    have hrw : (∑ z' : Fin (n ^ n_copies), (p - min p (lam * q z')) * o z')
        = (∑ z' : Fin (n ^ n_copies), p * o z')
          - ∑ z' : Fin (n ^ n_copies), min p (lam * q z') * o z' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun z' _ => by ring)
    rw [hrw, ← hp_eq, ← key]
  rw [hsub]
  refine Finset.sum_le_sum (fun z' _ => ?_)
  by_cases hcase : lam * q z' < p
  · rw [ite_eq_left hcase, min_eq_right hcase.le]
    have hlam_nn : (0 : ℝ) ≤ lam := (weightCapScale_pos W).le
    nlinarith [ho_nn z', hq_nn z', hlam_nn, mul_nonneg hlam_nn (hq_nn z')]
  · rw [ite_eq_right hcase, min_eq_left (not_lt.mp hcase)]
    simp

/-- The total operator discarded mass `Σ_xs [tr(ρ^{⊗}_xs) − tr(ρ̄_xs).re]` is bounded
by Renner's discarded spectral mass `iidAEPDiscardedSpectralMass`
(main.tex:4707–4757, `eq:tracelowbound`).

`hreference` is required: the sorted cumulative reference resolution fixes the
projector geometry (`B_z = Σ_{z ≤ z'} P_{z'}`, with idempotent Hermitian
increments `P_z` summing to `1`) that the overlap accounting reads off. -/
theorem iidAEP_discardedOperatorMass_le_discardedSpectralMass
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W) :
    ∑ xs : Fin n_copies → X,
        ( ((iidAEPTensorState ρ n_copies).stateMap xs).trace
          - (weightCapBlockOp ρ n_copies W xs).trace.re )
      ≤ iidAEPDiscardedSpectralMass ρ n_copies W := by
  classical
  obtain ⟨hq_nn, hincr, _haction, hcum⟩ := hreference
  obtain ⟨hPidem, hPherm, _hPne, _hPorth, hPsum⟩ := hincr
  obtain ⟨_hbeta_nn, hBdef, hBidem, _hBherm, _hBnest, _htau, _hq_eq⟩ := hcum
  unfold iidAEPDiscardedSpectralMass
  apply Finset.sum_le_sum
  intro xs _
  rw [← blockEigenvalue_sum_eq_block_trace ρ n_copies xs,
    weightCapBlockOp_trace_re_eq ρ n_copies W xs, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro x _
  exact blockDiscarded_le_overThreshold ρ n_copies W hPsum hBdef hBidem hPidem hPherm hq_nn xs x

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
