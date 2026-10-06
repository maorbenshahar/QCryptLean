import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDCollisionMGF
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.RtFunction
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQJointEntropyLowerBound
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.IsometricInvariance

/-!
# Single-copy spectral moments

Spectral (eigenvalue/overlap) expansion of the single-copy tilted MGF
`m(s) = iidAEPSingleCopyMGF ρ σ s = Σ_x tr[ρ_x^{1+s} σ^{-s}]`, and the moment
identities derived from it, for a CQ state `ρ` with blocks `ρ_x = ρ.stateMap x` and
reference density `σ`.

## Spectral data

All identities are read off the finite distribution

  `P(x,a,b) := p_{x,a} · |⟨φ_b|ψ_{x,a}⟩|²`

over triples `(x, a, b)`, where `{p_{x,a}, ψ_{x,a}}` is the Hermitian
eigendecomposition of `ρ_x` and `{q_b, φ_b}` that of `σ`.

## Main definitions
- `singleCopyBlockEigenvalue` / `singleCopyBlockProjector` — eigenvalues `p_{x,a}` and
  rank-one eigenprojectors of `ρ_x`.
- `singleCopyReferenceEigenvalue` / `singleCopyReferenceProjector` — eigenvalues `q_b`
  and rank-one eigenprojectors of `σ`.
- `singleCopyOverlap` — the squared overlap `|⟨φ_b|ψ_{x,a}⟩|²`.
- `singleCopyProbWeight` — the weight `P(x,a,b)`.

## Main statements
- `singleCopyMGF_spectral_expansion` — `m(s) = Σ_{x,a,b} p_{x,a}^{1+s} q_b^{-s} |⟨φ_b|ψ_{x,a}⟩|²`.
- `singleCopyMGF_entropyMoment` — `Σ P·ln(q/p) = (ln 2)·H_bits`.
- `singleCopyMGF_pOverq_moment` — `Σ P·(p/q) = tracedSquareTimesInvFactor`.
- `singleCopyMGF_qOverp_le_classicalRank` — `Σ P·(q/p) ≤ classicalRank`.
- `four_le_iidAEPSpectralRadius`, `s_le_half_of_mul_log_spectralRadius_le_log_two` — `4 ≤ μ` and `s
≤ 1/2`.
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.VonNeumannEntropy
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Single-copy spectral data -/

/-- **Block eigenvalues** `p_{x,a}` of the single-copy block `ρ_x = ρ.stateMap x`,
read off its Hermitian eigen-decomposition. An explicit, total function
`Fin n → ℝ`; nonnegative since each block is PSD. -/
def singleCopyBlockEigenvalue
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) : Fin n → ℝ :=
  (ρ.stateMap x).isHermitian.eigenvalues

/-- **Block eigen-projectors** `|ψ_{x,a}⟩⟨ψ_{x,a}|` of the single-copy block
`ρ_x = ρ.stateMap x`, formed from its Hermitian eigenvector basis. Rank-one
orthogonal projectors summing to `1` (the spectral resolution of `ρ_x`). -/
def singleCopyBlockProjector
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) (a : Fin n) : Op n :=
  Matrix.vecMulVec (((ρ.stateMap x).isHermitian.eigenvectorBasis a).ofLp)
    (star (((ρ.stateMap x).isHermitian.eigenvectorBasis a).ofLp))

/-- **Reference eigenvalues** `q_b` of the reference density `σ`, read off its
Hermitian eigen-decomposition. An explicit, total function `Fin n → ℝ`;
nonnegative since `σ` is PSD. -/
def singleCopyReferenceEigenvalue
    {n : ℕ} (σ : DensityOp n) : Fin n → ℝ :=
  σ.toPosSemidefOp.toHermitianOp.isHermitian.eigenvalues

/-- **Reference eigen-projectors** `|φ_b⟩⟨φ_b|` of the reference density `σ`,
formed from its Hermitian eigenvector basis. Rank-one orthogonal projectors
summing to `1` (the spectral resolution of `σ`). -/
def singleCopyReferenceProjector
    {n : ℕ} (σ : DensityOp n) (b : Fin n) : Op n :=
  Matrix.vecMulVec
    ((σ.toPosSemidefOp.toHermitianOp.isHermitian.eigenvectorBasis b).ofLp)
    (star ((σ.toPosSemidefOp.toHermitianOp.isHermitian.eigenvectorBasis b).ofLp))

/-- **Squared overlap** `|⟨φ_b|ψ_{x,a}⟩|²` between the `b`-th reference
eigenvector `|φ_b⟩` and the `a`-th block eigenvector `|ψ_{x,a}⟩`, read off as
`tr(|φ_b⟩⟨φ_b| · |ψ_{x,a}⟩⟨ψ_{x,a}|).re`. For the rank-one eigen-projectors this
equals `|⟨φ_b|ψ_{x,a}⟩|²` and lies in `[0,1]`. -/
def singleCopyOverlap
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (x : X) (a b : Fin n) : ℝ :=
  (singleCopyReferenceProjector σ b * singleCopyBlockProjector ρ x a).trace.re

/-- **Probability weight** `P(x,a,b) := p_{x,a} · |⟨φ_b|ψ_{x,a}⟩|²` of the
direct-distribution argument. Summed over `(x,a,b)` it equals `1`
(`{φ_b}` is an ONB so `Σ_b |overlap|² = 1`, and `Σ_{x,a} p_{x,a} = Σ_x tr ρ_x = 1`
under `hρ_norm`). -/
def singleCopyProbWeight
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) (x : X) (a b : Fin n) : ℝ :=
  singleCopyBlockEigenvalue ρ x a * singleCopyOverlap ρ σ x a b

/-- **Nonnegativity of the block eigenvalues** `p_{x,a} ≥ 0`, since each block
`ρ_x = ρ.stateMap x` is PSD. -/
lemma singleCopyBlockEigenvalue_nonneg
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (x : X) (a : Fin n) :
    0 ≤ singleCopyBlockEigenvalue ρ x a :=
  (posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp).eigenvalues_nonneg a

/-- **Nonnegativity of the reference eigenvalues** `q_b ≥ 0`, since `σ` is PSD. -/
lemma singleCopyReferenceEigenvalue_nonneg
    {n : ℕ} (σ : DensityOp n) (b : Fin n) :
    0 ≤ singleCopyReferenceEigenvalue σ b :=
  (posSemidefOp_implies_mathlib σ.toPosSemidefOp).eigenvalues_nonneg b

/-! ## Spectral resolutions of the block and reference eigen-data -/

/-- Spectral resolution of the single-copy block `ρ_x` over its rank-one
eigen-projectors: `ρ_x = Σ_a p_{x,a} · |ψ_{x,a}⟩⟨ψ_{x,a}|`. -/
private lemma singleCopyBlock_spectral_resolution
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (x : X) :
    (ρ.stateMap x).toOp
      = ∑ a : Fin n,
          (singleCopyBlockEigenvalue ρ x a : ℂ) • singleCopyBlockProjector ρ x a := by
  have h := (isHermitian_eigenvectorBasis_rankOneProjectors_action
    (ρ.stateMap x).isHermitian).1
  simpa only [singleCopyBlockEigenvalue, singleCopyBlockProjector] using h

/-- Spectral resolution of the reference density `σ` over its rank-one
eigen-projectors: `σ = Σ_b q_b · |φ_b⟩⟨φ_b|`. -/
private lemma singleCopyReference_spectral_resolution
    {n : ℕ} [NeZero n] (σ : DensityOp n) :
    σ.toOp
      = ∑ b : Fin n,
          (singleCopyReferenceEigenvalue σ b : ℂ) • singleCopyReferenceProjector σ b := by
  have h := (isHermitian_eigenvectorBasis_rankOneProjectors_action
    σ.toPosSemidefOp.toHermitianOp.isHermitian).1
  simpa only [singleCopyReferenceEigenvalue, singleCopyReferenceProjector] using h

/-- The block eigen-projectors resolve the identity: `Σ_a |ψ_{x,a}⟩⟨ψ_{x,a}| = 1`. -/
private lemma singleCopyBlock_sum_projector
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (x : X) :
    ∑ a : Fin n, singleCopyBlockProjector ρ x a = 1 :=
  (isHermitian_eigenvectorBasis_rankOneProjectors_increments
    (ρ.stateMap x).isHermitian).2.2.2.2

/-- The reference eigen-projectors resolve the identity: `Σ_b |φ_b⟩⟨φ_b| = 1`. -/
private lemma singleCopyReference_sum_projector
    {n : ℕ} [NeZero n] (σ : DensityOp n) :
    ∑ b : Fin n, singleCopyReferenceProjector σ b = 1 :=
  (isHermitian_eigenvectorBasis_rankOneProjectors_increments
    σ.toPosSemidefOp.toHermitianOp.isHermitian).2.2.2.2

/-! ## Spectral expansion of the single-copy MGF -/

/-- Per-block tilted trace expansion: for one letter `x`,

  `tr[ρ_x^{1+s} σ^{-s}].re = Σ_{a,b} p_{x,a}^{1+s} q_b^{-s} |⟨φ_b|ψ_{x,a}⟩|²`.

Both `ρ_x` and `σ` are PSD, so `CfcSpectral.rpow_of_orthogonalResolution` expands
each CFC real power coefficientwise over the rank-one eigenprojectors; the product
distributes and the per-`(a,b)` trace `tr[P_a Q_b]` matches `singleCopyOverlap` via
`Matrix.trace_mul_comm`. -/
private lemma singleCopyBlock_tilted_trace_expansion
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (s : ℝ) (x : X) :
    ((ρ.stateMap x).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re
      = ∑ a : Fin n, ∑ b : Fin n,
          singleCopyBlockEigenvalue ρ x a ^ (1 + s)
            * singleCopyReferenceEigenvalue σ b ^ (-s)
            * singleCopyOverlap ρ σ x a b := by
  classical
  -- block eigen-projector data (idempotent/Hermitian/orthogonal), matched to the defs
  have hincrR := isHermitian_eigenvectorBasis_rankOneProjectors_increments
    (ρ.stateMap x).isHermitian
  have hconvR : ∀ a, singleCopyBlockProjector ρ x a
      = Matrix.vecMulVec (((ρ.stateMap x).isHermitian.eigenvectorBasis a).ofLp)
          (star (((ρ.stateMap x).isHermitian.eigenvectorBasis a).ofLp)) :=
    fun a => rfl
  have hRa_idem : ∀ a, singleCopyBlockProjector ρ x a
      * singleCopyBlockProjector ρ x a = singleCopyBlockProjector ρ x a := by
    intro a; rw [hconvR]; exact hincrR.1 a
  have hRa_herm : ∀ a, (singleCopyBlockProjector ρ x a).IsHermitian := by
    intro a; rw [Matrix.IsHermitian, hconvR]; exact hincrR.2.1 a
  have hRa_orth : ∀ a a', a ≠ a' →
      singleCopyBlockProjector ρ x a * singleCopyBlockProjector ρ x a' = 0 := by
    intro a a' haa'; rw [hconvR, hconvR]; exact hincrR.2.2.2.1 a a' haa'
  have hRa_sum := singleCopyBlock_sum_projector ρ x
  have hRdecomp := singleCopyBlock_spectral_resolution ρ x
  -- reference eigen-projector data
  have hincrS := isHermitian_eigenvectorBasis_rankOneProjectors_increments
    σ.toPosSemidefOp.toHermitianOp.isHermitian
  have hconvS : ∀ b, singleCopyReferenceProjector σ b
      = Matrix.vecMulVec
          ((σ.toPosSemidefOp.toHermitianOp.isHermitian.eigenvectorBasis b).ofLp)
          (star ((σ.toPosSemidefOp.toHermitianOp.isHermitian.eigenvectorBasis b).ofLp)) :=
    fun b => rfl
  have hSb_idem : ∀ b, singleCopyReferenceProjector σ b
      * singleCopyReferenceProjector σ b = singleCopyReferenceProjector σ b := by
    intro b; rw [hconvS]; exact hincrS.1 b
  have hSb_herm : ∀ b, (singleCopyReferenceProjector σ b).IsHermitian := by
    intro b; rw [Matrix.IsHermitian, hconvS]; exact hincrS.2.1 b
  have hSb_orth : ∀ b b', b ≠ b' →
      singleCopyReferenceProjector σ b * singleCopyReferenceProjector σ b' = 0 := by
    intro b b' hbb'; rw [hconvS, hconvS]; exact hincrS.2.2.2.1 b b' hbb'
  have hSb_sum := singleCopyReference_sum_projector σ
  have hSdecomp := singleCopyReference_spectral_resolution σ
  -- expand both CFC real powers coefficientwise, then distribute
  rw [CfcSpectral.rpow_of_orthogonalResolution _ (singleCopyBlockEigenvalue ρ x)
      (singleCopyBlockProjector ρ x)
      (Matrix.nonneg_iff_posSemidef.mpr
        (posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp))
      hRa_herm hRa_idem hRa_orth hRa_sum hRdecomp (1 + s),
    CfcSpectral.rpow_of_orthogonalResolution _ (singleCopyReferenceEigenvalue σ)
      (singleCopyReferenceProjector σ)
      (Matrix.nonneg_iff_posSemidef.mpr
        (posSemidefOp_implies_mathlib σ.toPosSemidefOp))
      hSb_herm hSb_idem hSb_orth hSb_sum hSdecomp (-s),
    Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_smul,
    smul_eq_mul,
    show ((singleCopyBlockEigenvalue ρ x a ^ (1 + s) : ℝ) : ℂ)
          * ((singleCopyReferenceEigenvalue σ b ^ (-s) : ℝ) : ℂ)
        = (((singleCopyBlockEigenvalue ρ x a ^ (1 + s))
            * (singleCopyReferenceEigenvalue σ b ^ (-s)) : ℝ) : ℂ) from by push_cast; ring,
    Complex.re_ofReal_mul,
    show (singleCopyBlockProjector ρ x a * singleCopyReferenceProjector σ b).trace
        = (singleCopyReferenceProjector σ b * singleCopyBlockProjector ρ x a).trace
        from Matrix.trace_mul_comm _ _,
    singleCopyOverlap]

/-- Spectral expansion of the single-copy tilted MGF over the eigendata of the blocks
`ρ_x` and the reference `σ`:

  `m(s) = Σ_{x,a,b} p_{x,a}^{1+s} · q_b^{-s} · |⟨φ_b|ψ_{x,a}⟩|²`.

By the Hermitian spectral theorem the CFC real powers act diagonally
(`ρ_x^{1+s} = Σ_a p_{x,a}^{1+s} |ψ_{x,a}⟩⟨ψ_{x,a}|`, `σ^{-s} = Σ_b q_b^{-s} |φ_b⟩⟨φ_b|`)
and the trace is real. The powers are total (`q_b^{-s}` is the real `rpow`, well
defined at `q_b = 0`), so the identity is unconditional in `s`. -/
theorem singleCopyMGF_spectral_expansion
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (_hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    {s : ℝ} (_hs : 0 ≤ s) :
    iidAEPSingleCopyMGF ρ σ s
      = ∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
          singleCopyBlockEigenvalue ρ x a ^ (1 + s)
            * singleCopyReferenceEigenvalue σ b ^ (-s)
            * singleCopyOverlap ρ σ x a b := by
  classical
  unfold iidAEPSingleCopyMGF
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl
    (fun x _ => singleCopyBlock_tilted_trace_expansion ρ σ s x)

/-! ## The entropy moment -/

/-- **ONB completeness collapses the per-block overlap.** Summing the squared
overlaps of a fixed block eigen-projector `P_{x,a} = |ψ_{x,a}⟩⟨ψ_{x,a}|` against
the reference spectral resolution `Σ_b |φ_b⟩⟨φ_b| = 1` recovers the unit trace of
the rank-one projector:

  `Σ_b singleCopyOverlap ρ σ x a b = 1`.

This is the `b`-completeness fact `Σ_b tr[Q_b P_{x,a}] = tr[1 · P_{x,a}] = tr P_{x,a} = 1`
used to collapse the reference index in the entropy moment. -/
lemma singleCopy_sum_overlap_eq_one
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (x : X) (a : Fin n) :
    ∑ b : Fin n, singleCopyOverlap ρ σ x a b = 1 := by
  classical
  -- reference resolution of the identity `Σ_b Q_b = 1`
  have hSb_sum := singleCopyReference_sum_projector σ
  -- the rank-one block projector has unit trace
  have htr : (singleCopyBlockProjector ρ x a).trace = 1 := by
    rw [singleCopyBlockProjector, Matrix.trace_vecMulVec,
      ← EuclideanSpace.inner_eq_star_dotProduct]
    simp
  -- collapse `Σ_b tr[Q_b P] = tr[(Σ_b Q_b) P] = tr P = 1`
  unfold singleCopyOverlap
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hSb_sum, one_mul, htr]
  simp

/-- **Nonnegativity of the single-copy probability weight** `P(x,a,b) = p_{x,a}·overlap`. -/
lemma singleCopyProbWeight_nonneg
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (x : X) (a b : Fin n) :
    0 ≤ singleCopyProbWeight ρ σ x a b := by
  refine mul_nonneg (singleCopyBlockEigenvalue_nonneg ρ x a) ?_
  exact trace_mul_psd_nonneg _ _ (Matrix.posSemidef_vecMulVec_self_star _)
    (Matrix.posSemidef_vecMulVec_self_star _)

/-- Normalization of the direct distribution. Summing `P(x,a,b)` over all triples
gives `1`: the `b`-sum collapses by ONB completeness (`singleCopy_sum_overlap_eq_one`)
to `Σ_{x,a} p_{x,a}`, then `Σ_a p_{x,a} = tr ρ_x` and `Σ_x tr ρ_x = 1` (`hρ_norm`). -/
lemma sum_singleCopyProbWeight_eq_one
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) :
    ∑ x : X, ∑ a : Fin n, ∑ b : Fin n, singleCopyProbWeight ρ σ x a b = 1 := by
  classical
  have hb : ∀ (x : X) (a : Fin n),
      ∑ b : Fin n, singleCopyProbWeight ρ σ x a b = singleCopyBlockEigenvalue ρ x a := by
    intro x a
    rw [show (∑ b : Fin n, singleCopyProbWeight ρ σ x a b)
          = singleCopyBlockEigenvalue ρ x a * ∑ b : Fin n, singleCopyOverlap ρ σ x a b from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => by unfold singleCopyProbWeight; ring),
      singleCopy_sum_overlap_eq_one, mul_one]
  have ha : ∀ x : X,
      ∑ a : Fin n, singleCopyBlockEigenvalue ρ x a = (ρ.stateMap x).trace := by
    intro x
    rw [show (ρ.stateMap x).trace = (ρ.stateMap x).toOp.trace.re from rfl,
      (ρ.stateMap x).isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl (fun a _ => by simp [singleCopyBlockEigenvalue])
  calc ∑ x : X, ∑ a : Fin n, ∑ b : Fin n, singleCopyProbWeight ρ σ x a b
      = ∑ x : X, ∑ a : Fin n, singleCopyBlockEigenvalue ρ x a :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ => hb x a))
    _ = ∑ x : X, (ρ.stateMap x).trace :=
        Finset.sum_congr rfl (fun x _ => ha x)
    _ = 1 := hρ_norm

/-- The block-eigenvalue log moment equals `−S(ρ_XB)`. Collapsing the reference index
`b` (via `singleCopy_sum_overlap_eq_one`) leaves `Σ_{x,a} p_{x,a} · ln p_{x,a}`, and
the joint spectrum of the block-diagonal `ρ_XB` is exactly `{p_{x,a}}`, so

  `Σ_{x,a,b} P(x,a,b) · ln p_{x,a} = − vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)`.

Unconditional: the `b`-sum collapses by ONB completeness. -/
private lemma singleCopy_entropyMoment_logBlock_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) :
    ∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
        singleCopyProbWeight ρ σ x a b
          * Real.log (singleCopyBlockEigenvalue ρ x a)
      = - vonNeumannEntropy (ρ.toJointDensityOp hρ_norm) := by
  classical
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  -- collapse the b-sum using ONB completeness `Σ_b overlap = 1`
  have hcollapse : ∀ x : X, ∀ a : Fin n,
      ∑ b : Fin n, singleCopyProbWeight ρ σ x a b
          * Real.log (singleCopyBlockEigenvalue ρ x a)
        = singleCopyBlockEigenvalue ρ x a
            * Real.log (singleCopyBlockEigenvalue ρ x a) := by
    intro x a
    have hsum : ∑ b : Fin n, singleCopyProbWeight ρ σ x a b
          * Real.log (singleCopyBlockEigenvalue ρ x a)
        = (singleCopyBlockEigenvalue ρ x a * Real.log (singleCopyBlockEigenvalue ρ x a))
            * ∑ b : Fin n, singleCopyOverlap ρ σ x a b := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      unfold singleCopyProbWeight; ring
    rw [hsum, singleCopy_sum_overlap_eq_one, mul_one]
  rw [Finset.sum_congr rfl (fun x _ =>
    Finset.sum_congr rfl (fun a _ => hcollapse x a))]
  -- relate `Σ_{x,a} p log p` to `S(ρ_XB) = H(jointEigenvalues)`
  rw [vonNeumannEntropy_eq_shannonEntropy (ρ.toJointDensityOp hρ_norm)
        ρ.jointEigenvalues
        (ρ.isEigenvalueSpectrum_toJointDensityOp_jointEigenvalues hρ_norm)]
  set e := cqJointEquiv X n with he
  -- `S(ρ_XB) = -∑_k jointEig_k log jointEig_k`; reindex to `(i,x)` and cancel signs
  rw [Math.ClassicalEntropy.shannonEntropy_eq_neg_sum_mul_log,
    show (∑ k, ρ.jointEigenvalues k * Real.log (ρ.jointEigenvalues k))
        = ∑ p : Fin n × X,
            ρ.blockEigenvalues p.2 p.1 * Real.log (ρ.blockEigenvalues p.2 p.1) from by
      rw [← Equiv.sum_comp e.symm
        (fun p : Fin n × X =>
          ρ.blockEigenvalues p.2 p.1 * Real.log (ρ.blockEigenvalues p.2 p.1))]
      rfl,
    Fintype.sum_prod_type_right, neg_neg]
  rfl

/-- **Functional calculus in the Hermitian eigenbasis.** For any coefficient
function `c`, the `c`-weighted sum of the rank-one eigen-projectors
`|e_z⟩⟨e_z|` of a Hermitian `M` equals `U · diag c · U†`, with `U` the eigenvector
unitary. (The `c = eigenvalues` case is the spectral resolution; here `c` is
arbitrary, used below with `c = log q`.) -/
private lemma eigenvectorBasis_weighted_rankOneProjectors
    {d : ℕ} [NeZero d] {M : Op d} (hM : M.IsHermitian) (c : Fin d → ℂ) :
    ∑ z : Fin d, c z • Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
        (star ((hM.eigenvectorBasis z).ofLp))
      = (↑hM.eigenvectorUnitary : Op d)
          * Matrix.diagonal c * (↑hM.eigenvectorUnitary : Op d)ᴴ := by
  classical
  set U : Op d := (↑hM.eigenvectorUnitary : Op d) with hU_def
  ext a b
  rw [Matrix.sum_apply]
  have hLHS : ∀ z : Fin d,
      (c z • Matrix.vecMulVec ((hM.eigenvectorBasis z).ofLp)
          (star ((hM.eigenvectorBasis z).ofLp))) a b
        = c z * ((hM.eigenvectorBasis z).ofLp a * star ((hM.eigenvectorBasis z).ofLp b)) := by
    intro z
    simp [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun z _ => hLHS z)]
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Matrix.diagonal_mul, Matrix.conjTranspose_apply, hU_def]
  have hcol : (hM.eigenvectorBasis z).ofLp a = (↑hM.eigenvectorUnitary : Op d) a z := by
    simp
  have hcol' : (hM.eigenvectorBasis z).ofLp b = (↑hM.eigenvectorUnitary : Op d) b z := by
    simp
  rw [hcol, hcol']
  ring

/-- **Block contraction of the probability weight against a reference projector.**
Summing `P(x,a,b)` over the block index `a` collapses the block spectral resolution
`Σ_a p_{x,a} |ψ_{x,a}⟩⟨ψ_{x,a}| = ρ_x`, leaving `tr[Q_b · ρ_x].re`. -/
private lemma singleCopy_sum_a_probWeight_eq
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (x : X) (b : Fin n) :
    ∑ a : Fin n, singleCopyProbWeight ρ σ x a b
      = (singleCopyReferenceProjector σ b * (ρ.stateMap x).toOp).trace.re := by
  classical
  rw [singleCopyBlock_spectral_resolution ρ x, Finset.mul_sum, Matrix.trace_sum,
    Complex.re_sum]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  unfold singleCopyProbWeight singleCopyOverlap
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- **Eigenbasis bridge for the reference-log trace.** The `q_b`-log–weighted sum
of the diagonal traces `tr[Q_b · ρ_B]` (Mathlib eigenbasis of `σ`) equals
`traceProductLogSigma ρ_B σ` (phrased in the `eigenbasisOf σ` basis). Both equal
`Tr(ρ_B log σ)`; the two diagonalizing unitaries are reconciled via
`spectral_decomp_function_invariance` applied to `f = log`. -/
private lemma singleCopy_entropyMoment_logRef_trace
    {n : ℕ} [NeZero n] (ρB σ : DensityOp n) :
    ∑ b : Fin n, (singleCopyReferenceProjector σ b * ρB.toOp).trace.re
        * Real.log (singleCopyReferenceEigenvalue σ b)
      = InfoTheory.RelativeEntropy.traceProductLogSigma ρB σ := by
  classical
  set hσH := σ.toPosSemidefOp.toHermitianOp.isHermitian with hσH_def
  set U : Op n := (↑hσH.eigenvectorUnitary : Op n) with hU_def
  set c : Fin n → ℂ := fun b => (Real.log (eigenvaluesOf σ b) : ℂ) with hc_def
  -- unitarity of the Mathlib eigenvector unitary `U`
  -- (`star` on matrices is `conjTranspose`, so these are the unitary identities themselves)
  have hUH_U : Uᴴ * U = 1 := Unitary.coe_star_mul_self hσH.eigenvectorUnitary
  have hU_UH : U * Uᴴ = 1 := Unitary.coe_mul_star_self hσH.eigenvectorUnitary
  -- σ diagonalized in the Mathlib eigenbasis: σ = U · diag(ev) · U†
  have hSdecomp := singleCopyReference_spectral_resolution σ
  have hU_spec : σ.toOp
      = U * Matrix.diagonal (fun b => (eigenvaluesOf σ b : ℂ)) * Uᴴ := by
    rw [hSdecomp, hU_def]
    exact eigenvectorBasis_weighted_rankOneProjectors hσH (fun b => (eigenvaluesOf σ b : ℂ))
  -- bridge: U · diag c · U† = W† · diag c · W via functional-calculus invariance
  have h₁ : (Uᴴ)ᴴ * Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ)) * Uᴴ
        = (InfoTheory.RelativeEntropy.eigenbasisOf σ)ᴴ
            * Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ))
            * InfoTheory.RelativeEntropy.eigenbasisOf σ := by
    rw [Matrix.conjTranspose_conjTranspose, ← hU_spec,
      InfoTheory.RelativeEntropy.eigenbasisOf_spectral_decomp σ]
  have hMM' : U * Matrix.diagonal c * Uᴴ
      = (InfoTheory.RelativeEntropy.eigenbasisOf σ)ᴴ * Matrix.diagonal c
          * InfoTheory.RelativeEntropy.eigenbasisOf σ := by
    have h := InfoTheory.RelativeEntropy.spectral_decomp_function_invariance Uᴴ
      (InfoTheory.RelativeEntropy.eigenbasisOf σ)
      (by rw [Matrix.conjTranspose_conjTranspose]; exact hU_UH)
      (by rw [Matrix.conjTranspose_conjTranspose]; exact hUH_U)
      (InfoTheory.RelativeEntropy.eigenbasisOf_unitary_left σ)
      (InfoTheory.RelativeEntropy.eigenbasisOf_unitary_right σ)
      (eigenvaluesOf σ) (eigenvaluesOf σ) h₁ Real.log
    rw [Matrix.conjTranspose_conjTranspose] at h
    exact h
  -- M = U · diag c · U†
  have hM : (∑ b : Fin n, c b • singleCopyReferenceProjector σ b)
      = U * Matrix.diagonal c * Uᴴ := by
    rw [hU_def]
    exact eigenvectorBasis_weighted_rankOneProjectors hσH c
  -- LHS as a single trace
  have hterm : ∀ b : Fin n,
      (singleCopyReferenceProjector σ b * ρB.toOp).trace.re
          * Real.log (singleCopyReferenceEigenvalue σ b)
        = (c b • (singleCopyReferenceProjector σ b * ρB.toOp)).trace.re := by
    intro b
    rw [show singleCopyReferenceEigenvalue σ b = eigenvaluesOf σ b from rfl,
      Matrix.trace_smul, smul_eq_mul, hc_def, Complex.re_ofReal_mul, mul_comm]
  have hLHS : (∑ b : Fin n, (singleCopyReferenceProjector σ b * ρB.toOp).trace.re
          * Real.log (singleCopyReferenceEigenvalue σ b))
      = ((∑ b : Fin n, c b • singleCopyReferenceProjector σ b) * ρB.toOp).trace.re := by
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_mul, Matrix.trace_sum,
      Complex.re_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [smul_mul_assoc]
  -- RHS as a single trace
  have hRHS : InfoTheory.RelativeEntropy.traceProductLogSigma ρB σ
      = ((InfoTheory.RelativeEntropy.eigenbasisOf σ)ᴴ * Matrix.diagonal c
          * InfoTheory.RelativeEntropy.eigenbasisOf σ * ρB.toOp).trace.re := by
    rw [InfoTheory.RelativeEntropy.traceProductLogSigma_eq_trace]
    rw [show ρB.toOp * (InfoTheory.RelativeEntropy.eigenbasisOf σ)ᴴ
          * Matrix.diagonal (fun i => (Real.log (eigenvaluesOf σ i) : ℂ))
          * InfoTheory.RelativeEntropy.eigenbasisOf σ
        = ρB.toOp * ((InfoTheory.RelativeEntropy.eigenbasisOf σ)ᴴ * Matrix.diagonal c
            * InfoTheory.RelativeEntropy.eigenbasisOf σ) from by
      rw [hc_def]; simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
  rw [hLHS, hM, hMM', hRHS]

/-- The reference-eigenvalue log moment equals `Tr(ρ_B ln σ)`. Contracting the block
resolution `Σ_{x,a} p_{x,a} |ψ_{x,a}⟩⟨ψ_{x,a}| = ρ_B` (the quantum marginal) against
the reference eigenprojectors,

  `Σ_{x,a,b} P(x,a,b) · ln q_b = Σ_b ⟨φ_b|ρ_B|φ_b⟩ · ln q_b = traceProductLogSigma ρ_B σ`.

The last step reconciles the Mathlib eigenvector basis `φ_b` with the
`eigenbasisOf σ` basis of `traceProductLogSigma` via
`spectral_decomp_function_invariance` applied to `f = log` (functional calculus is
basis-independent). -/
private lemma singleCopy_entropyMoment_logRef_eq
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n) :
    ∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
        singleCopyProbWeight ρ σ x a b
          * Real.log (singleCopyReferenceEigenvalue σ b)
      = InfoTheory.RelativeEntropy.traceProductLogSigma
          (ρ.quantumMarginalDensityOp hρ_norm) σ := by
  classical
  set ρB := ρ.quantumMarginalDensityOp hρ_norm with hρB_def
  -- Step 1: bring `b` to the front and factor the `log q_b`.
  have hreorg : (∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
        singleCopyProbWeight ρ σ x a b * Real.log (singleCopyReferenceEigenvalue σ b))
      = ∑ b : Fin n, (∑ x : X, ∑ a : Fin n, singleCopyProbWeight ρ σ x a b)
          * Real.log (singleCopyReferenceEigenvalue σ b) := by
    rw [show (∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
          singleCopyProbWeight ρ σ x a b * Real.log (singleCopyReferenceEigenvalue σ b))
        = ∑ x : X, ∑ b : Fin n, ∑ a : Fin n,
          singleCopyProbWeight ρ σ x a b * Real.log (singleCopyReferenceEigenvalue σ b) from
        Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul]
  rw [hreorg]
  -- Step 2: collapse the `(x,a)`-sum to a diagonal trace against `ρ_B`.
  have hcol : ∀ b : Fin n,
      (∑ x : X, ∑ a : Fin n, singleCopyProbWeight ρ σ x a b)
        = (singleCopyReferenceProjector σ b * ρB.toOp).trace.re := by
    intro b
    rw [Finset.sum_congr rfl (fun x _ => singleCopy_sum_a_probWeight_eq ρ σ x b)]
    have hmul : singleCopyReferenceProjector σ b * ρB.toOp
        = ∑ x : X, singleCopyReferenceProjector σ b * (ρ.stateMap x).toOp := by
      rw [← Finset.mul_sum]; rfl
    rw [hmul, Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_congr rfl (fun b _ => by rw [hcol b])]
  -- Step 3: the eigenbasis-bridge trace identity.
  exact singleCopy_entropyMoment_logRef_trace ρB σ

/-- **Support vanishing of overlaps.** Under feasibility `hfeas` (some `t·σ ⪰ ρ_x`
in the Löwner order), every block `ρ_x` lives in `supp σ`, so any overlap of a
live block eigenvector `ψ_{x,a}` with a *zero-eigenvalue* reference eigenvector
`φ_b` (`q_b = 0`) vanishes. Hence the probability weight `P(x,a,b)` is zero at
every reference index `b` with `q_b = 0`.

This is the support-containment input that validates the per-term log split
`ln(q_b/p_{x,a}) = ln q_b − ln p_{x,a}` in the entropy moment: without it (singular
`σ` with support leakage) the moment identity fails. -/
lemma singleCopy_probWeight_eq_zero_of_ref_zero
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (x : X) (a : Fin n) (b : Fin n)
    (hqb : singleCopyReferenceEigenvalue σ b = 0) :
    singleCopyProbWeight ρ σ x a b = 0 := by
  classical
  -- the reference projector is PSD and `σ` kills it (zero eigenvalue)
  have hQpsd : (singleCopyReferenceProjector σ b).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  have hact : σ.toOp * singleCopyReferenceProjector σ b
      = (singleCopyReferenceEigenvalue σ b : ℂ) • singleCopyReferenceProjector σ b := by
    have h := ((isHermitian_eigenvectorBasis_rankOneProjectors_action
      σ.toPosSemidefOp.toHermitianOp.isHermitian).2 b).1
    simpa only [singleCopyReferenceEigenvalue, singleCopyReferenceProjector] using h
  -- `(Q_b · t·σ)` has zero trace because `σ Q_b = q_b Q_b = 0`
  obtain ⟨t, ht⟩ := hfeas
  have hMB0 : (singleCopyReferenceProjector σ b * (Complex.ofReal t • σ.toOp)).trace.re = 0 := by
    rw [Matrix.mul_smul, Matrix.trace_smul,
      show (singleCopyReferenceProjector σ b * σ.toOp).trace
          = (σ.toOp * singleCopyReferenceProjector σ b).trace from Matrix.trace_mul_comm _ _,
      hact, hqb]
    simp
  -- feasibility: `Q_b · ρ_x ≤ Q_b · t·σ`, so its trace ≤ 0; PSD gives ≥ 0
  have hσherm : σ.toOp.IsHermitian := (posSemidefOp_implies_mathlib σ.toPosSemidefOp).1
  have hBherm : (Complex.ofReal t • σ.toOp).IsHermitian := by
    change (Complex.ofReal t • σ.toOp)ᴴ = Complex.ofReal t • σ.toOp
    rw [Matrix.conjTranspose_smul, hσherm]
    simp
  have hmono := trace_mul_le_of_opLe hQpsd (ρ.stateMap x).isHermitian hBherm (ht.2 x)
  rw [hMB0] at hmono
  have hge : 0 ≤ (singleCopyReferenceProjector σ b * (ρ.stateMap x).toOp).trace.re :=
    trace_mul_psd_nonneg _ _ hQpsd
      (posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)
  have hMA0 : (singleCopyReferenceProjector σ b * (ρ.stateMap x).toOp).trace.re = 0 :=
    le_antisymm hmono hge
  -- `Σ_{a'} P(x,a',b) = (Q_b · ρ_x).trace.re = 0`, each summand ≥ 0
  have hsumP := singleCopy_sum_a_probWeight_eq ρ σ x b
  have hP_nonneg : ∀ a' : Fin n, 0 ≤ singleCopyProbWeight ρ σ x a' b := by
    intro a'
    refine mul_nonneg ?_ ?_
    · exact singleCopyBlockEigenvalue_nonneg ρ x a'
    · exact trace_mul_psd_nonneg _ _ hQpsd (Matrix.posSemidef_vecMulVec_self_star _)
  have hsum0 : ∑ a' : Fin n, singleCopyProbWeight ρ σ x a' b = 0 := by
    rw [hsumP, hMA0]
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun a' _ => hP_nonneg a')).mp hsum0 a
    (Finset.mem_univ a)

/-- The `P`-expectation of `ln(q_b / p_{x,a})` equals `ln 2` times the σ-relative
conditional bit-entropy contribution:

  `Σ_{x,a,b} P(x,a,b) · ln(q_b / p_{x,a}) = (ln 2) · iidAEPBitEntropyContribution ρ hρ_norm σ`.

Splitting the log re-expresses the sum as `S(ρ_XB) + Tr(ρ_B ln σ)` (nats), with the
`S(ρ_B)` term cancelling. Feasibility `hfeas` is required: it forces every block
into `supp σ`, so the `q_b = 0` overlaps vanish and the per-term split
`ln(q/p) = ln q − ln p` is valid (it fails for singular `σ` with support leakage).
Reference: Renner, eq. (entrAB). -/
theorem singleCopyMGF_entropyMoment
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ)) :
    ∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
        singleCopyProbWeight ρ σ x a b
          * Real.log (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)
      = Real.log 2 * iidAEPBitEntropyContribution ρ hρ_norm σ := by
  classical
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  -- RHS simplification: `log2 · H_bits = S(ρ_XB) + Tr(ρ_B log σ)` (the `S(ρ_B)` cancels)
  have hRHS : Real.log 2 * iidAEPBitEntropyContribution ρ hρ_norm σ
      = vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        + InfoTheory.RelativeEntropy.traceProductLogSigma
            (ρ.quantumMarginalDensityOp hρ_norm) σ := by
    unfold iidAEPBitEntropyContribution
      InfoTheory.RelativeEntropy.relativeEntropyReal
    field_simp
    ring
  rw [hRHS]
  -- per-term log split, valid because `hfeas` kills the `q_b = 0` overlaps
  have hsplit : ∀ (x : X) (a b : Fin n),
      singleCopyProbWeight ρ σ x a b
          * Real.log (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)
        = singleCopyProbWeight ρ σ x a b
            * Real.log (singleCopyReferenceEigenvalue σ b)
          - singleCopyProbWeight ρ σ x a b
            * Real.log (singleCopyBlockEigenvalue ρ x a) := by
    intro x a b
    rcases eq_or_ne (singleCopyBlockEigenvalue ρ x a) 0 with hp | hp
    · have hP0 : singleCopyProbWeight ρ σ x a b = 0 := by
        unfold singleCopyProbWeight; rw [hp]; ring
      rw [hP0]; ring
    · rcases eq_or_ne (singleCopyReferenceEigenvalue σ b) 0 with hq | hq
      · have hP0 := singleCopy_probWeight_eq_zero_of_ref_zero ρ σ hfeas x a b hq
        rw [hP0]; ring
      · rw [Real.log_div hq hp, mul_sub]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => hsplit x a b)))]
  simp only [Finset.sum_sub_distrib]
  rw [singleCopy_entropyMoment_logRef_eq ρ hρ_norm σ,
    singleCopy_entropyMoment_logBlock_eq ρ hρ_norm σ]
  ring

/-! ## The `p/q` collision moment -/

/-- Operator square as a CFC real power: for the PSD block `ρ_x`,
`ρ_x · ρ_x = ρ_x ^ (1 + 1 : ℝ)`. -/
private lemma singleCopy_op_sq_eq_rpow
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (x : X) :
    (ρ.stateMap x).toOp * (ρ.stateMap x).toOp
      = (ρ.stateMap x).toOp ^ (1 + 1 : ℝ) := by
  have hpsd : (0 : Op n) ≤ (ρ.stateMap x).toOp :=
    Matrix.nonneg_iff_posSemidef.mpr
      (posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)
  rw [show (1 + 1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, CFC.rpow_natCast _ 2 hpsd, pow_two]

/-- **Per-`(a,b)` scalar identity** for the `p/q` collision moment. With `q ≥ 0`,
`p ^ (1+1) · q ^ (-1) · ov = (p · ov) · (p / q)` (the CFC `q ^ (-1)` is the real
`rpow`, so the identity is valid even at `q = 0`, where both sides vanish). -/
private lemma singleCopy_pOverq_term (p q ov : ℝ) (hq : 0 ≤ q) :
    p ^ (1 + 1 : ℝ) * q ^ (-1 : ℝ) * ov = (p * ov) * (p / q) := by
  rw [show (1 + 1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hq, Real.rpow_one]
  ring

/-- **Per-block `p/q` collision moment.** The `s = 1` slice of
`singleCopyBlock_tilted_trace_expansion`, rewritten as the probability-weighted
`p/q` sum:

  `tr[ρ_x · ρ_x · σ^{−1}].re = Σ_a Σ_b P(x,a,b) · (p_{x,a} / q_b)`. -/
private lemma singleCopy_pOverq_block
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (x : X) :
    ((ρ.stateMap x).toOp * (ρ.stateMap x).toOp * σ.toOp ^ (-1 : ℝ)).trace.re
      = ∑ a : Fin n, ∑ b : Fin n,
          singleCopyProbWeight ρ σ x a b
            * (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b) := by
  have hq_nonneg : ∀ b, 0 ≤ singleCopyReferenceEigenvalue σ b :=
    singleCopyReferenceEigenvalue_nonneg σ
  rw [singleCopy_op_sq_eq_rpow, singleCopyBlock_tilted_trace_expansion ρ σ 1 x]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [singleCopyProbWeight]
  exact singleCopy_pOverq_term _ _ _ (hq_nonneg b)

/-- The `P`-expectation of the ratio `p_{x,a}/q_b` equals Renner's collision factor:

  `Σ_{x,a,b} P(x,a,b) · (p_{x,a}/q_b) = ρ.tracedSquareTimesInvFactor σ = Σ_x tr[ρ_x² σ⁻¹]`.

Spectrally `ρ_x² = Σ_a p_{x,a}² |ψ_{x,a}⟩⟨ψ_{x,a}|` and `P·(p/q) = p_{x,a}² |overlap|² q_b^{-1}`.
The CFC `q_b^{-1}` is the real `rpow`, so the per-term identity holds even at
`q_b = 0` (both sides vanish); no feasibility hypothesis is needed. -/
theorem singleCopyMGF_pOverq_moment
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (_hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ)) :
    ∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
        singleCopyProbWeight ρ σ x a b
          * (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b)
      = ρ.tracedSquareTimesInvFactor σ := by
  classical
  unfold InfoTheory.SmoothMinEntropy.CQState.tracedSquareTimesInvFactor
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl (fun x _ => (singleCopy_pOverq_block ρ σ x).symm)

/-! ## The `q/p` collision moment bound -/

/-- Reference spectral collapse of the block trace. For a
fixed block eigen-projector `P_a = |ψ_{x,a}⟩⟨ψ_{x,a}|`, the reference spectral
resolution `σ = Σ_b q_b |φ_b⟩⟨φ_b|` collapses the trace against it:

  `tr[σ · P_a].re = Σ_b q_b · |⟨φ_b|ψ_{x,a}⟩|²`. -/
private lemma singleCopy_traceBlock_eq_sum
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (x : X) (a : Fin n) :
    (σ.toOp * singleCopyBlockProjector ρ x a).trace.re
      = ∑ b : Fin n,
          singleCopyReferenceEigenvalue σ b * singleCopyOverlap ρ σ x a b := by
  classical
  rw [singleCopyReference_spectral_resolution σ, Finset.sum_mul, Matrix.trace_sum,
    Complex.re_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    singleCopyOverlap]

/-- Per-block `q/p` bound. The inner double sum for one block
`x` is bounded by the indicator of the block being nonzero: it is `≤ 1` for live
blocks and `= 0` (hence `≤ 0`) for blocks with vanishing trace. -/
private lemma singleCopy_qOverp_block_le
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) (x : X) :
    ∑ a : Fin n, ∑ b : Fin n,
        singleCopyProbWeight ρ σ x a b
          * (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)
      ≤ if 0 < (ρ.stateMap x).trace then (1 : ℝ) else 0 := by
  classical
  -- eigenvalues of the PSD block are nonnegative
  have hev_nonneg : ∀ a, 0 ≤ singleCopyBlockEigenvalue ρ x a :=
    singleCopyBlockEigenvalue_nonneg ρ x
  -- the per-projector reference trace is nonnegative (product of two PSDs)
  have hT_nonneg : ∀ a,
      0 ≤ (σ.toOp * singleCopyBlockProjector ρ x a).trace.re := fun a =>
    trace_mul_psd_nonneg _ _ (posSemidefOp_implies_mathlib σ.toPosSemidefOp)
      (Matrix.posSemidef_vecMulVec_self_star _)
  -- per-block resolution of the identity and the total trace
  have hRa_sum := singleCopyBlock_sum_projector ρ x
  have hT_total :
      ∑ a : Fin n, (σ.toOp * singleCopyBlockProjector ρ x a).trace.re = 1 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hRa_sum, mul_one,
      σ.trace_one]
    simp
  -- inner sum over `b` per fixed `a`
  have hinner : ∀ a, ∑ b : Fin n,
        singleCopyProbWeight ρ σ x a b
          * (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)
      = if 0 < singleCopyBlockEigenvalue ρ x a
        then (σ.toOp * singleCopyBlockProjector ρ x a).trace.re else 0 := by
    intro a
    rcases eq_or_lt_of_le (hev_nonneg a) with hp0 | hppos
    · rw [if_neg (by rw [← hp0]; exact lt_irrefl 0)]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      unfold singleCopyProbWeight
      rw [← hp0]; simp
    · rw [if_pos hppos, singleCopy_traceBlock_eq_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      unfold singleCopyProbWeight
      have hpne : singleCopyBlockEigenvalue ρ x a ≠ 0 := hppos.ne'
      field_simp
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  by_cases htr : 0 < (ρ.stateMap x).trace
  · rw [if_pos htr]
    calc ∑ a : Fin n, (if 0 < singleCopyBlockEigenvalue ρ x a
            then (σ.toOp * singleCopyBlockProjector ρ x a).trace.re else 0)
        ≤ ∑ a : Fin n, (σ.toOp * singleCopyBlockProjector ρ x a).trace.re := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          by_cases h : 0 < singleCopyBlockEigenvalue ρ x a
          · rw [if_pos h]
          · rw [if_neg h]; exact hT_nonneg a
      _ = 1 := hT_total
  · rw [if_neg htr]
    -- vanishing block: all eigenvalues are zero, so every summand is zero
    have htr0 : (ρ.stateMap x).trace = 0 :=
      le_antisymm (not_lt.mp htr) (ρ.stateMap x).trace_nonneg
    have hsum0 : ∑ a : Fin n, singleCopyBlockEigenvalue ρ x a = 0 := by
      have htr_eq := (ρ.stateMap x).isHermitian.trace_eq_sum_eigenvalues
      have hre : (ρ.stateMap x).toOp.trace.re
          = ∑ a : Fin n, singleCopyBlockEigenvalue ρ x a := by
        rw [htr_eq, Complex.re_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        simp [singleCopyBlockEigenvalue]
      rw [← hre]
      exact htr0
    have hzero : ∀ a, singleCopyBlockEigenvalue ρ x a = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => hev_nonneg a)).mp hsum0
      exact fun a => this a (Finset.mem_univ a)
    refine le_of_eq (Finset.sum_eq_zero (fun a _ => ?_))
    rw [if_neg (by rw [hzero a]; exact lt_irrefl 0)]

/-- The `P`-expectation of `q_b/p_{x,a}` is bounded by the classical rank:

  `Σ_{x,a,b} P(x,a,b) · (q_b / p_{x,a}) ≤ classicalRank ρ`.

For the live terms `P·(q/p) = |⟨φ_b|ψ_{x,a}⟩|² q_b`; summing over `b` gives
`⟨ψ_{x,a}|σ|ψ_{x,a}⟩`, and summing over the live eigenvectors `a` of block `x`
gives `tr[Π_x σ] ≤ 1`, which is positive only for nonzero blocks. Hence the total
is at most the number of nonzero blocks `= classicalRank ρ`. -/
theorem singleCopyMGF_qOverp_le_classicalRank
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n) :
    ∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
        singleCopyProbWeight ρ σ x a b
          * (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)
      ≤ (ρ.classicalRank : ℝ) := by
  classical
  have hrank : (ρ.classicalRank : ℝ)
      = ∑ x : X, if 0 < (ρ.stateMap x).trace then (1 : ℝ) else 0 := by
    rw [CQState.classicalRank, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> simp
  rw [hrank]
  exact Finset.sum_le_sum (fun x _ => singleCopy_qOverp_block_le ρ σ x)

/-! ## Admissibility chain `4 ≤ μ` and `s ≤ 1/2` -/

/-- **Scalar AM–GM for the collision pair.** For positive `p, q`, the collision
ratio sum `q/p + p/q` is at least `2` (`(p - q)² ≥ 0`). -/
private lemma two_le_qOverp_add_pOverq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (2 : ℝ) ≤ q / p + p / q := by
  rw [div_add_div _ _ hp.ne' hq.ne', le_div_iff₀ (mul_pos hp hq)]
  nlinarith [sq_nonneg (p - q)]

/-- The reference spectral radius is at least `4`:

  `4 ≤ iidAEPSpectralRadius ρ σ`.

From the two collision moments and normalization of `P`,
`E_P[q/p] + E_P[p/q] + 2 ≤ μ`, while every `q/p + p/q ≥ 2` by AM–GM
(`(p − q)² ≥ 0`), so `4 ≤ μ`. Feasibility `hfeas` is required to kill the
`q_b = 0` terms in the moment sums. -/
theorem four_le_iidAEPSpectralRadius
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ)) :
    (4 : ℝ) ≤ iidAEPSpectralRadius ρ σ := by
  classical
  unfold iidAEPSpectralRadius
  -- the two collision moments, plus normalization of `P`
  have hqp := singleCopyMGF_qOverp_le_classicalRank ρ σ
  have hpq := singleCopyMGF_pOverq_moment ρ σ hfeas
  have hsum1 := sum_singleCopyProbWeight_eq_one ρ hρ_norm σ
  -- per-triple AM–GM bound: `2·P ≤ P·(q/p) + P·(p/q)`
  have hterm : ∀ (x : X) (a b : Fin n),
      2 * singleCopyProbWeight ρ σ x a b
        ≤ singleCopyProbWeight ρ σ x a b
              * (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)
          + singleCopyProbWeight ρ σ x a b
              * (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b) := by
    intro x a b
    have hp_nn : 0 ≤ singleCopyBlockEigenvalue ρ x a := singleCopyBlockEigenvalue_nonneg ρ x a
    have hq_nn : 0 ≤ singleCopyReferenceEigenvalue σ b := singleCopyReferenceEigenvalue_nonneg σ b
    rcases eq_or_lt_of_le hp_nn with hp0 | hppos
    · have hP0 : singleCopyProbWeight ρ σ x a b = 0 := by
        unfold singleCopyProbWeight; rw [← hp0]; ring
      rw [hP0]; simp
    · rcases eq_or_lt_of_le hq_nn with hq0 | hqpos
      · have hP0 := singleCopy_probWeight_eq_zero_of_ref_zero ρ σ hfeas x a b hq0.symm
        rw [hP0]; simp
      · have hP_nn := singleCopyProbWeight_nonneg ρ σ x a b
        have hamgm := two_le_qOverp_add_pOverq hppos hqpos
        rw [← mul_add, mul_comm 2 (singleCopyProbWeight ρ σ x a b)]
        exact mul_le_mul_of_nonneg_left hamgm hP_nn
  -- sum the per-triple bound: `2 = 2·Σ P ≤ Σ (P·(q/p) + P·(p/q))`
  have hLB : (2 : ℝ)
      ≤ ∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
          (singleCopyProbWeight ρ σ x a b
              * (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)
            + singleCopyProbWeight ρ σ x a b
              * (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b)) := by
    calc (2 : ℝ)
        = 2 * ∑ x : X, ∑ a : Fin n, ∑ b : Fin n, singleCopyProbWeight ρ σ x a b := by
          rw [hsum1]; ring
      _ = ∑ x : X, ∑ a : Fin n, ∑ b : Fin n, 2 * singleCopyProbWeight ρ σ x a b := by
          simp only [Finset.mul_sum]
      _ ≤ _ :=
          Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun a _ =>
            Finset.sum_le_sum (fun b _ => hterm x a b)))
  -- split the combined sum into the two moments
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_add_distrib)),
    Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib),
    Finset.sum_add_distrib] at hLB
  linarith [hqp, hpq, hLB]

/-- The tilt parameter satisfies `s ≤ 1/2`.

Given `4 ≤ μ`, `ln μ ≥ ln 4 = 2 ln 2 > 0`, so the range hypothesis
`s · ln μ ≤ ln 2` forces `s ≤ ln 2 / ln μ ≤ ln 2 / (2 ln 2) = 1/2`. With `0 ≤ s`
this places `s ∈ [0, 1/2]`. -/
theorem s_le_half_of_mul_log_spectralRadius_le_log_two
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n)
    (hμ4 : (4 : ℝ) ≤ iidAEPSpectralRadius ρ σ)
    {s : ℝ} (hs : 0 ≤ s)
    (hrange : s * Real.log (iidAEPSpectralRadius ρ σ) ≤ Real.log 2) :
    s ≤ 1 / 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  have h4le : Real.log 4 ≤ Real.log (iidAEPSpectralRadius ρ σ) :=
    Real.log_le_log (by norm_num) hμ4
  have hμlog : 2 * Real.log 2 ≤ Real.log (iidAEPSpectralRadius ρ σ) := by
    rw [hlog4] at h4le; exact h4le
  nlinarith [hrange, mul_le_mul_of_nonneg_left hμlog hs, hl2]

end InfoTheory.SmoothMinEntropy
