import QCryptLean.Quantum.Metrics.SameAncillaPurification
import QCryptLean.Quantum.Metrics.RectangularPolar
import QCryptLean.Quantum.Metrics.RectangularCoisometryTransport
import QCryptLean.Quantum.Metrics.UhlmannWitness
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.DirectSumEmbed

/-!
# Sub-Normalized Uhlmann Theorems — generalized-fidelity witnesses and live-branch bounds

This module proves the Uhlmann-style interface for sub-normalized states used
by smooth min-entropy arguments.  The direct-sum extension converts generalized
fidelity of sub-density operators into ordinary fidelity of density operators,
and rectangular-polar estimates bound overlaps of arbitrary live purification
branches by ordinary fidelity of their marginals.

## Main definitions
This file introduces no new definitions.

## Main statements
- `SubDensityOp.exists_purification_overlap_eq_fidelityGen`: normalized
  purifications whose overlap realizes generalized fidelity
- `SubDensityOp.livePurificationOverlap_norm_le_fidelity`: live-branch overlap
  bounded by ordinary fidelity of the sub-normalized marginals
- `SubDensityOp.livePurificationOverlap_re_le_fidelity`: real-part form of the
  live-branch overlap bound
- `SubDensityOp.exists_right_coisometry_sameAncillaPurificationKetOfOp`:
  any large-enough live purification factors through the canonical
  same-ancilla purification by a right coisometry
- `SubDensityOp.exists_livePurification_overlap_eq_fidelity_fixed_source`:
  fixed-source live-branch achievability for ordinary fidelity
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Metrics Matrix
open Quantum.Metrics.KitaevWatrousPurification
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Uhlmann witness for sub-normalized states.**

For sub-normalized `ρ, σ : SubDensityOp n`, there exist normalized
purifications (on a doubled space `(n+1) × (n+1)`) whose cross-overlap's
real part equals `fidelityGen ρ σ`.

**Strategy.** Block-extend via `SubDensityOp.toDensityOpExtend`; generalized
fidelity becomes ordinary fidelity of the extensions via
`toDensityOpExtend_fidelity`; invoke
`sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich`
on the normalized extensions. -/
theorem SubDensityOp.exists_purification_overlap_eq_fidelityGen
    {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    ∃ (ψρ ψσ : Ket ((n + 1) * (n + 1))) (U : UnitaryOp (n + 1)),
      ψρ.dag * ψρ = 1 ∧ ψσ.dag * ψσ = 1 ∧
      ((ψσ.dag * (Op.tensor U.toOp (1 : Op (n + 1))) * ψρ).re
        = fidelityGen ρ σ) := by
  let ρE : DensityOp (n + 1) := ρ.toDensityOpExtend
  let σE : DensityOp (n + 1) := σ.toDensityOpExtend
  obtain ⟨U, hU⟩ :=
    sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich
      ρE σE
  refine ⟨(sameAncillaPurificationDensity ρE).pureKetOf
            (sameAncillaPurificationDensity_isPure ρE),
          (sameAncillaPurificationDensity σE).pureKetOf
            (sameAncillaPurificationDensity_isPure σE),
          U, ?_, ?_, ?_⟩
  · exact DensityOp.pureKetOf_normalized _ _
  · exact DensityOp.pureKetOf_normalized _ _
  · rw [hU, ← toDensityOpExtend_fidelity ρ σ]
    rfl

/-- **Sub-normalized Uhlmann upper bound for live branches.**

If two live purification branches reduce to sub-density operators `ρ` and `σ`
after tracing out the same auxiliary carrier, then their overlap is bounded by
the ordinary Uhlmann fidelity of the two PSD marginals. -/
theorem SubDensityOp.livePurificationOverlap_norm_le_fidelity
    {d anc : ℕ} [NeZero d] [NeZero anc]
    (ρ σ : SubDensityOp d)
    (ψ φ : Ket (d * anc))
    (hψ : Quantum.TensorProducts.partialTraceB (ψ * ψ.dag) = ρ.toOp)
    (hφ : Quantum.TensorProducts.partialTraceB (φ * φ.dag) = σ.toOp) :
    ‖(ψ.dag * φ : ℂ)‖ ≤
      Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
  simpa using
    Quantum.Metrics.RectangularPolar.norm_overlap_le_fidelity_of_polar_psd
      ρ.toPosSemidefOp σ.toPosSemidefOp ψ φ hψ hφ

/-- Real-part form of `SubDensityOp.livePurificationOverlap_norm_le_fidelity`. -/
theorem SubDensityOp.livePurificationOverlap_re_le_fidelity
    {d anc : ℕ} [NeZero d] [NeZero anc]
    (ρ σ : SubDensityOp d)
    (ψ φ : Ket (d * anc))
    (hψ : Quantum.TensorProducts.partialTraceB (ψ * ψ.dag) = ρ.toOp)
    (hφ : Quantum.TensorProducts.partialTraceB (φ * φ.dag) = σ.toOp) :
    (ψ.dag * φ : ℂ).re ≤
      Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp :=
  (Complex.re_le_norm _).trans
    (SubDensityOp.livePurificationOverlap_norm_le_fidelity ρ σ ψ φ hψ hφ)

/-- The canonical same-ancilla purification of a sub-density operator has row
Gram matrix equal to the operator itself. -/
lemma SubDensityOp.sameAncillaPurificationKetOfOp_vecMatrix_mul_conjTranspose
    {d : ℕ} (ρ : SubDensityOp d) :
    Quantum.Metrics.RectangularPolar.ketVecMatrix
          (sameAncillaPurificationKetOfOp ρ.toOp) *
        (Quantum.Metrics.RectangularPolar.ketVecMatrix
          (sameAncillaPurificationKetOfOp ρ.toOp)).conjTranspose =
      ρ.toOp := by
  have hρ_psd : Matrix.PosSemidef ρ.toOp := by
    simpa using Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  simpa using
    (Quantum.Metrics.RectangularPolar.ketVecMatrix_mul_conjTranspose_eq_partialTraceB
      (sameAncillaPurificationKetOfOp ρ.toOp)).trans
        (partialTraceB_sameAncillaPurificationKetOfOp ρ.toOp hρ_psd)

/-- Any live purification on a large enough right carrier is obtained from the
canonical same-ancilla purification by right multiplication with a coisometry. -/
lemma SubDensityOp.exists_right_coisometry_sameAncillaPurificationKetOfOp
    {d anc : ℕ} [NeZero d] [NeZero anc]
    (ρ : SubDensityOp d) (ψ : Ket (d * anc))
    (hψ : Quantum.TensorProducts.partialTraceB (ψ * ψ.dag) = ρ.toOp)
    (hdim : d ≤ anc) :
    ∃ W : Matrix (Fin d) (Fin anc) ℂ,
      W * W.conjTranspose = (1 : Matrix (Fin d) (Fin d) ℂ) ∧
      Quantum.Metrics.RectangularPolar.ketVecMatrix ψ =
        Quantum.Metrics.RectangularPolar.ketVecMatrix
          (sameAncillaPurificationKetOfOp ρ.toOp) * W := by
  let χ : Ket (d * d) := sameAncillaPurificationKetOfOp ρ.toOp
  have hχ_gram :
      Quantum.Metrics.RectangularPolar.ketVecMatrix χ *
          (Quantum.Metrics.RectangularPolar.ketVecMatrix χ).conjTranspose =
        ρ.toOp := by
    simpa [χ] using
      SubDensityOp.sameAncillaPurificationKetOfOp_vecMatrix_mul_conjTranspose ρ
  have hψ_gram :
      Quantum.Metrics.RectangularPolar.ketVecMatrix ψ *
          (Quantum.Metrics.RectangularPolar.ketVecMatrix ψ).conjTranspose =
        ρ.toOp := by
    simpa using
      (Quantum.Metrics.RectangularPolar.ketVecMatrix_mul_conjTranspose_eq_partialTraceB
        ψ).trans hψ
  have hgram :
      Quantum.Metrics.RectangularPolar.ketVecMatrix χ *
          (Quantum.Metrics.RectangularPolar.ketVecMatrix χ).conjTranspose =
        Quantum.Metrics.RectangularPolar.ketVecMatrix ψ *
          (Quantum.Metrics.RectangularPolar.ketVecMatrix ψ).conjTranspose := by
    rw [hχ_gram, hψ_gram]
  exact
    Matrix.exists_coisometry_right_factor_of_mul_conjTranspose_eq
      (Quantum.Metrics.RectangularPolar.ketVecMatrix χ)
      (Quantum.Metrics.RectangularPolar.ketVecMatrix ψ)
      hgram hdim

/-- Fixed-source live Uhlmann achievability for sub-density operators.

For a fixed live branch `ψ` reducing to `ρ`, and a sufficiently large right
carrier, there is a live branch on the same carrier reducing to `σ` whose real
overlap with `ψ` realizes the ordinary Uhlmann fidelity of the two live
marginals. -/
theorem SubDensityOp.exists_livePurification_overlap_eq_fidelity_fixed_source
    {d anc : ℕ} [NeZero d] [NeZero anc]
    (ρ σ : SubDensityOp d) (ψ : Ket (d * anc))
    (hψ : Quantum.TensorProducts.partialTraceB (ψ * ψ.dag) = ρ.toOp)
    (hdim : d ≤ anc) :
    ∃ φ : Ket (d * anc),
      Quantum.TensorProducts.partialTraceB (φ * φ.dag) = σ.toOp ∧
      (ψ.dag * φ : ℂ).re =
        Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
  let χ : Ket (d * d) := sameAncillaPurificationKetOfOp ρ.toOp
  obtain ⟨φ₀, hφ₀, hoverlap₀⟩ :=
    Quantum.Metrics.UhlmannWitness.exists_sameAncillaPurificationKetOfOp_overlap_re_eq_fidelity
      ρ.toPosSemidefOp σ.toPosSemidefOp
  obtain ⟨W, hW, hψW⟩ :=
    SubDensityOp.exists_right_coisometry_sameAncillaPurificationKetOfOp
      ρ ψ hψ hdim
  obtain ⟨φ, hφ_partial, hφ_overlap⟩ :=
    Quantum.Metrics.RectangularCoisometryTransport.exists_transport_right_coisometry_re
      χ ψ φ₀ W hW hψW
  refine ⟨φ, ?_, ?_⟩
  · calc
      Quantum.TensorProducts.partialTraceB (φ * φ.dag)
          = Quantum.TensorProducts.partialTraceB (φ₀ * φ₀.dag) := hφ_partial
      _ = σ.toOp := by
          simpa using hφ₀
  · calc
      (ψ.dag * φ : ℂ).re = (χ.dag * φ₀ : ℂ).re := hφ_overlap
      _ = Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
          simpa [χ] using hoverlap₀

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
