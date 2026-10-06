import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.Quantum.Metrics.FidelityScaling
import QCryptLean.Quantum.Metrics.FidelityPurificationGeneralized
import QCryptLean.Quantum.Metrics.PurificationReshape
import QCryptLean.Quantum.Metrics.SameAncillaPurification
import QCryptLean.Quantum.Metrics.UhlmannWitness
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Uhlmann monotonicity under partial trace — density-operator and PSD forms

This file collects the partial-trace monotonicity statements for Uhlmann
fidelity:

* the density-operator-level statement
  `fidelity_le_fidelity_partialTraceB_ofDensity`, and
* the PSD-level corollary `fidelity_le_fidelity_partialTraceB`, which
  follows from the density-operator-level statement via the homogeneity
  identity `fidelity_smul_smul` (`FidelityScaling.lean`) after handling
  the trace-zero boundary cases separately.

The textbook proof of the density-operator statement (Watrous
Prop. 3.20) routes through two applications of Uhlmann's upper bound:

  F(ρ, τ)
    = Re ⟨Ψρ' | Ψτ'⟩       -- achievability for the joint states
    ≤ ‖⟨Ψρ' | Ψτ'⟩‖
    ≤ F(Tr_R ρ, Tr_R τ)     -- regrouped purifications and Uhlmann upper bound

The second step requires the *generalized*-ancilla form of the
purification overlap bound (the regrouped purifications live in a tensor
factor of the form `H_E ⊗ (H_R ⊗ H_R)`).  The generalized-ancilla
Uhlmann upper bound is stated in `FidelityPurificationGeneralized.lean`; the regrouping
reshape `reshapedPurificationPair`, which is namespaced under the main
theorem here, is packaged in this file as a private-section helper for
the density-operator-level monotonicity statement.

## Main statements

- `fidelity_le_fidelity_partialTraceB_ofDensity.reshapedPurificationPair`:
  the regrouping reshape — there exist reshaped purifications of the
  reduced states on the combined ancilla, whose overlap norm equals the
  norm of the original `(sameAncillaPurificationKet ρ).dag * ketB τ U`
  overlap.
- `fidelity_le_fidelity_partialTraceB_ofDensity`: density-operator-level
  Uhlmann monotonicity under partial trace.  Reduces to (i) the Uhlmann
  witness achievability (`UhlmannWitness.ketB_re_overlap_of_witness`),
  (ii) the regrouping reshape `reshapedPurificationPair`,
  (iii) the generalized-ancilla Uhlmann upper bound
  (`Quantum.Metrics.RectangularPolar.norm_overlap_le_fidelity_of_polar`), and
  (iv) `Complex.re_le_norm`.
- `fidelity_le_fidelity_partialTraceB`: PSD-level corollary obtained by
  normalizing each PSD operator by its trace and rescaling.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

open KitaevWatrousPurification UhlmannWitness

namespace fidelity_le_fidelity_partialTraceB_ofDensity

/-- **Regrouping lemma for partial-trace monotonicity.**

The canonical joint purification ket `sameAncillaPurificationKet ρ` of
`ρ : DensityOp (dE * dR)` lives in `Ket ((dE * dR) * (dE * dR))` and
purifies `ρ` on an ancilla of size `dE * dR`.  When we reassociate the
carrier as `Ket (dE * (dR * (dE * dR)))`, the right partial trace (over
the combined ancilla of size `dR * (dE * dR)`) recovers the reduced
state `(DensityOp.partialTraceB ρ).toOp`.

Simultaneously, the Uhlmann-witness ket `ketB τ U` admits a reshape
whose right partial trace recovers `(DensityOp.partialTraceB τ).toOp`,
and the joint norm of the overlap is preserved under the reshape (the
reshape is a unitary reassociation of carriers).

This lemma packages both reshapes and the norm-preserving overlap
identity into one existence statement, ready to feed into
`Quantum.Metrics.RectangularPolar.norm_overlap_le_fidelity_of_polar`. The mathematical
content is a reassociation
`((dE * dR) * (dE * dR)) ≃ (dE * (dR * (dE * dR)))` plus the iterated-
partial-trace identity. -/
lemma reshapedPurificationPair
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρ τ : DensityOp (dE * dR)) (U : UnitaryOp (dE * dR)) :
    letI : NeZero (dR * (dE * dR)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne dR) (Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR))⟩
    ∃ ψρ ψτ : Ket (dE * (dR * (dE * dR))),
      partialTraceB (ψρ * ψρ.dag) = (DensityOp.partialTraceB ρ).toOp ∧
      partialTraceB (ψτ * ψτ.dag) = (DensityOp.partialTraceB τ).toOp ∧
      ‖((sameAncillaPurificationKet ρ).dag * (ketB τ U) : ℂ)‖ =
        ‖(ψρ.dag * ψτ : ℂ)‖ := by
  let : NeZero (dR * (dE * dR)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dR) (Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR))⟩
  -- Reshape the two original kets into the new carrier.
  refine ⟨Quantum.TensorProducts.reshapeKet (sameAncillaPurificationKet ρ),
          Quantum.TensorProducts.reshapeKet (ketB τ U),
          ?_, ?_, ?_⟩
  · -- partialTraceB of reshaped ρ-ket = (DensityOp.partialTraceB ρ).toOp.
    have hρ_psd : ρ.toOp.PosSemidef :=
      Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp
    have h_outer :
        partialTraceB ((sameAncillaPurificationKet ρ) *
            (sameAncillaPurificationKet ρ).dag) = ρ.toOp := by
      rw [← sameAncillaPurification_eq_ketbra_sameAncillaPurificationKet]
      exact partialTraceB_sameAncillaPurification ρ.toOp hρ_psd
    rw [Quantum.TensorProducts.reshapeKet_partialTraceB_iterated_eq, h_outer]
    rfl
  · -- partialTraceB of reshaped τ-ket = (DensityOp.partialTraceB τ).toOp.
    have h_outer :
        partialTraceB ((ketB τ U) * (ketB τ U).dag) = τ.toOp :=
      ketB_partialTraceB τ U
    rw [Quantum.TensorProducts.reshapeKet_partialTraceB_iterated_eq, h_outer]
    rfl
  · -- Overlap norm preserved.
    exact (Quantum.TensorProducts.reshapeKet_overlap_norm_eq
      (sameAncillaPurificationKet ρ) (ketB τ U)).symm

end fidelity_le_fidelity_partialTraceB_ofDensity

/-- **Uhlmann monotonicity under partial trace, density-operator form.**

For density operators `ρ τ : DensityOp (dE * dR)`,

    `F(ρ, τ) ≤ F(Tr_R ρ, Tr_R τ)`.

This is the genuine analytic core of the partial-trace monotonicity
statement; the PSD-level statement
`fidelity_le_fidelity_partialTraceB` reduces to this one via the
homogeneity identity `fidelity_smul_smul` after normalizing each PSD
operator by its trace and handling the trace-zero boundary cases
separately.

The proof (Watrous Prop. 3.20) combines Uhlmann-witness achievability of
the canonical-purification overlap with the generalized-ancilla form of
`fidelity_ge_purification_overlap_norm` applied to the regrouped
purifications viewed as purifications of the reduced states.  See
`Quantum.Metrics.RectangularPolar.norm_overlap_le_fidelity_of_polar` (in
`FidelityPurificationGeneralized.lean`) and the regrouping
lemma `reshapedPurificationPair` above. -/
theorem fidelity_le_fidelity_partialTraceB_ofDensity
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρ τ : DensityOp (dE * dR)) :
    fidelity ρ.toPosSemidefOp τ.toPosSemidefOp ≤
      fidelity ρ.toPosSemidefOp.partialTraceB τ.toPosSemidefOp.partialTraceB := by
  -- (i) Uhlmann-witness achievability for the joint pair `(ρ, τ)`:
  -- choose `U` so the real part of the canonical overlap equals `F(ρ, τ)`.
  obtain ⟨U, hU⟩ :=
    sameAncillaPurificationKet_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich
      ρ τ
  have hAchieve :
      ((KitaevWatrousPurification.sameAncillaPurificationKet ρ).dag *
          (UhlmannWitness.ketB τ U) : ℂ).re =
        fidelity ρ.toPosSemidefOp τ.toPosSemidefOp :=
    UhlmannWitness.ketB_re_overlap_of_witness ρ τ U hU
  -- (ii) Regrouping: reshape the joint kets into `Ket (dE * (dR * (dE * dR)))`
  -- so they purify the reduced states `(Tr_R ρ, Tr_R τ)` on the combined
  -- ancilla, with overlap norm preserved.
  let : NeZero (dR * (dE * dR)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dR) (Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR))⟩
  obtain ⟨ψρ', ψτ', hψρ'_pt, hψτ'_pt, h_overlap_eq⟩ :=
    fidelity_le_fidelity_partialTraceB_ofDensity.reshapedPurificationPair ρ τ U
  -- (iii) Generalized-ancilla Uhlmann upper bound on the reshaped pair.
  have hGenAnc :=
    Quantum.Metrics.RectangularPolar.norm_overlap_le_fidelity_of_polar
      (d := dE) (a := dR * (dE * dR))
      (DensityOp.partialTraceB ρ) (DensityOp.partialTraceB τ)
      ψρ' ψτ' hψρ'_pt hψτ'_pt
  -- (iv) Compose: `F(ρ,τ) = Re overlap ≤ ‖overlap‖ = ‖reshaped overlap‖ ≤ F(Tr_R ρ, Tr_R τ)`.
  calc fidelity ρ.toPosSemidefOp τ.toPosSemidefOp
      = ((KitaevWatrousPurification.sameAncillaPurificationKet ρ).dag *
          (UhlmannWitness.ketB τ U) : ℂ).re := hAchieve.symm
    _ ≤ ‖((KitaevWatrousPurification.sameAncillaPurificationKet ρ).dag *
            (UhlmannWitness.ketB τ U) : ℂ)‖ := Complex.re_le_norm _
    _ = ‖(ψρ'.dag * ψτ' : ℂ)‖ := h_overlap_eq
    _ ≤ fidelity (DensityOp.partialTraceB ρ).toPosSemidefOp
                  (DensityOp.partialTraceB τ).toPosSemidefOp := hGenAnc

/-- Uhlmann fidelity vanishes when the left PSD operand is the zero operator. -/
lemma fidelity_eq_zero_of_left_toOp_eq_zero {n : ℕ} [NeZero n]
    (A B : PosSemidefOp n) (hA : A.toOp = 0) : fidelity A B = 0 := by
  unfold fidelity sqrtPosSemidefOp
  simp [hA]

/-- Uhlmann fidelity vanishes when the right PSD operand is the zero operator. -/
lemma fidelity_eq_zero_of_right_toOp_eq_zero {n : ℕ} [NeZero n]
    (A B : PosSemidefOp n) (hB : B.toOp = 0) : fidelity A B = 0 := by
  unfold fidelity sqrtPosSemidefOp
  simp [hB]

/-- Scalar-recovery for trace-normalization: scaling `normalizePosSemidefOp A ha`
by `(tr A).re` returns `A`. -/
lemma trace_smul_normalizePosSemidefOp_toOp {n : ℕ}
    (A : PosSemidefOp n) (ha : 0 < (Matrix.trace A.toOp).re) :
    ((Matrix.trace A.toOp).re : ℂ) • (normalizePosSemidefOp A ha).toOp = A.toOp := by
  rw [normalizePosSemidefOp_toOp, Complex.ofReal_inv, smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne'), one_smul]

/-- Uhlmann fidelity is monotone under tracing out a right tensor factor.

This is the standard CPTP monotonicity statement specialized to the
partial-trace channel `partialTraceB`.  The intended proof derives it from
`fidelity_ge_purification_overlap_norm`: an optimal purification overlap for
`A,B` is also a purification overlap for the reduced states after tracing out
the discarded tensor factor. -/
theorem fidelity_le_fidelity_partialTraceB
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (A B : PosSemidefOp (dE * dR)) :
    fidelity A B ≤ fidelity A.partialTraceB B.partialTraceB := by
  let : PartialOrder (Op (dE * dR)) := Matrix.instPartialOrder
  let : StarOrderedRing (Op (dE * dR)) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op (dE * dR)) := Matrix.instNonnegSpectrumClass
  -- Set the trace scalars `a := (Tr A).re` and `b := (Tr B).re`.
  set a : ℝ := (Matrix.trace A.toOp).re
  set b : ℝ := (Matrix.trace B.toOp).re
  have hA_ps : A.toOp.PosSemidef := posSemidefOp_implies_mathlib A
  have hB_ps : B.toOp.PosSemidef := posSemidefOp_implies_mathlib B
  have ha_nn : 0 ≤ a := (Complex.nonneg_iff.mp hA_ps.trace_nonneg).1
  have hb_nn : 0 ≤ b := (Complex.nonneg_iff.mp hB_ps.trace_nonneg).1
  have hA_im : (Matrix.trace A.toOp).im = 0 :=
    ((Complex.nonneg_iff.mp hA_ps.trace_nonneg).2).symm
  have hB_im : (Matrix.trace B.toOp).im = 0 :=
    ((Complex.nonneg_iff.mp hB_ps.trace_nonneg).2).symm
  -- Boundary case: `a = 0`.  Then `A.toOp = 0` and both fidelities vanish/are
  -- non-negative.
  by_cases ha_zero : a = 0
  · have hA_trace_zero : Matrix.trace A.toOp = 0 :=
      Complex.ext ha_zero hA_im
    have hA_zero : A.toOp = 0 := hA_ps.trace_eq_zero_iff.mp hA_trace_zero
    rw [fidelity_eq_zero_of_left_toOp_eq_zero A B hA_zero]
    exact fidelity_nonneg_posSemidefOp _ _
  -- Boundary case: `b = 0`.
  by_cases hb_zero : b = 0
  · have hB_trace_zero : Matrix.trace B.toOp = 0 :=
      Complex.ext hb_zero hB_im
    have hB_zero : B.toOp = 0 := hB_ps.trace_eq_zero_iff.mp hB_trace_zero
    rw [fidelity_eq_zero_of_right_toOp_eq_zero A B hB_zero]
    exact fidelity_nonneg_posSemidefOp _ _
  -- Generic case: both traces strictly positive.  Normalize and apply the
  -- density-operator-level bound `fidelity_le_fidelity_partialTraceB_ofDensity`,
  -- then rescale via `fidelity_smul_smul`.
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nn (Ne.symm ha_zero)
  have hb_pos : 0 < b := lt_of_le_of_ne hb_nn (Ne.symm hb_zero)
  set A' : DensityOp (dE * dR) := normalizePosSemidefOp A ha_pos
  set B' : DensityOp (dE * dR) := normalizePosSemidefOp B hb_pos
  have hA_scale : ((a : ℂ) • A'.toOp) = A.toOp :=
    trace_smul_normalizePosSemidefOp_toOp A ha_pos
  have hB_scale : ((b : ℂ) • B'.toOp) = B.toOp :=
    trace_smul_normalizePosSemidefOp_toOp B hb_pos
  -- Partial trace commutes with scalar multiplication, so the same
  -- decomposition transfers to the reduced operators.
  have hAptB_scale :
      ((a : ℂ) • A'.toPosSemidefOp.partialTraceB.toOp) = A.partialTraceB.toOp := by
    change ((a : ℂ) • Quantum.TensorProducts.partialTraceB A'.toOp)
      = Quantum.TensorProducts.partialTraceB A.toOp
    rw [← partialTraceB_smul, hA_scale]
  have hBptB_scale :
      ((b : ℂ) • B'.toPosSemidefOp.partialTraceB.toOp) = B.partialTraceB.toOp := by
    change ((b : ℂ) • Quantum.TensorProducts.partialTraceB B'.toOp)
      = Quantum.TensorProducts.partialTraceB B.toOp
    rw [← partialTraceB_smul, hB_scale]
  -- Scaling identity for the full operators.
  have h_scaling :=
    fidelity_smul_smul (α := a) (β := b) ha_nn hb_nn
      A'.toPosSemidefOp B'.toPosSemidefOp
  have h_expand : fidelity A B =
      Real.sqrt (a * b) * fidelity A'.toPosSemidefOp B'.toPosSemidefOp := by
    rw [← h_scaling, hA_scale, hB_scale]
    rfl
  -- Scaling identity for the reduced operators.
  have h_scaling_pt :=
    fidelity_smul_smul (α := a) (β := b) ha_nn hb_nn
      A'.toPosSemidefOp.partialTraceB B'.toPosSemidefOp.partialTraceB
  have h_expand_pt : fidelity A.partialTraceB B.partialTraceB =
      Real.sqrt (a * b) *
        fidelity A'.toPosSemidefOp.partialTraceB B'.toPosSemidefOp.partialTraceB := by
    rw [← h_scaling_pt, hAptB_scale, hBptB_scale]
    rfl
  -- The genuine analytic content: density-op-level partial-trace monotonicity.
  have h_density :
      fidelity A'.toPosSemidefOp B'.toPosSemidefOp ≤
        fidelity A'.toPosSemidefOp.partialTraceB B'.toPosSemidefOp.partialTraceB :=
    fidelity_le_fidelity_partialTraceB_ofDensity A' B'
  have h_sqrt_nn : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  rw [h_expand, h_expand_pt]
  exact mul_le_mul_of_nonneg_left h_density h_sqrt_nn

end Quantum.Metrics

end
