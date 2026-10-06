import QCryptLean.Quantum.Metrics.FidelityPartialTraceMonotone
import QCryptLean.Quantum.Metrics.FidelityIsometry
import QCryptLean.Quantum.Channels.Stinespring.Minimal.Existence

/-!
# Fidelity is monotone under CPTP maps

This module packages the per-block fidelity data-processing inequality (DPI)
for completely positive trace-preserving (CPTP) linear maps, derived from the
Stinespring dilation by composing two existing pieces:

* `Quantum.Metrics.fidelity_isometry_conj_of_toOp_eq` — fidelity is invariant
  under simultaneous conjugation by a rectangular isometry; and
* `Quantum.Metrics.fidelity_le_fidelity_partialTraceB` — fidelity is monotone
  under tracing out a right tensor factor.

The Stinespring dilation `Φ A = Tr_E (V A V†)` lets us realize a CPTP map as
the partial trace of an isometric conjugation, so Uhlmann fidelity can only
*increase* under a CPTP map applied to PSD operators.

## Main statement

* `Quantum.Metrics.fidelity_le_fidelity_cptp_image`: for any CPTP linear map
  `Φ : Op n →ₗ[ℂ] Op m` and PSD operators `A, B : PosSemidefOp n` with images
  `A', B' : PosSemidefOp m` (i.e. `A'.toOp = Φ A.toOp` and `B'.toOp = Φ B.toOp`),
  `fidelity A B ≤ fidelity A' B'`.

## References

* Uhlmann (1976). *The "transition probability" in the state space of a
  ∗-algebra.* Rep. Math. Phys. 9.
* Watrous (2018). *Theory of Quantum Information*, §3.5.
-/

open Quantum.Operators Quantum.Channels Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-- **Per-block CPTP fidelity DPI (Uhlmann monotonicity).**

For any CPTP linear map `Φ : Op n →ₗ[ℂ] Op m` and PSD operators
`A, B : PosSemidefOp n`, bundled images `A', B' : PosSemidefOp m` with
`A'.toOp = Φ A.toOp` and `B'.toOp = Φ B.toOp` satisfy
`fidelity A B ≤ fidelity A' B'`.

The proof dilates `Φ` via Stinespring to `Φ A = Tr_E (V A V†)`, then
applies (i) isometric invariance of fidelity under conjugation by `V` and
(ii) partial-trace monotonicity of fidelity over the environment. -/
theorem fidelity_le_fidelity_cptp_image
    {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m)
    (hCP : IsCompletelyPositive ⇑Φ) (hTP : IsTracePreserving ⇑Φ)
    (A B : PosSemidefOp n) (A' B' : PosSemidefOp m)
    (hA' : A'.toOp = Φ A.toOp) (hB' : B'.toOp = Φ B.toOp) :
    fidelity A B ≤ fidelity A' B' := by
  -- Step 1: Minimal Stinespring dilation of Φ.
  obtain ⟨envDim, henv, hme, dil, _⟩ := minimal_stinespring_exists Φ hCP hTP
  haveI : NeZero envDim := henv
  haveI : NeZero (m * envDim) := hme
  have hVV : dil.isometry.conjTranspose * dil.isometry = 1 := dil.isometry_adj_mul
  have hrec : ∀ X : Op n,
      Φ X = partialTraceB (dil.isometry * X * dil.isometry.conjTranspose) :=
    dil.recovers
  -- Step 2: Lift A and B to PSD operators on the dilated space via V · _ · V†.
  have hA_dil_psd :
      (dil.isometry * A.toOp * dil.isometry.conjTranspose).PosSemidef :=
    (posSemidefOp_implies_mathlib A).mul_mul_conjTranspose_same dil.isometry
  have hB_dil_psd :
      (dil.isometry * B.toOp * dil.isometry.conjTranspose).PosSemidef :=
    (posSemidefOp_implies_mathlib B).mul_mul_conjTranspose_same dil.isometry
  let A_dil : PosSemidefOp (m * envDim) :=
    { toOp := dil.isometry * A.toOp * dil.isometry.conjTranspose
      isHermitian := hA_dil_psd.isHermitian
      pos_semidef := posSemidef_re_quadraticForm_nonneg hA_dil_psd }
  let B_dil : PosSemidefOp (m * envDim) :=
    { toOp := dil.isometry * B.toOp * dil.isometry.conjTranspose
      isHermitian := hB_dil_psd.isHermitian
      pos_semidef := posSemidef_re_quadraticForm_nonneg hB_dil_psd }
  -- Step 3: Isometric invariance of fidelity.
  have h_iso : fidelity A_dil B_dil = fidelity A B :=
    fidelity_isometry_conj_of_toOp_eq dil.isometry A B A_dil B_dil hVV rfl rfl
  -- Step 4: Partial-trace DPI of fidelity on the environment.
  have h_pt :
      fidelity A_dil B_dil ≤
        fidelity A_dil.partialTraceB B_dil.partialTraceB :=
    fidelity_le_fidelity_partialTraceB A_dil B_dil
  -- Step 5: Stinespring recovery identifies the partial trace with Φ(_).
  have hA_recover : A_dil.partialTraceB.toOp = A'.toOp := by
    change partialTraceB (dil.isometry * A.toOp * dil.isometry.conjTranspose) = A'.toOp
    rw [← hrec A.toOp, ← hA']
  have hB_recover : B_dil.partialTraceB.toOp = B'.toOp := by
    change partialTraceB (dil.isometry * B.toOp * dil.isometry.conjTranspose) = B'.toOp
    rw [← hrec B.toOp, ← hB']
  have hA_eq : A_dil.partialTraceB = A' := PosSemidefOp.ext hA_recover
  have hB_eq : B_dil.partialTraceB = B' := PosSemidefOp.ext hB_recover
  -- Step 6: Assemble the inequality.
  calc fidelity A B
      = fidelity A_dil B_dil := h_iso.symm
    _ ≤ fidelity A_dil.partialTraceB B_dil.partialTraceB := h_pt
    _ = fidelity A' B' := by rw [hA_eq, hB_eq]

end Quantum.Metrics

end
