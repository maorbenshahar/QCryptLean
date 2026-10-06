import QCryptLean.Quantum.Symmetry.BellDickeCore
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.PairedTensorPow
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementDilation

/-!
# Joint Bell de Finetti domination

The embedded pure tensor power is supported on the joint Bell symmetric projector and is
bounded by `C(n+3,3)` times the Bell de Finetti state. Partial tracing gives the corresponding
marginal domination.

Reference: Nahar et al. (2024), arXiv:2403.11851, Lemma 2 and Appendix B.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti InfoTheory.SmoothMinEntropy
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Engine

noncomputable section

namespace Quantum.Symmetry

/-! ## The marginal symmetric-subspace domination of a pure IID power -/

/-- **A pure IID power is fixed by the symmetric projector on the left.**

`P_sym · φ^{⊗n} = φ^{⊗n}` for pure `φ`.  `P_sym = (1/n!)·Σ_σ U_σ` and every `U_σ` fixes a pure IID
power on the left (`permRep_mul_tensorPowGen_of_isPure`), so the average collapses. -/
theorem symmetricProjector_mul_tensorPowGen_of_isPure {D n : ℕ} [NeZero D] [NeZero n]
    [NeZero (D ^ n)] (φ : DensityOp D) (hφ : φ.IsPure) :
    symmetricProjector D n * (φ.tensorPowGen n).toOp = (φ.tensorPowGen n).toOp := by
  simp only [symmetricProjector, symmetricProjectorRep]
  rw [smul_mul_assoc, Finset.sum_mul]
  conv_lhs =>
    arg 2; arg 2; ext σ
    rw [permRep_mul_tensorPowGen_of_isPure φ hφ σ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

/-- **The symmetric projector dominates a pure IID power.**

`P_sym − φ^{⊗n} ⪰ 0`: a trace-one PSD operator supported on a projector is dominated by it
(`projector_sub_psd_of_support`), and `symmetricProjector_mul_tensorPowGen_of_isPure` supplies the
support hypothesis. -/
theorem symmetricProjector_sub_tensorPowGen_posSemidef {D n : ℕ} [NeZero D] [NeZero n]
    [NeZero (D ^ n)] (φ : DensityOp D) (hφ : φ.IsPure) :
    (symmetricProjector D n - (φ.tensorPowGen n).toOp).PosSemidef :=
  projector_sub_psd_of_support (symmetricProjector D n) (φ.tensorPowGen n).toOp
    (symmetricProjector_is_projector D n).1 (symmetricProjector_is_projector D n).2
    (posSemidefOp_implies_mathlib (φ.tensorPowGen n).toPosSemidefOp)
    (by rw [(φ.tensorPowGen n).trace_one, Complex.one_re])
    (symmetricProjector_mul_tensorPowGen_of_isPure φ hφ)

/-- The Löwner form of `symmetricProjector_sub_tensorPowGen_posSemidef`. -/
theorem tensorPowGen_opLe_symmetricProjector_of_isPure {D n : ℕ} [NeZero D] [NeZero n]
    [NeZero (D ^ n)] (φ : DensityOp D) (hφ : φ.IsPure) :
    opLe (φ.tensorPowGen n).toOp (symmetricProjector D n) :=
  opLe_of_posSemidef_sub (symmetricProjector_sub_tensorPowGen_posSemidef φ hφ)

/-! ## (i) The joint Bell de Finetti domination -/

/-- `C(n+3,3) • bb84BellPairedDeFinettiState n` is the interleaved `W`-conjugate of the
    **unnormalized**
symmetric projector on `(ℂ⁴)^{⊗n}` — the scaled form of the CORE identity
`bb84BellPairedDeFinettiState_eq_Wconj_symProj`. -/
theorem bb84PolyDimTight_smul_bellPairedDeFinettiState_eq_Wconj_symProj (n : ℕ) [NeZero n] :
    ((bb84PolyDimTight n : ℂ)) • (bb84BellPairedDeFinettiState n).toOp =
      Matrix.reindex (interleavingEquiv 4 n).symm (interleavingEquiv 4 n).symm
        (bellDoublingIsometryPow n * symmetricProjector 4 n * (bellDoublingIsometryPow n)ᴴ) := by
  have hne : (bb84PolyDimTight n : ℂ) ≠ 0 := by
    have : 0 < bb84PolyDimTight n := bb84PolyDimTight_pos n
    exact_mod_cast this.ne'
  have hcore : (bb84BellPairedDeFinettiState n).toOp =
      Matrix.reindex (interleavingEquiv 4 n).symm (interleavingEquiv 4 n).symm
        (bellDoublingIsometryPow n *
          ((bb84PolyDimTight n : ℂ)⁻¹ • symmetricProjector 4 n) *
          (bellDoublingIsometryPow n)ᴴ) :=
    bb84BellPairedDeFinettiState_eq_Wconj_symProj n
  rw [hcore, Matrix.mul_smul, Matrix.smul_mul, Matrix.reindex_smul, smul_smul,
    mul_inv_cancel₀ hne, one_smul]

/-- **(i) The JOINT Bell de Finetti domination at the tight constant `C(n+3,3)`.**

For every **pure** single-pair state `φ` on `ℂ⁴`, the interleaved `n`-fold paired power of the
Bell-doubled state `bellWembed φ = W·φ·Wᴴ` is Löwner-dominated by `bb84PolyDimTight n = C(n+3,3)`
times the Bell joint de Finetti mixture:

`(bellWembed φ)^{⊗n}(interleaved)  ⪯  C(n+3,3) · bb84BellPairedDeFinettiState n`.

This is the Bell counterpart of `pairedDeFinettiState_opGe_inv_choose_smul_pairedTensorPow`, in the
same statement shape (interleaved paired power on the left, a scalar multiple of a fixed
source-independent paired reference on the right), so it drops into the same slot of the labelled
announce machinery; the constant drops from `bb84PolyDim n = C(n+15,15)` to `C(n+3,3)` because the
Bell-doubled source never leaves the `W^{⊗n}`-image.

The proof is the marginal domination `φ^{⊗n} ⪯ symmetricProjector 4 n`
(`tensorPowGen_opLe_symmetricProjector_of_isPure`) pushed through the rectangular congruence by
`W^{⊗n} = bellDoublingIsometryPow n` (`opLe_kraus_sandwich`) and the interleaving reindex
(`opLe_reindex_rect`), with the two sides identified by `bellWembed_tensorPow_eq_Wconj` and
`bb84BellPairedDeFinettiState_eq_Wconj_symProj`.

Purity supplies symmetric-subspace support of the tensor power. -/
theorem bb84_bellWembedPairedTensorPow_opLe_polyDimTight_smul_bellPairedDeFinettiState
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)] (φ : DensityOp 4) (hφ : φ.IsPure) :
    opLe (densityOp_reindex (interleavingEquiv 4 n).symm
        ((bellWembed φ).tensorPowGen n)).toOp
      ((bb84PolyDimTight n : ℂ) • (bb84BellPairedDeFinettiState n).toOp) := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  -- The marginal symmetric-subspace domination on `(ℂ⁴)^{⊗n}`, conjugated by `W^{⊗n}`.
  have hsand := opLe_kraus_sandwich (bellDoublingIsometryPow n)
    (tensorPowGen_opLe_symmetricProjector_of_isPure (D := 4) (n := n) φ hφ)
  -- Transport to the concatenated `A^n ⊗ E^n` register.
  have hre := opLe_reindex_rect (interleavingEquiv 4 n).symm hsand
  rw [← bellWembed_tensorPow_eq_Wconj φ,
    ← bb84PolyDimTight_smul_bellPairedDeFinettiState_eq_Wconj_symProj n] at hre
  exact hre

end Quantum.Symmetry

end -- noncomputable section
