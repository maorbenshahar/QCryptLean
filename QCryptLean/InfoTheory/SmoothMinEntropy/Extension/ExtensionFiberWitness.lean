import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.UhlmannSubNormalized
import QCryptLean.Quantum.Metrics.SameAncillaPurification
import QCryptLean.Quantum.Metrics.PurificationReshape
import QCryptLean.Quantum.Channels.Stinespring.PartialTrace
import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# External-Flag Purification Witnesses for Sub-Normalized Extension Fibers

This module isolates the witness layer behind the partial-trace fiber
achievability statement for generalized fidelity.  A sub-normalized state is
represented by a live purification branch together with a scalar failure flag
kept outside the physical tensor factors.

## Main definitions
- `generalizedPurificationOverlap`: live-branch overlap plus external flag overlap
- `SubDensityOp.fromKetPartialTrace`: sub-density operator obtained by tracing out
  an explicit auxiliary purifier
- `SubDensityOp.IsExternalFlagPurification`: live branch plus external failure flag

## Main statements
- `SubDensityOp.exists_externalFlagPurification_selfAncilla`
- `SubDensityOp.externalFlagPurification_partialTraceB_regroup`
- `SubDensityOp.exists_externalFlagPurification_fixed_regrouping_overlap`
- `SubDensityOp.externalFlagPurification_extract_extension`
- `SubDensityOp.exists_extension_of_partialTraceB_fidelityGen_ge_of_externalFlagPurification`
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Quantum.Metrics.KitaevWatrousPurification
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Generalized purification overlap with an explicit external failure flag.

The first summand is the live-branch ket overlap; the second summand is the
overlap of the one-dimensional failure flags. -/
def generalizedPurificationOverlap {n : ℕ}
    (ψ φ : Ket n) (η ξ : ℂ) : ℂ :=
  ψ.dag * φ + star η * ξ

/-- Trace out an explicit auxiliary purifier from a live purification branch.

The caller supplies the trace bound for the resulting operator.  The Hermitian
and positive-semidefinite fields are the direct partial-trace images of the
rank-one live branch. -/
def SubDensityOp.fromKetPartialTrace {d anc : ℕ}
    (ψ : Ket (d * anc))
    (htrace_le_one :
      (Quantum.TensorProducts.partialTraceB (ψ * ψ.dag)).trace.re ≤ 1) :
    SubDensityOp d where
  toOp := Quantum.TensorProducts.partialTraceB (ψ * ψ.dag)
  isHermitian :=
    Quantum.TensorProducts.partialTraceB_hermitian (ψ * ψ.dag)
      (ketbra_hermitian ψ)
  pos_semidef :=
    Quantum.TensorProducts.partialTraceB_posSemidef (ketbraPosSemidefOp ψ)
  trace_le_one := htrace_le_one

@[simp]
lemma SubDensityOp.fromKetPartialTrace_toOp {d anc : ℕ}
    (ψ : Ket (d * anc))
    (htrace_le_one :
      (Quantum.TensorProducts.partialTraceB (ψ * ψ.dag)).trace.re ≤ 1) :
    (SubDensityOp.fromKetPartialTrace ψ htrace_le_one).toOp =
      Quantum.TensorProducts.partialTraceB (ψ * ψ.dag) :=
  rfl

/-- A live purification branch of a sub-normalized state, plus an external
one-dimensional failure flag.

The live branch reduces to `ρ` after tracing out the auxiliary purifier, while
the live norm and flag norm together make a normalized generalized
purification. -/
def SubDensityOp.IsExternalFlagPurification {d anc : ℕ}
    (ρ : SubDensityOp d) (ψ : Ket (d * anc)) (η : ℂ) : Prop :=
  Quantum.TensorProducts.partialTraceB (ψ * ψ.dag) = ρ.toOp ∧
  ψ.dag * ψ + star η * η = 1

/-- The canonical same-ancilla live branch of a sub-density operator reduces to
the operator after tracing out the auxiliary copy. -/
lemma SubDensityOp.partialTraceB_sameAncillaPurificationKet
    {d : ℕ} (ρ : SubDensityOp d) :
    Quantum.TensorProducts.partialTraceB
      (sameAncillaPurificationKetOfOp ρ.toOp *
        (sameAncillaPurificationKetOfOp ρ.toOp).dag) = ρ.toOp := by
  have hρ_psd : ρ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  exact partialTraceB_sameAncillaPurificationKetOfOp ρ.toOp hρ_psd

/-- The canonical same-ancilla live branch of a sub-density operator has norm
equal to the operator trace. -/
lemma SubDensityOp.sameAncillaPurificationKet_norm
    {d : ℕ} (ρ : SubDensityOp d) :
    (sameAncillaPurificationKetOfOp ρ.toOp).dag *
        sameAncillaPurificationKetOfOp ρ.toOp = (ρ.trace : ℂ) := by
  have hρ_psd : ρ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  rw [← SubDensityOp.trace_complex_eq ρ]
  exact sameAncillaPurificationKetOfOp_norm ρ.toOp hρ_psd

/-- The square-root trace defect has squared norm equal to the trace defect. -/
lemma SubDensityOp.sqrt_one_sub_trace_flag_norm
    {d : ℕ} (ρ : SubDensityOp d) :
    star ((Real.sqrt (1 - ρ.trace) : ℂ)) *
        (Real.sqrt (1 - ρ.trace) : ℂ) =
      ((1 - ρ.trace : ℝ) : ℂ) := by
  have hnonneg : 0 ≤ 1 - ρ.trace := SubDensityOp.one_sub_trace_nonneg ρ
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hnonneg]

/-- The canonical same-ancilla live branch and square-root defect flag form a
normalized external-flag vector. -/
lemma SubDensityOp.sameAncillaPurificationKet_externalFlag_norm
    {d : ℕ} (ρ : SubDensityOp d) :
    (sameAncillaPurificationKetOfOp ρ.toOp).dag *
          sameAncillaPurificationKetOfOp ρ.toOp +
        star ((Real.sqrt (1 - ρ.trace) : ℂ)) *
          (Real.sqrt (1 - ρ.trace) : ℂ) = 1 := by
  rw [SubDensityOp.sameAncillaPurificationKet_norm,
    SubDensityOp.sqrt_one_sub_trace_flag_norm]
  norm_num

/-- Generalized overlaps are invariant under shifting the associativity cast
from the source live branch to the target live branch. -/
theorem generalizedPurificationOverlap_regroup_ungroup_eq {dE dR anc : ℕ}
    (ψ : Ket ((dE * dR) * anc)) (φ : Ket (dE * (dR * anc)))
    (η ξ : ℂ) :
    generalizedPurificationOverlap
        (regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ)
        φ η ξ =
      generalizedPurificationOverlap ψ
        (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) φ)
        η ξ := by
  unfold generalizedPurificationOverlap
  rw [← regroupJointPurification_overlap_ungroup_eq
    (dE := dE) (dR := dR) (anc := anc) ψ φ]

/-- Generalized overlap real parts are invariant under shifting the
associativity cast from the source branch to the target branch. -/
theorem generalized_purification_overlap_regroup_ungroup_re_eq {dE dR anc : ℕ}
    (ψ : Ket ((dE * dR) * anc)) (φ : Ket (dE * (dR * anc)))
    (η ξ : ℂ) :
    (generalizedPurificationOverlap
        (regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ)
        φ η ξ).re =
      (generalizedPurificationOverlap ψ
        (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) φ)
        η ξ).re := by
  exact congrArg Complex.re
    (generalizedPurificationOverlap_regroup_ungroup_eq
      (dE := dE) (dR := dR) (anc := anc) ψ φ η ξ)

/-- An external-flag purification of an `E` marginal gives the trace bound needed
to package the inverse-reassociated live branch as an `E ⊗ R` sub-density
operator. -/
theorem SubDensityOp.externalFlagPurification_ungroup_trace_le_one
    {dE dR anc : ℕ}
    (ρE : SubDensityOp dE) (ψ : Ket (dE * (dR * anc))) (η : ℂ)
    (hψ : ρE.IsExternalFlagPurification ψ η) :
    (Quantum.TensorProducts.partialTraceB
      ((ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) *
        (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag)).trace.re
      ≤ 1 := by
  calc
    (Quantum.TensorProducts.partialTraceB
      ((ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) *
        (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag)).trace.re
        = (Quantum.TensorProducts.partialTraceB (ψ * ψ.dag)).trace.re :=
          ungroup_joint_purification_partialTraceB_trace_re_eq
            (dE := dE) (dR := dR) (anc := anc) ψ
    _ = ρE.trace := by
          rw [hψ.1]
          rfl
    _ ≤ 1 := ρE.trace_le_one

/-- The sub-density operator built from an inverse-reassociated live branch has
the original `E` marginal. -/
theorem SubDensityOp.fromKetPartialTrace_ungroup_partialTraceB_eq
    {dE dR anc : ℕ}
    (ρE : SubDensityOp dE) (ψ : Ket (dE * (dR * anc))) (η : ℂ)
    (hψ : ρE.IsExternalFlagPurification ψ η)
    (htrace_live :
      (Quantum.TensorProducts.partialTraceB
        ((ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) *
          (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag)).trace.re
        ≤ 1) :
    (SubDensityOp.fromKetPartialTrace
      (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ)
      htrace_live).partialTraceB = ρE := by
  apply SubDensityOp.ext
  dsimp [SubDensityOp.partialTraceB]
  exact (ungroupJointPurification_iterated_partialTraceB_ketbra
    (dE := dE) (dR := dR) (anc := anc) ψ).trans hψ.1

/-- The inverse-reassociated live branch and the same external flag purify the
sub-density operator built from that branch. -/
theorem SubDensityOp.fromKetPartialTrace_ungroup_isExternalFlagPurification
    {dE dR anc : ℕ}
    (ρE : SubDensityOp dE) (ψ : Ket (dE * (dR * anc))) (η : ℂ)
    (hψ : ρE.IsExternalFlagPurification ψ η)
    (htrace_live :
      (Quantum.TensorProducts.partialTraceB
        ((ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) *
          (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ).dag)).trace.re
        ≤ 1) :
    (SubDensityOp.fromKetPartialTrace
      (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ)
      htrace_live).IsExternalFlagPurification
        (ungroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψ) η := by
  constructor
  · rfl
  · have hnorm := ungroupJointPurification_overlap_eq
      (dE := dE) (dR := dR) (anc := anc) ψ ψ
    simpa [hnorm] using hψ.2

/-- A live branch reducing to a sub-density operator has squared norm with real
part equal to the operator trace. -/
theorem SubDensityOp.live_branch_norm_re_eq_trace
    {d anc : ℕ} (ρ : SubDensityOp d) (ψ : Ket (d * anc))
    (hψ : Quantum.TensorProducts.partialTraceB (ψ * ψ.dag) = ρ.toOp) :
    (ψ.dag * ψ).re = ρ.trace := by
  have htrace_eq := congrArg Matrix.trace hψ
  rw [Quantum.TensorProducts.trace_partialTraceB, ketbra_trace_eq_inner,
    SubDensityOp.trace_complex_eq ρ] at htrace_eq
  simpa using congrArg Complex.re htrace_eq

/-- A live branch reducing to a sub-density operator has squared norm equal to
the operator trace as a complex scalar. -/
theorem SubDensityOp.live_branch_norm_eq_trace
    {d anc : ℕ} (ρ : SubDensityOp d) (ψ : Ket (d * anc))
    (hψ : Quantum.TensorProducts.partialTraceB (ψ * ψ.dag) = ρ.toOp) :
    ψ.dag * ψ = (ρ.trace : ℂ) := by
  have htrace_eq := congrArg Matrix.trace hψ
  rw [Quantum.TensorProducts.trace_partialTraceB, ketbra_trace_eq_inner,
    SubDensityOp.trace_complex_eq ρ] at htrace_eq
  simpa using htrace_eq

/-- In an external-flag purification, the scalar flag inner product is the
trace defect of the sub-normalized state. -/
theorem SubDensityOp.external_flag_inner_re_eq_trace_defect
    {d anc : ℕ}
    (ρ : SubDensityOp d) (ψ : Ket (d * anc)) (η : ℂ)
    (hψ : ρ.IsExternalFlagPurification ψ η) :
    (star η * η).re = 1 - ρ.trace := by
  have hψ_trace : (ψ.dag * ψ).re = ρ.trace := by
    exact SubDensityOp.live_branch_norm_re_eq_trace ρ ψ hψ.1
  have hnorm_re :
      (ψ.dag * ψ).re + (star η * η).re = 1 := by
    simpa only [Complex.add_re, Complex.one_re] using congrArg Complex.re hψ.2
  rw [← hψ_trace, eq_sub_iff_add_eq, add_comm]
  exact hnorm_re

/-- In an external-flag purification, the flag norm squared is the missing
trace mass of the sub-normalized state. -/
theorem SubDensityOp.externalFlag_norm_sq_eq_traceDefect
    {d anc : ℕ}
    (ρ : SubDensityOp d) (ψ : Ket (d * anc)) (η : ℂ)
    (hψ : ρ.IsExternalFlagPurification ψ η) :
    ‖η‖ ^ 2 = 1 - ρ.trace := by
  have hflag_re : (star η * η).re = 1 - ρ.trace := by
    exact SubDensityOp.external_flag_inner_re_eq_trace_defect ρ ψ η hψ
  rw [← Complex.normSq_eq_norm_sq, ← hflag_re]
  change Complex.normSq η = ((starRingEnd ℂ) η * η).re
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- A complex norm is the square root of any real number equal to its square. -/
lemma complex_norm_eq_sqrt_of_sq_eq (z : ℂ) {a : ℝ}
    (hz : ‖z‖ ^ 2 = a) :
    ‖z‖ = Real.sqrt a := by
  rw [← hz, Real.sqrt_sq (norm_nonneg z)]

/-- Scalar external flags contribute at most the generalized-fidelity trace
defect term. -/
theorem SubDensityOp.externalFlag_scalarOverlap_re_le_traceDefect
    {d anc : ℕ}
    (ρ σ : SubDensityOp d) (ψ φ : Ket (d * anc)) (η ξ : ℂ)
    (hψ : ρ.IsExternalFlagPurification ψ η)
    (hφ : σ.IsExternalFlagPurification φ ξ) :
    (star η * ξ : ℂ).re ≤ Real.sqrt ((1 - ρ.trace) * (1 - σ.trace)) := by
  have hη_sq : ‖η‖ ^ 2 = 1 - ρ.trace :=
    SubDensityOp.externalFlag_norm_sq_eq_traceDefect ρ ψ η hψ
  have hξ_sq : ‖ξ‖ ^ 2 = 1 - σ.trace :=
    SubDensityOp.externalFlag_norm_sq_eq_traceDefect σ φ ξ hφ
  have hη_norm : ‖η‖ = Real.sqrt (1 - ρ.trace) :=
    complex_norm_eq_sqrt_of_sq_eq η hη_sq
  have hξ_norm : ‖ξ‖ = Real.sqrt (1 - σ.trace) :=
    complex_norm_eq_sqrt_of_sq_eq ξ hξ_sq
  calc
    (star η * ξ : ℂ).re ≤ ‖(star η * ξ : ℂ)‖ :=
      Complex.re_le_norm _
    _ = ‖η‖ * ‖ξ‖ := by rw [norm_mul, norm_star]
    _ = Real.sqrt (1 - ρ.trace) * Real.sqrt (1 - σ.trace) := by
      rw [hη_norm, hξ_norm]
    _ = Real.sqrt ((1 - ρ.trace) * (1 - σ.trace)) :=
      (Real.sqrt_mul (SubDensityOp.one_sub_trace_nonneg ρ) _).symm

/-- External-flag purification overlaps are bounded by generalized fidelity. -/
theorem SubDensityOp.externalFlagPurification_overlap_re_le_fidelityGen
    {d anc : ℕ} [NeZero d] [NeZero anc]
    (ρ σ : SubDensityOp d) (ψ φ : Ket (d * anc)) (η ξ : ℂ)
    (hψ : ρ.IsExternalFlagPurification ψ η)
    (hφ : σ.IsExternalFlagPurification φ ξ) :
    (generalizedPurificationOverlap ψ φ η ξ).re ≤ fidelityGen ρ σ := by
  have hlive :
      (ψ.dag * φ : ℂ).re ≤
        Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp :=
    SubDensityOp.livePurificationOverlap_re_le_fidelity ρ σ ψ φ hψ.1 hφ.1
  have hflag :
      (star η * ξ : ℂ).re ≤
        Real.sqrt ((1 - ρ.trace) * (1 - σ.trace)) :=
    SubDensityOp.externalFlag_scalarOverlap_re_le_traceDefect ρ σ ψ φ η ξ hψ hφ
  simpa only [generalizedPurificationOverlap, fidelityGen, Complex.add_re] using
    add_le_add hlive hflag

/-- Any real lower bound on an external-flag purification overlap is bounded by
generalized fidelity. -/
theorem SubDensityOp.le_fidelity_gen_of_external_flag_purification_overlap
    {d anc : ℕ} [NeZero d] [NeZero anc]
    (ρ σ : SubDensityOp d) (ψ φ : Ket (d * anc)) (η ξ : ℂ)
    (hψ : ρ.IsExternalFlagPurification ψ η)
    (hφ : σ.IsExternalFlagPurification φ ξ)
    {a : ℝ}
    (ha : a ≤ (generalizedPurificationOverlap ψ φ η ξ).re) :
    a ≤ fidelityGen ρ σ :=
  ha.trans
    (SubDensityOp.externalFlagPurification_overlap_re_le_fidelityGen
      ρ σ ψ φ η ξ hψ hφ)

/-- Every sub-normalized operator has a same-system-dimension live purification
branch with an explicit external failure flag. -/
theorem SubDensityOp.exists_externalFlagPurification_selfAncilla
    {d : ℕ} [NeZero d] (ρ : SubDensityOp d) :
    ∃ (ψ : Ket (d * d)) (η : ℂ),
      ρ.IsExternalFlagPurification ψ η := by
  exact ⟨sameAncillaPurificationKetOfOp ρ.toOp,
    (Real.sqrt (1 - ρ.trace) : ℂ),
    SubDensityOp.partialTraceB_sameAncillaPurificationKet ρ,
    SubDensityOp.sameAncillaPurificationKet_externalFlag_norm ρ⟩

/-- Regrouping a joint external-flag purification of `ρER` gives an
external-flag purification of the marginal `ρER.partialTraceB`. -/
theorem SubDensityOp.externalFlagPurification_partialTraceB_regroup
    {dE dR anc : ℕ} [NeZero dE] [NeZero dR] [NeZero anc] [NeZero (dE * dR)]
    (ρER : SubDensityOp (dE * dR))
    (ψER : Ket ((dE * dR) * anc)) (η : ℂ)
    (hψER : ρER.IsExternalFlagPurification ψER η) :
    (ρER.partialTraceB).IsExternalFlagPurification
      (regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψER) η := by
  constructor
  · calc
      Quantum.TensorProducts.partialTraceB
        ((regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψER) *
          (regroupJointPurification (dE := dE) (dR := dR) (anc := anc) ψER).dag)
          =
        Quantum.TensorProducts.partialTraceB
          (Quantum.TensorProducts.partialTraceB (ψER * ψER.dag)) :=
            partialTraceB_regroupJointPurification_ketbra
              (dE := dE) (dR := dR) (anc := anc) ψER
      _ = (ρER.partialTraceB).toOp := by
            rw [hψER.1, SubDensityOp.partialTraceB_toOp]
  · simpa [regroupJointPurification_dag_mul] using hψER.2

/-- The regrouped right carrier `R ⊗ (E ⊗ R)` is large enough to host a
fixed-source purification of an `E`-system state. -/
lemma SubDensityOp.regrouping_rightAncilla_dim_ge_left
    {dE dR : ℕ} [NeZero dR] :
    dE ≤ dR * (dE * dR) := by
  have hdR_pos : 0 < dR := Nat.pos_of_ne_zero (NeZero.ne dR)
  calc
    dE ≤ dE * dR := Nat.le_mul_of_pos_right dE hdR_pos
    _ ≤ dR * (dE * dR) := Nat.le_mul_of_pos_left (dE * dR) hdR_pos

/-- Multiplying real amplitudes by the same unit complex phase preserves their
scalar overlap. -/
lemma complex_unit_phase_ofReal_overlap
    (u : ℂ) (hu : ‖u‖ = 1) (r s : ℝ) :
    star (u * (r : ℂ)) * (u * (s : ℂ)) = (r : ℂ) * (s : ℂ) := by
  have hr : star (r : ℂ) = (r : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  calc
    star (u * (r : ℂ)) * (u * (s : ℂ)) =
        (star u * (r : ℂ)) * (u * (s : ℂ)) := by
          rw [star_mul', hr]
    _ = ((r : ℂ) * (star u * u)) * (s : ℂ) := by
          rw [mul_comm (star u) (r : ℂ), ← mul_assoc,
            mul_assoc (r : ℂ) (star u) u]
    _ = (r : ℂ) * (s : ℂ) := by
          rw [Quantum.Operators.star_mul_self_eq_one_of_norm_eq_one u hu]
          simp

/-- A unit complex phase times a nonnegative square root has squared norm equal
to the original nonnegative real. -/
lemma complex_unit_phase_sqrt_norm_sq
    (u : ℂ) {b : ℝ} (hu : ‖u‖ = 1) (hb : 0 ≤ b) :
    star (u * (Real.sqrt b : ℂ)) * (u * (Real.sqrt b : ℂ)) = (b : ℂ) := by
  calc
    star (u * (Real.sqrt b : ℂ)) * (u * (Real.sqrt b : ℂ)) =
        (Real.sqrt b : ℂ) * (Real.sqrt b : ℂ) := by
          exact complex_unit_phase_ofReal_overlap u hu (Real.sqrt b) (Real.sqrt b)
    _ = (b : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt hb]

/-- A target scalar flag can be phase-aligned with a fixed source scalar while
having any prescribed nonnegative squared norm. -/
lemma exists_complex_flag_phase_align
    (η : ℂ) {a b : ℝ}
    (hη : ‖η‖ ^ 2 = a) (hb : 0 ≤ b) :
    ∃ ξ : ℂ,
      star ξ * ξ = (b : ℂ) ∧
      (star η * ξ : ℂ).re = Real.sqrt (a * b) := by
  obtain ⟨u, hu_norm, huη⟩ := Complex.exists_norm_mul_eq_self η
  refine ⟨u * (Real.sqrt b : ℂ), ?_, ?_⟩
  · exact complex_unit_phase_sqrt_norm_sq u hu_norm hb
  · have ha_nonneg : 0 ≤ a := by
      rw [← hη]
      exact sq_nonneg ‖η‖
    have hnorm_eq : ‖η‖ = Real.sqrt a :=
      complex_norm_eq_sqrt_of_sq_eq η hη
    calc
      (star η * (u * (Real.sqrt b : ℂ)) : ℂ).re =
          (star (u * (‖η‖ : ℂ)) *
              (u * (Real.sqrt b : ℂ)) : ℂ).re := by
            rw [huη]
      _ = ((‖η‖ : ℂ) * (Real.sqrt b : ℂ) : ℂ).re := by
            rw [complex_unit_phase_ofReal_overlap u hu_norm ‖η‖ (Real.sqrt b)]
      _ = ‖η‖ * Real.sqrt b := by simp
      _ = Real.sqrt a * Real.sqrt b := by rw [hnorm_eq]
      _ = Real.sqrt (a * b) := (Real.sqrt_mul ha_nonneg b).symm

/-- External failure flags can be phase-aligned once the target live branch is
fixed.

The target flag completes `φ` to an external-flag purification of `σ`, and its
scalar overlap with the fixed source flag realizes the generalized-fidelity
trace-defect term. -/
theorem SubDensityOp.exists_externalFlag_scalarOverlap_re_eq_traceDefect
    {d anc : ℕ}
    (ρ σ : SubDensityOp d) (ψ φ : Ket (d * anc)) (η : ℂ)
    (hψ : ρ.IsExternalFlagPurification ψ η)
    (hφ : Quantum.TensorProducts.partialTraceB (φ * φ.dag) = σ.toOp) :
    ∃ ξ : ℂ,
      σ.IsExternalFlagPurification φ ξ ∧
      (star η * ξ : ℂ).re =
        Real.sqrt ((1 - ρ.trace) * (1 - σ.trace)) := by
  have hη_sq : ‖η‖ ^ 2 = 1 - ρ.trace :=
    SubDensityOp.externalFlag_norm_sq_eq_traceDefect ρ ψ η hψ
  obtain ⟨ξ, hξ_norm, hξ_overlap⟩ :=
    exists_complex_flag_phase_align η hη_sq (SubDensityOp.one_sub_trace_nonneg σ)
  refine ⟨ξ, ⟨hφ, ?_⟩, hξ_overlap⟩
  have hφ_norm : φ.dag * φ = (σ.trace : ℂ) :=
    SubDensityOp.live_branch_norm_eq_trace σ φ hφ
  rw [hφ_norm, hξ_norm]
  norm_num

/-- Fixed-source external-flag Uhlmann achievability for sub-density
operators.

This combines live fixed-source achievability with scalar external-flag phase
alignment on the same right carrier. -/
theorem SubDensityOp.exists_externalFlagPurification_fixed_source_overlap
    {d anc : ℕ} [NeZero d] [NeZero anc]
    (ρ σ : SubDensityOp d) (ψ : Ket (d * anc)) (η : ℂ)
    (hψ : ρ.IsExternalFlagPurification ψ η)
    (hdim : d ≤ anc) :
    ∃ (φ : Ket (d * anc)) (ξ : ℂ),
      σ.IsExternalFlagPurification φ ξ ∧
      (generalizedPurificationOverlap ψ φ η ξ).re =
        fidelityGen ρ σ := by
  obtain ⟨φ, hφ_live, hlive⟩ :=
    SubDensityOp.exists_livePurification_overlap_eq_fidelity_fixed_source
      ρ σ ψ hψ.1 hdim
  obtain ⟨ξ, hξ, hflag⟩ :=
    SubDensityOp.exists_externalFlag_scalarOverlap_re_eq_traceDefect
      ρ σ ψ φ η hψ hφ_live
  refine ⟨φ, ξ, hξ, ?_⟩
  calc
    (generalizedPurificationOverlap ψ φ η ξ).re =
        (ψ.dag * φ : ℂ).re + (star η * ξ : ℂ).re := by
          simp only [generalizedPurificationOverlap, Complex.add_re]
    _ =
        Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp +
          Real.sqrt ((1 - ρ.trace) * (1 - σ.trace)) := by
          rw [hlive, hflag]
    _ = fidelityGen ρ σ := rfl

/-- Fixed-source generalized Uhlmann witness for an `E` marginal obtained by
regrouping a live purification of `ρER`.

The source purification is fixed.  The theorem chooses a compatible live branch
and failure flag for `ρEtilde` on the same right/purifier space, and its
generalized overlap realizes the marginal generalized fidelity. -/
theorem SubDensityOp.exists_externalFlagPurification_fixed_regrouping_overlap
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρER : SubDensityOp (dE * dR))
    (ρEtilde : SubDensityOp dE)
    (ψER : Ket ((dE * dR) * (dE * dR))) (η : ℂ)
    (hψE :
      (ρER.partialTraceB).IsExternalFlagPurification
        (regroupJointPurification
          (dE := dE) (dR := dR) (anc := dE * dR) ψER) η) :
    ∃ (ψEtilde : Ket (dE * (dR * (dE * dR)))) (ηtilde : ℂ),
      ρEtilde.IsExternalFlagPurification ψEtilde ηtilde ∧
      (generalizedPurificationOverlap
          (regroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψER)
          ψEtilde η ηtilde).re =
        fidelityGen ρER.partialTraceB ρEtilde := by
  have : NeZero (dR * (dE * dR)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dR) (NeZero.ne (dE * dR))⟩
  exact
    SubDensityOp.exists_externalFlagPurification_fixed_source_overlap
      (ρ := ρER.partialTraceB) (σ := ρEtilde)
      (ψ := regroupJointPurification
        (dE := dE) (dR := dR) (anc := dE * dR) ψER)
      (η := η) hψE
      (SubDensityOp.regrouping_rightAncilla_dim_ge_left
        (dE := dE) (dR := dR))

/-- A regrouped external-flag overlap lower bound transfers to the joint
extension built from the inverse-reassociated target branch. -/
theorem SubDensityOp.fidelityGen_le_ungroup_extension_of_regrouped_overlap
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρER : SubDensityOp (dE * dR))
    (ρEtilde : SubDensityOp dE)
    (ψER : Ket ((dE * dR) * (dE * dR))) (η : ℂ)
    (ψEtilde : Ket (dE * (dR * (dE * dR)))) (ηtilde : ℂ)
    (hψER : ρER.IsExternalFlagPurification ψER η)
    (hψEtilde : ρEtilde.IsExternalFlagPurification ψEtilde ηtilde)
    (htrace_live :
      (Quantum.TensorProducts.partialTraceB
        ((ungroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψEtilde) *
          (ungroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψEtilde).dag)).trace.re ≤ 1)
    (hachieve :
      fidelityGen ρER.partialTraceB ρEtilde ≤
        (generalizedPurificationOverlap
          (regroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψER)
          ψEtilde η ηtilde).re) :
    fidelityGen ρER.partialTraceB ρEtilde ≤
      fidelityGen ρER
        (SubDensityOp.fromKetPartialTrace
          (ungroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψEtilde)
          htrace_live) := by
  let ψERtilde :=
    ungroupJointPurification
      (dE := dE) (dR := dR) (anc := dE * dR) ψEtilde
  let ρERtilde := SubDensityOp.fromKetPartialTrace ψERtilde htrace_live
  have hρERtilde_pur :
      ρERtilde.IsExternalFlagPurification ψERtilde ηtilde := by
    simpa [ψERtilde, ρERtilde] using
      SubDensityOp.fromKetPartialTrace_ungroup_isExternalFlagPurification
        (dE := dE) (dR := dR) (anc := dE * dR)
        ρEtilde ψEtilde ηtilde hψEtilde htrace_live
  refine
    SubDensityOp.le_fidelity_gen_of_external_flag_purification_overlap
      (d := dE * dR) (anc := dE * dR)
      ρER ρERtilde ψER ψERtilde η ηtilde hψER hρERtilde_pur ?_
  simpa [ψERtilde,
    generalized_purification_overlap_regroup_ungroup_re_eq
      (dE := dE) (dR := dR) (anc := dE * dR) ψER ψEtilde η ηtilde] using hachieve

/-- Extract an `E ⊗ R` extension from a compatible external-flag purification.

The target live branch is reassociated back to `(E ⊗ R) ⊗ A`; tracing out only
`A` gives the extension.  The generalized purification overlap then gives the
joint generalized-fidelity lower bound. -/
theorem SubDensityOp.externalFlagPurification_extract_extension
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρER : SubDensityOp (dE * dR))
    (ρEtilde : SubDensityOp dE)
    (ψER : Ket ((dE * dR) * (dE * dR))) (η : ℂ)
    (ψEtilde : Ket (dE * (dR * (dE * dR)))) (ηtilde : ℂ)
    (hψER : ρER.IsExternalFlagPurification ψER η)
    (hψEtilde : ρEtilde.IsExternalFlagPurification ψEtilde ηtilde)
    (hachieve :
      fidelityGen ρER.partialTraceB ρEtilde ≤
        (generalizedPurificationOverlap
          (regroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψER)
          ψEtilde η ηtilde).re) :
    ∃ htrace_live :
      (Quantum.TensorProducts.partialTraceB
        ((ungroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψEtilde) *
          (ungroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψEtilde).dag)).trace.re ≤ 1,
      let ρERtilde : SubDensityOp (dE * dR) :=
        SubDensityOp.fromKetPartialTrace
          (ungroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψEtilde)
          htrace_live
      ρERtilde.partialTraceB = ρEtilde ∧
      fidelityGen ρER.partialTraceB ρEtilde ≤
        fidelityGen ρER ρERtilde := by
  let htrace_live :=
    SubDensityOp.externalFlagPurification_ungroup_trace_le_one
      (dE := dE) (dR := dR) (anc := dE * dR)
      ρEtilde ψEtilde ηtilde hψEtilde
  refine ⟨htrace_live, ?_⟩
  dsimp
  constructor
  · exact SubDensityOp.fromKetPartialTrace_ungroup_partialTraceB_eq
      (dE := dE) (dR := dR) (anc := dE * dR)
      ρEtilde ψEtilde ηtilde hψEtilde htrace_live
  · exact SubDensityOp.fidelityGen_le_ungroup_extension_of_regrouped_overlap
      ρER ρEtilde ψER η ψEtilde ηtilde
      hψER hψEtilde htrace_live hachieve

/-- A joint external-flag purification gives a marginal generalized Uhlmann
witness with the same regrouped live source branch. -/
theorem SubDensityOp.exists_externalFlagPurification_marginal_overlap_of_joint
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρER : SubDensityOp (dE * dR))
    (ρEtilde : SubDensityOp dE)
    (ψER : Ket ((dE * dR) * (dE * dR))) (η : ℂ)
    (hψER : ρER.IsExternalFlagPurification ψER η) :
    ∃ (ψEtilde : Ket (dE * (dR * (dE * dR)))) (ηtilde : ℂ),
      ρEtilde.IsExternalFlagPurification ψEtilde ηtilde ∧
      fidelityGen ρER.partialTraceB ρEtilde ≤
        (generalizedPurificationOverlap
          (regroupJointPurification
            (dE := dE) (dR := dR) (anc := dE * dR) ψER)
          ψEtilde η ηtilde).re := by
  obtain ⟨ψEtilde, ηtilde, hψEtilde, hoverlap⟩ :=
    SubDensityOp.exists_externalFlagPurification_fixed_regrouping_overlap
      ρER ρEtilde ψER η
      (SubDensityOp.externalFlagPurification_partialTraceB_regroup
        ρER ψER η hψER)
  refine ⟨ψEtilde, ηtilde, hψEtilde, ?_⟩
  rw [hoverlap]

/-- Reduction from a chosen external-flag purification of `ρER` to the
partial-trace fiber achievability statement. -/
theorem SubDensityOp.exists_extension_of_partialTraceB_fidelityGen_ge_of_externalFlagPurification
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρER : SubDensityOp (dE * dR))
    (ρEtilde : SubDensityOp dE)
    (ψER : Ket ((dE * dR) * (dE * dR))) (η : ℂ)
    (hψER : ρER.IsExternalFlagPurification ψER η) :
    ∃ ρERtilde : SubDensityOp (dE * dR),
      ρERtilde.partialTraceB = ρEtilde ∧
      fidelityGen ρER.partialTraceB ρEtilde ≤
        fidelityGen ρER ρERtilde := by
  obtain ⟨ψEtilde, ηtilde, hψEtilde, hachieve⟩ :=
    SubDensityOp.exists_externalFlagPurification_marginal_overlap_of_joint
      ρER ρEtilde ψER η hψER
  obtain ⟨htrace_live, hpartial, hfid⟩ :=
    SubDensityOp.externalFlagPurification_extract_extension
      ρER ρEtilde ψER η ψEtilde ηtilde hψER hψEtilde hachieve
  exact ⟨SubDensityOp.fromKetPartialTrace
      (ungroupJointPurification
        (dE := dE) (dR := dR) (anc := dE * dR) ψEtilde)
      htrace_live,
    hpartial, hfid⟩

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
