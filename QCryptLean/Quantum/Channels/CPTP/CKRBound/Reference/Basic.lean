import QCryptLean.Quantum.Channels.CPTP.CKRBound.HermitianContractivity
import QCryptLean.Quantum.Channels.CPTP.CKRBound.MapTensorIdAdjoint
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction
import QCryptLean.Quantum.Operators.PSDTraceBound
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import QCryptLean.Quantum.Metrics.TraceNormIntegral
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Math.Combinatorics.PermutationAction
import QCryptLean.InfoTheory.DeFinetti.Purification

/-!
# CKR Reference Basics — tensor trace norms and ordinary symmetric-projector bounds

Generic trace-norm wrappers and ordinary de Finetti reference-state infrastructure
for the Christandl-Konig-Renner postselection argument.

## Main definitions
- `ckrTensorTraceNorm`: generic CKR trace-norm wrapper `‖(Δ ⊗ id_R)(τ)‖₁`
- `IsDeFinettiPurification`: pure state whose `H^n` marginal is `deFinettiState d n`
- `HasDeFinettiTraceNormBound`: ordinary de Finetti purification plus a CKR bound

## Main statements
- `ckrTensorTraceNorm_nonneg`: nonnegativity of the CKR tensor trace norm
- `ckrTensorTraceNorm_add_le`: triangle inequality for `ckrTensorTraceNorm`
- `partial_trace_symmetric_bound`: ordinary de Finetti marginal domination
- `ckr_psd_bound`: `d = 4` CKR PSD bound against an ordinary de Finetti purification
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The generic CKR trace-norm wrapper `‖(Δ ⊗ id_R)(τ)‖₁`. -/
noncomputable def ckrTensorTraceNorm {d n dimOut dimR : ℕ} [NeZero d] [NeZero n]
    [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR)) : ℝ :=
  Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ τ.toOp)

/-- CKR tensor trace norm contracts under CPTP postprocessing of the channel output. -/
lemma ckrTensorTraceNorm_postcomp_cptp_le
    {d n dimOut dimOut' dimR : ℕ} [NeZero d] [NeZero n]
    [NeZero dimOut] [NeZero dimOut'] [NeZero dimR]
    (K : Op dimOut →ₗ[ℂ] Op dimOut') (hK : IsCPTP (⇑K))
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR)) :
    ckrTensorTraceNorm (K.comp Δ) τ ≤ ckrTensorTraceNorm Δ τ := by
  unfold ckrTensorTraceNorm
  rw [← mapTensorId_comp Δ K τ.toOp]
  exact traceNorm_mapTensorId_cptp_contractive K hK (mapTensorId Δ τ.toOp)

/-- Equality after a CPTP postprocess gives the corresponding CKR tensor trace-norm bound. -/
lemma ckrTensorTraceNorm_postcomp_eq_le
    {d n dimOut dimOut' dimR : ℕ} [NeZero d] [NeZero n]
    [NeZero dimOut] [NeZero dimOut'] [NeZero dimR]
    (K : Op dimOut →ₗ[ℂ] Op dimOut') (hK : IsCPTP (⇑K))
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (Δ' : Op (d ^ n) →ₗ[ℂ] Op dimOut')
    (τ : DensityOp ((d ^ n) * dimR))
    (hcomp : K.comp Δ = Δ') :
    ckrTensorTraceNorm Δ' τ ≤ ckrTensorTraceNorm Δ τ := by
  rw [← hcomp]
  exact ckrTensorTraceNorm_postcomp_cptp_le K hK Δ τ

/-- A CKR tensor trace norm is bounded by twice a generalized trace distance
whenever the tensor-extended output is a CPTP postprocessing of the corresponding
operator difference. -/
lemma ckrTensorTraceNorm_le_two_traceDistanceGen_of_cptp_postprocess_eq
    {d n dimOut dimR inDim : ℕ} [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    [NeZero inDim]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR))
    (Φ : Op inDim → Op (dimOut * dimR)) (hΦ : IsCPTP Φ)
    (ρ σ : Op inDim)
    (hout : mapTensorId Δ τ.toOp = Φ (ρ - σ)) :
    ckrTensorTraceNorm Δ τ ≤ 2 * Quantum.Metrics.traceDistanceGen ρ σ := by
  unfold ckrTensorTraceNorm
  exact Quantum.Metrics.traceNorm_le_two_traceDistanceGen_of_cptp_postprocess_eq
    Φ hΦ ρ σ (mapTensorId Δ τ.toOp) hout

/-- Existential form of
`ckrTensorTraceNorm_le_two_traceDistanceGen_of_cptp_postprocess_eq`. -/
lemma ckrTensorTraceNorm_le_two_traceDistanceGen_of_exists_cptp_postprocess
    {d n dimOut dimR inDim : ℕ} [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    [NeZero inDim]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR))
    (ρ σ : Op inDim)
    (hpost :
      ∃ Φ : Op inDim →ₗ[ℂ] Op (dimOut * dimR),
        IsCPTP (⇑Φ) ∧ mapTensorId Δ τ.toOp = Φ (ρ - σ)) :
    ckrTensorTraceNorm Δ τ ≤ 2 * Quantum.Metrics.traceDistanceGen ρ σ := by
  rcases hpost with ⟨Φ, hΦ, hout⟩
  exact ckrTensorTraceNorm_le_two_traceDistanceGen_of_cptp_postprocess_eq
    Δ τ Φ hΦ ρ σ hout

/-- The generic CKR trace norm is nonnegative. -/
lemma ckrTensorTraceNorm_nonneg
    {d n dimOut dimR : ℕ} [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR)) :
    0 ≤ ckrTensorTraceNorm Δ τ := by
  unfold ckrTensorTraceNorm Quantum.Metrics.traceNorm
  positivity

/-- Triangle inequality for the CKR tensor trace norm. -/
lemma ckrTensorTraceNorm_add_le
    {d n dimOut dimR : ℕ} [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ₁ Δ₂ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR)) :
    ckrTensorTraceNorm (Δ₁ + Δ₂) τ ≤
      ckrTensorTraceNorm Δ₁ τ + ckrTensorTraceNorm Δ₂ τ := by
  unfold ckrTensorTraceNorm
  have h_add : mapTensorId (Δ₁ + Δ₂) τ.toOp =
      mapTensorId Δ₁ τ.toOp + mapTensorId Δ₂ τ.toOp := by
    ext p q
    simp only [mapTensorId, Matrix.of_apply, Matrix.add_apply, LinearMap.add_apply,
               add_mul, Finset.sum_add_distrib]
  rw [h_add]
  exact traceNorm_add_le _ _

/-- The CKR tensor trace norm of the zero map is zero. -/
lemma ckr_tensor_trace_norm_zero
    {d n dimOut dimR : ℕ} [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    (τ : DensityOp ((d ^ n) * dimR)) :
    ckrTensorTraceNorm (0 : Op (d ^ n) →ₗ[ℂ] Op dimOut) τ = 0 := by
  unfold ckrTensorTraceNorm
  rw [mapTensorId_zero_map, traceNorm_zero]

/-- A state τ on `H^⊗n ⊗ R` is an ordinary de Finetti purification if:
    1. τ is a pure state on the joint system `H^⊗n ⊗ R`
    2. Tracing out `R` gives the Haar-pure de Finetti state `deFinettiState d n`.

    This is the ordinary reference-state hypothesis that appears in the
    single-copy symmetric-support version of the CKR argument. -/
structure IsDeFinettiPurification (d : ℕ) [NeZero d] {n dimR : ℕ} [NeZero n] [NeZero dimR]
    (τ : DensityOp ((d ^ n) * dimR)) : Prop where
  /-- τ is pure on the joint system. -/
  isPure : τ.IsPure
  /-- The `H^⊗n` marginal is the Haar-pure de Finetti state. -/
  isDeFinetti : τ.partialTraceB = deFinettiState d n

/-- A CKR-style trace-norm bound for a chosen ordinary de Finetti purification τ. -/
def HasDeFinettiTraceNormBound (d : ℕ) [NeZero d] {n dimOut dimR : ℕ}
    [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR))
    (ε_coll : ℝ) : Prop :=
  IsDeFinettiPurification d τ ∧ ckrTensorTraceNorm Δ τ ≤ ε_coll

/-- Package a chosen ordinary de Finetti purification together with its CKR bound. -/
theorem HasDeFinettiTraceNormBound.of_bound (d : ℕ) [NeZero d]
    {n dimOut dimR : ℕ} [NeZero n] [NeZero dimOut] [NeZero dimR]
    {Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut} {τ : DensityOp ((d ^ n) * dimR)}
    {ε_coll : ℝ}
    (hτ : IsDeFinettiPurification d τ)
    (hbound : ckrTensorTraceNorm Δ τ ≤ ε_coll) :
    HasDeFinettiTraceNormBound d Δ τ ε_coll := by
  exact ⟨hτ, hbound⟩

/-- Accessor for the trace-norm component of an explicit Haar-state bound.

    The equality
    `InfoTheory.DeFinetti.deFinettiState d n = integralTensorPower n (deFinetti_haarMeasure d)`
    identifies only the `H^⊗n` marginal. It does not by itself produce a
    trace-norm bound for an arbitrary pure purification, so this theorem merely
    unpacks an already established `HasDeFinettiTraceNormBound` hypothesis. -/
theorem ckrTensorTraceNorm_le_haar_integral
    {d n dimR dimOut : ℕ} [NeZero d] [NeZero n] [NeZero dimR] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR))
    (ε_coll : ℝ)
    (hbound : HasDeFinettiTraceNormBound d Δ τ ε_coll) :
    ckrTensorTraceNorm Δ τ ≤ ε_coll :=
  hbound.2

/-- For Hermitian operators, left support by a projector implies the
corresponding right-support identity. -/
lemma right_support_of_left_support_of_isHermitian {d : ℕ} [NeZero d]
    {P A : Op d}
    (hP_herm : P.IsHermitian) (hA_herm : A.IsHermitian)
    (h_support : P * A = A) :
    A * P = A := by
  calc A * P = (A * P)ᴴᴴ := by rw [conjTranspose_conjTranspose]
    _ = (Pᴴ * Aᴴ)ᴴ := by rw [conjTranspose_mul]
    _ = (P * A)ᴴ := by rw [hP_herm, hA_herm]
    _ = Aᴴ := by rw [h_support]
    _ = A := hA_herm

/-- A PSD operator of trace at most one and supported on a projector is dominated
by that projector. -/
lemma projector_sub_psd_of_support {d : ℕ} [NeZero d]
    (P A : Op d)
    (hP_idem : P * P = P) (hP_herm : P.IsHermitian)
    (hA_psd : A.PosSemidef) (hA_tr : A.trace.re ≤ 1)
    (h_support : P * A = A) :
    (P - A).PosSemidef := by
  have hAP : A * P = A :=
    right_support_of_left_support_of_isHermitian hP_herm hA_psd.isHermitian h_support
  have h1A := Quantum.Operators.psd_le_one_of_trace_le_one A hA_psd hA_tr
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hP_herm.sub hA_psd.isHermitian, fun x => ?_⟩
  set w := P.mulVec x with hw_def
  have h_adj : ∀ u v, star u ⬝ᵥ P.mulVec v = star (P.mulVec u) ⬝ᵥ v := by
    intro u v
    rw [dotProduct_mulVec, Matrix.star_mulVec, hP_herm]
  have hxPx : star x ⬝ᵥ P.mulVec x = star w ⬝ᵥ w := by
    conv_lhs => rw [show P.mulVec x = P.mulVec w from by
      rw [hw_def]
      conv_lhs => rw [← hP_idem]
      rw [← Matrix.mulVec_mulVec]]
    exact h_adj x w
  have hxAx : star x ⬝ᵥ A.mulVec x = star w ⬝ᵥ A.mulVec w := by
    calc star x ⬝ᵥ A.mulVec x
        = star x ⬝ᵥ A.mulVec w := by
            congr 1
            rw [hw_def]
            conv_lhs => rw [← hAP]
            rw [← Matrix.mulVec_mulVec]
      _ = star x ⬝ᵥ P.mulVec (A.mulVec w) := by
            congr 1
            conv_lhs => rw [← h_support]
            rw [← Matrix.mulVec_mulVec]
      _ = star w ⬝ᵥ A.mulVec w := by
            rw [h_adj, hw_def]
  rw [Matrix.sub_mulVec, dotProduct_sub, hxPx, hxAx]
  have h1A_dot := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h1A).2 w
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at h1A_dot

/-- Binomial coefficient monotonicity: `C(n+3, 3) ≤ C(n+15, 15)`. -/
lemma choose_three_le_choose_fifteen (n : ℕ) :
    Nat.choose (n + 3) 3 ≤ Nat.choose (n + 15) 15 := by
  rw [show n + 3 = 3 + n from by omega, Nat.choose_symm_add,
      show n + 15 = 15 + n from by omega, Nat.choose_symm_add]
  exact Nat.choose_le_choose n (by omega)

/-- The excess scalar `C(n+3,3) / tr(P) - 1` times the symmetric projector is PSD. -/
private lemma symmetricProjector_choose_smul_psd (n : ℕ) [NeZero n] :
    ((↑(Nat.choose (n + 3) 3) * (1 / Matrix.trace (symmetricProjector 4 n)) - 1) •
      symmetricProjector 4 n).PosSemidef := by
  set P := symmetricProjector 4 n with hP_def
  set trP := Matrix.trace P with htrP_def
  have ⟨hP_idem, hP_herm⟩ := symmetricProjector_is_projector 4 n
  have hP_psd : P.PosSemidef := by
    rw [hP_def,
      show symmetricProjector 4 n =
        (symmetricProjector 4 n)ᴴ * symmetricProjector 4 n
        from by rw [hP_herm, hP_idem]]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have htrP_real : trP.im = 0 := by
    have : star trP = trP := by
      rw [htrP_def, ← Matrix.trace_conjTranspose, hP_herm]
    have := congr_arg Complex.im this
    simp [Complex.conj_im] at this
    linarith
  have htrP_re_pos : 0 < trP.re := by
    rw [htrP_def, hP_def, symmetricSubspace_dim]
    exact Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have h_sc : (↑(Nat.choose (n + 3) 3) * (1 / trP) - 1) • P =
      ((↑(Nat.choose (n + 3) 3) / trP.re - 1 : ℝ) : ℂ) • P := by
    congr 1
    rw [show trP = (trP.re : ℂ) from
        Complex.ext (Complex.ofReal_re _).symm (by simp [htrP_real]),
      one_div, ← Complex.ofReal_inv, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    congr 1
  rw [h_sc]
  apply hP_psd.smul
  rw [Complex.zero_le_real, sub_nonneg, le_div_iff₀ htrP_re_pos, one_mul]
  rw [htrP_def, hP_def, symmetricSubspace_dim]
  simp only [show 4 - 1 = 3 from by omega, show n + 4 - 1 = n + 3 from by omega]
  exact le_refl _

/-- The scaled de Finetti marginal dominates the partial trace of any PSD state
    with symmetric support and trace at most one. -/
lemma partial_trace_deFinetti_gap_posSemidef {n dimK dimR : ℕ}
    [NeZero n]
    (ρ : Op (4 ^ n * dimK))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1)
    (τ : DensityOp ((4 ^ n) * dimR))
    (hτ_deFinetti : τ.partialTraceB.toOp =
      (1 / Matrix.trace (symmetricProjector 4 n)) •
        symmetricProjector 4 n)
    (h_support : symmetricProjector 4 n * partialTraceB ρ = partialTraceB ρ) :
    (((↑(Nat.choose (n + 3) 3) : ℂ) • τ.partialTraceB.toOp) -
      partialTraceB ρ).PosSemidef := by
  set A := partialTraceB ρ with hA_def
  set P := symmetricProjector 4 n
  have ⟨hP_idem, hP_herm⟩ := symmetricProjector_is_projector 4 n
  rw [hτ_deFinetti, smul_smul]
  have h_eq : (↑(Nat.choose (n + 3) 3) * (1 / Matrix.trace P)) • P - A =
      ((↑(Nat.choose (n + 3) 3) * (1 / Matrix.trace P) - 1) • P) + (P - A) := by
    rw [sub_smul, one_smul]
    abel
  rw [h_eq]
  exact (symmetricProjector_choose_smul_psd n).add
    (projector_sub_psd_of_support P A hP_idem hP_herm
      (hA_def ▸ partialTraceB_posSemidef_mathlib ρ hρ_psd)
      (by rw [hA_def, trace_partialTraceB]; exact hρ_trace) h_support)

/-- For PSD `ρ` with symmetric support and `Tr(ρ) ≤ 1`, the partial trace is dominated by
    `C(n+3,3)` times the ordinary de Finetti marginal. -/
theorem partial_trace_symmetric_bound {n dimR : ℕ} [NeZero n]
    (ρ : Op (4 ^ n * (4 ^ n)))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1)
    (τ : DensityOp ((4 ^ n) * dimR))
    (hτ_deFinetti : τ.partialTraceB.toOp =
      (1 / Matrix.trace (symmetricProjector 4 n)) •
        symmetricProjector 4 n)
    (h_support : symmetricProjector 4 n * partialTraceB ρ = partialTraceB ρ) :
    (((↑(Nat.choose (n + 3) 3) : ℂ) • τ.partialTraceB.toOp) -
      partialTraceB ρ).PosSemidef := by
  exact partial_trace_deFinetti_gap_posSemidef ρ hρ_psd hρ_trace τ hτ_deFinetti h_support

/-- CKR bound for PSD operators against the ordinary de Finetti marginal. -/
theorem ckr_psd_bound {n dimOut dimR : ℕ}
    [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (_hΔ_conj : ∀ M : Op (4 ^ n), Δ M.conjTranspose = (Δ M).conjTranspose)
    (ρ : Op (4 ^ n * (4 ^ n)))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1)
    (τ : DensityOp ((4 ^ n) * dimR))
    (hτ_pure : τ.IsPure)
    (hτ_deFinetti : τ.partialTraceB.toOp =
      (1 / Matrix.trace (symmetricProjector 4 n)) •
        symmetricProjector 4 n)
    (hρ_support : symmetricProjector 4 n * partialTraceB ρ = partialTraceB ρ) :
    traceNorm (mapTensorId Δ ρ) ≤
      ↑(Nat.choose (n + 3) 3) * traceNorm (mapTensorId Δ τ.toOp) := by
  have h_dom := partial_trace_symmetric_bound ρ hρ_psd hρ_trace τ hτ_deFinetti hρ_support
  have hC_pos : (0 : ℝ) < ↑(Nat.choose (n + 3) 3) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  exact traceNorm_mapTensorId_substate_bound Δ ρ hρ_psd τ hτ_pure
    (Nat.choose (n + 3) 3 : ℝ) hC_pos h_dom

end Quantum.Channels

end
