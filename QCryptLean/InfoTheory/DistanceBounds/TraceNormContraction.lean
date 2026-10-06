import QCryptLean.Quantum.Metrics.TraceNorm.Jordan
import QCryptLean.InfoTheory.DistanceBounds.Basic
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Trace Norm Contraction under Partial Trace — Jordan decomposition, PSD trace norm, contractivity

Jordan decomposition of Hermitian matrices, trace norm for PSD matrices,
and partial trace contraction of trace norm and trace distance.

## Main definitions
- `Quantum.Metrics.traceDistance_densityOp_eq_traceNormHermitian`: D(ρ,σ) = ½ ‖ρ - σ‖₁
- `traceNormHermitian_eq_trace_pos_neg`: Jordan decomposition A = A₊ - A₋ with ‖A‖₁ = Tr(A₊) +
Tr(A₋)
- `traceNormHermitian_of_posSemidef`: ‖P‖₁ = Tr(P) for PSD P

## Main statements
- `traceNormHermitian_partialTraceB_le`: ‖Tr_B(A)‖₁ ≤ ‖A‖₁
- `partialTraceB_contracts_traceDistance`: D(Tr_B(ρ), Tr_B(σ)) ≤ D(ρ,σ)
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.DistanceBounds.TraceNormContraction

/-- Partial trace contracts trace norm: ||Tr_B(A)||₁ ≤ ||A||₁ for Hermitian A.

    This is the key inequality underlying CPTP contraction of trace distance.
    The proof uses the Jordan decomposition A = A₊ - A₋ (positive and negative parts),
    combined with the fact that partial trace preserves positive semidefiniteness
    and trace. Since Tr_B(A) = Tr_B(A₊) - Tr_B(A₋) with both parts PSD,
    ||Tr_B(A)||₁ ≤ Tr(Tr_B(A₊)) + Tr(Tr_B(A₋)) = Tr(A₊) + Tr(A₋) = ||A||₁. -/
lemma traceNormHermitian_partialTraceB_le {n m : ℕ}
    [NeZero n] [NeZero m] [NeZero (n * m)]
    (A : Op (n * m)) (hA : A.IsHermitian)
    (hB : (partialTraceB A).IsHermitian) :
    traceNormHermitian (partialTraceB A) hB ≤ traceNormHermitian A hA := by
  -- Step 1: Get the Jordan decomposition A = Apos - Aneg
  obtain ⟨Apos, Aneg, hApos, hAneg, h_decomp, h_norm_eq⟩ :=
    traceNormHermitian_eq_trace_pos_neg A hA
  -- Step 2: Partial trace preserves the decomposition
  have h_TrB_decomp : partialTraceB A = partialTraceB Apos - partialTraceB Aneg := by
    rw [h_decomp]
    ext i j
    simp only [partialTraceB, Matrix.sub_apply, Matrix.of_apply, Finset.sum_sub_distrib]
  -- Step 3: Partial traces of PSD matrices are PSD
  -- Bridge Mathlib's PosSemidef to QI's PosSemidefOp for partialTraceB_posSemidef
  have hApos_qi : ∀ x : Fin (n * m) → ℂ, 0 ≤ (quadraticForm Apos x).re := by
    have hApos' := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hApos).2
    intro x; exact (Complex.le_def.mp (hApos' x)).1
  have hAneg_qi : ∀ x : Fin (n * m) → ℂ, 0 ≤ (quadraticForm Aneg x).re := by
    have hAneg' := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAneg).2
    intro x; exact (Complex.le_def.mp (hAneg' x)).1
  let AposPSD : PosSemidefOp (n * m) := ⟨⟨Apos, hApos.1⟩, hApos_qi⟩
  let AnegPSD : PosSemidefOp (n * m) := ⟨⟨Aneg, hAneg.1⟩, hAneg_qi⟩
  -- Build Mathlib's PosSemidef for partial traces from QI's partialTraceB_posSemidef
  have hTrBpos : (partialTraceB Apos).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    have h_herm := partialTraceB_hermitian Apos hApos.1
    constructor
    · exact h_herm
    · intro x
      have h_re := partialTraceB_posSemidef AposPSD x
      have h_real := quadraticForm_hermitian_conj_eq_self (partialTraceB Apos) h_herm x
      have h_im : (quadraticForm (partialTraceB Apos) x).im = 0 := by
        rw [Complex.ext_iff] at h_real
        simp only [Complex.conj_re, Complex.conj_im] at h_real
        linarith [h_real.2]
      rw [show star x ⬝ᵥ (partialTraceB Apos *ᵥ x) = quadraticForm (partialTraceB Apos) x from rfl]
      rw [Complex.nonneg_iff]
      exact ⟨h_re, h_im.symm⟩
  have hTrBneg : (partialTraceB Aneg).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    have h_herm := partialTraceB_hermitian Aneg hAneg.1
    constructor
    · exact h_herm
    · intro x
      have h_re := partialTraceB_posSemidef AnegPSD x
      have h_real := quadraticForm_hermitian_conj_eq_self (partialTraceB Aneg) h_herm x
      have h_im : (quadraticForm (partialTraceB Aneg) x).im = 0 := by
        rw [Complex.ext_iff] at h_real
        simp only [Complex.conj_re, Complex.conj_im] at h_real
        linarith [h_real.2]
      rw [show star x ⬝ᵥ (partialTraceB Aneg *ᵥ x) = quadraticForm (partialTraceB Aneg) x from rfl]
      rw [Complex.nonneg_iff]
      exact ⟨h_re, h_im.symm⟩
  -- Step 4: Apply traceNormHermitian ≤ trace for PSD decomposition
  have h_le := traceNormHermitian_le_trace_posSemidef_sub
    (partialTraceB A) (partialTraceB Apos) (partialTraceB Aneg)
    hB hTrBpos hTrBneg h_TrB_decomp
  -- Step 5: Trace is preserved under partial trace
  have h_trace_pos : (partialTraceB Apos).trace = Apos.trace :=
    trace_partialTraceB Apos
  have h_trace_neg : (partialTraceB Aneg).trace = Aneg.trace :=
    trace_partialTraceB Aneg
  -- Step 6: Combine
  calc traceNormHermitian (partialTraceB A) hB
      ≤ ((partialTraceB Apos).trace + (partialTraceB Aneg).trace).re := h_le
    _ = (Apos.trace + Aneg.trace).re := by rw [h_trace_pos, h_trace_neg]
    _ = traceNormHermitian A hA := h_norm_eq.symm

/-- Partial trace B contracts trace distance.

    For density operators ρ, σ on ℂⁿ ⊗ ℂᵐ:
      D(Tr_B(ρ), Tr_B(σ)) ≤ D(ρ, σ)

    This is a special case of CPTP contraction: partial trace is a CPTP map,
    and CPTP maps do not increase trace distance.

    **Reference**: CKMR 2007, used implicitly in Theorem II.7 proof (line 626-627).
    Standard result in quantum information theory. -/
lemma partialTraceB_contracts_traceDistance {n m : ℕ}
    [NeZero n] [NeZero m] [NeZero (n * m)]
    (ρ σ : DensityOp (n * m)) :
    traceDistance (DensityOp.partialTraceB ρ).toOp (DensityOp.partialTraceB σ).toOp ≤
      traceDistance ρ.toOp σ.toOp := by
  -- Reduce both sides to traceNormHermitian using
  -- Quantum.Metrics.traceDistance_densityOp_eq_traceNormHermitian.
  rw [Quantum.Metrics.traceDistance_densityOp_eq_traceNormHermitian ρ.partialTraceB σ.partialTraceB,
      Quantum.Metrics.traceDistance_densityOp_eq_traceNormHermitian ρ σ]
  -- Goal: (1/2) * traceNormHermitian(TrB(ρ).toOp - TrB(σ).toOp) ≤ (1/2) * traceNormHermitian(ρ.toOp
  -- - σ.toOp)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1 / 2)
  -- Need: traceNormHermitian(TrB(ρ).toOp - TrB(σ).toOp) ≤ traceNormHermitian(ρ.toOp - σ.toOp)
  -- By linearity: TrB(ρ).toOp - TrB(σ).toOp = partialTraceB(ρ.toOp - σ.toOp)
  have h_lin : ρ.partialTraceB.toOp - σ.partialTraceB.toOp =
      partialTraceB (ρ.toOp - σ.toOp) := by
    ext i j
    simp only [DensityOp.partialTraceB, PosSemidefOp.partialTraceB,
      partialTraceB, Matrix.sub_apply, Matrix.of_apply, Finset.sum_sub_distrib]
  -- Dependent rewrite: traceNormHermitian depends on the hermiticity proof.
  -- Use calc to handle the dependency.
  have hA := densityOp_sub_isHermitian ρ σ
  have hB := densityOp_sub_isHermitian ρ.partialTraceB σ.partialTraceB
  have hPB : (partialTraceB (ρ.toOp - σ.toOp)).IsHermitian :=
    partialTraceB_hermitian _ hA
  calc traceNormHermitian (ρ.partialTraceB.toOp - σ.partialTraceB.toOp) hB
      = traceNormHermitian (partialTraceB (ρ.toOp - σ.toOp)) hPB := by
        congr 1
    _ ≤ traceNormHermitian (ρ.toOp - σ.toOp) hA :=
        traceNormHermitian_partialTraceB_le _ _ _

/-- For a projector P and state ρ, the trace norm of PρP is at most Tr(Pρ).re.
    Since PρP is PSD (as P†=P and ρ ≥ 0), its trace norm equals its trace,
    and Tr(PρP) = Tr(P²ρ) = Tr(Pρ) since P is idempotent.
    Used in de Finetti trace distance bounds. -/
lemma traceNormHermitian_projector_sandwich_le {m : ℕ} [NeZero m]
    (P : Op m) (hP_proj : P * P = P) (hP_herm : P† = P)
    (ρ : DensityOp m)
    (hPρP_herm : (P * ρ.toOp * P).IsHermitian) :
    traceNormHermitian (P * ρ.toOp * P) hPρP_herm ≤ (P * ρ.toOp).trace.re := by
  -- Step 1: PρP is PSD (congruence: P†ρP is PSD when ρ is PSD and P† = P)
  have hρ_psd : ρ.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have hPρP_psd : (P * ρ.toOp * P).PosSemidef := by
    have h := hρ_psd.conjTranspose_mul_mul_same P
    rwa [hP_herm] at h
  -- Step 2: For PSD, trace norm = trace.re
  rw [traceNormHermitian_of_posSemidef _ hPρP_psd]
  -- Step 3: Tr(PρP) = Tr(PPρ) = Tr(Pρ) by cyclicity and P²=P
  have htrace_eq : (P * ρ.toOp * P).trace = (P * ρ.toOp).trace := by
    rw [Matrix.trace_mul_cycle P ρ.toOp P, hP_proj]
  rw [htrace_eq]

end InfoTheory.DistanceBounds.TraceNormContraction

end
