import QCryptLean.Quantum.Metrics.TraceNorm.Basic

/-!
# Jordan decomposition and Hermitian trace norm

`traceNormHermitian_eq_trace_pos_neg` decomposes a Hermitian operator into positive and negative
parts. `traceNormHermitian_of_posSemidef` identifies the trace norm of a positive operator with
its trace, and `traceNormHermitian_le_trace_posSemidef_sub` bounds a positive-operator difference.
-/

open Quantum.Operators Matrix Math.SpectralTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Metrics

/-- The trace norm of a Hermitian matrix equals the real part of the trace of its
    absolute value. For Hermitian A: ||A||₁ = Tr(A₊) + Tr(A₋) where A = A₊ - A₋
    is the Jordan decomposition. Equivalently, ||A||₁ = (∑ᵢ λᵢ⁺) + (∑ᵢ λᵢ⁻)
    where the sums are over positive and negative eigenvalues respectively,
    which equals (∑ᵢ λᵢ⁺) + (∑ᵢ |λᵢ⁻|) = ∑ᵢ |λᵢ|.

    This is used to relate traceNormHermitian (defined via eigenvalues) to trace
    (computable from matrix entries), enabling the partial trace contraction proof. -/
lemma traceNormHermitian_eq_trace_pos_neg {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    ∃ (Apos Aneg : Matrix (Fin n) (Fin n) ℂ),
      Apos.PosSemidef ∧ Aneg.PosSemidef ∧
      A = Apos - Aneg ∧
      traceNormHermitian A hA = (Apos.trace + Aneg.trace).re := by
  -- Spectral theorem: A = U * diag(λ) * U^H
  set U := (hA.eigenvectorUnitary.val : Matrix (Fin n) (Fin n) ℂ) with hU_def
  set ev := hA.eigenvalues with hevdef
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  -- h_spec : A = U * diagonal(ofReal ∘ ev) * U^H
  -- Define positive and negative diagonal parts
  set dpos : Fin n → ℂ := fun i => ↑(max (ev i) 0) with hdpos_def
  set dneg : Fin n → ℂ := fun i => ↑(max (-ev i) 0) with hdneg_def
  -- Define Apos and Aneg
  set Apos := U * Matrix.diagonal dpos * Uᴴ with hApos_def
  set Aneg := U * Matrix.diagonal dneg * Uᴴ with hAneg_def
  refine ⟨Apos, Aneg, ?_, ?_, ?_, ?_⟩
  · -- Apos is PSD: diagonal has nonneg entries, conjugated by U
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    rw [Matrix.posSemidef_diagonal_iff]
    intro i; rw [Complex.zero_le_real]; exact le_max_right _ _
  · -- Aneg is PSD: similar
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    rw [Matrix.posSemidef_diagonal_iff]
    intro i; rw [Complex.zero_le_real]; exact le_max_right _ _
  · -- A = Apos - Aneg: diag(max(λ,0)) - diag(max(-λ,0)) = diag(λ)
    have h_diag_sub : Matrix.diagonal dpos - Matrix.diagonal dneg =
        Matrix.diagonal (RCLike.ofReal ∘ ev) := by
      ext i j
      simp only [Matrix.diagonal, sub_apply, Matrix.of_apply, Function.comp_apply, dpos, dneg]
      split
      · next h =>
          subst h
          rw [← Complex.ofReal_sub]
          congr 1
          simp [max_def]; split <;> split <;> linarith
      · simp
    change A = Apos - Aneg
    rw [hApos_def, hAneg_def]
    have h_factor : U * Matrix.diagonal dpos * Uᴴ - U * Matrix.diagonal dneg * Uᴴ =
        U * (Matrix.diagonal dpos - Matrix.diagonal dneg) * Uᴴ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    rw [h_factor, h_diag_sub]
    exact h_spec
  · -- traceNormHermitian A = (trace Apos + trace Aneg).re
    -- Use trace(U * D * U^H) = trace(D) via cyclic property: trace(ABC) = trace(CAB)
    have h_UhU : Uᴴ * U = 1 := by
      have := Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
      simp only [star_eq_conjTranspose] at this
      exact this
    have h_trace_cycle : ∀ (D : Matrix (Fin n) (Fin n) ℂ),
        (U * D * Uᴴ).trace = D.trace := by
      intro D
      calc (U * D * Uᴴ).trace
          = (Uᴴ * (U * D)).trace := by rw [Matrix.trace_mul_comm]
        _ = (Uᴴ * U * D).trace := by rw [Matrix.mul_assoc]
        _ = ((1 : Matrix (Fin n) (Fin n) ℂ) * D).trace := by rw [h_UhU]
        _ = D.trace := by rw [Matrix.one_mul]
    rw [hApos_def, hAneg_def, h_trace_cycle, h_trace_cycle,
        Matrix.trace_diagonal, Matrix.trace_diagonal]
    -- Now: traceNormHermitian A hA = (∑ max(λᵢ,0) + ∑ max(-λᵢ,0)).re = ∑ |λᵢ|
    unfold traceNormHermitian
    simp only [dpos, dneg, ← Finset.sum_add_distrib]
    -- Goal: ∑ |ev i| = (∑ (↑(max (ev i) 0) + ↑(max (-ev i) 0))).re
    have : ∀ i : Fin n, |ev i| = max (ev i) 0 + max (-ev i) 0 := by
      intro i; simp [abs_eq_max_neg, max_def]; split <;> split <;> linarith
    conv_lhs => arg 2; ext i; rw [this i]
    simp [Complex.add_re, Complex.ofReal_re]

/-- For a PSD matrix, trace norm equals the trace (since all eigenvalues are nonneg). -/
lemma traceNormHermitian_of_posSemidef {n : ℕ} [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.PosSemidef) :
    traceNormHermitian P hP.1 = P.trace.re := by
  unfold traceNormHermitian
  -- For PSD: eigenvalues ≥ 0, so |λᵢ| = λᵢ
  have h_nonneg := hP.eigenvalues_nonneg
  conv_lhs => arg 2; ext i; rw [abs_of_nonneg (h_nonneg i)]
  -- ∑ eigenvalues = trace.re (via trace_eq_sum_eigenvalues)
  have h_trace := hP.1.trace_eq_sum_eigenvalues
  -- h_trace : P.trace = ∑ i, (hP.1.eigenvalues i : ℂ)
  rw [h_trace]
  simp [Complex.ofReal_re]

/-- Trace norm is the same for A and -A. -/
lemma traceNormHermitian_neg {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    let h_neg : (-A).IsHermitian := by unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_neg, hA]
    traceNormHermitian (-A) h_neg = traceNormHermitian A hA := by
  intro h_neg
  unfold traceNormHermitian
  exact hermitian_neg_eigenvalues_abs_sum A hA h_neg

/-- The trace norm of a difference of positive operators is bounded by their total trace. -/
lemma traceNormHermitian_le_trace_posSemidef_sub {n : ℕ} [NeZero n]
    (B P Q : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.IsHermitian) (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (h_eq : B = P - Q) :
    traceNormHermitian B hB ≤ (P.trace + Q.trace).re := by
  -- Strategy: ||B||₁ = ||P + (-Q)||₁ ≤ ||P||₁ + ||-Q||₁ = ||P||₁ + ||Q||₁
  -- For PSD matrices: ||P||₁ = tr(P).re and ||Q||₁ = tr(Q).re
  have hP_herm : P.IsHermitian := hP.1
  have hQ_herm : Q.IsHermitian := hQ.1
  have h_negQ_herm : (-Q).IsHermitian := by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_neg, hQ_herm]
  -- B = P + (-Q), so rewrite as a sum for the triangle inequality
  have h_sum : B = P + (-Q) := by rw [h_eq]; simp [sub_eq_add_neg]
  have h_sum_herm : (P + (-Q)).IsHermitian := h_sum ▸ hB
  -- Apply triangle inequality: ||P + (-Q)||₁ ≤ ||P||₁ + ||-Q||₁
  have h_tri := traceNormHermitian_triangle P (-Q) hP_herm h_negQ_herm
  -- ||P||₁ = tr(P).re for PSD P
  have h_normP := traceNormHermitian_of_posSemidef P hP
  -- ||-Q||₁ = ||Q||₁ = tr(Q).re
  have h_negQ_norm := traceNormHermitian_neg Q hQ_herm
  have h_normQ := traceNormHermitian_of_posSemidef Q hQ
  -- Combine: ||B||₁ ≤ ||P||₁ + ||Q||₁ = tr(P).re + tr(Q).re
  -- First handle the proof-irrelevance for traceNormHermitian
  have h_eq_norm : traceNormHermitian B hB = traceNormHermitian (P + (-Q)) h_sum_herm := by
    have : B = P + (-Q) := h_sum
    subst this; exact traceNormHermitian_proof_irrel _ _ _
  calc traceNormHermitian B hB
      = traceNormHermitian (P + (-Q)) h_sum_herm := h_eq_norm
    _ ≤ traceNormHermitian P hP_herm + traceNormHermitian (-Q) h_negQ_herm := h_tri
    _ = traceNormHermitian P hP.1 + traceNormHermitian (-Q) h_negQ_herm := by
        rw [traceNormHermitian_proof_irrel P hP_herm hP.1]
    _ = P.trace.re + traceNormHermitian (-Q) h_negQ_herm := by rw [h_normP]
    _ = P.trace.re + traceNormHermitian Q hQ_herm := by rw [h_negQ_norm]
    _ = P.trace.re + traceNormHermitian Q hQ.1 := by rw [traceNormHermitian_proof_irrel Q hQ_herm
        hQ.1]
    _ = P.trace.re + Q.trace.re := by rw [h_normQ]
    _ = (P.trace + Q.trace).re := (Complex.add_re _ _).symm

end Quantum.Metrics

end
