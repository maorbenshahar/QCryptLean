import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundTwoUniversal
import QCryptLean.Quantum.Operators.InverseSqrt

/-!
# Quantum LHL λ-bound — inverse-fourth-root sandwich lemmas

The inverse-fourth-root trace identities that feed the two-universal quantum leftover
hash λ-bound: the fourth-root sandwich `σ^{-1/4} ρ σ^{-1/4}` preserves `ρ`'s trace when
squared against `σ`'s inverse square root, and its squared trace is controlled by the
operator-order feasibility bound `ρ ≤ t • σ`.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

/-- Trace cyclicity for the inverse-fourth-root feasibility weight. -/
lemma tr_invFourthRoot_rho_invFourthRoot_mul_invFourthRoot_sigma_invFourthRoot_eq_tr_rho
    {n : ℕ} {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef)
    (ρx : Matrix (Fin n) (Fin n) ℂ) :
    ((hσ.inverseFourthRoot * ρx * hσ.inverseFourthRoot) *
      (hσ.inverseFourthRoot * σ * hσ.inverseFourthRoot)).trace = ρx.trace := by
  set F : Matrix (Fin n) (Fin n) ℂ := hσ.inverseFourthRoot with hF_def
  set S : Matrix (Fin n) (Fin n) ℂ := hσ.inverseSqrt with hS_def
  have hF_sq : F * F = S := by
    rw [hF_def, hS_def]
    exact hσ.inverseFourthRoot_sq
  have hSand : S * σ * S = 1 := by
    rw [hS_def]
    exact hσ.inverseSqrt_sandwich_eq_one
  have hmid : F * F * σ * F * F = S * σ * S := by
    rw [← hF_sq]
    noncomm_ring
  have hcycle :
      ((F * ρx * F) * (F * σ * F)).trace =
        ((ρx * F) * (F * σ * F) * F).trace := by
    have hleft : (F * ρx * F) * (F * σ * F) =
        F * (ρx * F) * (F * σ * F) := by
      noncomm_ring
    rw [hleft]
    have hassoc : F * (ρx * F) * (F * σ * F) =
        F * ((ρx * F) * (F * σ * F)) := by
      simp only [Matrix.mul_assoc]
    rw [hassoc]
    exact Matrix.trace_mul_comm F ((ρx * F) * (F * σ * F))
  change ((F * ρx * F) * (F * σ * F)).trace = ρx.trace
  calc ((F * ρx * F) * (F * σ * F)).trace
      = ((ρx * F) * (F * σ * F) * F).trace := hcycle
    _ = (ρx * (F * F * σ * F * F)).trace := by
      congr 1
      noncomm_ring
    _ = (ρx * (S * σ * S)).trace := by rw [hmid]
    _ = (ρx * 1).trace := by rw [hSand]
    _ = ρx.trace := by rw [Matrix.mul_one]

/-- Per-block squared-sandwich feasibility bound for the inverse fourth root. -/
lemma tr_inverseFourthRoot_sandwich_sq_le_of_opLe
    {n : ℕ} {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef)
    {ρx : Matrix (Fin n) (Fin n) ℂ} (hρx : ρx.PosSemidef)
    {t : ℝ} (h : opLe ρx (Complex.ofReal t • σ)) :
    ((hσ.inverseFourthRoot * ρx * hσ.inverseFourthRoot) *
      (hσ.inverseFourthRoot * ρx * hσ.inverseFourthRoot)).trace.re
      ≤ t * ρx.trace.re := by
  set F : Matrix (Fin n) (Fin n) ℂ := hσ.inverseFourthRoot with hF_def
  set Q : Matrix (Fin n) (Fin n) ℂ := F * ρx * F with hQ_def
  set P : Matrix (Fin n) (Fin n) ℂ := F * σ * F with hP_def
  have hF_herm : F.IsHermitian := by
    rw [hF_def]
    exact hσ.inverseFourthRoot_isHermitian
  have hF_conj : F.conjTranspose = F := hF_herm.eq
  have hQ_psd : Q.PosSemidef := by
    simpa [hQ_def, hF_conj] using hρx.conjTranspose_mul_mul_same F
  have hP_psd : P.PosSemidef := by
    simpa [hP_def, hF_conj] using hσ.posSemidef.conjTranspose_mul_mul_same F
  have hQ_herm : Q.IsHermitian := hQ_psd.isHermitian
  have hP_herm : P.IsHermitian := hP_psd.isHermitian
  have ht_sa : IsSelfAdjoint (Complex.ofReal t : ℂ) := by
    change star (Complex.ofReal t) = Complex.ofReal t
    rw [Complex.star_def, Complex.conj_ofReal]
  have htP_herm : (Complex.ofReal t • P).IsHermitian := ht_sa.smul hP_herm
  have hQ_le_tP : opLe Q (Complex.ofReal t • P) := by
    have hsand : opLe (F * ρx * F) (F * (Complex.ofReal t • σ) * F) :=
      opLe_sandwich_of_isHermitian hF_herm h
    have hRHS : F * (Complex.ofReal t • σ) * F = Complex.ofReal t • P := by
      calc F * (Complex.ofReal t • σ) * F
          = (Complex.ofReal t • (F * σ)) * F := by rw [mul_smul_comm]
        _ = Complex.ofReal t • ((F * σ) * F) := by rw [smul_mul_assoc]
        _ = Complex.ofReal t • P := by rw [hP_def]
    rw [hRHS] at hsand
    simpa [hQ_def] using hsand
  have hdiff_psd : (Complex.ofReal t • P - Q).PosSemidef :=
    opLe.posSemidef_sub hQ_herm htP_herm hQ_le_tP
  have hprod_nonneg :
      0 ≤ (Q * (Complex.ofReal t • P - Q)).trace.re := by
    have h1 : (1 : Matrix (Fin n) (Fin n) ℂ).IsHermitian := Matrix.isHermitian_one
    have hnn := tr_prod_sandwich_re_nonneg h1 hQ_psd hdiff_psd
    simpa using hnn
  have hQP_trace : (Q * P).trace = ρx.trace := by
    rw [hQ_def, hP_def, hF_def]
    exact
      tr_invFourthRoot_rho_invFourthRoot_mul_invFourthRoot_sigma_invFourthRoot_eq_tr_rho
        hσ ρx
  have htrace_decomp :
      (Q * (Complex.ofReal t • P - Q)).trace.re =
        t * ρx.trace.re - (Q * Q).trace.re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    have h_smul : (Q * (Complex.ofReal t • P)).trace.re = t * ρx.trace.re := by
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hQP_trace]
    rw [h_smul]
  have hineq : 0 ≤ t * ρx.trace.re - (Q * Q).trace.re := by
    rwa [htrace_decomp] at hprod_nonneg
  change (Q * Q).trace.re ≤ t * ρx.trace.re
  linarith

end InfoTheory.QuantumLHL

end
