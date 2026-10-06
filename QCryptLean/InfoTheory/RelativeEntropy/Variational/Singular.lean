import
  QCryptLean.InfoTheory.RelativeEntropy.Variational.GoldenThompson
import
  QCryptLean.InfoTheory.RelativeEntropy.Variational.LogCompression
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.SupportCompression
import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Singular Variational Bounds — support compression and kernel-based Gibbs estimates

This file extends the variational Holevo-bound machinery from full-rank
reference states to singular ones. It uses support compression to compare the
compressed logarithmic perturbation with the ambient diagonal term and derives
the kernel-containment form of the diagonal Gibbs variational bound.

## Main statements
- `trace_compressedState_support_diagonal_re`: support compression preserves the
  ambient diagonal pairing
- `compressedSigma_trace_support_exp_diagonal_eq`: the denominator trace is the
  ambient diagonal exponential term
- `gibbs_variational_diagonal_bound_of_ker_sub`: singular-reference diagonal
  Gibbs bound under kernel containment
- `InfoTheory.RelativeEntropy.gibbs_variational_diagonal_bound_of_ker_sub`: compatibility alias for
  the kernel-containment theorem
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

private local instance (n : Type*) [Fintype n] [DecidableEq n] : CStarAlgebra (Matrix n n ℂ) := {}

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-- Taking the real part of the trace pairing is linear in the right factor. -/
lemma trace_re_mul_sub {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ) :
    (A * (B - C)).trace.re =
      (A * B).trace.re - (A * C).trace.re := by
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

/-- Re-embedding a compressed supported state transports the support-compressed
    diagonal pairing back to the ambient diagonal pairing. -/
lemma trace_compressedState_support_diagonal_re {N : ℕ}
    (σ ρ : DensityOp N) (h : Fin N → ℝ)
    (hρP : ρ.toOp * supportProjector σ = ρ.toOp) :
    (((compressedState σ ρ hρP).toOp *
        ((supportIsometry σ).conjTranspose *
          Matrix.diagonal (fun j => (h j : ℂ)) *
          supportIsometry σ)).trace.re) =
      ∑ j, (ρ.toOp j j).re * h j := by
  letI : NeZero N := neZero_of_densityOp σ
  set S := supportIsometry σ
  set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun j => (h j : ℂ))
  set ρs : DensityOp (positiveSpectrumDim σ) := compressedState σ ρ hρP
  have hρ_embed_toOp : ρ.toOp = S * ρs.toOp * S.conjTranspose := by
    have h := congrArg (fun τ => τ.toOp)
      (compressedState_embed (σ := σ) (ρ := ρ) (hρP := hρP))
    exact h.symm
  calc
    ((ρs.toOp * (S.conjTranspose * D * S)).trace.re)
        = (((S * ρs.toOp * S.conjTranspose) * D).trace.re) := by
            rw [trace_mul_support_compression]
    _ = ((ρ.toOp * D).trace.re) := by
      rw [hρ_embed_toOp]
    _ = ∑ j, (ρ.toOp j j).re * h j := by
      simpa [D] using trace_mul_real_diagonal_re ρ.toOp h

/-- The denominator term for the singular-reference bridge is exact: tracing the
compressed ambient exponential against `compressedSigma σ` reproduces the
ambient weighted diagonal exponential sum. -/
lemma compressedSigma_trace_support_exp_diagonal_eq {N : ℕ}
    (σ : DensityOp N) (h : Fin N → ℝ) :
    ((compressedSigma σ).toOp *
      ((supportIsometry σ).conjTranspose *
        NormedSpace.exp (Matrix.diagonal (fun j => (h j : ℂ))) *
        supportIsometry σ)).trace.re =
    ∑ j, (σ.toOp j j).re * Real.exp (h j) := by
  letI : NeZero N := neZero_of_densityOp σ
  set S := supportIsometry σ
  set D : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.diagonal (fun j => (h j : ℂ))
  set σs := compressedSigma σ
  have h_sum_trace :
      ∑ j, (σ.toOp j j).re * Real.exp (h j) =
      (σ.toOp * Matrix.diagonal
        (fun j => (Real.exp (h j) : ℂ))).trace.re :=
    (trace_mul_real_diagonal_re σ.toOp
      (fun j => Real.exp (h j))).symm
  have hexpD :
      NormedSpace.exp D =
        Matrix.diagonal
          (fun j => (Real.exp (h j) : ℂ)) := by
    change NormedSpace.exp
      (Matrix.diagonal (fun j => (h j : ℂ))) =
        Matrix.diagonal
          (fun j => (Real.exp (h j) : ℂ))
    rw [Matrix.exp_diagonal]
    congr 1
    ext j
    simp [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
  have hσ_embed : σ.toOp =
      S * σs.toOp * S.conjTranspose := by
    have := congrArg (fun τ => τ.toOp)
      (compressedSigma_embed σ)
    simpa [σs, S, DensityOp.isometryEmbed]
      using this.symm
  rw [h_sum_trace, ← hexpD, hσ_embed]
  rw [trace_mul_support_compression]

/-- Tracing a compressed supported state against the compressed diagonal
perturbation is bounded by tracing it against the logarithm of the compressed
ambient diagonal exponential. This is the trace-level bridge supplied by the
matrix-log Jensen helper. -/
lemma trace_compressedState_support_diagonal_le_log_support_exp_diagonal {N : ℕ}
    (σ ρ : DensityOp N) (h : Fin N → ℝ)
    (hρP : ρ.toOp * supportProjector σ = ρ.toOp) :
    (((compressedState σ ρ hρP).toOp *
        ((supportIsometry σ).conjTranspose *
          Matrix.diagonal (fun j => (h j : ℂ)) *
          supportIsometry σ)).trace.re) ≤
      (((compressedState σ ρ hρP).toOp *
          CFC.log
            ((supportIsometry σ).conjTranspose *
              NormedSpace.exp (Matrix.diagonal (fun j => (h j : ℂ))) *
              supportIsometry σ)).trace.re) := by
  set S := supportIsometry σ
  set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun j => (h j : ℂ))
  set ρs : DensityOp (positiveSpectrumDim σ) := compressedState σ ρ hρP
  set A : Matrix (Fin (positiveSpectrumDim σ))
      (Fin (positiveSpectrumDim σ)) ℂ :=
    S.conjTranspose * NormedSpace.exp D * S
  have hρs_psd : ρs.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib ρs.toPosSemidefOp
  have hlog_diff_psd :
      (CFC.log A - S.conjTranspose * D * S).PosSemidef := by
    exact Matrix.le_iff.mp
      (compression_diagonal_le_log_compression_exp_diagonal
        S (supportIsometry_isometry σ) h)
  have htrace_nonneg :
      0 ≤ (ρs.toOp * (CFC.log A - S.conjTranspose * D * S)).trace.re :=
    Quantum.Operators.trace_mul_psd_nonneg ρs.toOp
      (CFC.log A - S.conjTranspose * D * S) hρs_psd hlog_diff_psd
  rw [trace_re_mul_sub] at htrace_nonneg
  linarith

/-- Singular-reference diagonal Gibbs variational bound under kernel containment.

    This is the diagonal Gibbs estimate needed for pinching when `σ` may be
    singular, provided `ker σ ⊆ ker ρ`. -/
lemma gibbs_variational_diagonal_bound_of_ker_sub {N : ℕ} [NeZero N]
    (ρ σ : DensityOp N) (h : Fin N → ℝ)
    (h_ker : ∀ v : Fin N → ℂ,
      σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    (∑ j, (ρ.toOp j j).re * h j) -
      Real.log (∑ j, (σ.toOp j j).re * Real.exp (h j)) ≤
    relativeEntropyReal ρ σ := by
  set S := supportIsometry σ
  set Hs : Matrix (Fin (positiveSpectrumDim σ)) (Fin (positiveSpectrumDim σ)) ℂ :=
    S.conjTranspose * Matrix.diagonal (fun j => (h j : ℂ)) * S
  set ρs : DensityOp (positiveSpectrumDim σ) := compressedRhoOfKerSub ρ σ h_ker
  set σs : DensityOp (positiveSpectrumDim σ) := compressedSigma σ
  set A : Matrix (Fin (positiveSpectrumDim σ)) (Fin (positiveSpectrumDim σ)) ℂ :=
    S.conjTranspose *
      NormedSpace.exp (Matrix.diagonal (fun j => (h j : ℂ))) * S
  set Ls : Matrix (Fin (positiveSpectrumDim σ)) (Fin (positiveSpectrumDim σ)) ℂ :=
    CFC.log A
  have hLs_herm : Ls.IsHermitian := by
    change IsSelfAdjoint (CFC.log A)
    exact IsSelfAdjoint.log (a := A)
  have hmain :=
    gibbs_variational_bound_of_isHermitian ρs σs Ls hLs_herm
      (compressedSigma_eigenvalues_pos σ)
  have hnum_eq :
      (ρs.toOp * Hs).trace.re = ∑ j, (ρ.toOp j j).re * h j := by
    exact
      (trace_compressedState_support_diagonal_re σ ρ h
        (rho_mul_supportProjector_of_ker_sub ρ σ h_ker))
  have hnum_le :
      ∑ j, (ρ.toOp j j).re * h j ≤ (ρs.toOp * Ls).trace.re := by
    have hbridge :
        (ρs.toOp * Hs).trace.re ≤ (ρs.toOp * Ls).trace.re := by
      exact
        (trace_compressedState_support_diagonal_le_log_support_exp_diagonal
          σ ρ h (rho_mul_supportProjector_of_ker_sub ρ σ h_ker))
    linarith [hnum_eq]
  have hden_eq :
      (σs.toOp * NormedSpace.exp Ls).trace.re =
        ∑ j, (σ.toOp j j).re * Real.exp (h j) := by
    have hexpLs : NormedSpace.exp Ls = A := by
      simpa [Ls] using
        (exp_log_compression_exp_diagonal
          S (supportIsometry_isometry σ) h)
    calc
      (σs.toOp * NormedSpace.exp Ls).trace.re
          = (σs.toOp * A).trace.re := by rw [hexpLs]
      _ = ∑ j, (σ.toOp j j).re * Real.exp (h j) := by
            simpa [σs, A, S] using
              compressedSigma_trace_support_exp_diagonal_eq σ h
  have hrel :
      relativeEntropyReal ρ σ = relativeEntropyReal ρs σs := by
    have hrel_embed :=
      relativeEntropyReal_isometry_invariance
        (V := S) (hV := supportIsometry_isometry σ) (ρ := ρs) (σ := σs)
    rw [compressedRhoOfKerSub_embed ρ σ h_ker, compressedSigma_embed σ] at hrel_embed
    exact hrel_embed
  have hmain' :
      (ρs.toOp * Ls).trace.re -
        Real.log (∑ j, (σ.toOp j j).re * Real.exp (h j)) ≤
      relativeEntropyReal ρ σ := by
    rw [hden_eq, ← hrel] at hmain
    exact hmain
  have hcompare :
      (∑ j, (ρ.toOp j j).re * h j) -
        Real.log (∑ j, (σ.toOp j j).re * Real.exp (h j)) ≤
      (ρs.toOp * Ls).trace.re -
        Real.log (∑ j, (σ.toOp j j).re * Real.exp (h j)) := by
    linarith
  exact le_trans hcompare hmain'

end InfoTheory.RelativeEntropy

end
