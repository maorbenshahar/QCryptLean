import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.Quantum.Metrics.TraceNorm.ScalarBlock
import QCryptLean.Quantum.Metrics.TraceNorm.ScalarBlockFidelity
import QCryptLean.Quantum.Metrics.TraceNormDilation
import QCryptLean.Quantum.Operators.Types
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD

/-!
# Block-diagonal embedding of sub-normalized operators into density operators

For a sub-normalized `ρ : SubDensityOp n` on `Fin n`, the block-diagonal
construction

  ρ̃ := ρ ⊕ (1 - tr ρ) : DensityOp (n+1)

places `ρ` in the top-left `n × n` block and the real scalar `1 - tr ρ` in the
bottom-right `1 × 1` block. This is a standard device used to reduce
identities for generalized fidelity / generalized trace distance between
sub-normalized operators to their analogues on normalized density operators
on the `(n+1)`-dimensional space (Tomamichel 2016, around Lemma 3.17).

## Main definitions
- `SubDensityOp.defect` — the scalar `((1 - tr ρ : ℝ) : ℂ)`
- `SubDensityOp.extendOp` — the underlying `(n+1) × (n+1)` matrix
- `SubDensityOp.toDensityOpExtend` — the extension as a `DensityOp (n+1)`

## Main statements
- `SubDensityOp.extendOp_isHermitian` — Hermiticity of the extension
- `SubDensityOp.extendOp_pos_semidef` — positive semidefiniteness
- `SubDensityOp.extendOp_trace` — trace of the extension before normalization
- `SubDensityOp.extendOp_trace_one` — the extension has unit trace
- `toDensityOpExtend_trace` — follow-through from `trace_one`
- `toDensityOpExtend_fidelity` — block-diagonal fidelity identity
- `Quantum.Metrics.traceNorm_fromBlocks_scalar_abs` — arbitrary-sign scalar block trace norm
- `SubDensityOp.extendOp_sub_traceNorm` — trace norm of differences of extensions
- `toDensityOpExtend_traceDistance` — block-diagonal trace-norm identity
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The scalar defect `1 - tr ρ`. -/

/-- The real scalar `(1 - tr ρ : ℝ)` lifted to `ℂ`.

    Used as the bottom-right `1 × 1` block of the block-diagonal extension. -/
def SubDensityOp.defect {n : ℕ} (ρ : SubDensityOp n) : ℂ :=
  ((1 - ρ.trace : ℝ) : ℂ)

lemma SubDensityOp.defect_re {n : ℕ} (ρ : SubDensityOp n) :
    ρ.defect.re = 1 - ρ.trace := by
  simp [SubDensityOp.defect]

lemma SubDensityOp.defect_im {n : ℕ} (ρ : SubDensityOp n) :
    ρ.defect.im = 0 := by
  simp [SubDensityOp.defect]

lemma SubDensityOp.defect_star {n : ℕ} (ρ : SubDensityOp n) :
    star ρ.defect = ρ.defect := by
  unfold SubDensityOp.defect
  exact Complex.conj_ofReal _

lemma SubDensityOp.defect_nonneg_re {n : ℕ} (ρ : SubDensityOp n) :
    0 ≤ ρ.defect.re := by
  rw [ρ.defect_re]; exact ρ.one_sub_trace_nonneg

/-! ## The extended matrix. -/

/-- The `1 × 1` bottom-right block `(1 - tr ρ) · I`. -/
def SubDensityOp.defectBlock {n : ℕ} (ρ : SubDensityOp n) :
    Matrix (Fin 1) (Fin 1) ℂ :=
  ρ.defect • (1 : Matrix (Fin 1) (Fin 1) ℂ)

/-- The block-diagonal extension matrix `ρ ⊕ (1 - tr ρ)` as an `Op (n+1)`.

    The underlying `Fin n ⊕ Fin 1`-indexed block matrix is reindexed to
    `Fin (n+1)` via `finSumFinEquiv`. -/
def SubDensityOp.extendOp {n : ℕ} (ρ : SubDensityOp n) : Op (n+1) :=
  (Matrix.fromBlocks ρ.toOp 0 0 ρ.defectBlock).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-! ## Hermiticity of the extended matrix. -/

/-- The bottom-right `1 × 1` block is Hermitian. It is `(1 - tr ρ) · I` with
    `(1 - tr ρ)` real. -/
lemma SubDensityOp.defectBlock_isHermitian {n : ℕ} (ρ : SubDensityOp n) :
    ρ.defectBlock.IsHermitian := by
  unfold SubDensityOp.defectBlock Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_one, ρ.defect_star]

/-- The block-diagonal extension is Hermitian. -/
lemma SubDensityOp.extendOp_isHermitian {n : ℕ} (ρ : SubDensityOp n) :
    ρ.extendOp.IsHermitian := by
  unfold SubDensityOp.extendOp
  apply Matrix.IsHermitian.submatrix
  exact Matrix.IsHermitian.fromBlocks ρ.isHermitian
    (by simp) ρ.defectBlock_isHermitian

/-! ## Positive-semidefiniteness and unit trace. -/

/-- The `1 × 1` defect block is PSD: `(1 - tr ρ) ≥ 0` makes
    `(1 - tr ρ) • I₁` positive semidefinite. -/
lemma SubDensityOp.defectBlock_posSemidef {n : ℕ} (ρ : SubDensityOp n) :
    ρ.defectBlock.PosSemidef := by
  -- Rewrite `defect • 1` as `diagonal (fun _ => defect)`.
  have hrewrite :
      ρ.defectBlock = Matrix.diagonal (fun _ : Fin 1 => ρ.defect) := by
    unfold SubDensityOp.defectBlock
    funext i j
    fin_cases i; fin_cases j
    simp
  rw [hrewrite]
  -- Diagonal with a nonneg (complex) entry is PSD.
  apply Matrix.PosSemidef.diagonal
  intro _
  change (0 : ℂ) ≤ ρ.defect
  rw [Complex.nonneg_iff]
  exact ⟨ρ.defect_nonneg_re, ρ.defect_im.symm⟩

/-- The block-diagonal extension is PSD as a Mathlib `Matrix.PosSemidef`. -/
lemma SubDensityOp.extendOp_posSemidef_mathlib {n : ℕ} (ρ : SubDensityOp n) :
    ρ.extendOp.PosSemidef := by
  have hA : ρ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have hFB : (Matrix.fromBlocks ρ.toOp 0 0 ρ.defectBlock).PosSemidef :=
    Matrix.PosSemidef.fromBlocks_zero hA ρ.defectBlock_posSemidef
  unfold SubDensityOp.extendOp
  exact hFB.submatrix _

/-- The block-diagonal extension is positive semidefinite.

    Mathematically: `ρ ⊕ (1 - tr ρ)` is PSD because both blocks are PSD
    (ρ is PSD; `(1 - tr ρ) · I₁` is PSD since `1 - tr ρ ≥ 0`). -/
lemma SubDensityOp.extendOp_pos_semidef {n : ℕ} (ρ : SubDensityOp n) :
    ∀ x : Fin (n+1) → ℂ, 0 ≤ (quadraticForm ρ.extendOp x).re := by
  intro x
  -- Bridge from Mathlib's `Matrix.PosSemidef` to the local quadratic-form form.
  have h := ρ.extendOp_posSemidef_mathlib.dotProduct_mulVec_nonneg x
  -- `quadraticForm M x = star x ⬝ᵥ M *ᵥ x`, so the complex-nonneg bound gives
  -- the nonnegativity of the real part.
  exact (Complex.nonneg_iff.mp h).1

/-- The trace of the bottom-right `1 × 1` defect block equals the defect scalar. -/
lemma SubDensityOp.defectBlock_trace {n : ℕ} (ρ : SubDensityOp n) :
    ρ.defectBlock.trace = ρ.defect := by
  unfold SubDensityOp.defectBlock
  simp [Matrix.trace, Matrix.diag]

/-- The trace of the extension splits as the trace of `ρ` plus the defect block. -/
lemma SubDensityOp.extendOp_trace {n : ℕ} (ρ : SubDensityOp n) :
    ρ.extendOp.trace = ρ.toOp.trace + ρ.defectBlock.trace := by
  have htrace_reindex :
      ρ.extendOp.trace = (Matrix.fromBlocks ρ.toOp 0 0 ρ.defectBlock).trace := by
    unfold SubDensityOp.extendOp
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact Fintype.sum_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)
  have hsplit :
      (Matrix.fromBlocks ρ.toOp 0 0 ρ.defectBlock).trace =
        ρ.toOp.trace + ρ.defectBlock.trace := by
    simp only [Matrix.trace, Matrix.diag]
    rw [Fintype.sum_sum_type]
    simp [Matrix.fromBlocks]
  rw [htrace_reindex, hsplit]

/-- The trace of the block-diagonal extension equals 1.

    Mathematically: `tr (ρ ⊕ (1 - tr ρ)) = tr ρ + (1 - tr ρ) = 1`. -/
lemma SubDensityOp.extendOp_trace_one {n : ℕ} (ρ : SubDensityOp n) :
    ρ.extendOp.trace = 1 := by
  rw [ρ.extendOp_trace, ρ.defectBlock_trace, ρ.trace_complex_eq, SubDensityOp.defect]
  push_cast
  ring

/-! ## The extension as a `DensityOp`. -/

/-- The block-diagonal extension of a sub-normalized operator into a density
    operator on `Fin (n+1)`:

        ρ ⟼ ρ ⊕ (1 - tr ρ). -/
def SubDensityOp.toDensityOpExtend {n : ℕ} (ρ : SubDensityOp n) : DensityOp (n+1) where
  toOp := ρ.extendOp
  isHermitian := ρ.extendOp_isHermitian
  pos_semidef := ρ.extendOp_pos_semidef
  trace_one := ρ.extendOp_trace_one

/-! ## Interface identities used by `traceDistanceGen_le_purifiedDistance`. -/

/-- The extended operator has real trace equal to 1. Follow-through from the
    `trace_one` field of `DensityOp`. -/
lemma toDensityOpExtend_trace {n : ℕ} (ρ : SubDensityOp n) :
    (ρ.toDensityOpExtend.toOp.trace).re = 1 := by
  rw [ρ.toDensityOpExtend.trace_one, Complex.one_re]

/-- Block-diagonal fidelity identity:

    `F(ρ ⊕ (1 - tr ρ), σ ⊕ (1 - tr σ)) = F(ρ, σ) + √((1 - tr ρ)(1 - tr σ))
       = fidelityGen ρ σ`.

    This is the core identity relating standard fidelity on the extended
    density operators to the generalized fidelity on the sub-normalized
    originals. -/
lemma toDensityOpExtend_fidelity {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    Quantum.Metrics.fidelity
        (ρ.toDensityOpExtend.toPosSemidefOp)
        (σ.toDensityOpExtend.toPosSemidefOp)
      = fidelityGen ρ σ := by
  simpa [fidelityGen, Quantum.Metrics.scalarBlockPosSemidefOp,
    Quantum.Metrics.scalarBlockMatrix, SubDensityOp.toDensityOpExtend,
    SubDensityOp.extendOp, SubDensityOp.defectBlock, SubDensityOp.defect] using
      Quantum.Metrics.fidelity_scalarBlock
        ρ.toPosSemidefOp σ.toPosSemidefOp
        (1 - ρ.trace) (1 - σ.trace)
        ρ.one_sub_trace_nonneg σ.one_sub_trace_nonneg

/-- Difference of `defectBlock`s is a `1 × 1` diagonal scalar. -/
lemma SubDensityOp.defectBlock_sub {n : ℕ} (ρ σ : SubDensityOp n) :
    ρ.defectBlock - σ.defectBlock =
      Matrix.diagonal (fun _ : Fin 1 => (((σ.trace - ρ.trace : ℝ) : ℂ))) := by
  unfold SubDensityOp.defectBlock SubDensityOp.defect
  funext i j
  fin_cases i; fin_cases j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Matrix.diagonal_apply_eq]
  push_cast; ring

/-- Difference of the block-diagonal extensions is the reindex of a
    `fromBlocks` with a scalar `(σ.trace − ρ.trace)` in the bottom-right
    `1 × 1` block. -/
lemma SubDensityOp.extendOp_sub {n : ℕ} (ρ σ : SubDensityOp n) :
    ρ.extendOp - σ.extendOp =
      ((Matrix.fromBlocks (ρ.toOp - σ.toOp)
          (0 : Matrix (Fin n) (Fin 1) ℂ)
          (0 : Matrix (Fin 1) (Fin n) ℂ)
          (Matrix.diagonal
            (fun _ : Fin 1 => (((σ.trace - ρ.trace : ℝ) : ℂ))))).reindex
        finSumFinEquiv finSumFinEquiv) := by
  -- Pointwise: split by the Fin (n+1) index via finSumFinEquiv.
  have hdef := ρ.defectBlock_sub σ
  ext i j
  unfold SubDensityOp.extendOp
  simp only [Matrix.sub_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases h_i : finSumFinEquiv.symm i with a | a
  · rcases h_j : finSumFinEquiv.symm j with b | b
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.sub_apply]
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, sub_zero]
  · rcases h_j : finSumFinEquiv.symm j with b | b
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, sub_zero]
    · -- (inr, inr): bottom-right scalar-diagonal block diff.
      simp only [Matrix.fromBlocks_apply₂₂]
      exact congrFun (congrFun hdef a) b

end InfoTheory.SmoothMinEntropy

namespace Quantum.Metrics

/-- The trace norm of a block with a real `1 × 1` scalar block adds `|c|`. -/
lemma traceNorm_fromBlocks_scalar_abs {n : ℕ} [NeZero n] (M : Op n) (c : ℝ) :
    Quantum.Metrics.traceNorm
      ((Matrix.fromBlocks M
          (0 : Matrix (Fin n) (Fin 1) ℂ)
          (0 : Matrix (Fin 1) (Fin n) ℂ)
          (Matrix.diagonal (fun _ : Fin 1 => (c : ℂ)))).reindex
        finSumFinEquiv finSumFinEquiv) =
      Quantum.Metrics.traceNorm M + |c| := by
  rcases le_or_gt 0 c with hc | hc
  · rw [Quantum.Metrics.traceNorm_fromBlocks_scalar M c hc, abs_of_nonneg hc]
  · have hc' : 0 ≤ -c := by linarith
    have hneg :
        ((Matrix.fromBlocks M
            (0 : Matrix (Fin n) (Fin 1) ℂ)
            (0 : Matrix (Fin 1) (Fin n) ℂ)
            (Matrix.diagonal (fun _ : Fin 1 => (c : ℂ)))).reindex
          finSumFinEquiv finSumFinEquiv) =
        -((Matrix.fromBlocks (-M)
            (0 : Matrix (Fin n) (Fin 1) ℂ)
            (0 : Matrix (Fin 1) (Fin n) ℂ)
            (Matrix.diagonal (fun _ : Fin 1 => ((-c : ℝ) : ℂ)))).reindex
          finSumFinEquiv finSumFinEquiv) := by
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply]
      rcases finSumFinEquiv.symm i with a | a
      · rcases finSumFinEquiv.symm j with b | b
        · simp only [Matrix.fromBlocks_apply₁₁, Matrix.neg_apply, neg_neg]
        · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, neg_zero]
      · rcases finSumFinEquiv.symm j with b | b
        · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, neg_zero]
        · simp only [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
          by_cases h : a = b
          · simp only [h, if_true]
            push_cast
            ring
          · simp [h]
    rw [hneg, Quantum.Metrics.traceNorm_neg,
      Quantum.Metrics.traceNorm_fromBlocks_scalar (-M) (-c) hc',
      Quantum.Metrics.traceNorm_neg M, abs_of_neg hc]

end Quantum.Metrics

namespace InfoTheory.SmoothMinEntropy

/-- The trace norm of the difference of two extensions is the original trace norm
plus the absolute trace defect. -/
lemma SubDensityOp.extendOp_sub_traceNorm {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    Quantum.Metrics.traceNorm (ρ.extendOp - σ.extendOp) =
      Quantum.Metrics.traceNorm (ρ.toOp - σ.toOp) + |σ.trace - ρ.trace| := by
  rw [ρ.extendOp_sub σ]
  exact Quantum.Metrics.traceNorm_fromBlocks_scalar_abs
    (ρ.toOp - σ.toOp) (σ.trace - ρ.trace)

/-- Block-diagonal trace-distance identity:

    `D(ρ ⊕ (1 - tr ρ), σ ⊕ (1 - tr σ))
        = ½‖ρ - σ‖₁ + ½|tr ρ - tr σ|
        = traceDistanceGen ρ σ`. -/
lemma toDensityOpExtend_traceDistance {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    Quantum.Metrics.traceDistance ρ.toDensityOpExtend.toOp σ.toDensityOpExtend.toOp
      = Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp := by
  unfold Quantum.Metrics.traceDistance Quantum.Metrics.traceDistanceGen
  rw [show ρ.toDensityOpExtend.toOp - σ.toDensityOpExtend.toOp =
      ρ.extendOp - σ.extendOp from rfl, ρ.extendOp_sub_traceNorm σ]
  have htr : (ρ.toOp.trace - σ.toOp.trace).re = ρ.trace - σ.trace := by
    rw [ρ.trace_complex_eq, σ.trace_complex_eq]
    simp
  rw [htr, abs_sub_comm σ.trace ρ.trace]
  ring

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
