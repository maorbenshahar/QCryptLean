import QCryptLean.Math.Probability.Bhattacharyya
import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.Quantum.Metrics.TraceNorm.FidelitySymm
import QCryptLean.Quantum.Metrics.FidelityScaling
import QCryptLean.Quantum.Metrics.FidelityPartialTraceMonotone
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Sub-Normalized Density Operators and Generalized Fidelity

Sub-normalized states S•(A) = {ρ : ρ ≥ 0, tr ρ ≤ 1} and the generalized fidelity
for such states, following Tomamichel 2016.

## Main definitions
- `SubDensityOp`: PSD operator with trace ≤ 1 (Tomamichel §2.3.2, eq. 2.21)
- `SubDensityOp.trace`: real-valued trace
- `SubDensityOp.partialTraceB`: partial trace over a right tensor factor
- `SubDensityOp.transpose`: transpose of a sub-normalized density operator
- `SubDensityOp.unitaryConjugate`: unitary conjugation `ρ ↦ V · ρ · V†`
- `SubDensityOp.toPosSemidefOp`: coercion to `PosSemidefOp`
- `fidelityGen`: generalized fidelity for sub-normalized states (Tomamichel §3.3.1)

## Main statements
- `DensityOp.toSubDensityOp`: every normalized density operator is sub-normalized
- `SubDensityOp.trace_nonneg`: traces of sub-normalized operators are nonneg
- `SubDensityOp.trace_complex_eq`: complex trace equals the real trace coerced to `ℂ`
- `SubDensityOp.partialTraceB_toPosSemidefOp`: partial trace commutes with coercion
- `SubDensityOp.trace_transpose`: transposition preserves trace
- `fidelityGen_nonneg`: generalized fidelity is nonneg
- `fidelityGen_symm`: generalized fidelity is symmetric
- `SubDensityOp.fidelity_eq_of_fidelityGen_eq_of_trace_eq`: equal generalized
  fidelities with matching traces have equal ordinary fidelities
- `SubDensityOp.fidelityGen_le_fidelityGen_partialTraceB`: generalized fidelity is monotone
  under tracing out a right tensor factor
- `fidelity_sq_le_trace_mul_trace`: F(ρ,σ)² ≤ tr ρ · tr σ
- `fidelityGen_sq_le_one`: F*(ρ,σ)² ≤ 1 (needed for purified distance)
- `fidelityGen_le_one`: F*(ρ,σ) ≤ 1
- `fidelityGen_normalized_eq`: for normalized states, F* coincides with F
-/

open Quantum.Operators Matrix
open scoped ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## Sub-Normalized Density Operators

Tomamichel 2016, §2.3.2 (eq. 2.21):
  S•(A) := {ρ ∈ T(A) : ρ ≥ 0 ∧ Tr(ρ) ≤ 1}
-/

/-- A sub-normalized density operator on an n-dimensional Hilbert space.

    Tomamichel 2016, eq. 2.21: S•(A) = {ρ : ρ ≥ 0, Tr(ρ) ≤ 1}. -/
structure SubDensityOp (n : ℕ) extends PosSemidefOp n where
  /-- The trace is at most 1 -/
  trace_le_one : toOp.trace.re ≤ 1

@[ext]
theorem SubDensityOp.ext {n : ℕ} {ρ σ : SubDensityOp n} (h : ρ.toOp = σ.toOp) : ρ = σ := by
  cases ρ; cases σ
  simp only [SubDensityOp.mk.injEq]
  apply PosSemidefOp.ext
  exact h

instance {n : ℕ} : Coe (SubDensityOp n) (PosSemidefOp n) where
  coe := SubDensityOp.toPosSemidefOp

instance {n : ℕ} : Coe (SubDensityOp n) (HermitianOp n) where
  coe ρ := ρ.toHermitianOp

instance {n : ℕ} : Coe (SubDensityOp n) (Op n) where
  coe ρ := ρ.toOp

/-- The real-valued trace of a sub-normalized operator. -/
def SubDensityOp.trace {n : ℕ} (ρ : SubDensityOp n) : ℝ :=
  ρ.toOp.trace.re

/-- The trace is the real part of the underlying operator trace. -/
lemma SubDensityOp.trace_def {n : ℕ} (ρ : SubDensityOp n) :
    ρ.trace = ρ.toOp.trace.re := rfl

/-- `Matrix.reindex e e` of a sub-density operator along an equivalence `e : Fin n ≃ Fin m` of equal
cardinality; again sub-normalized (reindex by one equivalence on rows and columns is unitary
conjugation by a permutation). -/
noncomputable def SubDensityOp.reindexHetero {n m : ℕ} (e : Fin n ≃ Fin m)
    (ρ : SubDensityOp n) : SubDensityOp m where
  toOp := Matrix.reindex e e ρ.toOp
  isHermitian :=
    ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).reindex e).isHermitian
  pos_semidef :=
    posSemidef_re_quadraticForm_nonneg
      ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).reindex e)
  trace_le_one := by
    rw [Matrix.trace_reindex_self]
    exact ρ.trace_le_one

@[simp]
lemma SubDensityOp.reindexHetero_toOp {n m : ℕ} (e : Fin n ≃ Fin m) (ρ : SubDensityOp n) :
    (SubDensityOp.reindexHetero e ρ).toOp = Matrix.reindex e e ρ.toOp :=
  rfl

/-- A heterogeneous reindex is a permutation conjugation, hence trace-preserving. -/
@[simp]
lemma SubDensityOp.reindexHetero_trace {n m : ℕ} (e : Fin n ≃ Fin m) (ρ : SubDensityOp n) :
    (SubDensityOp.reindexHetero e ρ).trace = ρ.trace := by
  unfold SubDensityOp.trace
  rw [SubDensityOp.reindexHetero_toOp, Matrix.trace_reindex_self]

/-- The trace of a sub-normalized operator is nonneg.

    For PSD matrices, the trace equals the sum of eigenvalues, all nonneg. -/
theorem SubDensityOp.trace_nonneg {n : ℕ} (ρ : SubDensityOp n) : 0 ≤ ρ.trace := by
  unfold SubDensityOp.trace
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ =>
    Quantum.Operators.psd_diag_re_nonneg ρ.toOp
      (Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp) i

/-- The trace of a sub-normalized operator is in [0, 1]. -/
theorem SubDensityOp.trace_mem_unit_interval {n : ℕ} (ρ : SubDensityOp n) :
    ρ.trace ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ρ.trace_nonneg, ρ.trace_le_one⟩

/-- A sub-density operator's complex trace is its real-valued trace. -/
lemma SubDensityOp.trace_complex_eq {n : ℕ} (σ : SubDensityOp n) :
    σ.toOp.trace = (σ.trace : ℂ) := by
  apply Complex.ext
  · simp [SubDensityOp.trace]
  · have hpsd : Matrix.PosSemidef σ.toOp :=
      Quantum.Operators.posSemidefOp_implies_mathlib σ.toPosSemidefOp
    simpa using (hpsd.trace_nonneg.2).symm

/-- For sub-normalized operators, 1 - trace ≥ 0. -/
lemma SubDensityOp.one_sub_trace_nonneg {n : ℕ} (ρ : SubDensityOp n) :
    0 ≤ 1 - ρ.trace :=
  sub_nonneg.mpr ρ.trace_le_one

/-!
## Partial Trace
-/

/-- Partial trace over the right tensor factor of a sub-normalized operator. -/
def SubDensityOp.partialTraceB {n m : ℕ} (ρ : SubDensityOp (n * m)) :
    SubDensityOp n where
  toOp := Quantum.TensorProducts.partialTraceB ρ.toOp
  isHermitian :=
    Quantum.TensorProducts.partialTraceB_hermitian ρ.toOp ρ.isHermitian
  pos_semidef :=
    Quantum.TensorProducts.partialTraceB_posSemidef ρ.toPosSemidefOp
  trace_le_one := by
    rw [Quantum.TensorProducts.trace_partialTraceB]
    exact ρ.trace_le_one

@[simp]
lemma SubDensityOp.partialTraceB_toOp {n m : ℕ} (ρ : SubDensityOp (n * m)) :
    ρ.partialTraceB.toOp = Quantum.TensorProducts.partialTraceB ρ.toOp :=
  rfl

/-- Partial trace commutes with coercion from sub-density operators to PSD operators. -/
@[simp]
lemma SubDensityOp.partialTraceB_toPosSemidefOp {dE dR : ℕ}
    (ρ : SubDensityOp (dE * dR)) :
    ρ.partialTraceB.toPosSemidefOp = ρ.toPosSemidefOp.partialTraceB := by
  apply PosSemidefOp.ext
  rfl

/-- If the underlying operator of a sub-normalized density operator on `n * m` is
positive-definite, then so is its partial trace over the (nonempty) right factor:
the diagonal block sum of a PosDef operator is PosDef. -/
lemma SubDensityOp.partialTraceB_toOp_posDef {n m : ℕ} [NeZero m]
    {ρ : SubDensityOp (n * m)} (hρ : ρ.toOp.PosDef) :
    ρ.partialTraceB.toOp.PosDef := by
  rw [SubDensityOp.partialTraceB_toOp]
  exact Quantum.TensorProducts.partialTraceB_posDef hρ

@[simp]
lemma SubDensityOp.trace_partialTraceB {n m : ℕ} (ρ : SubDensityOp (n * m)) :
    ρ.partialTraceB.trace = ρ.trace := by
  unfold SubDensityOp.trace SubDensityOp.partialTraceB
  rw [Quantum.TensorProducts.trace_partialTraceB]

/-!
## Transpose

The transpose operation is used by the CQ conditional max-entropy duality.
-/

/-- For Hermitian `A`, `star (quadraticForm Aᵀ v) = quadraticForm A (star v)`.

The Hermitian identity `A j i = star (A i j)` (i.e. `star (A j i) = A i j`) converts
the star-of-transpose sum `∑_{i,j} v i * star (A j i) * star (v j)` directly
to the Hadamard-basis form `∑_{i,j} v i * A i j * star (v j)`. -/
private lemma quadraticForm_transpose_star_eq {n : ℕ} (A : Op n)
    (hA : A.IsHermitian) (v : Fin n → ℂ) :
    star (quadraticForm A.transpose v) = quadraticForm A (star v) := by
  have hHerm : ∀ i j : Fin n, A j i = star (A i j) := fun i j => by
    have h := congr_fun (congr_fun hA j) i
    simp only [Matrix.conjTranspose_apply] at h
    exact h.symm
  unfold quadraticForm
  simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct, Pi.star_apply,
    star_sum, star_mul', star_star, Finset.mul_sum]
  congr 1; ext i; congr 1; ext j
  have hstar : star (A j i) = A i j := by
    have := congr_arg star (hHerm i j)
    simp only [star_star] at this
    exact this
  rw [hstar]

/-- For Hermitian `A`, `Re(quadraticForm Aᵀ v) = Re(quadraticForm A (star v))`.

The two values are complex conjugates (for Hermitian A), hence equal real parts. -/
private lemma quadraticForm_transpose_re {n : ℕ} (A : Op n)
    (hA : A.IsHermitian) (v : Fin n → ℂ) :
    (quadraticForm A.transpose v).re = (quadraticForm A (star v)).re := by
  have h := quadraticForm_transpose_star_eq A hA v
  simpa using congr_arg Complex.re h

/-- The transpose of a `SubDensityOp n`.

For a sub-density operator `σ : SubDensityOp n` with matrix `A`, the transpose is
the sub-density operator with matrix `Aᵀ`.

Since `A` is Hermitian and PSD:
- `Aᵀ` is Hermitian: `Matrix.IsHermitian.transpose` (Mathlib).
- `Aᵀ` is PSD: `quadraticForm_transpose_re` reduces to `σ.pos_semidef (star v) ≥ 0`.
- `Tr(Aᵀ) = Tr(A)`: `Matrix.trace_transpose`.
- `Tr(Aᵀ) ≤ 1`: inherited from `σ.trace_le_one`. -/
def SubDensityOp.transpose {n : ℕ} (σ : SubDensityOp n) : SubDensityOp n where
  toOp := σ.toOp.transpose
  isHermitian := σ.isHermitian.transpose
  pos_semidef := fun v => by
    rw [quadraticForm_transpose_re σ.toOp σ.isHermitian v]
    exact σ.toPosSemidefOp.pos_semidef (star v)
  trace_le_one := by
    simp only [Matrix.trace_transpose]
    exact σ.trace_le_one

/-- The trace of a transposed sub-density operator equals the original trace.

Proof: `Matrix.trace_transpose` gives `Tr(Aᵀ) = Tr(A)`. -/
lemma SubDensityOp.trace_transpose {n : ℕ} (σ : SubDensityOp n) :
    σ.transpose.trace = σ.trace := by
  unfold SubDensityOp.trace SubDensityOp.transpose
  simp [Matrix.trace_transpose]

/-- The trace is real-linear: scaling a matrix by a real scalar scales the real
trace, `Re(tr(c • M)) = c · Re(tr M)`. -/
lemma trace_real_smul_re {n : ℕ} (c : ℝ) (M : Op n) :
    (((c : ℂ) • M).trace).re = c * M.trace.re := by
  rw [Matrix.trace_smul]
  simp [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- Scale a sub-normalized operator by a nonneg real scalar `c ≤ 1`.

    Result remains sub-normalized: `(ρ.smul c).trace = c · ρ.trace ≤ c ≤ 1`. -/
def SubDensityOp.smul {n : ℕ} (ρ : SubDensityOp n) (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1)
    : SubDensityOp n where
  toOp := (c : ℂ) • ρ.toOp
  isHermitian :=
    ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).smul
      (RCLike.ofReal_nonneg.mpr hc_nn)).isHermitian
  pos_semidef := fun v =>
    posSemidef_re_quadraticForm_nonneg
      ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).smul
        (RCLike.ofReal_nonneg.mpr hc_nn)) v
  trace_le_one := by
    rw [trace_real_smul_re]
    calc c * ρ.toOp.trace.re
        ≤ c * 1 := mul_le_mul_of_nonneg_left ρ.trace_le_one hc_nn
      _ = c := mul_one c
      _ ≤ 1 := hc_le

/-- A nonnegative real multiple of a sub-density operator is Hermitian. -/
lemma SubDensityOp.toOp_smul_isHermitian {n : ℕ} (ρ : SubDensityOp n)
    {c : ℝ} (hc : 0 ≤ c) :
    (((c : ℂ) • ρ.toOp) : Op n).IsHermitian := by
  have hρ_psd : ρ.toOp.PosSemidef :=
    posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  exact (Matrix.PosSemidef.smul hρ_psd (RCLike.ofReal_nonneg.mpr hc)).isHermitian

/-- The trace of a scaled sub-density operator is the scaled trace. -/
lemma SubDensityOp.smul_trace {n : ℕ} (ρ : SubDensityOp n)
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le : c ≤ 1) :
    (ρ.smul c hc_nn hc_le).trace = c * ρ.trace := by
  unfold SubDensityOp.trace SubDensityOp.smul
  exact trace_real_smul_re c ρ.toOp

/-- Every normalized density operator is a sub-normalized operator. -/
def DensityOp.toSubDensityOp {n : ℕ} (ρ : DensityOp n) : SubDensityOp n where
  toOp := ρ.toOp
  isHermitian := ρ.toPosSemidefOp.toHermitianOp.isHermitian
  pos_semidef := ρ.toPosSemidefOp.pos_semidef
  trace_le_one := by
    rw [ρ.trace_one, Complex.one_re]

/-- The trace of `toSubDensityOp ρ` equals 1. -/
lemma toSubDensityOp_trace {n : ℕ} (ρ : DensityOp n) :
    (DensityOp.toSubDensityOp ρ).trace = 1 := by
  change ρ.toOp.trace.re = 1
  rw [ρ.trace_one, Complex.one_re]

/-- Conjugate a sub-density operator by a unitary `V`:
    `ρ ↦ V · ρ · V†`. The result is again sub-normalized because:
    * conjugation by any matrix preserves positive semidefiniteness
      (`Matrix.PosSemidef.mul_mul_conjTranspose_same`);
    * Hermiticity follows from PSD;
    * `tr(V · ρ · V†) = tr(V† · V · ρ) = tr(ρ) ≤ 1` via `V† · V = 1`. -/
noncomputable def SubDensityOp.unitaryConjugate {n : ℕ} (ρ : SubDensityOp n)
    (V : UnitaryOp n) : SubDensityOp n where
  toOp := V.toOp * ρ.toOp * V.toOp.conjTranspose
  isHermitian :=
    ((posSemidefOp_implies_mathlib ρ.toPosSemidefOp).mul_mul_conjTranspose_same
      V.toOp).isHermitian
  pos_semidef := by
    intro v
    have hpsd_conj :
        Matrix.PosSemidef (V.toOp * ρ.toOp * V.toOp.conjTranspose) :=
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).mul_mul_conjTranspose_same V.toOp
    exact posSemidef_re_quadraticForm_nonneg hpsd_conj v
  trace_le_one := by
    have htr : (V.toOp * ρ.toOp * V.toOp.conjTranspose).trace = ρ.toOp.trace := by
      rw [Matrix.trace_mul_cycle, V.unitary_left, Matrix.one_mul]
    change (V.toOp * ρ.toOp * V.toOp.conjTranspose).trace.re ≤ 1
    rw [htr]
    exact ρ.trace_le_one

/-- The real-valued trace of a sub-density operator is preserved under
unitary conjugation: `tr(V · ρ · V†) = tr(ρ)`. -/
lemma SubDensityOp.unitaryConjugate_trace {n : ℕ} (ρ : SubDensityOp n)
    (V : UnitaryOp n) :
    (ρ.unitaryConjugate V).trace = ρ.trace := by
  change (V.toOp * ρ.toOp * V.toOp.conjTranspose).trace.re = ρ.toOp.trace.re
  congr 1
  rw [Matrix.trace_mul_cycle, V.unitary_left, Matrix.one_mul]

/-- The zero operator is sub-normalized. -/
instance {n : ℕ} : Zero (SubDensityOp n) where
  zero := {
    toOp := 0
    isHermitian := by simp [Matrix.IsHermitian]
    pos_semidef := by
      intro x
      simp [quadraticForm, Matrix.zero_mulVec]
    trace_le_one := by simp
  }

/-!
## Generalized Fidelity

Tomamichel 2016, §3.3.1:
  F*(ρ, σ) := F(ρ, σ) + √((1 - tr ρ)(1 - tr σ))

where F(ρ, σ) = Tr√(√ρ σ √ρ) is the standard Uhlmann fidelity.
-/

/-- Generalized fidelity for sub-normalized operators.

    Tomamichel 2016, §3.3.1:
      F*(ρ, σ) := F(ρ, σ) + √((1 - tr ρ)(1 - tr σ))

    The correction term √((1-trρ)(1-trσ)) accounts for the "missing weight"
    in sub-normalized states. When ρ and σ are normalized, tr ρ = tr σ = 1
    and F*(ρ,σ) = F(ρ,σ). -/
noncomputable def fidelityGen {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) : ℝ :=
  Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp +
    Real.sqrt ((1 - ρ.trace) * (1 - σ.trace))

/-- Generalized fidelity is nonneg. -/
theorem fidelityGen_nonneg {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    0 ≤ fidelityGen ρ σ := by
  unfold fidelityGen
  apply add_nonneg
  · exact Quantum.Metrics.fidelity_nonneg_posSemidefOp ρ.toPosSemidefOp σ.toPosSemidefOp
  · exact Real.sqrt_nonneg _

/-- Generalized fidelity is symmetric. -/
theorem fidelityGen_symm {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    fidelityGen ρ σ = fidelityGen σ ρ := by
  unfold fidelityGen
  congr 1
  · exact Quantum.Metrics.fidelity_comm ρ.toPosSemidefOp σ.toPosSemidefOp
  · rw [mul_comm]

/-- Equal generalized fidelities with matching traces have equal ordinary
Uhlmann fidelities. -/
lemma SubDensityOp.fidelity_eq_of_fidelityGen_eq_of_trace_eq
    {n m : ℕ} [NeZero n] [NeZero m]
    {ρ σ : SubDensityOp n} {τ υ : SubDensityOp m}
    (hfid : fidelityGen ρ σ = fidelityGen τ υ)
    (hρ : ρ.trace = τ.trace) (hσ : σ.trace = υ.trace) :
    Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp =
      Quantum.Metrics.fidelity τ.toPosSemidefOp υ.toPosSemidefOp := by
  unfold fidelityGen at hfid
  have hcorr :
      Real.sqrt ((1 - ρ.trace) * (1 - σ.trace)) =
        Real.sqrt ((1 - τ.trace) * (1 - υ.trace)) := by
    rw [hρ, hσ]
  linarith

/-- Generalized fidelity of sub-density operators is monotone under tracing out
a right tensor factor. -/
theorem SubDensityOp.fidelityGen_le_fidelityGen_partialTraceB
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (ρ σ : SubDensityOp (dE * dR)) :
    fidelityGen ρ σ ≤ fidelityGen ρ.partialTraceB σ.partialTraceB := by
  have hF :
      Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp ≤
        Quantum.Metrics.fidelity
          ρ.partialTraceB.toPosSemidefOp
          σ.partialTraceB.toPosSemidefOp := by
    simpa only [SubDensityOp.partialTraceB_toPosSemidefOp] using
      Quantum.Metrics.fidelity_le_fidelity_partialTraceB
        ρ.toPosSemidefOp σ.toPosSemidefOp
  unfold fidelityGen
  rw [SubDensityOp.trace_partialTraceB ρ, SubDensityOp.trace_partialTraceB σ]
  exact add_le_add hF le_rfl

/-- **Sub-normalized Uhlmann fidelity bound**: for sub-normalized density operators
    `ρ, σ`, the square of the Uhlmann fidelity is bounded by the product of their
    traces, `F(ρ, σ)^2 ≤ tr(ρ) · tr(σ)`. -/
theorem fidelity_sq_le_trace_mul_trace {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp ^ 2 ≤
      ρ.trace * σ.trace := by
  set F := Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp with hF_def
  have hF_nn : 0 ≤ F :=
    Quantum.Metrics.fidelity_nonneg_posSemidefOp ρ.toPosSemidefOp σ.toPosSemidefOp
  have h_bound :
      F ≤ Real.sqrt ((Matrix.trace ρ.toPosSemidefOp.toOp).re *
                      (Matrix.trace σ.toPosSemidefOp.toOp).re) :=
    Quantum.Metrics.fidelity_le_sqrt_trace_mul_trace ρ.toPosSemidefOp σ.toPosSemidefOp
  have htrace_nn : 0 ≤ ρ.trace * σ.trace :=
    mul_nonneg ρ.trace_nonneg σ.trace_nonneg
  have h_sqrt_eq : Real.sqrt ((Matrix.trace ρ.toPosSemidefOp.toOp).re *
                              (Matrix.trace σ.toPosSemidefOp.toOp).re) =
                   Real.sqrt (ρ.trace * σ.trace) := rfl
  rw [h_sqrt_eq] at h_bound
  have h_sq := sq_le_sq' (by linarith [Real.sqrt_nonneg (ρ.trace * σ.trace)]) h_bound
  rwa [Real.sq_sqrt htrace_nn] at h_sq

/-- Generalized fidelity squared is at most 1. This is the key bound needed to
    define the purified distance `P(ρ, σ) = √(1 - F*(ρ, σ)²)`. -/
theorem fidelityGen_sq_le_one {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    fidelityGen ρ σ ^ 2 ≤ 1 := by
  unfold fidelityGen
  set p := ρ.trace
  set q := σ.trace
  set F := Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp
  have hp : p ∈ Set.Icc (0 : ℝ) 1 := ρ.trace_mem_unit_interval
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := σ.trace_mem_unit_interval
  have hF_nn : 0 ≤ F :=
    Quantum.Metrics.fidelity_nonneg_posSemidefOp ρ.toPosSemidefOp σ.toPosSemidefOp
  have hF_sq_le : F ^ 2 ≤ p * q := fidelity_sq_le_trace_mul_trace ρ σ
  have hF_le_sqrt : F ≤ Real.sqrt (p * q) := by
    have hstep := Real.sqrt_le_sqrt hF_sq_le
    rwa [Real.sqrt_sq hF_nn] at hstep
  have hcorr_nn : 0 ≤ Real.sqrt ((1 - p) * (1 - q)) := Real.sqrt_nonneg _
  have hbound : F + Real.sqrt ((1 - p) * (1 - q)) ≤ 1 := by
    have hcs := Real.sqrt_mul_add_sqrt_one_sub_mul_one_sub_le_one hp hq
    linarith
  have hsum_nn : 0 ≤ F + Real.sqrt ((1 - p) * (1 - q)) := add_nonneg hF_nn hcorr_nn
  nlinarith [hbound, hsum_nn]

/-- Generalized fidelity is at most 1. -/
theorem fidelityGen_le_one {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    fidelityGen ρ σ ≤ 1 := by
  nlinarith [fidelityGen_sq_le_one ρ σ, fidelityGen_nonneg ρ σ]

/-- For normalized density operators, generalized fidelity coincides with
    standard Uhlmann fidelity. -/
theorem fidelityGen_normalized_eq {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    fidelityGen (DensityOp.toSubDensityOp ρ) (DensityOp.toSubDensityOp σ) =
    Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
  unfold fidelityGen
  rw [toSubDensityOp_trace, toSubDensityOp_trace]
  simp only [sub_self, mul_zero, Real.sqrt_zero, add_zero]
  congr 1

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
