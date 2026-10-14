import QCryptLean.Math.LinearAlgebra.Matrix.TraceBound
import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-!
# Trace-norm duality, Hölder inequalities, and rectangular purification overlaps

The trace norm of `A` is the maximum of `‖(W * A).trace‖` over the operator-norm unit
ball, attained at a unitary; the two Hölder inequalities for products follow. Only
this file's operator-norm bounds select `Matrix.Norms.L2Operator`, locally; the trace
norm itself is the explicit singular-value function. Positive square roots use matrix
star order. Frobenius instances in importing modules are unchanged.
-/

noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {X R : Type*} [Fintype X] [Fintype R]

/-- `‖(W * A).trace‖` is at most the operator norm of `W` times the trace norm of `A`. -/
theorem norm_trace_mul_le_opNorm_mul_traceNorm [DecidableEq X] (W A : Op X) :
    ‖(W * A).trace‖ ≤ ‖W‖ * traceNorm A := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · simp [Subsingleton.elim W 0, Subsingleton.elim A 0]
  · obtain ⟨U, he⟩ := Matrix.exists_unitary_mul_eq_sqrt_gram A
    have hA : A = U.valᴴ * CFC.sqrt (Aᴴ * A) := by
      rw [← he, ← Matrix.mul_assoc, show U.valᴴ * U.val = 1 from U.property.1,
        Matrix.one_mul]
    have hn : ‖W * U.valᴴ‖ ≤ ‖W‖ := by
      calc
        _ ≤ ‖W‖ * ‖U.valᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖W‖ := by
          rw [Matrix.l2_opNorm_conjTranspose, CStarRing.norm_of_mem_unitary U.property,
            mul_one]
    calc
      ‖(W * A).trace‖ = ‖(W * U.valᴴ * CFC.sqrt (Aᴴ * A)).trace‖ := by
        conv_lhs => rw [hA]
        rw [Matrix.mul_assoc]
      _ ≤ ‖W * U.valᴴ‖ * (CFC.sqrt (Aᴴ * A)).trace.re :=
        (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).norm_trace_mul_le _
      _ ≤ ‖W‖ * traceNorm A := by
        rw [← traceNorm_eq_trace_sqrt]
        exact mul_le_mul_of_nonneg_right hn (traceNorm_nonneg A)

/-- Some unitary `U` makes the trace of `U * A` equal to the trace norm of `A`. -/
theorem exists_unitary_trace_mul_eq_traceNorm [DecidableEq X] (A : Op X) :
    ∃ U ∈ unitaryGroup X ℂ, (U * A).trace = (traceNorm A : ℂ) := by
  obtain ⟨U, hU⟩ := Matrix.exists_unitary_mul_eq_sqrt_gram A
  have hSqrt : (CFC.sqrt (Aᴴ * A)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  refine ⟨U.val, U.property, ?_⟩
  calc
    (U.val * A).trace = (CFC.sqrt (Aᴴ * A)).trace := by rw [hU]
    _ = (traceNorm A : ℂ) := by
      apply Complex.ext
      · simpa using (traceNorm_eq_trace_sqrt A).symm
      · simpa using (Complex.nonneg_iff.mp hSqrt.trace_nonneg).2.symm

/-- The trace norm of `A` is the maximum of `‖(W * A).trace‖` over all `W` of operator norm at
most one; the maximum is attained. -/
theorem isGreatest_norm_trace_mul_traceNorm [DecidableEq X] (A : Op X) :
    IsGreatest ((fun W : Op X => ‖(W * A).trace‖) '' {W : Op X | ‖W‖ ≤ 1})
      (traceNorm A) := by
  obtain ⟨U, hUmem, hUtrace⟩ := exists_unitary_trace_mul_eq_traceNorm A
  have hUnorm : ‖U‖ ≤ 1 := by
    have h1 : ‖(1 : Op X)‖ ≤ 1 := by
      rw [Matrix.cstar_norm_def, map_one]
      exact ContinuousLinearMap.norm_id_le
    have h2 : ‖U‖ * ‖U‖ = ‖(1 : Op X)‖ := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self U, show Uᴴ * U = 1 from
        Matrix.mem_unitaryGroup_iff'.mp hUmem]
    exact (sq_le_sq₀ (norm_nonneg U) zero_le_one).mp
      (by rw [sq, sq, h2, mul_one]; exact h1)
  refine ⟨⟨U, hUnorm, ?_⟩, ?_⟩
  · change ‖(U * A).trace‖ = traceNorm A
    rw [hUtrace, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (traceNorm_nonneg A)]
  · rintro y ⟨W, hW, rfl⟩
    exact (norm_trace_mul_le_opNorm_mul_traceNorm W A).trans
      (mul_le_of_le_one_left (traceNorm_nonneg A) hW)

/-- Hölder's inequality: left multiplication scales the trace norm by at most the operator norm. -/
theorem traceNorm_mul_le_opNorm_mul_traceNorm [DecidableEq X] (A B : Op X) :
    traceNorm (A * B) ≤ ‖A‖ * traceNorm B := by
  have hGreatest := isGreatest_norm_trace_mul_traceNorm (A * B)
  have hUpper : ‖A‖ * traceNorm B ∈
      upperBounds ((fun W : Op X => ‖(W * (A * B)).trace‖) '' {W : Op X | ‖W‖ ≤ 1}) := by
    rintro y ⟨W, hW, rfl⟩
    have hnorm : ‖W * A‖ ≤ ‖A‖ :=
      (Matrix.l2_opNorm_mul W A).trans (mul_le_of_le_one_left (norm_nonneg A) hW)
    calc
      ‖(W * (A * B)).trace‖ = ‖((W * A) * B).trace‖ := by
        rw [Matrix.mul_assoc]
      _ ≤ ‖W * A‖ * traceNorm B := norm_trace_mul_le_opNorm_mul_traceNorm _ _
      _ ≤ ‖A‖ * traceNorm B := mul_le_mul_of_nonneg_right hnorm (traceNorm_nonneg B)
  exact (isLUB_le_iff hGreatest.isLUB).2 hUpper

/-- Hölder's inequality: right multiplication scales the trace norm by at most
the operator norm. -/
theorem traceNorm_mul_le_traceNorm_mul_opNorm [DecidableEq X] (A B : Op X) :
    traceNorm (A * B) ≤ traceNorm A * ‖B‖ := by
  calc
    traceNorm (A * B) = traceNorm (A * B)ᴴ := (traceNorm_conjTranspose (A * B)).symm
    _ = traceNorm (Bᴴ * Aᴴ) := by rw [conjTranspose_mul]
    _ ≤ ‖Bᴴ‖ * traceNorm Aᴴ := traceNorm_mul_le_opNorm_mul_traceNorm Bᴴ Aᴴ
    _ = traceNorm A * ‖B‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, traceNorm_conjTranspose]
      ring

/-- Fidelity is the trace norm of the product of the positive square roots. -/
theorem traceNorm_sqrt_mul_sqrt (A B : PosSemidefOp X) :
    traceNorm (sqrtPosSemidefOp A * sqrtPosSemidefOp B) = fidelity A B := by
  classical
  rw [← traceNorm_conjTranspose, traceNorm_eq_trace_sqrt, conjTranspose_conjTranspose,
    conjTranspose_mul, (isHermitian_sqrtPosSemidefOp A).eq,
    (isHermitian_sqrtPosSemidefOp B).eq]
  rw [Matrix.mul_assoc (sqrtPosSemidefOp A), ← Matrix.mul_assoc (sqrtPosSemidefOp B),
    sqrtPosSemidefOp_mul_self, ← Matrix.mul_assoc]
  rfl

/-- Rectangular purifying matrices have overlap bounded by fidelity of their left Grams. -/
theorem norm_trace_conjTranspose_mul_le_fidelity (A B : Matrix X R ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ fidelity ⟨A * Aᴴ, posSemidef_self_mul_conjTranspose A⟩
      ⟨B * Bᴴ, posSemidef_self_mul_conjTranspose B⟩ := by
  classical
  obtain ⟨U, hA, hU⟩ := Matrix.exists_sqrt_gram_mul_contraction A
  obtain ⟨V, hB, hV⟩ := Matrix.exists_sqrt_gram_mul_contraction B
  let P : PosSemidefOp X := ⟨A * Aᴴ, posSemidef_self_mul_conjTranspose A⟩
  let Q : PosSemidefOp X := ⟨B * Bᴴ, posSemidef_self_mul_conjTranspose B⟩
  have hn : ‖V * Uᴴ‖ ≤ 1 := by
    apply (Matrix.l2_opNorm_mul _ _).trans
    rw [Matrix.l2_opNorm_conjTranspose]
    exact (mul_le_mul_of_nonneg_right hV (norm_nonneg _)).trans (by simpa using hU)
  have he : (Aᴴ * B).trace = (V * Uᴴ *
      (sqrtPosSemidefOp P * sqrtPosSemidefOp Q)).trace := by
    calc
      _ = ((sqrtPosSemidefOp P * U)ᴴ * (sqrtPosSemidefOp Q * V)).trace := by
        conv_lhs => rw [hA, hB]
        rfl
      _ = _ := by
        rw [conjTranspose_mul, (isHermitian_sqrtPosSemidefOp P).eq]
        simp only [← Matrix.mul_assoc]
        rw [Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
  rw [he]
  exact (norm_trace_mul_le_opNorm_mul_traceNorm _ _).trans
    ((mul_le_of_le_one_left (traceNorm_nonneg _) hn).trans_eq (traceNorm_sqrt_mul_sqrt P Q))

/-- Arbitrary finite ancillas obey the purification overlap bound. -/
theorem norm_overlap_le_fidelity (A B : PosSemidefOp X)
    (v w : Ket (X × R)) (hv : partialTraceRight v.projector = A.val)
    (hw : partialTraceRight w.projector = B.val) :
    ‖(v.dag * w : ℂ)‖ ≤ fidelity A B := by
  classical
  let V : Matrix X R ℂ := fun i r => v.vec (i, r)
  let W : Matrix X R ℂ := fun i r => w.vec (i, r)
  have hV : V * Vᴴ = A.val := hv
  have hW : W * Wᴴ = B.val := hw
  have he := norm_trace_conjTranspose_mul_le_fidelity V W
  have hp : (⟨V * Vᴴ, posSemidef_self_mul_conjTranspose V⟩ : PosSemidefOp X) = A :=
    Subtype.ext hV
  have hq : (⟨W * Wᴴ, posSemidef_self_mul_conjTranspose W⟩ : PosSemidefOp X) = B :=
    Subtype.ext hW
  rw [hp, hq, ← Ket.vectorize_inner] at he
  exact he


end Quantum.Metrics
