import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Projective Conditioning — projector sandwiches and partial-trace bounds

Small finite-dimensional linear-algebra lemmas for conditioning a bipartite
operator by a projector on the first tensor factor and then tracing out that
factor.

## Main definitions

- `projector_sandwich_posSemidefOp`: PSD witness for a projector sandwich.
- `partialTraceA_projector_sandwich_posSemidefOp`: PSD witness after
  conditioning and tracing out the first tensor factor.

## Main statements

- `projector_complement_posSemidef`: the complement of a Hermitian idempotent
  projector is PSD.
- `projector_sandwich_posSemidef`: sandwiching a PSD operator by a Hermitian
  projector is PSD.
- `trace_re_projector_sandwich_le`: a projector sandwich has no larger trace.
- `partialTraceA_projector_sandwich_posSemidef`: conditioned partial trace is PSD.
- `trace_partialTraceA_projector_sandwich_le`: conditioned partial trace has
  trace bounded by the original PSD trace.
- `trace_partialTraceA_projector_sandwich_eq_trace_projector_partialTraceB`:
  the conditioned partial trace equals tracing against the projector on the
  opposite marginal.
-/

open Quantum.Operators Matrix
open scoped ComplexConjugate ComplexOrder BigOperators

noncomputable section

namespace Quantum.TensorProducts

/-- The complement of an idempotent projector is idempotent. -/
lemma projector_complement_idempotent {n : ℕ} {P : Op n}
    (hP_idem : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  rw [sub_mul, one_mul, mul_sub, mul_one, hP_idem, sub_self, sub_zero]

/-- The complement of a Hermitian projector is Hermitian. -/
lemma projector_complement_hermitian {n : ℕ} {P : Op n}
    (hP_herm : P† = P) :
    Matrix.conjTranspose (1 - P) = 1 - P := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm]

/-- The complement of a Hermitian idempotent is positive semidefinite. -/
lemma projector_complement_posSemidef {n : ℕ} (P : Op n)
    (hP_idem : P * P = P) (hP_herm : Pᴴ = P) :
    (1 - P).PosSemidef := by
  have h_comp_herm : (1 - P)ᴴ = 1 - P :=
    projector_complement_hermitian hP_herm
  have h_comp_idem : (1 - P) * (1 - P) = 1 - P :=
    projector_complement_idempotent hP_idem
  rw [show (1 : Op n) - P = (1 - P)ᴴ * (1 - P) from by
    rw [h_comp_herm, h_comp_idem]]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

/-- Sandwiching a Hermitian operator by a Hermitian projector preserves Hermiticity. -/
lemma projector_sandwich_isHermitian {n : ℕ} {P M : Op n}
    (hP_herm : P† = P) (hM_herm : M.IsHermitian) :
    (P * M * P).IsHermitian := by
  unfold Matrix.IsHermitian at hM_herm ⊢
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP_herm, hM_herm]
  simp only [Matrix.mul_assoc]

/-- Sandwiching a positive semidefinite operator by a Hermitian projector is PSD. -/
lemma projector_sandwich_posSemidef {n : ℕ} {P M : Op n}
    (hP_herm : P† = P) (hM_psd : M.PosSemidef) :
    (P * M * P).PosSemidef := by
  have h := hM_psd.conjTranspose_mul_mul_same P
  rwa [hP_herm] at h

/-- The QI `PosSemidefOp` witness for a Hermitian projector sandwich. -/
def projector_sandwich_posSemidefOp {n : ℕ} (P M : Op n)
    (hP_herm : P† = P) (hM_psd : M.PosSemidef) : PosSemidefOp n where
  toOp := P * M * P
  isHermitian := projector_sandwich_isHermitian hP_herm hM_psd.isHermitian.eq
  pos_semidef := Quantum.Operators.posSemidef_re_quadraticForm_nonneg
    (projector_sandwich_posSemidef hP_herm hM_psd)

/-- Quadratic-form nonnegativity for a Hermitian projector sandwich. -/
lemma projector_sandwich_quadraticForm_re_nonneg {n : ℕ} {P M : Op n}
    (hP_herm : P† = P) (hM_psd : M.PosSemidef) :
    ∀ v : Fin n → ℂ, 0 ≤ (quadraticForm (P * M * P) v).re :=
  (projector_sandwich_posSemidefOp P M hP_herm hM_psd).pos_semidef

/-- The trace of an idempotent projector sandwich has only one left projector. -/
lemma trace_projector_sandwich_eq {n : ℕ} {P M : Op n}
    (hP_idem : P * P = P) :
    (P * M * P).trace = (P * M).trace := by
  calc
    (P * M * P).trace = (P * (P * M)).trace := by
      rw [Matrix.trace_mul_comm (P * M) P]
    _ = ((P * P) * M).trace := by rw [Matrix.mul_assoc]
    _ = (P * M).trace := by rw [hP_idem]

/-- The trace of an idempotent projector sandwich has only one right projector. -/
lemma trace_projector_sandwich_eq_trace_mul_right {n : ℕ} {P M : Op n}
    (hP_idem : P * P = P) :
    (P * M * P).trace = (M * P).trace := by
  calc
    (P * M * P).trace = (P * M).trace := trace_projector_sandwich_eq hP_idem
    _ = (M * P).trace := Matrix.trace_mul_comm P M

/-- Trace against the complement of an idempotent projector splits off the sandwich trace. -/
lemma trace_mul_projector_complement_re_eq_sub {n : ℕ} {P M : Op n}
    (hP_idem : P * P = P) :
    (M * (1 - P)).trace.re = M.trace.re - (P * M * P).trace.re := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re,
    ← trace_projector_sandwich_eq_trace_mul_right hP_idem]

/-- A PSD operator has no larger real trace after sandwiching by a projector. -/
lemma trace_re_projector_sandwich_le {n : ℕ} {P M : Op n}
    (hP_idem : P * P = P) (hP_herm : P† = P)
    (hM_psd : M.PosSemidef) :
    (P * M * P).trace.re ≤ M.trace.re := by
  have h_comp_psd : (1 - P).PosSemidef :=
    projector_complement_posSemidef P hP_idem hP_herm
  have h_nonneg : 0 ≤ (M * (1 - P)).trace.re :=
    Quantum.Operators.trace_mul_psd_nonneg M (1 - P) hM_psd h_comp_psd
  have h_split := trace_mul_projector_complement_re_eq_sub (P := P) (M := M) hP_idem
  linarith

/-- Tensoring an idempotent projector with the identity remains idempotent. -/
lemma tensor_projector_one_idempotent {n m : ℕ} {P : Op n}
    (hP_idem : P * P = P) :
    Op.tensor P (1 : Op m) * Op.tensor P (1 : Op m) =
      Op.tensor P (1 : Op m) := by
  rw [Op.tensor_mul, hP_idem, mul_one]

/-- Tensoring a Hermitian projector with the identity remains Hermitian. -/
lemma tensor_projector_one_hermitian {n m : ℕ} {P : Op n}
    (hP_herm : P† = P) :
    (Op.tensor P (1 : Op m))† = Op.tensor P (1 : Op m) := by
  rw [Op.tensor_conjTranspose, hP_herm, Matrix.conjTranspose_one]

/-- Partial trace over `A` preserves Hermiticity of a projector sandwich on `A`. -/
lemma partialTraceA_projector_sandwich_isHermitian {n m : ℕ}
    (P : Op n) (M : Op (n * m))
    (hP_herm : P† = P) (hM_herm : M.IsHermitian) :
    (partialTraceA (Op.tensor P (1 : Op m) * M * Op.tensor P (1 : Op m))).IsHermitian := by
  exact partialTraceA_hermitian _ <|
    projector_sandwich_isHermitian
      (tensor_projector_one_hermitian (m := m) hP_herm) hM_herm

/-- The conditioned partial trace as a QI positive semidefinite operator. -/
def partialTraceA_projector_sandwich_posSemidefOp {n m : ℕ}
    (P : Op n) (M : Op (n * m))
    (hP_herm : P† = P) (hM_psd : M.PosSemidef) : PosSemidefOp m := by
  let PI : Op (n * m) := Op.tensor P (1 : Op m)
  exact PosSemidefOp.partialTraceA
    (projector_sandwich_posSemidefOp PI M
      (by simpa [PI] using tensor_projector_one_hermitian (m := m) hP_herm)
      hM_psd)

/-- The conditioned partial trace of a PSD operator is PSD. -/
lemma partialTraceA_projector_sandwich_posSemidef {n m : ℕ}
    (P : Op n) (M : Op (n * m))
    (hP_herm : P† = P) (hM_psd : M.PosSemidef) :
    (partialTraceA (Op.tensor P (1 : Op m) * M * Op.tensor P (1 : Op m))).PosSemidef := by
  exact posSemidefOp_implies_mathlib
      (partialTraceA_projector_sandwich_posSemidefOp P M hP_herm hM_psd)

/-- Quadratic-form nonnegativity for the conditioned partial trace. -/
lemma partialTraceA_projector_sandwich_quadraticForm_re_nonneg {n m : ℕ}
    (P : Op n) (M : Op (n * m))
    (hP_herm : P† = P) (hM_psd : M.PosSemidef) :
    ∀ v : Fin m → ℂ,
      0 ≤ (quadraticForm
        (partialTraceA (Op.tensor P (1 : Op m) * M * Op.tensor P (1 : Op m))) v).re :=
  Quantum.Operators.posSemidef_re_quadraticForm_nonneg
    (partialTraceA_projector_sandwich_posSemidef P M hP_herm hM_psd)

/-- The conditioned partial trace has trace bounded by the original PSD trace. -/
lemma trace_partialTraceA_projector_sandwich_le {n m : ℕ}
    (P : Op n) (M : Op (n * m))
    (hP_idem : P * P = P) (hP_herm : P† = P)
    (hM_psd : M.PosSemidef) :
    (partialTraceA (Op.tensor P (1 : Op m) * M * Op.tensor P (1 : Op m))).trace.re ≤
      M.trace.re := by
  rw [trace_partialTraceA]
  exact trace_re_projector_sandwich_le
    (tensor_projector_one_idempotent (m := m) hP_idem)
    (tensor_projector_one_hermitian (m := m) hP_herm)
    hM_psd

/-- Trace of a tensor-projector sandwich is trace against `P` after tracing out `B`. -/
lemma trace_tensor_projector_sandwich_eq_trace_projector_partialTraceB
    {n m : ℕ} (P : Op n) (M : Op (n * m))
    (hP_idem : P * P = P) :
    (Op.tensor P (1 : Op m) * M * Op.tensor P (1 : Op m)).trace =
      (P * partialTraceB M).trace := by
  calc
    (Op.tensor P (1 : Op m) * M * Op.tensor P (1 : Op m)).trace
        = (partialTraceB
          (Op.tensor P (1 : Op m) * M * Op.tensor P (1 : Op m))).trace := by
          rw [trace_partialTraceB]
    _ = (P * partialTraceB M * P).trace := by
          rw [partialTraceB_sandwich_tensor_one]
    _ = (P * partialTraceB M).trace := trace_projector_sandwich_eq hP_idem

/-- Trace of the conditioned partial trace equals trace against `P` on `partialTraceB`. -/
lemma trace_partialTraceA_projector_sandwich_eq_trace_projector_partialTraceB
    {n m : ℕ} (P : Op n) (M : Op (n * m))
    (hP_idem : P * P = P) :
    (partialTraceA (Op.tensor P (1 : Op m) * M * Op.tensor P (1 : Op m))).trace =
      (P * partialTraceB M).trace := by
  rw [trace_partialTraceA]
  exact trace_tensor_projector_sandwich_eq_trace_projector_partialTraceB P M hP_idem

end Quantum.TensorProducts

end -- noncomputable section
