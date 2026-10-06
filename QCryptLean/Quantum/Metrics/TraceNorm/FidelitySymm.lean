import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.Quantum.Metrics.WatrousFactorization
import QCryptLean.Quantum.Metrics.TraceNormDilation

/-!
# Symmetry of Uhlmann Fidelity on PSD Operators

This module proves symmetry of the Uhlmann fidelity,
`fidelity A B = fidelity B A`, for arbitrary positive semidefinite operators
`A, B : PosSemidefOp n`.

The proof uses the trace-norm identity
  `‖√(X† X)‖₁ = ‖X‖₁`
(`traceNorm_sqrt_conjTranspose_mul_self` from `WatrousFactorization.lean`) together
with the fact that `‖Mᴴ‖₁ = ‖M‖₁` and, for PSD `P`, `‖P‖₁ = Tr(P).re`.

Concretely, set `M := √A · √B`. Then
  `M · Mᴴ = √A · B · √A`  and  `Mᴴ · M = √B · A · √B`
so both sides of the fidelity equation reduce to `‖M‖₁`.

## Main statements

- `fidelity_eq_traceNorm_sqrtProduct`: `F(A, B) = ‖√A · √B‖₁` for PSD operators.
- `fidelity_eq_traceNorm_cfcSqrt_mul`: the density-operator specialization,
  `F(ρ, τ) = ‖√ρ · √τ‖₁` in terms of `CFC.sqrt`.
- `fidelity_comm`: symmetry of the Uhlmann fidelity, `F(A, B) = F(B, A)`.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

variable {n : ℕ}

/-- The conjugate transpose of `√A · √B` is `√B · √A`, since each PSD square
root is Hermitian. -/
private lemma sqrtPosSemidefOp_mul_conjTranspose_eq (A B : PosSemidefOp n) :
    (sqrtPosSemidefOp A * sqrtPosSemidefOp B).conjTranspose =
      sqrtPosSemidefOp B * sqrtPosSemidefOp A := by
  rw [Matrix.conjTranspose_mul,
      (sqrtPosSemidefOp_isHermitian A).eq,
      (sqrtPosSemidefOp_isHermitian B).eq]

/-- `(√A · √B) · (√A · √B)ᴴ = √A · B · √A`. -/
private lemma sqrtPosSemidefOp_mul_self_conjTranspose (A B : PosSemidefOp n) :
    (sqrtPosSemidefOp A * sqrtPosSemidefOp B) *
        (sqrtPosSemidefOp A * sqrtPosSemidefOp B).conjTranspose =
      sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A := by
  rw [sqrtPosSemidefOp_mul_conjTranspose_eq,
      Matrix.mul_assoc (sqrtPosSemidefOp A) (sqrtPosSemidefOp B)
        (sqrtPosSemidefOp B * sqrtPosSemidefOp A),
      ← Matrix.mul_assoc (sqrtPosSemidefOp B) (sqrtPosSemidefOp B)
        (sqrtPosSemidefOp A),
      sqrtPosSemidefOp_sq B,
      ← Matrix.mul_assoc]

/-- `(√A · √B)ᴴ · (√A · √B) = √B · A · √B`. -/
private lemma sqrtPosSemidefOp_conjTranspose_mul_self (A B : PosSemidefOp n) :
    (sqrtPosSemidefOp A * sqrtPosSemidefOp B).conjTranspose *
        (sqrtPosSemidefOp A * sqrtPosSemidefOp B) =
      sqrtPosSemidefOp B * A.toOp * sqrtPosSemidefOp B := by
  rw [sqrtPosSemidefOp_mul_conjTranspose_eq,
      Matrix.mul_assoc (sqrtPosSemidefOp B) (sqrtPosSemidefOp A)
        (sqrtPosSemidefOp A * sqrtPosSemidefOp B),
      ← Matrix.mul_assoc (sqrtPosSemidefOp A) (sqrtPosSemidefOp A)
        (sqrtPosSemidefOp B),
      sqrtPosSemidefOp_sq A,
      ← Matrix.mul_assoc]

/-- **Trace-norm characterization of Uhlmann fidelity** (Watrous Prop. 3.10 /
    Nielsen–Chuang eq. 9.74): `F(A, B) = ‖√A · √B‖₁`. -/
theorem fidelity_eq_traceNorm_sqrtProduct [NeZero n] (A B : PosSemidefOp n) :
    fidelity A B = traceNorm (sqrtPosSemidefOp A * sqrtPosSemidefOp B) := by
  set M : Op n := sqrtPosSemidefOp A * sqrtPosSemidefOp B
  have h_MM : M * M.conjTranspose = sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A :=
    sqrtPosSemidefOp_mul_self_conjTranspose A B
  have h_sqrt_MM_psd : (CFC.sqrt (M * M.conjTranspose)).PosSemidef :=
    (CFC.sqrt_nonneg (a := M * M.conjTranspose)).posSemidef
  unfold fidelity
  rw [show sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A
        = M * M.conjTranspose from h_MM.symm,
      ← Quantum.Channels.traceNorm_posSemidef_eq_trace _ h_sqrt_MM_psd,
      show M * M.conjTranspose
        = M.conjTranspose.conjTranspose * M.conjTranspose from by
        rw [Matrix.conjTranspose_conjTranspose],
      Quantum.Metrics.WatrousFactorization.traceNorm_sqrt_conjTranspose_mul_self,
      traceNorm_conjTranspose]

/-- The Uhlmann fidelity of two density operators equals the trace norm of the
product of their operator square roots. -/
lemma fidelity_eq_traceNorm_cfcSqrt_mul {d : ℕ} [NeZero d] (ρ τ : DensityOp d) :
    fidelity ρ.toPosSemidefOp τ.toPosSemidefOp =
      traceNorm (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp) := by
  have h := fidelity_eq_traceNorm_sqrtProduct ρ.toPosSemidefOp τ.toPosSemidefOp
  simpa [sqrtPosSemidefOp] using h


/-- **Symmetry of the Uhlmann fidelity** on PSD operators:
    `F(A, B) = F(B, A)`. -/
theorem fidelity_comm [NeZero n] (A B : PosSemidefOp n) :
    fidelity A B = fidelity B A := by
  -- M := √A · √B; key identities below.
  set M : Op n := sqrtPosSemidefOp A * sqrtPosSemidefOp B
  have h_MadjM : M.conjTranspose * M = sqrtPosSemidefOp B * A.toOp * sqrtPosSemidefOp B :=
    sqrtPosSemidefOp_conjTranspose_mul_self A B
  have h_sqrt_MadjM_psd : (CFC.sqrt (M.conjTranspose * M)).PosSemidef :=
    (CFC.sqrt_nonneg (a := M.conjTranspose * M)).posSemidef
  -- LHS: fidelity A B = traceNorm M by `fidelity_eq_traceNorm_sqrtProduct`.
  have h_lhs : fidelity A B = traceNorm M := fidelity_eq_traceNorm_sqrtProduct A B
  -- RHS: fidelity B A = traceNorm M
  have h_rhs : fidelity B A = traceNorm M := by
    unfold fidelity
    rw [show sqrtPosSemidefOp B * A.toOp * sqrtPosSemidefOp B
          = M.conjTranspose * M from h_MadjM.symm,
        ← Quantum.Channels.traceNorm_posSemidef_eq_trace _ h_sqrt_MadjM_psd,
        Quantum.Metrics.WatrousFactorization.traceNorm_sqrt_conjTranspose_mul_self]
  rw [h_lhs, h_rhs]

end Quantum.Metrics

end
