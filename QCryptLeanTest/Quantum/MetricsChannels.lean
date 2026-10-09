import QCryptLean.Quantum.Channels.CompletelyPositive
import QCryptLean.Quantum.Channels.DiamondInequality
import QCryptLean.Quantum.Channels.Stinespring
import QCryptLean.Quantum.Metrics.Inequality

/-! Regression probes for universes, empty registers, conventions, and instance isolation. -/

noncomputable section

open Quantum.Operators Quantum.Metrics Quantum.Channels

universe u v

variable {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]

example (Φ : Operation X Y) : Op (X × Y) := choiMatrix Φ

example (A B : Op X) : traceDistance A B = (1 / 2) * traceNorm (A - B) := rfl

example (Φ Ψ : Operation X Y) : diamondDist Φ Ψ = (1 / 2) * diamondNorm (Φ - Ψ) := rfl

example (Φ : Operation X Y) :
    diamondNorm Φ = sSup {t : ℝ | ∃ A : Op (X × X), traceNorm A ≤ 1 ∧
      t = traceNorm (mapTensorId Φ X A)} := rfl

example : traceNorm (0 : Op Empty) = 0 := traceNorm_zero

example : diamondNorm (0 : Operation Empty (Fin 2)) = 0 := diamondNorm_zero

example (ρ σ : DensityOp X) :
    1 - fidelity ρ.toPosSemidefOp σ.toPosSemidefOp ≤ traceDistance ρ.toOp σ.toOp :=
  one_sub_fidelity_le_traceDistance ρ σ

example (ρ σ : DensityOp X) :
    traceDistance ρ.toOp σ.toOp ≤ Real.sqrt (1 - fidelitySq ρ.toPosSemidefOp σ.toPosSemidefOp) :=
  traceDistance_le_sqrt_one_sub_fidelitySq ρ σ

example (K : KrausRepresentation X Y Empty) : IsChannel K.toOperation := K.isChannel

example (Φ : Operation X Y) (h : IsChannel Φ) :
    Nonempty (StinespringRepresentation Φ (X × Y)) := h.exists_stinespring

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator in
example [DecidableEq X] [DecidableEq Y] (Φ : Operation X Y) (h : IsCompletelyPositive Φ) :
    ∃ Ψ : CompletelyPositiveMap (Op X) (Op Y), Ψ.toLinearMap = Φ :=
  (isCompletelyPositive_iff_exists_mathlib Φ).mp h

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

-- Importing the CP bridge leaves it possible to use Frobenius statements directly.
example (A : Op X) : ‖A‖ ≤ traceNorm A := frobenius_le_traceNorm A

end Frobenius
