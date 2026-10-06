import QCryptLean.Quantum.Metrics.RectangularPolar
import QCryptLean.Quantum.Matrix.RectangularGramIsometry

/-!
# Rectangular Coisometry Transport — live-purification branch transfer

This module transports rectangular ket witnesses along right coisometries.  It
is used to move a same-ancilla purification witness onto a larger fixed
reference system while preserving the `B`-partial trace and the source-target
overlap.

## Main definitions
This file introduces no new definitions.

## Main statements
- `Quantum.Metrics.RectangularCoisometryTransport.exists_transport_right_coisometry`:
  coisometric transport preserving partial traces and complex overlap.
- `Quantum.Metrics.RectangularCoisometryTransport.exists_transport_right_coisometry_re`:
  real-part version of the coisometric transport theorem.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix ComplexConjugate

noncomputable section

namespace Quantum.Metrics.RectangularCoisometryTransport

/-- Transport a target ket along a right coisometry preserving the source
rectangular matrix.

If `ψ` is obtained from `χ` by right multiplication with a coisometry `W`, then
right multiplying a target branch `φ₀` by the same `W` preserves its `B`-partial
trace and preserves the complex overlap with the transported source. -/
theorem exists_transport_right_coisometry
    {d r anc : ℕ}
    (χ : Ket (d * r)) (ψ : Ket (d * anc)) (φ₀ : Ket (d * r))
    (W : Matrix (Fin r) (Fin anc) ℂ)
    (hW : W * W.conjTranspose = (1 : Op r))
    (hψ : RectangularPolar.ketVecMatrix ψ =
      RectangularPolar.ketVecMatrix χ * W) :
    ∃ φ : Ket (d * anc),
      partialTraceB (φ * φ.dag) = partialTraceB (φ₀ * φ₀.dag) ∧
      (ψ.dag * φ : ℂ) = (χ.dag * φ₀ : ℂ) := by
  let Mχ : Matrix (Fin d) (Fin r) ℂ := RectangularPolar.ketVecMatrix χ
  let Mφ : Matrix (Fin d) (Fin r) ℂ := RectangularPolar.ketVecMatrix φ₀
  let φ : Ket (d * anc) := RectangularPolar.ketOfVecMatrix (Mφ * W)
  refine ⟨φ, ?_, ?_⟩
  · calc
      partialTraceB (φ * φ.dag)
          = (Mφ * W) * (Mφ * W).conjTranspose := by
              simpa [φ] using
                RectangularPolar.partialTraceB_ketOfVecMatrix (Mφ * W)
      _ = Mφ * Mφ.conjTranspose :=
              Matrix.mul_coisometry_mul_conjTranspose Mφ W hW
      _ = partialTraceB (φ₀ * φ₀.dag) := by
              simpa [Mφ] using
                (RectangularPolar.ketVecMatrix_mul_conjTranspose_eq_partialTraceB φ₀)
  · calc
      (ψ.dag * φ : ℂ)
          = ((RectangularPolar.ketVecMatrix ψ).conjTranspose * (Mφ * W)).trace := by
              simpa [φ] using
                RectangularPolar.dag_mul_ketOfVecMatrix_eq_trace ψ (Mφ * W)
      _ = (((Mχ * W).conjTranspose * (Mφ * W)).trace) := by
              rw [hψ]
      _ = (Mχ.conjTranspose * Mφ).trace :=
              Matrix.trace_conjTranspose_mul_right_coisometry Mχ Mφ W hW
      _ = (χ.dag * φ₀ : ℂ) := by
              symm
              simpa [Mχ, Mφ] using
                RectangularPolar.dag_mul_eq_trace_vecMatrix_mul χ φ₀

/-- Real-part version of `exists_transport_right_coisometry`. -/
theorem exists_transport_right_coisometry_re
    {d r anc : ℕ}
    (χ : Ket (d * r)) (ψ : Ket (d * anc)) (φ₀ : Ket (d * r))
    (W : Matrix (Fin r) (Fin anc) ℂ)
    (hW : W * W.conjTranspose = (1 : Op r))
    (hψ : RectangularPolar.ketVecMatrix ψ =
      RectangularPolar.ketVecMatrix χ * W) :
    ∃ φ : Ket (d * anc),
      partialTraceB (φ * φ.dag) = partialTraceB (φ₀ * φ₀.dag) ∧
      (ψ.dag * φ : ℂ).re = (χ.dag * φ₀ : ℂ).re := by
  obtain ⟨φ, hφ, hoverlap⟩ :=
    exists_transport_right_coisometry χ ψ φ₀ W hW hψ
  exact ⟨φ, hφ, congrArg Complex.re hoverlap⟩

end Quantum.Metrics.RectangularCoisometryTransport

end -- noncomputable section
