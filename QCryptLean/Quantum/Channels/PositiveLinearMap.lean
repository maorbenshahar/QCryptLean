import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# Positive linear maps from quantum operations

Quantum channels and rectangular Kraus conjugations define Mathlib `PositiveLinearMap`s.
Adjoint preservation follows from `map_star` after bundling the scoped matrix instances in
`Matrix.Norms.L2Operator` into `CStarAlgebra`. Positivity uses the order in `MatrixOrder`.
-/

open Quantum.Operators Matrix
open scoped MatrixOrder

noncomputable section

namespace Quantum.Channels

/-- A quantum channel as a positive linear map. -/
def positiveLinearMapOfIsCPTP {p q : ℕ} [NeZero p] [NeZero q] (Θ : Op p →ₗ[ℂ] Op q)
    (h : IsCPTP ⇑Θ) : Op p →ₚ[ℂ] Op q :=
  PositiveLinearMap.mk₀ Θ fun W hW => Matrix.nonneg_iff_posSemidef.mpr
    (cptp_preserves_posSemidef _ h W (Matrix.nonneg_iff_posSemidef.mp hW))

/-- Conjugation by a rectangular matrix as a positive linear map. -/
def matrixConjPositiveLinearMap {p q : ℕ} (N : Matrix (Fin q) (Fin p) ℂ) :
    Op p →ₚ[ℂ] Op q :=
  PositiveLinearMap.mk₀ (krausMapFintype (fun _ : Unit => N)) fun _ hW =>
    Matrix.nonneg_iff_posSemidef.mpr
      (krausMapFintype_posSemidef _ (Matrix.nonneg_iff_posSemidef.mp hW))

end Quantum.Channels
