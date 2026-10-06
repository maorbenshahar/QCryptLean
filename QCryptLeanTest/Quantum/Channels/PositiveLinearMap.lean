import QCryptLean.Quantum.Channels.PositiveLinearMap

/-!
# Adjoint preservation for bundled positive quantum maps
-/

open Quantum.Operators Quantum.Channels
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

example {p q : ℕ} [NeZero p] [NeZero q] (Θ : Op p →ₗ[ℂ] Op q)
    (h : IsCPTP ⇑Θ) (W : Op p) :
    positiveLinearMapOfIsCPTP Θ h Wᴴ = (positiveLinearMapOfIsCPTP Θ h W)ᴴ := by
  let : CStarAlgebra (Op p) := {}
  let : CStarAlgebra (Op q) := {}
  exact map_star (positiveLinearMapOfIsCPTP Θ h) W

example {p q : ℕ} (N : Matrix (Fin q) (Fin p) ℂ) (W : Op p) :
    matrixConjPositiveLinearMap N Wᴴ = (matrixConjPositiveLinearMap N W)ᴴ := by
  let : CStarAlgebra (Op p) := {}
  let : CStarAlgebra (Op q) := {}
  exact map_star (matrixConjPositiveLinearMap N) W
