import QCryptLean.Quantum.Symmetry.BellHaarIntegral
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.PureCoreUncertainty

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

/-!
# Bell de Finetti inner-budget core — purity of the Bell-doubling embedding

Part of the Bell reference/floor construction (with `BellPurifier.lean`, `BellDickeCore.lean`
and `BellHaarIntegral.lean`): the Bell-doubling embedding `bellWembed` preserves purity.

## Main results
- `bellWembed_isPure`: `Wembed φ` is pure whenever `φ` is pure.
-/

noncomputable section

namespace QKD.BB84.Engine

section BellFloorChain

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace


/-- **Purity is preserved by the Bell-doubling embedding** `Wembed φ = W·φ·Wᴴ`.  Conjugation by the
isometry `W` (`Wᴴ·W = 𝟙`, `bellDoublingIsometry_isometry`) sends idempotents to idempotents, so
`(Wembed φ)² = Wembed φ` whenever `φ² = φ`.  Used to lift the pure-state support of the `d = 4` de
Finetti Haar measure (the post-filter host's `P = {φ | φ.IsPure}`) to the purity of `Wembed φ` the
CKR register bridge needs. -/
theorem bellWembed_isPure {φ : DensityOp 4} (hφ : φ.IsPure) : (bellWembed φ).IsPure := by
  change (bellWembed φ).toOp * (bellWembed φ).toOp = (bellWembed φ).toOp
  change (bellDoublingIsometry * φ.toOp * (bellDoublingIsometry)ᴴ) *
      (bellDoublingIsometry * φ.toOp * (bellDoublingIsometry)ᴴ) =
      bellDoublingIsometry * φ.toOp * (bellDoublingIsometry)ᴴ
  have hidem : φ.toOp * φ.toOp = φ.toOp := hφ
  calc (bellDoublingIsometry * φ.toOp * (bellDoublingIsometry)ᴴ) *
        (bellDoublingIsometry * φ.toOp * (bellDoublingIsometry)ᴴ)
      = bellDoublingIsometry * φ.toOp *
          ((bellDoublingIsometry)ᴴ * bellDoublingIsometry) * φ.toOp * (bellDoublingIsometry)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = bellDoublingIsometry * (φ.toOp * φ.toOp) * (bellDoublingIsometry)ᴴ := by
        rw [bellDoublingIsometry_isometry]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = bellDoublingIsometry * φ.toOp * (bellDoublingIsometry)ᴴ := by rw [hidem]

end BellFloorChain

end QKD.BB84.Engine

end -- noncomputable section
