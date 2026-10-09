import QCryptLean.Quantum.Bases.Basic
import QCryptLean.Quantum.Channels.PostselectionBound
import QCryptLean.Quantum.DeFinetti.Approximation
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Symmetry.CentralizerHaarAlgebra
import QCryptLean.Quantum.Symmetry.DirectSumAlgebra
import QCryptLean.Quantum.Symmetry.BellSpectrum

/-! # Register, normalization, and universe regression probes -/

noncomputable section

open scoped ComplexOrder

open Matrix Quantum.Operators Quantum.Symmetry
open Quantum.Channels Quantum.Metrics

universe u v w

variable {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]

-- The empty local register still has a one-dimensional zero-site function register.
example : (symmetricProjector Empty 0).PosSemidef := symmetricProjector_posSemidef

example : (symmetricProjector Empty 1).PosSemidef := symmetricProjector_posSemidef

example [DecidableEq X] [DecidableEq Y] (k : ℕ) :
    (pairedProjectorOf X Y k).PosSemidef := pairedProjectorOf_posSemidef X Y k

example (k : ℕ) : (bellRotation k)ᴴ * bellRotation k = 1 := bellRotation_unitary k

example (k : ℕ) :
    (bellDoublingIsometryPow k)ᴴ * bellDoublingIsometryPow k = 1 := by
  rw [bellDoublingIsometryPow, conjTranspose_piTensorProduct, piTensorProduct_mul]
  simp only [bellDoublingIsometry_isometry, piTensorProduct_one]

-- Classical labels and their dependent quantum fibres can live in different universes.
example {I : Type w} [Fintype I] [DecidableEq I]
    (A : I → Type u) (R : I → Type v)
    [∀ i, Fintype (A i)] [∀ i, Fintype (R i)]
    [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (R i)] (k : ℕ) :
    (alignedDirectSumProjector A R k).PosSemidef := posSemidef_alignedDirectSumProjector A R k

example [Nonempty X] (ρ σ τ : SubDensityOp X) :
    purifiedDistance ρ τ ≤ purifiedDistance ρ σ + purifiedDistance σ τ :=
  purifiedDistance_triangle ρ σ τ

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

-- Haar/CFC imports must leave the existing analytic Frobenius convention usable.
example (A : Op X) : ‖A‖ ≤ traceNorm A := frobenius_le_traceNorm A

end Frobenius
