import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Classical support entropy and a support-inverse trace

* `CQState.classicalSupport` is the support of the classical marginal.
* `CQState.rankClassical` is its cardinality.
* `CQState.HmaxClassical` is the Hartley entropy `log₂ |supp ρ_X|` on nonempty support.
* `CQState.traceRhoSqInvSigma` is `Re Tr(ρ_XB² (I_X ⊗ σ_B⁺))`, using the support
  pseudoinverse in the quantum-first layout of `CQState.toJointOp`.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Support of the classical X-marginal of a CQ state: the finite set of
    classical outcomes with strictly positive weight.

    Uses `Classical.dec` to make the predicate `0 < ρ.classicalMarginal x`
    decidable; the resulting `Finset` is therefore noncomputable. -/
noncomputable def CQState.classicalSupport
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) : Finset X :=
  open Classical in
    Finset.univ.filter (fun x : X => 0 < ρ.classicalMarginal x)

/-- Rank of the classical X-marginal of a CQ state, i.e. the cardinality of
    the support of `classicalMarginal`. -/
noncomputable def CQState.rankClassical
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) : ℕ :=
  ρ.classicalSupport.card

/-- Renyi-0 / Hartley max-entropy of the classical X-marginal of a CQ
    state with nonempty support: `H_max(ρ_X) = log₂ |supp ρ_X|`. -/
noncomputable def CQState.HmaxClassical
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) (_hρ : 0 < ρ.rankClassical) : ℝ :=
  Real.logb 2 ((ρ.rankClassical : ℝ))

/-- Real part of `Tr(ρ_XB² · (I_X ⊗ σ_B⁺))`, with the support pseudoinverse `σ_B⁺`.

The CFC power `σ.toOp ^ (-1 : ℝ)` inverts positive eigenvalues and is zero on the kernel.
The quantum-first layout `Fin n × X` places this factor before the classical identity.
This is a finite algebraic trace; its interpretation as a collision quantity requires
`supp ρ_XB ⊆ X ⊗ supp σ_B`. -/
noncomputable def CQState.traceRhoSqInvSigma
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (σ : DensityOp n) : ℝ :=
  let id_X : Matrix X X ℂ := 1
  let M : Matrix (Fin n × X) (Fin n × X) ℂ :=
    Matrix.kroneckerMap (· * ·) (σ.toOp ^ (-1 : ℝ)) id_X
  ((ρ.toJointOp ^ 2) * M).trace.re

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
