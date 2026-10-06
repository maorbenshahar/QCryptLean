import QCryptLean.QKD.BB84.Model.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.Operators.PrincipalSubmatrix
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState
import QCryptLean.InfoTheory.QuantumLHL.SmoothingSideConditions
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy

/-!
# BB84 single-round post-measurement CQ state

The single-round layer is indexed by Eve's ancilla dimension `dE` together with the
tripartite round state `Ψ : DensityOp (signalDim * dE)` on the joint Alice-Bob ⊗ Eve
register — the only data the construction reads: Eve's sub-density conditioned on Alice's
single-round measurement outcome, and the CQ state assembled from those conditioned blocks.

## Main definitions

- `QKD.BB84.Engine.bb84SingleRoundConditioned`: Eve's sub-density
  conditioned on a single measurement outcome for one round of `Ψ`.
- `QKD.BB84.Engine.bb84SingleRoundCQState`: the single-round CQ state, classical register
  `Fin signalDim` (Alice's outcome), quantum register `dE` (Eve's ancilla).

## Main results

- `bb84SingleRoundConditioned_trace`: conditioned block weights are
  diagonal sums of the tripartite round state.
- `bb84SingleRoundConditioned_weight_sum`: the conditioned blocks partition the round state.
- `bb84SingleRoundCQState_stateMap_toOp_apply`: CQ blocks are the
  computational-basis Eve blocks of the round state.

The generic sub-density tensor-product operations used here live in
`InfoTheory.SmoothMinEntropy.TensorProduct`.
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open Math.ClassicalEntropy
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

open InfoTheory.SmoothMinEntropy

/-!
## Single-round conditioned state
-/

/-- Eve's sub-density conditioned on a single measurement outcome `x : Fin signalDim`
    for one round.

    The tripartite round state `Ψ` lives on `ℂ^4 ⊗ ℂ^dE` (joint Alice-Bob ⊗ Eve register).
    After indexing `Fin (4 * dE) ≃ Fin 4 × Fin dE` in row-major order, the diagonal block at
    `(x, x)` is a `dE × dE` sub-density giving Eve's state when Alice
    observes signal `x`. -/
noncomputable def bb84SingleRoundConditioned (dE : ℕ) [NeZero dE]
    (Ψ : DensityOp (signalDim * dE)) (x : Fin signalDim) :
    SubDensityOp dE := by
  let embed : Fin dE → Fin (signalDim * dE) :=
    fun a => finProdFinEquiv (x, a)
  exact { toOp := Ψ.toOp.submatrix embed embed
          isHermitian := densityOp_submatrix_isHermitian Ψ embed
          pos_semidef := densityOp_submatrix_pos_semidef Ψ embed
          trace_le_one := densityOp_submatrix_trace_le_one Ψ embed
            (fun a b h => congrArg Prod.snd (finProdFinEquiv.injective h)) }

/-- The trace of a single-round conditioned Eve block is the sum of the
corresponding diagonal entries of the tripartite round state. -/
theorem bb84SingleRoundConditioned_trace (dE : ℕ) [NeZero dE]
    (Ψ : DensityOp (signalDim * dE)) (x : Fin signalDim) :
    (bb84SingleRoundConditioned dE Ψ x).trace =
      ∑ a : Fin dE,
        (Ψ.toOp (finProdFinEquiv (x, a)) (finProdFinEquiv (x, a))).re := by
  simp only [SubDensityOp.trace, bb84SingleRoundConditioned,
    trace_re_submatrix_eq_sum_diag_re]

/-- The single-round conditioned sub-densities partition the round state:
    `∑_{x : Fin 4} tr(Eve(x)) = 1`. -/
theorem bb84SingleRoundConditioned_weight_sum (dE : ℕ) [NeZero dE]
    (Ψ : DensityOp (signalDim * dE)) :
    ∑ x : Fin signalDim,
      (bb84SingleRoundConditioned dE Ψ x).trace = 1 := by
  simp_rw [bb84SingleRoundConditioned_trace dE Ψ]
  rw [← Fintype.sum_prod_type']
  rw [← densityOp_sum_diag_re_eq_one Ψ]
  apply Fintype.sum_equiv finProdFinEquiv
  intro p
  simp [finProdFinEquiv]

/-!
## Single-round CQ state and calibration reference
-/

/-- The single-round post-measurement CQ state of a tripartite round state.

    Classical register: `Fin signalDim` (Alice's single-round measurement outcome).
    Quantum register: `dE` (Eve's single-round ancilla).

    At outcome `x : Fin signalDim`, the quantum state is
    `bb84SingleRoundConditioned dE Ψ x`.
    The collection sums to trace 1 by `bb84SingleRoundConditioned_weight_sum`. -/
noncomputable def bb84SingleRoundCQState (dE : ℕ) [NeZero dE]
    (Ψ : DensityOp (signalDim * dE)) :
    NormalizedCQState (Fin signalDim) dE where
  stateMap := bb84SingleRoundConditioned dE Ψ
  weight_le_one := (bb84SingleRoundConditioned_weight_sum dE Ψ).le
  weight_eq_one := bb84SingleRoundConditioned_weight_sum dE Ψ

/-- Entries of the single-round CQ blocks are the computational-basis Eve blocks of
the underlying tripartite round state. -/
theorem bb84SingleRoundCQState_stateMap_toOp_apply (dE : ℕ) [NeZero dE]
    (Ψ : DensityOp (signalDim * dE)) (x : Fin signalDim)
    (a b : Fin dE) :
    ((bb84SingleRoundCQState dE Ψ :
      CQState (Fin signalDim) dE).stateMap x).toOp a b =
      Ψ.toOp (finProdFinEquiv (x, a)) (finProdFinEquiv (x, b)) := by
  rfl

end QKD.BB84.Engine

end -- noncomputable section
