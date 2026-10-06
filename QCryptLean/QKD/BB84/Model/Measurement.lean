import QCryptLean.QKD.BB84.Constants
import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.Operators.PrincipalSubmatrix

/-!
# BB84 measurement outcomes — POVM and packed indices

Per-round 4-outcome computational-basis measurement for the BB84 protocol, and the packed
indexing of an `n`-round outcome string into `Fin (4 ^ n)`. The 4 outcomes encode
(Alice bit, Bob bit) pairs.

## Encoding convention

Outcome `k : Fin signalDim` encodes (Alice bit, Bob bit) as
  `k.val = 2 * (alice bit) + (bob bit)`.
Concretely: 0 ↔ (0,0), 1 ↔ (0,1), 2 ↔ (1,0), 3 ↔ (1,1).
A mismatch occurs when `k = 1` or `k = 2`.

## Main definitions

- `bb84ComputationalPOVM`: 4 orthogonal projectors on `Op signalDim`.
- `bb84AliceBitMap`: extract Alice's bit from a 4-outcome BB84 round outcome.
- `bb84AliceZProjector`: Alice's coarse Z-bit projector, summed over the outcome fiber.
- `bb84OutcomeIndex`: packed index in `Fin (4 ^ n)` for an n-round outcome string.
- `bb84OutcomeIndexEquiv`: equivalence between outcome strings and packed indices.

## Main statements

- `bb84ComputationalPOVM_complete`: the 4 projectors sum to the identity.
- `bb84ComputationalPOVM_isProjection`: each projector is idempotent.
- `bb84ComputationalPOVM_isHermitian`: each projector is Hermitian.
- `bb84OutcomeIndex_sum`: reindex sums over outcome strings by packed indices.
-/

open Quantum.Operators Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-!
## Per-Round Computational-Basis POVM
-/

/-- The map from a 4-outcome joint (Alice, Bob) measurement outcome to Alice's
Z-basis key bit.

Outcome `k : Fin signalDim` encodes `(Alice bit, Bob bit)` as
`k.val = 2 * alice_bit + bob_bit`, so Alice's bit is `k.val / 2`. -/
def bb84AliceBitMap : Fin signalDim → Fin 2 :=
  fun k => ⟨k.val / 2, by simp [signalDim]; omega⟩

/-- The k-th projector of the BB84 computational-basis POVM on `Op signalDim`.

    `bb84ComputationalPOVM k = |k⟩⟨k|`, the rank-1 projector onto the k-th
    standard basis vector in `ℂ⁴`.

    The 4 outcomes encode (Alice bit, Bob bit) pairs:
      0 = (0,0), 1 = (0,1), 2 = (1,0), 3 = (1,1). -/
noncomputable def bb84ComputationalPOVM : Fin signalDim → Op signalDim :=
  fun k => Matrix.single k k 1

/-- Each `bb84ComputationalPOVM k` is an idempotent projector:
    `|k⟩⟨k| * |k⟩⟨k| = |k⟩⟨k|`. -/
theorem bb84ComputationalPOVM_isProjection (k : Fin signalDim) :
    bb84ComputationalPOVM k * bb84ComputationalPOVM k = bb84ComputationalPOVM k := by
  simp [bb84ComputationalPOVM]

/-- Each `bb84ComputationalPOVM k` is Hermitian: `(|k⟩⟨k|)† = |k⟩⟨k|`. -/
theorem bb84ComputationalPOVM_isHermitian (k : Fin signalDim) :
    (bb84ComputationalPOVM k).IsHermitian := by
  rw [bb84ComputationalPOVM, ← Matrix.diagonal_single, Matrix.isHermitian_diagonal_iff]
  intro i
  rw [IsSelfAdjoint]
  by_cases h : i = k
  · subst h
    simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

/-- The 4 projectors sum to the identity on `Op signalDim`. -/
theorem bb84ComputationalPOVM_complete :
    ∑ k : Fin signalDim, bb84ComputationalPOVM k = (1 : Op signalDim) := by
  simpa [bb84ComputationalPOVM] using
    (Matrix.sum_single_one :
      (∑ k : Fin signalDim, Matrix.single k k (1 : ℂ)) = (1 : Op signalDim))

/-- Alice's coarse Z-bit projector obtained by summing computational-basis
projectors over the fiber of `bb84AliceBitMap`. -/
noncomputable def bb84AliceZProjector (z : Fin 2) : Op signalDim :=
  ∑ k : Fin signalDim,
    if bb84AliceBitMap k = z then bb84ComputationalPOVM k else 0

/-- The coarse Alice Z-bit projector as a diagonal selector matrix. -/
lemma bb84AliceZProjector_eq_diagonal (z : Fin 2) :
    bb84AliceZProjector z =
      Matrix.diagonal
        (fun k : Fin signalDim =>
          if bb84AliceBitMap k = z then (1 : ℂ) else 0) := by
  rw [← Matrix.sum_single_eq_diagonal
    (fun k : Fin signalDim =>
      if bb84AliceBitMap k = z then (1 : ℂ) else 0)]
  unfold bb84AliceZProjector bb84ComputationalPOVM
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hkz : bb84AliceBitMap k = z <;> simp [hkz]

/-!
## N-Round Outcome Indexing
-/

/-- Index in `Fin (4 ^ n)` corresponding to an n-round BB84 outcome string. -/
noncomputable def bb84OutcomeIndex {n : ℕ} (ω : Fin n → Fin signalDim) : Fin (4 ^ n) :=
  finFunctionFinEquiv ω

/-- The BB84 outcome-index map as an equivalence. -/
noncomputable def bb84OutcomeIndexEquiv {n : ℕ} :
    (Fin n → Fin signalDim) ≃ Fin (4 ^ n) :=
  finFunctionFinEquiv

/-- `bb84OutcomeIndexEquiv` computes to `bb84OutcomeIndex`. -/
lemma bb84OutcomeIndexEquiv_apply {n : ℕ} (ω : Fin n → Fin signalDim) :
    bb84OutcomeIndexEquiv ω = bb84OutcomeIndex ω := by
  rfl

/-- `bb84OutcomeIndex` uses the canonical tensor-power indexing convention. -/
lemma bb84OutcomeIndex_eq_finFunctionFinEquiv {n : ℕ}
    (ω : Fin n → Fin signalDim) :
    bb84OutcomeIndex ω = finFunctionFinEquiv ω := by
  rfl

/-- Unpacking a packed BB84 outcome index with the tensor-power inverse recovers
    the original outcome string. -/
lemma finFunctionFinEquiv_symm_bb84OutcomeIndex {n : ℕ}
    (ω : Fin n → Fin signalDim) :
    finFunctionFinEquiv.symm (bb84OutcomeIndex ω) = ω := by
  rw [bb84OutcomeIndex_eq_finFunctionFinEquiv]
  exact Equiv.symm_apply_apply finFunctionFinEquiv ω

/-- Reindex a finite sum over BB84 outcome strings by their packed outcome index. -/
lemma bb84OutcomeIndex_sum {n : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin (4 ^ n) → α) :
    (∑ ω : Fin n → Fin signalDim, f (bb84OutcomeIndex ω)) =
      ∑ i : Fin (4 ^ n), f i := by
  simpa only [bb84OutcomeIndexEquiv_apply]
    using Equiv.sum_comp (bb84OutcomeIndexEquiv (n := n)) f

/-!
## Eve's conditional sub-density: the outcome/Eve register embedding

Moved here from `QKD.BB84.Engine.EntropyFloor.PostMeasurementCQ`: pure register-index bookkeeping
built only on `bb84OutcomeIndex`/`bb84OutcomeIndex_sum` above and generic `DensityOp` submatrix
lemmas, consumed by the Model's post-measurement CQ stack
(`QKD.BB84.Model.SiftedMeasurement.bb84SiftedEveConditioned`), so it belongs here rather than in
one Engine analysis file. -/

/-- Embedding of Eve indices into the joint outcome-Eve register at a fixed outcome. -/
def bb84OutcomeEveEmbedding {n eveDim : ℕ} (ωIdx : Fin (4 ^ n)) :
    Fin eveDim → Fin (4 ^ n * eveDim) :=
  fun a => finProdFinEquiv (ωIdx, a)

/-- The fixed-outcome Eve embedding is injective in the Eve index. -/
lemma bb84OutcomeEveEmbedding_injective {n eveDim : ℕ}
    (ωIdx : Fin (4 ^ n)) :
    Function.Injective (bb84OutcomeEveEmbedding (eveDim := eveDim) ωIdx) := by
  intro a b h
  have hp : (ωIdx, a) = (ωIdx, b) := finProdFinEquiv.injective h
  exact congrArg Prod.snd hp

/-- The BB84 outcome/Eve diagonal blocks partition the diagonal trace sum. -/
lemma bb84OutcomeEveEmbedding_diag_sum_eq_one {n eveDim : ℕ}
    (ρ : DensityOp (4 ^ n * eveDim)) :
    (∑ ω : Fin n → Fin signalDim, ∑ a : Fin eveDim,
      (ρ.toOp (bb84OutcomeEveEmbedding (eveDim := eveDim) (bb84OutcomeIndex ω) a)
          (bb84OutcomeEveEmbedding (eveDim := eveDim) (bb84OutcomeIndex ω) a)).re) = 1 := by
  rw [bb84OutcomeIndex_sum (n := n)
    (f := fun ωIdx : Fin (4 ^ n) => ∑ a : Fin eveDim,
      (ρ.toOp (bb84OutcomeEveEmbedding (eveDim := eveDim) ωIdx a)
          (bb84OutcomeEveEmbedding (eveDim := eveDim) ωIdx a)).re)]
  rw [← densityOp_sum_diag_re_eq_one ρ]
  unfold bb84OutcomeEveEmbedding
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv finProdFinEquiv
  intro x
  cases x with
  | mk ωIdx a =>
    simp

end QKD.BB84.Model

end -- noncomputable section
