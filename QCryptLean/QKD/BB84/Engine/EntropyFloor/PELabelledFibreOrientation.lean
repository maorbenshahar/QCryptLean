import QCryptLean.QKD.BB84.Engine.EntropyFloor.IsometricInvariance
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AgreeBlockLHLBridge

/-!
# Register bookkeeping for the PE-labelled fibre orientation

Small register-arithmetic and marginal facts consumed by the PE-labelled leftover-hashing input
construction: the one-dimensional bare-slot collapse, the key-round CQ quantum marginal, and the
key-first sorted split of the signal register at a general test-set size `m`.

## Main results
- `bb84SiftedKeyRoundCQ_quantumMarginal_toOp`: the key-round bit-CQ state's quantum marginal is
  `Tr_A ψ`.
- `bb84SignalPow_keyPE_split`: `signalDim ^ n_K * signalDim ^ (n − n_K) = signalDim ^ n` at
  `n_K = bb84KeyRoundCount n m`, for every test-set size `m`.

Reference: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`),
`main.tex:452` (the round-by-round announcements `C^n` are inside the
conditioning register from the start), `:909`, `:913` (the general test-set size `m`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.SmoothMinEntropy.SymmetricAEP InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## Register bookkeeping -/

/-- The bare slot's side register is one-dimensional, so the per-σ family's register collapses
onto the signal register.  Named because it appears inside the statements below. -/
lemma bb84UnitEveDim_mul_signalPow (n : ℕ) :
    1 * signalDim ^ n = signalDim ^ n :=
  Nat.one_mul _

/-! ## The key factor's marginal -/

/-- **The key-round bit-CQ state's quantum marginal is `Tr_A ψ`.**  Its two Alice-bit blocks
coarsen the four outcome blocks of a single sifted key round, whose sum is `Tr_A ψ`
(`bb84_referee_siftedRoundRefBlock_sum_eq_partialTraceA`, `IsometricInvariance.lean:128`). -/
lemma bb84SiftedKeyRoundCQ_quantumMarginal_toOp (ψ : DensityOp (signalDim * signalDim)) :
    (bb84SiftedKeyRoundCQ ψ).quantumMarginal.toOp = (DensityOp.partialTraceA ψ).toOp := by
  change (CQState.coarsen bb84AliceBitMap (bb84SiftedKeyRoundCQRaw ψ)).quantumMarginalOp = _
  rw [CQState.coarsen_quantumMarginalOp]
  change ∑ k, (bb84RefereeSiftedSingleRoundRefBlock ψ false k).toOp =
      (DensityOp.partialTraceA ψ).toOp
  rw [bb84_referee_siftedRoundRefBlock_sum_eq_partialTraceA]
  rfl

/-- **The key-first sorted split of the signal register, at a general test-set size `m`.**

Over the split-point-parametrised key-round count `bb84KeyRoundCount n m = n − m`.  It holds
at every `m`: the underlying split identity `bb84KeyRoundCount_add'` is unconditional.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
lemma bb84SignalPow_keyPE_split (n m : ℕ) :
    signalDim ^ bb84KeyRoundCount n m *
        signalDim ^ (n - bb84KeyRoundCount n m) = signalDim ^ n := by
  rw [← pow_add, bb84KeyRoundCount_add']

end QKD.BB84.Engine

end -- noncomputable section
