import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.Classical
import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.OutputBlock
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubDensityOpTraceZero
import QCryptLean.Quantum.Channels.CPTP.CKRBound.SignalPermutationInvariance
import QCryptLean.QKD.BB84.Model.PermAnnounceRegister
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PostMeasurementCQTrace
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.QKD.BB84.Engine.Postselection.Basic
import QCryptLean.Quantum.Channels.CPTP.FiniteMixture
import QCryptLean.Quantum.Channels.CPTP.PureStateExtension
import QCryptLean.Quantum.Operators.BraKet.Projector

/-!
# Permutation invariance of the CKR de Finetti purification

The CKR de Finetti reference state and its square-root-vectorization purification are invariant
under the diagonal (paired) action of the symmetric group, which is what lets a per-permutation
symmetrization argument collapse to a single representative summand.

## Main results

* `ckrDeFinettiState_isPermutationInvariant` — the CKR de Finetti state is permutation-invariant.
* `purificationDensityOp_isPairedPermInvariant` — permutation invariance of a density operator
  lifts to paired permutation invariance of its purification.
* `bb84SymCKRDeFinettiPurification_isPairedPermInvariant` — the BB84 specialization.

## References

Renner (2005) §6.5; CKR (2009) main.tex:268–:401 (Main Result: Theorem `\label{thm:main}`
:291–:301, Lemma `\label{lem:extractpart}` :319–:328).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.QuantumLHL
open Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-!
### Permutation invariance of the CKR de Finetti reference
-/

/-- The CKR de Finetti state `ckrDeFinettiState signalDim n` is permutation-invariant.

    The CKR state is the partial trace of `pairedDeFinettiState`, which is defined as the
    normalized paired symmetric projector `(1/n!) Σ_σ U_σ ⊗ U_σ`.  After tracing out the
    second register:

    `partialTraceB((1/n!) Σ_σ U_σ ⊗ U_σ) = (1/n!) Σ_σ trace(U_σ) • U_σ`

    (using `partialTraceB_tensor_self_eq`).  The resulting sum is permutation-invariant by
    `sum_permRep_trace_smul_conj_eq`, which uses trace cyclicity and sum reindexing.

    References: CKR (2009) eq. (1); Renner (2005) §6.5. -/
theorem ckrDeFinettiState_isPermutationInvariant (n : ℕ) [NeZero n] [NeZero (4 ^ n)] :
    IsPermutationInvariant (ckrDeFinettiState signalDim n) :=
  Quantum.Channels.ckrDeFinettiState_isPermutationInvariant_gen signalDim n

/-- The square-root-vectorization purification of a permutation-invariant density operator
    is paired-permutation-invariant.

    Given `ρ : DensityOp (d^n)` with `IsPermutationInvariant ρ`, the purification
    `purificationDensityOp ρ : DensityOp (d^n * d^n)` satisfies
    `(U_σ ⊗ U_σ) * (purificationDensityOp ρ).toOp * (U_σ ⊗ U_σ)† = (purificationDensityOp ρ).toOp`
    for every `σ : Equiv.Perm (Fin n)`.

    This follows directly from `InfoTheory.DeFinetti.purificationOp_perm_invariant`,
    since `purificationDensityOp ρ` is built from the same underlying `purificationOp ρ`. -/
theorem purificationDensityOp_isPairedPermInvariant {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    IsPairedPermInvariant (InfoTheory.DeFinetti.purificationDensityOp ρ) := by
  intro σ
  exact InfoTheory.DeFinetti.purificationOp_perm_invariant ρ hinv σ

/-- The canonical BB84 CKR de Finetti purification is paired-permutation-invariant:
    `(U_π ⊗ U_π) * (bb84SymCKRDeFinettiPurification n).toOp * (U_π ⊗ U_π)† =
       (bb84SymCKRDeFinettiPurification n).toOp`
    for every `π : Equiv.Perm (Fin n)`.

    Follows from `ckrDeFinettiState_isPermutationInvariant` and
    `purificationDensityOp_isPairedPermInvariant`.

    Note: The paired invariance `(U_π ⊗ U_π)` is the correct statement.
    The one-sided action `(U_π ⊗ id)` does NOT preserve the purification
    (for example, at `d = 4`, `n = 2`, with the swap permutation).

    References: Renner (2005) §6.5; CKR (2009) main.tex:268–:401 (\emph{Main Result}: Theorem
    `\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328). -/
theorem bb84SymCKRDeFinettiPurification_isPairedPermInvariant (n : ℕ) [NeZero n]
    [NeZero (4 ^ n)] :
    IsPairedPermInvariant (bb84SymCKRDeFinettiPurification n) :=
  purificationDensityOp_isPairedPermInvariant (ckrDeFinettiState signalDim n)
    (ckrDeFinettiState_isPermutationInvariant n)

end QKD.BB84.Engine

end -- noncomputable section
