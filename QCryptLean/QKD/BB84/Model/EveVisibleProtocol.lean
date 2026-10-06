import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.Classical
import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.OutputBlock
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubDensityOpTraceZero
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.Quantum.Channels.CPTP.FiniteMixture
import QCryptLean.Quantum.Channels.CPTP.PureStateExtension
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity

/-!
# The Eve-visible protocol interface

The protocol-level interface (`BB84EveVisibleProtocolScheme`) whose real/ideal maps retain Eve as
a right tensor factor.

## Main definitions

* `BB84EveVisibleProtocolScheme` — the protocol interface: a transcript dimension factored as
  `2 * transcriptInnerDim` (the PE flag), and real/ideal protocol maps retaining Eve's register.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.QuantumLHL
open Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-! ## Parallel Eve-visible protocol interface -/

/-- Protocol-level interface whose outputs retain Eve as a right tensor factor. -/
structure BB84EveVisibleProtocolScheme (n ℓ : ℕ) [NeZero n] where
  /-- Public transcript dimension before the symmetrizing permutation announcement. -/
  transcriptDim : ℕ
  /-- Inner transcript dimension for the PE flag factorization. -/
  transcriptInnerDim : ℕ
  /-- The transcript dimension factors as `2 * transcriptInnerDim`. -/
  transcriptDim_factored : transcriptDim = 2 * transcriptInnerDim
  /-- The inner transcript dimension is nonzero. -/
  transcriptInnerDim_neZero : NeZero transcriptInnerDim
  /-- Real protocol map with retained Eve output. -/
  realProtocolMap : {eveDim : ℕ} → [NeZero eveDim] →
    Op (4 ^ n * eveDim) →ₗ[ℂ] Op ((2 ^ ℓ * 2 ^ ℓ * transcriptDim) * eveDim)
  /-- Ideal protocol map with retained Eve output. -/
  idealProtocolMap : {eveDim : ℕ} → [NeZero eveDim] →
    Op (4 ^ n * eveDim) →ₗ[ℂ] Op ((2 ^ ℓ * 2 ^ ℓ * transcriptDim) * eveDim)

end QKD.BB84.Model

end -- noncomputable section
