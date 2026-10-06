import QCryptLean.InfoTheory.Postselection.Lift
import QCryptLean.InfoTheory.Postselection.LiftToCoherent

/-!
# Fixed-reference group-symmetric postselection lift

This is a fixed-reference specialization of Nahar et al., arXiv:2403.11851,
Corollary 3.2 (`main.tex`, `cor:liftToCoherentSymmetries`,
:521–530). The IID entropy premise uses one common positive-definite reference
`M.sigmaE` for every IID state; the paper's Eq. (11) (`eq:condLHL`, :462–467)
optimizes the reference for each state.

The lift is for finite groups `G = G_A × G_B` acting through product representations
(`prodRep`). It assumes a full-rank fixed marginal `σA` (`hσA`) invariant under `G_A`
(`hσinv`) and a closed good set (`hClosed`). The round-grouped difference map is
permutation-invariant (Def. 5, main.tex:415–421) and IID-`G`-invariant
(Def. 6, main.tex:513–519).

Main result: `postselection_security_of_measureThenHash_groupSymmetric`.
Its ingredients live upstream: the
fixed-marginal reduction `deFinetti_groupSymmetric_traceNorm_le` and the group-invariant
lift `groupInvariant_postselection_security_of_referenceBound` in `Lift.lean`, and the
fixed-reference form of Theorem 3
`postselection_referenceBound_of_measureThenHash_groupSymmetric` in `LiftToCoherent.lean`.
The plain theorems
`permInvariant_postselection_security_of_referenceBound` (Lift.lean) and
`postselection_referenceBound_of_measureThenHash` (LiftToCoherent.lean) are the
trivial-group corollaries of the group-invariant ones.

The cost is `deFinettiPrefactor (∑ i, ∑ j, (mA i)² (mB j)²) n` in place of
`deFinettiPrefactor (dA² dB²) n`. Finite groups only (the paper states compact groups;
Haar integration is replaced by finite uniform averages, see `GroupSymmetricDeFinetti.lean`).
-/

open Quantum.Operators Quantum.Symmetry Quantum.TensorProducts
open InfoTheory.DeFinetti InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder

-- Frobenius normed structure on matrices, needed to integrate operator-valued functions
-- (same local instances as `InfoTheory.DeFinetti.IntegralPurification`).
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-- Extended IID entropy gives coherent security for a group- and permutation-invariant
measure-then-hash protocol with the group-symmetric de Finetti prefactor. -/
theorem postselection_security_of_measureThenHash_groupSymmetric
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {kA kB : ℕ}
    (M : RawKeyMeasurement dA dB n) (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (εAT εPA εbar : ℝ) (l' : ℕ)
    (goodSet : Set (DensityOp (dA * dB)))
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (hσinv : IsGroupInvariantState πA σA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2))
    (hcondS : SatisfiesAcceptTestBound (fixedMarginalSet σA)
      (goodSet ∩ fixedMarginalSet σA) M.pAcc εAT)
    (hcondLHL : ∀ σ ∈ goodSet ∩ fixedMarginalSet σA,
      hashingError M.toProtocol.l (smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE) ≤ εPA)
    (hεPA : 0 ≤ εPA) (hεbar : 0 ≤ εbar)
    (C : MeasureThenHash M l')
    (hl' : (l' : ℝ) ≤
      (M.toProtocol.l : ℝ) -
        2 * Real.logb 2
          (deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n))
    (hperm :
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
        ⟨Nat.pos_iff_ne_zero.mp
          (Nat.mul_pos M.toProtocol.keyDim_neZero.pos M.toProtocol.annDim_neZero.pos)⟩
      IsPermutationInvariantMap (M.toProtocol.roundDifferenceMap l'))
    (hG :
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      haveI : NeZero (M.toProtocol.keyDim * M.toProtocol.annDim) :=
        ⟨Nat.pos_iff_ne_zero.mp
          (Nat.mul_pos M.toProtocol.keyDim_neZero.pos M.toProtocol.annDim_neZero.pos)⟩
      ∀ (W : (G_A × G_B) → UnitaryOp (dA * dB)), (∀ g : G_A × G_B,
        (W g).toOp = prodRep πA πB g) →
        IsIIDGroupInvariantMap W (M.toProtocol.roundDifferenceMap l'))
    (hClosed : IsClosed goodSet) :
    M.toProtocol.IsSecretAt l' σA
      ((deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℝ) *
        coherentIIDSecrecy εAT εPA εbar) := by
  apply groupInvariant_postselection_security_of_referenceBound M.toProtocol σA hσA
    πA hπA hσinv πB hπB mA mB hxA hxB (coherentIIDSecrecy εAT εPA εbar) l' _ hperm hG
  intro μ hμ hμinv
  exact postselection_referenceBound_of_measureThenHash_groupSymmetric M σA εAT εPA εbar
    l' goodSet πA hπA πB hπB mA mB hxA hxB hcondS hcondLHL hεPA hεbar C hl' hClosed μ hμ hμinv

end InfoTheory.Postselection
