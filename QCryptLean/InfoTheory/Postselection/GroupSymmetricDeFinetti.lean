import QCryptLean.Quantum.Symmetry.FiniteGroupUnitaryRep
import QCryptLean.InfoTheory.Postselection.Mixture
import QCryptLean.InfoTheory.Postselection.PairedBlockedOperators
import QCryptLean.Quantum.TensorProducts.FixedMarginalDomination
import QCryptLean.InfoTheory.Postselection.GroupInvariantStates
import QCryptLean.InfoTheory.Postselection.GroupPurification
import QCryptLean.InfoTheory.Postselection.BlockedGroupTwirl
import QCryptLean.InfoTheory.Postselection.BlockedSymmetricTwirl

/-!
# Group-symmetric de Finetti reduction with fixed marginal

Finite-group versions of the purification lemma and fixed-marginal de Finetti
reduction of Nahar–Tupkary–Zhao–Lütkenhaus–Tan, arXiv:2403.11851, Lemma
`lem:groupPurification` and Corollary `cor:symmetryDeFinetti`.

For a unitary representation `π`, its paired twirl projects onto the invariant
vectors of `π ⊗ conj π`. Its trace is the sum of the squares of the irreducible
multiplicities. An IID-group-invariant, permutation-invariant state has a
purification in the symmetric tensor power of this invariant subspace.

For product representations on Alice and Bob, the resulting de Finetti cost is
`deFinettiPrefactor (∑ i, ∑ j, mA i ^ 2 * mB j ^ 2) n`. The reference measure
is supported on group-invariant extensions of the prescribed Alice marginal.

The group averages here are finite uniform averages. The paper uses compact
groups and Haar integration. Multiplicities enter the main corollary through
trace identities, supplied by `groupTwirlProjector_trace_isotypic` whenever an
isotypic decomposition is available.
-/


open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Matrix
open InfoTheory.DeFinetti MeasureTheory
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.Postselection

/-! ### The main corollary -/

/-- A purification supported on both the paired symmetric subspace and the
paired group-twirl range is dominated by a group-invariant fixed-marginal reference
at the symmetric-power dimension of the twirl range. The proof transports to the
blocked register, normalizes the prescribed marginal, bounds the normalized
operator by its supporting projection, and transports back. -/
theorem deFinetti_groupSymmetric_purified_op_le
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n kA kB : ℕ} [NeZero dA] [NeZero dB] [NeZero (dA * dB)] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2))
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (ρ : DensityOp ((dA * dB) ^ n))
    (hiid : IsIIDGroupInvariant (prodRep πA πB) ρ)
    (hmarg : roundwiseAliceMarginal ρ = σA.tensorPowGen n)
    (Ψ : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n))
    (hΨ_grp : groupPairedTwirlProjector n (prodRep πA πB) * Ψ.toOp *
      groupPairedTwirlProjector n (prodRep πA πB) = Ψ.toOp)
    (hΨ_supp : symmetricProjectorPaired (dA * dB) n * Ψ.toOp *
      symmetricProjectorPaired (dA * dB) n = Ψ.toOp)
    (hΨ_marg : partialTraceB Ψ.toOp = ρ.toOp) :
    ∃ μ : DensityMeasure (dA * dB), IsFixedMarginalMeasure σA μ ∧
      IsGroupInvariantMeasure (prodRep πA πB) μ ∧
      ∃ τ_ABE : Op ((dA * dB) ^ n * (dA * dB) ^ n), τ_ABE.PosSemidef ∧
        partialTraceB τ_ABE = (deFinettiMixtureFixedMarginal dA dB n μ).toOp ∧
        (((deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℕ) : ℂ) •
          τ_ABE - Ψ.toOp).PosSemidef := by
  haveI : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  haveI : NeZero (dA ^ n) := ⟨pow_ne_zero n (NeZero.ne dA)⟩
  obtain ⟨κG, hκG_psd, hκG_unit, hκG_comm, hκGinv⟩ :=
    exists_flatten_groupSymmetricTwirl (dA := dA) (dB := dB) (n := n) πA hπA πB hπB
  have hκG_pd : κG.PosDef := (Matrix.PosSemidef.posDef_iff_isUnit hκG_psd).mpr hκG_unit
  -- the projectors: `P_G` (blocked group twirl), `P` (symmetric); intersection `P_G * P`
  let PG : Op (dA ^ n * (dA * dB ^ 2) ^ n) := groupBlockedTwirlProjector πA πB
  let P : Op (dA ^ n * (dA * dB ^ 2) ^ n) := symmetricProjectorPairedGen dA (dA * dB ^ 2) n
  -- the full-rank Alice tensor power
  set PA : Op (dA ^ n) := (σA.tensorPowGen n).toOp with hPA_def
  have hPA_pd : PA.PosDef := by rw [hPA_def, DensityOp.tensorPowGen_toOp]; exact hσA.tensorPow n
  have hAcomm : Commute (Op.tensor PA (1 : Op ((dA * dB ^ 2) ^ n))) (PG * P) := by
    have hG := sigmaA_tensorPowGen_commute_groupBlockedTwirlProjector
      πA hπA πB hπB σA ρ hiid hmarg
    have hperm := (isPermutationInvariant_iff_commutes (σA.tensorPowGen n)).mp
      (tensorPow_isPermutationInvariant σA)
    have hP := tensor_one_commute_symmetricProjectorPairedGen
      (dR := dA * dB ^ 2) (σA.tensorPowGen n).toOp hperm
    exact Commute.mul_right hG hP
  -- transported Ψ facts (blocked register)
  set e := pairedToBlockedEquiv dA dB n with he_def
  set Ψb : Op (dA ^ n * (dA * dB ^ 2) ^ n) := Matrix.reindex e e Ψ.toOp with hΨb_def
  have hΨb_psd : Ψb.PosSemidef :=
    (posSemidefOp_implies_mathlib Ψ.toPosSemidefOp).reindex e
  obtain ⟨hPQ_herm, hPQ_proj⟩ :=
    groupBlockedSymmetricTwirl_isOrthogonalProjection (n := n) πA hπA πB hπB
  have hQX : (PG * P) * Ψb = Ψb :=
    groupBlockedSymmetricTwirl_mul_reindex_of_supported πA hπA πB hπB Ψ.toOp hΨ_grp hΨ_supp
  have hΨb_marg : partialTraceB Ψb = PA := by
    rw [hΨb_def, he_def, pairedToBlockedEquiv_partialTraceB_eq_roundGroup dA dB n Ψ.toOp,
      hΨ_marg, hPA_def]
    exact congrArg (fun τ : DensityOp (dA ^ n) => τ.toOp) hmarg
  let g : ℕ := deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n
  -- The trace of the product representation's twirl projector is `x` as a complex number
  -- (`groupTwirlProjector_prod_trace` + `hxA` + `hxB` + sum-product)
  have hxc : (groupTwirlProjector (prodRep πA πB)).trace =
      (((∑ i : Fin kA, ∑ j : Fin kB, mA i ^ 2 * mB j ^ 2 : ℕ) : ℕ) : ℂ) := by
    rw [groupTwirlProjector_prod_trace_sumSq πA hπA πB hπB mA mB hxA hxB]
    push_cast
    rfl
  have hPQ_trace : (PG * P).trace = (g : ℂ) :=
    groupBlockedSymmetricTwirl_trace πA hπA πB hπB hxc
  have hgC_ne : ((g : ℕ) : ℂ) ≠ 0 := by
    haveI : NeZero (∑ i : Fin kA, ∑ j : Fin kB, mA i ^ 2 * mB j ^ 2) :=
      ⟨Nat.cast_ne_zero.mp (by
        rw [← hxc]
        exact groupTwirlProjector_trace_ne_zero (prodRep πA πB)
          (prodRep_isUnitaryRep πA hπA πB hπB))⟩
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (deFinettiPrefactor_pos _ _))
  let S := Op.tensor (CFC.sqrt PA) (1 : Op ((dA * dB ^ 2) ^ n))
  let W := Op.tensor (CFC.sqrt κG) (1 : Op ((dA * dB ^ 2) ^ n))
  let T := S * (W * (PG * P) * W) * S
  obtain ⟨hT_psd, hdom⟩ := fixedMarginal_projection_domination (PG * P) Ψb hPA_pd hκG_pd
    hPQ_herm hPQ_proj hΨb_psd hQX hΨb_marg hAcomm hκG_comm hκGinv hPQ_trace
    (Nat.cast_ne_zero.mp hgC_ne)
  obtain ⟨μ, hμ_marg, hμ_grp, hμ_ref⟩ :=
    exists_groupMeasure_of_blockedReference πA hπA πB hπB σA hσA ρ hiid hmarg
      κG hκG_pd hκGinv
  refine ⟨μ, hμ_marg, hμ_grp, Matrix.reindex e.symm e.symm T,
    hT_psd.reindex e.symm, hμ_ref, ?_⟩
  have hswap : Matrix.reindex e.symm e.symm ((g : ℂ) • T - Ψb) =
      (g : ℂ) • Matrix.reindex e.symm e.symm T - Ψ.toOp := by
    rw [hΨb_def]
    ext a b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.smul_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  have h := hdom.reindex e.symm
  rwa [hswap] at h

/-- The group-symmetric de Finetti reduction with fixed marginal
(Nahar–Tupkary–Zhao–Lütkenhaus–Tan, Corollary `cor:symmetryDeFinetti`).

A permutation-invariant, IID product-group-invariant extension of `σA^⊗n` is
dominated by a mixture of tensor powers of group-invariant extensions of `σA`.
The prefactor is the dimension of the symmetric power of the paired group-twirl
range, whose dimension is `∑ i, ∑ j, (mA i)^2 * (mB j)^2`. -/
theorem deFinetti_groupSymmetric_fixedMarginal_op_le
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {dA dB n kA kB : ℕ} [NeZero dA] [NeZero dB] [NeZero (dA * dB)] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2))
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (ρ : DensityOp ((dA * dB) ^ n))
    (hperm : IsPermutationInvariant ρ)
    (hiid : IsIIDGroupInvariant (prodRep πA πB) ρ)
    (hmarg : roundwiseAliceMarginal ρ = σA.tensorPowGen n) :
    ∃ μ : DensityMeasure (dA * dB),
      IsFixedMarginalMeasure σA μ ∧
      IsGroupInvariantMeasure (prodRep πA πB) μ ∧
    (((deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℕ) : ℂ) •
        (deFinettiMixtureFixedMarginal dA dB n μ).toOp - ρ.toOp).PosSemidef := by
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  -- The group-symmetric purification (Lemma `lem:groupPurification`)
  obtain ⟨Ψ, _hΨ_pure, hΨ_marg, hΨ_grp, hΨ_supp⟩ :=
    groupPurification (prodRep πA πB) (prodRep_isUnitaryRep πA hπA πB hπB) ρ hperm hiid
  -- The purified group-symmetric domination, then trace out the purifying register
  obtain ⟨μ, hμ_marg, hμ_grp, τ_ABE, _hτ_psd, hτ_ptb, hτ_op⟩ :=
    deFinetti_groupSymmetric_purified_op_le πA hπA πB hπB mA mB hxA hxB σA hσA ρ hiid hmarg Ψ
      hΨ_grp hΨ_supp hΨ_marg
  refine ⟨μ, hμ_marg, hμ_grp, ?_⟩
  have hmono := Quantum.Channels.partialTraceB_psd_mono
    ((deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℂ) • τ_ABE)
    Ψ.toOp hτ_op
  rwa [partialTraceB_smul, hτ_ptb, hΨ_marg] at hmono

end InfoTheory.Postselection

end
