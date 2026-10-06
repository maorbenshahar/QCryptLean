import QCryptLean.Quantum.TensorProducts.TensorFamily
import QCryptLean.Quantum.Symmetry.FiniteGroupUnitaryRep
import QCryptLean.InfoTheory.DeFinetti.Measure
import QCryptLean.InfoTheory.Postselection.FixedMarginalDeFinetti
import QCryptLean.InfoTheory.Postselection.PairedBlockedOperators

/-!
# Group-invariant states and measures

Predicates for unitary representations acting on states: a state fixed by
conjugation under every group element, a tensor power invariant under
independent group actions on its factors, and a probability measure supported
on group-invariant states.
-/

open Equiv

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Matrix
open InfoTheory.DeFinetti
open scoped Matrix

noncomputable section

namespace InfoTheory.Postselection

/-! ### Group invariance predicates -/

/-- A state fixed by conjugation under every group element. -/
def IsGroupInvariantState {G : Type*} [Group G] {d : ℕ} (π : G → Op d) (σ : DensityOp d) : Prop :=
  ∀ g : G, π g * σ.toOp * (π g)ᴴ = σ.toOp

/-- A state invariant under independent group actions on its tensor factors. -/
def IsIIDGroupInvariant {G : Type*} [Group G] {d n : ℕ} (π : G → Op d)
    (ρ : DensityOp (d ^ n)) : Prop :=
  ∀ v : Fin n → G,
    tensorFamily (fun a => π (v a)) * ρ.toOp *
      (tensorFamily fun a => π (v a))ᴴ = ρ.toOp

/-- A probability measure supported almost everywhere on group-invariant states. -/
def IsGroupInvariantMeasure {G : Type*} [Group G] {d : ℕ} (π : G → Op d)
    (μ : DensityMeasure d) : Prop :=
  ∀ᵐ σ ∂μ.measure, IsGroupInvariantState π σ

/-- Every state is invariant under the trivial (constant-identity) representation. -/
lemma isGroupInvariantState_const_one {d : ℕ} (σ : DensityOp d) :
    IsGroupInvariantState (fun _ : Unit => (1 : Op d)) σ := by
  intro _g; simp

/-- Every measure is supported on states invariant under the trivial
(constant-identity) representation. -/
lemma isGroupInvariantMeasure_const_one {d : ℕ} (μ : DensityMeasure d) :
    IsGroupInvariantMeasure (fun _ : Unit => (1 : Op d)) μ := by
  filter_upwards with σ using isGroupInvariantState_const_one σ

/-- A nonempty tensor power determines its single-round density operator. -/
lemma tensorPowGen_injective {d n : ℕ} [NeZero d] [NeZero n] :
    Function.Injective (fun σ : DensityOp d => σ.tensorPowGen n) := by
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  exact Function.LeftInverse.injective (fun σ => partialTraceToFirst_tensorPowGen σ n)

/-- A tensor power is IID group-invariant exactly when its single-round state
is group-invariant. -/
lemma isIIDGroupInvariant_tensorPowGen_iff {G : Type*} [Group G]
    {d n : ℕ} [NeZero d] [NeZero n] (π : G → Op d) (hπ : IsUnitaryRep π)
    (σ : DensityOp d) :
    IsIIDGroupInvariant π (σ.tensorPowGen n) ↔ IsGroupInvariantState π σ := by
  constructor
  · intro h g
    let U : UnitaryOp d := ⟨π g, hπ.2 g,
      by rw [← hπ.inv, ← hπ.1, mul_inv_cancel, hπ.one]⟩
    have hpow : (U.evolve σ).tensorPowGen n = σ.tensorPowGen n := by
      apply DensityOp.ext
      simpa only [DensityOp.tensorPowGen_toOp_eq_tensorFamily, UnitaryOp.evolve, U,
        conjTranspose_tensorFamily, tensorFamily_mul] using h (fun _ => g)
    exact congrArg (fun τ : DensityOp d => τ.toOp) (tensorPowGen_injective hpow)
  · intro h v
    change ∀ g, π g * σ.toOp * (π g)ᴴ = σ.toOp at h
    simp only [DensityOp.tensorPowGen_toOp_eq_tensorFamily, conjTranspose_tensorFamily,
      tensorFamily_mul, h]

/-- Group-invariant states form a closed subset of the density operators. -/
lemma isClosed_isGroupInvariantState {G : Type*} [Group G] {d : ℕ}
    (π : G → Op d) : IsClosed (setOf (IsGroupInvariantState π)) := by
  change IsClosed (setOf fun σ : DensityOp d => ∀ g, π g * σ.toOp * (π g)ᴴ = σ.toOp)
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun g => isClosed_eq
    ((continuous_const.matrix_mul DensityOp.continuous_toOp).matrix_mul continuous_const)
    DensityOp.continuous_toOp

/-! ### Group-invariance of the fixed marginal -/

/-- **Round-wise marginal transport**: conjugating the interleaved state round-wise by
    `⊗ₖ (Xₖ ⊗ Yₖ)` with the `Yₖ` unitary conjugates the round-wise Alice marginal
    (`partialTraceB ∘ reindex roundGroupEquiv`) by `⊗ₖ Xₖ` — the `Yₖ`-conjugation of the
    traced `B`-register cancels under the partial trace
    (`partialTraceB_sandwich_tensor_unitary`). -/
lemma roundwiseAliceMarginal_conj {dA dB n : ℕ} [NeZero dA] [NeZero dB]
    (X : Fin n → Op dA) (Y : Fin n → Op dB) (hY : ∀ k, (Y k)ᴴ * Y k = 1)
    (M : Op ((dA * dB) ^ n)) :
    partialTraceB (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        (tensorFamily (fun k => Op.tensor (X k) (Y k)) * M *
          (tensorFamily fun k => Op.tensor (X k) (Y k))ᴴ))
      = tensorFamily X * partialTraceB (Matrix.reindex (roundGroupEquiv dA dB n)
          (roundGroupEquiv dA dB n) M) * (tensorFamily X)ᴴ := by
  set RG := roundGroupEquiv dA dB n with hRG
  set U := tensorFamily fun k => Op.tensor (X k) (Y k) with hU
  -- reindexing is multiplicative and star-preserving
  have h1 : Matrix.reindex RG RG (U * M * Uᴴ)
      = Matrix.reindex RG RG U * Matrix.reindex RG RG M * Matrix.reindex RG RG Uᴴ := by
    rw [Matrix.reindex_mul RG (U * M) Uᴴ, Matrix.reindex_mul RG U M]
  have h2 : Matrix.reindex RG RG U = Op.tensor (tensorFamily X) (tensorFamily Y) := by
    rw [hRG, roundGroupEquiv_eq_interleavingEquivGen_symm]
    exact tensorFamily_tensor_interleaving X Y
  have h3 : Matrix.reindex RG RG Uᴴ = Op.tensor (tensorFamily X)ᴴ (tensorFamily Y)ᴴ := by
    rw [← Matrix.conjTranspose_reindex RG RG U, h2, Op.tensor_conjTranspose]
  rw [h1, h2, h3]
  exact partialTraceB_sandwich_tensor_unitary (tensorFamily X) (tensorFamily X)ᴴ
    (tensorFamily Y) (conjTranspose_tensorFamily_mul_self hY) (Matrix.reindex RG RG M)

/-- **The fixed marginal is round-family `G_A`-invariant**: the round-wise Alice marginal
    `σ̂A^{⊗n}` of an IID-`G`-invariant state (`G = G_A × G_B` acting round-wise through
    `prodRep`) is invariant under the round-wise `G_A`-action `⊗ₖ πA(vₖ)` for every pattern
    `v : Fin n → G_A` — the `B`-half of the group action is unitary and cancels under the
    partial trace (`roundwiseAliceMarginal_conj`). -/
theorem sigmaA_tensorPowGen_invariant {G_A G_B : Type*} [Group G_A] [Group G_B]
    {dA dB n : ℕ} [NeZero dA] [NeZero dB]
    (πA : G_A → Op dA) (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (σA : DensityOp dA) (ρ : DensityOp ((dA * dB) ^ n))
    (hiid : IsIIDGroupInvariant (prodRep πA πB) ρ)
    (hmarg : roundwiseAliceMarginal ρ = σA.tensorPowGen n) :
    ∀ v : Fin n → G_A,
      tensorFamily (fun a => πA (v a)) * (σA.tensorPowGen n).toOp *
        (tensorFamily fun a => πA (v a))ᴴ = (σA.tensorPowGen n).toOp := by
  intro v
  -- The round-wise `G`-action with trivial `B`-pattern fixes `ρ` (`IsIIDGroupInvariant`)
  have hin : tensorFamily (fun a => Op.tensor (πA (v a)) (πB 1)) * ρ.toOp *
      (tensorFamily fun a => Op.tensor (πA (v a)) (πB 1))ᴴ = ρ.toOp :=
    hiid (fun a => (v a, 1))
  -- Transport through the round-wise Alice marginal: the `B`-unitary cancels
  have htrans := roundwiseAliceMarginal_conj (fun a => πA (v a)) (fun _ => πB 1)
    (fun _ => hπB.2 1) ρ.toOp
  rw [hin] at htrans
  -- `(roundwiseAliceMarginal ρ).toOp` is the blocked-Alice partial trace of `ρ`
  have hXdef : (roundwiseAliceMarginal ρ).toOp =
      partialTraceB (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        ρ.toOp) := rfl
  have htoOp : (roundwiseAliceMarginal ρ).toOp = (σA.tensorPowGen n).toOp := by
    rw [hmarg]
  rw [← htoOp, hXdef]
  exact htrans.symm

end InfoTheory.Postselection
