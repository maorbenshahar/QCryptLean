import QCryptLean.Quantum.TensorProducts.TensorFamily
import QCryptLean.Quantum.Symmetry.FiniteGroupUnitaryRep
import QCryptLean.Quantum.Channels.CPTP.CKRBound.UnitaryFamilyReduction
import QCryptLean.InfoTheory.DeFinetti.Purification
import QCryptLean.InfoTheory.Postselection.MapSymmetry
import QCryptLean.InfoTheory.Postselection.GroupInvariantStates
import QCryptLean.InfoTheory.Postselection.PairedBlockedTransport

/-!
# Group twirl of round-grouped states

The group twirl of a state on the round-grouped register `(dA * dB) ^ n` over the round
patterns `v : Fin n → G_A × G_B`, acting through the product representation
`prodRep πA πB` of finite groups `G_A, G_B` (Nahar et al., arXiv:2403.11851, Def. 6).

## Main definitions

- `InfoTheory.Postselection.prodRepUnitary` : the single-round product-representation
  operators `prodRep πA πB g`, bundled as `UnitaryOp`s.
- `InfoTheory.Postselection.groupTwirlDensity` : the round-grouped group twirl of a density
  state, `(1/|G|ⁿ) • ∑_v (⊗ⱼ prodRep πA πB (v j)) σ (⊗ⱼ prodRep πA πB (v j))ᴴ`, as a density
  operator.

## Main statements

- `Quantum.Channels.purification_bound_of_family_twirl` : purification bound for a state
  with an arbitrary Eve ancilla against a purification of the family-twirl of its marginal
  (the generic unitary-family reduction underlying the group twirl).
- `InfoTheory.Postselection.purification_bound_of_groupTwirl` : the group-twirl
  instantiation of `purification_bound_of_family_twirl` through
  `IsIIDGroupInvariantMap` of `prodRep πA πB`.
- `InfoTheory.Postselection.roundwiseAliceMarginal_groupTwirl` : the twirl preserves
  round-wise Alice marginals fixed by a `πA`-invariant state.
- `InfoTheory.Postselection.isIIDGroupInvariant_groupTwirlDensity` : the twirl is
  IID-`G`-invariant for `prodRep πA πB`.

## References

- Nahar, Tupkary, Zhao, Lütkenhaus, Tan, arXiv:2403.11851, Def. 6; the proof sketch of
  `cor:symmetryDeFinetti` (main.tex:527–529).
-/

open Equiv

open Quantum.Operators Quantum.Symmetry Quantum.TensorProducts Matrix Quantum.Metrics
  Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Fixed-marginal reduction over a unitary family: a state `ρ` with an
arbitrary Eve ancilla is dominated in `mapTensorId Δ`-trace norm by any purification `Ψ` of
the family-twirl `(1/k) ∑ i, U i (Tr_E ρ) (U i)ᴴ` of its marginal. Step 1 folds the ancilla
into a square purification `Ψ₀` of the marginal (substate bound, no symmetry); step 2 is the
family block-diagonal averaging (`block_diagonal_purification_bound_family`). -/
lemma purification_bound_of_family_twirl {d n k eveDim dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero k] [NeZero eveDim] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (U : Fin k → Op (d ^ n))
    (hU_unit : ∀ i : Fin k, (U i)ᴴ * U i = 1 ∧ U i * (U i)ᴴ = 1)
    (hΔ_cov : ∀ i : Fin k, ∃ (K K' : Op dimOut → Op dimOut), IsCPTP K ∧ IsCPTP K' ∧
      (∀ σ : Op (d ^ n), Δ (U i * σ * (U i)ᴴ) = K (Δ σ)) ∧
      (∀ σ : Op (d ^ n), Δ ((U i)ᴴ * σ * U i) = K' (Δ σ)))
    (ρ : DensityOp (d ^ n * eveDim))
    (Ψ : DensityOp (d ^ n * d ^ n))
    (hΨ_pure : Ψ.IsPure)
    (hΨ_marg : partialTraceB Ψ.toOp =
      (1 / (k : ℂ)) • ∑ i : Fin k, U i * ρ.partialTraceB.toOp * (U i)ᴴ) :
    traceNorm (mapTensorId Δ ρ.toOp) ≤ traceNorm (mapTensorId Δ Ψ.toOp) := by
  have : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  -- square purification `Ψ₀` of the round-grouped marginal of `ρ`
  set σnorm : DensityOp (d ^ n) := ρ.partialTraceB with hσnorm_def
  set Ψ0 : DensityOp (d ^ n * d ^ n) := InfoTheory.DeFinetti.purificationDensityOp σnorm
    with hΨ0_def
  have hΨ0_pure : Ψ0.IsPure := InfoTheory.DeFinetti.purificationDensityOp_isPure _
  have hΨ0_marg : Ψ0.partialTraceB = σnorm :=
    InfoTheory.DeFinetti.purificationDensityOp_partialTraceB _
  have hσnorm_toOp : partialTraceB ρ.toOp = σnorm.toOp := rfl
  -- STEP 1: fold the ancilla `eveDim` into the square-ancilla purification `Ψ₀`
  have step1 : traceNorm (mapTensorId Δ ρ.toOp) ≤ traceNorm (mapTensorId Δ Ψ0.toOp) := by
    have h_dom : (((1 : ℝ) : ℂ) • Ψ0.partialTraceB.toOp - partialTraceB ρ.toOp).PosSemidef := by
      have h_eq : Ψ0.partialTraceB.toOp = partialTraceB ρ.toOp := by
        rw [hΨ0_marg, hσnorm_toOp]
      rw [Complex.ofReal_one, one_smul, h_eq, sub_self]
      exact Matrix.PosSemidef.zero
    have h := traceNorm_mapTensorId_substate_bound Δ ρ.toOp
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) Ψ0 hΨ0_pure 1 one_pos h_dom
    simpa using h
  -- STEP 2: family block-diagonal averaging → purification `Ψ` of the family-twirl marginal
  have hΨ0_nz : Ψ0.toOp ≠ 0 := by
    intro h
    have := Ψ0.trace_one
    rw [h] at this
    simp at this
  have hΨ0_trace : Ψ0.toOp.trace.re ≤ 1 := by rw [Ψ0.trace_one]; simp
  have hΨ0_ptB_toOp : partialTraceB Ψ0.toOp = σnorm.toOp :=
    congrArg (fun d => d.toOp) hΨ0_marg
  have hσnorm_rel : σnorm.toOp = (1 / Ψ0.toOp.trace) • partialTraceB Ψ0.toOp := by
    rw [hΨ0_ptB_toOp, Ψ0.trace_one]; simp
  have step2 : traceNorm (mapTensorId Δ Ψ0.toOp) ≤ traceNorm (mapTensorId Δ Ψ.toOp) := by
    have hΨ_marginal : partialTraceB Ψ.toOp =
        (1 / (k : ℂ)) • ∑ i : Fin k, U i * σnorm.toOp * (U i)ᴴ := by
      rw [hΨ_marg, hσnorm_def]
    exact block_diagonal_purification_bound_family Δ U hU_unit hΔ_cov Ψ0.toOp
      (posSemidefOp_implies_mathlib Ψ0.toPosSemidefOp) hΨ0_trace hΨ0_nz
      σnorm hσnorm_rel Ψ hΨ_pure hΨ_marginal
  calc traceNorm (mapTensorId Δ ρ.toOp)
      ≤ traceNorm (mapTensorId Δ Ψ0.toOp) := step1
    _ ≤ traceNorm (mapTensorId Δ Ψ.toOp) := step2

end Quantum.Channels

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-- The single-round product-representation operators `prodRep πA πB g`, bundled as
`UnitaryOp`s (unitarity from `IsUnitaryRep` of `prodRep`). -/
def prodRepUnitary {G_A G_B : Type*} [Group G_A] [Group G_B]
    {dA dB : ℕ} (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
    (G_A × G_B) → UnitaryOp (dA * dB) := fun g =>
  ⟨prodRep πA πB g, (prodRep_isUnitaryRep πA hπA πB hπB).2 g, by
    have hπG := prodRep_isUnitaryRep πA hπA πB hπB
    rw [← hπG.inv g, ← hπG.1, mul_inv_cancel, hπG.one]⟩

@[simp] lemma prodRepUnitary_toOp {G_A G_B : Type*} [Group G_A] [Group G_B]
    {dA dB : ℕ} (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) (g : G_A × G_B) :
    (prodRepUnitary πA hπA πB hπB g).toOp = prodRep πA πB g := rfl

/-- **Purification bound under the group twirl**: the group-twirl instantiation of
`Quantum.Channels.purification_bound_of_family_twirl`. The map-invariance hypothesis `hG`
(Nahar et al. Def. 6, instantiated at the product representation `prodRep πA πB`) makes `Δ`
CPTP-covariant in both directions under the round-pattern unitary families
`⊗ⱼ prodRep πA πB (v j)` (forward covariance at the pattern `v`, backward covariance at the
pointwise inverse `v⁻¹`, via `IsUnitaryRep.inv`). Hence a state `ρ` with an arbitrary Eve
ancilla is dominated in `mapTensorId Δ`-trace norm by any purification `Ψ` of the group twirl
of `ρ`'s round-marginal over the patterns `v : Fin n → G_A × G_B`; the `Fin k`-indexed family
of the generic lemma is obtained through `Fintype.equivFin`, and the marginal is reindexed
back to the group by `Equiv.sum_comp`. -/
lemma purification_bound_of_groupTwirl
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {eveDim dimOut : ℕ} [NeZero eveDim] [NeZero dimOut]
    (Δ : Op ((dA * dB) ^ n) →ₗ[ℂ] Op dimOut)
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (hG : ∀ (W : (G_A × G_B) → UnitaryOp (dA * dB)), (∀ g : G_A × G_B,
        (W g).toOp = prodRep πA πB g) → IsIIDGroupInvariantMap W Δ)
    (ρ : DensityOp ((dA * dB) ^ n * eveDim))
    (Ψ : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n))
    (hΨ_pure : Ψ.IsPure)
    (hΨ_marg : partialTraceB Ψ.toOp =
      ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
        ∑ v : Fin n → G_A × G_B,
          tensorFamily (fun j => prodRep πA πB (v j)) * ρ.partialTraceB.toOp *
            (tensorFamily fun j => prodRep πA πB (v j))ᴴ) :
    Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ ρ.toOp) ≤
      Quantum.Metrics.traceNorm (Quantum.Channels.mapTensorId Δ Ψ.toOp) := by
  have hAB : NeZero (dA * dB) := ⟨mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  have hABn : NeZero ((dA * dB) ^ n) := ⟨pow_ne_zero n (NeZero.ne (dA * dB))⟩
  have hπG : IsUnitaryRep (prodRep πA πB) := prodRep_isUnitaryRep πA hπA πB hπB
  -- bundle the single-round group unitaries as `UnitaryOp`s with toOp = prodRep πA πB
  set W : (G_A × G_B) → UnitaryOp (dA * dB) := prodRepUnitary πA hπA πB hπB with hW_def
  have hW_toOp : ∀ g : G_A × G_B, (W g).toOp = prodRep πA πB g := fun _ => rfl
  have hinvar : IsIIDGroupInvariantMap W Δ := hG W hW_toOp
  -- covariance of `Δ` under the round-pattern unitary families, in both directions
  have hΔ_cov : ∀ v : Fin n → G_A × G_B,
      ∃ (K K' : Op dimOut → Op dimOut), Quantum.Channels.IsCPTP K ∧
        Quantum.Channels.IsCPTP K' ∧
        (∀ σ : Op ((dA * dB) ^ n),
          Δ (tensorFamily (fun j => prodRep πA πB (v j)) * σ *
            (tensorFamily fun j => prodRep πA πB (v j))ᴴ) = K (Δ σ)) ∧
        (∀ σ : Op ((dA * dB) ^ n),
          Δ ((tensorFamily fun j => prodRep πA πB (v j))ᴴ * σ *
            tensorFamily (fun j => prodRep πA πB (v j))) = K' (Δ σ)) := by
    intro v
    -- forward: covariance at the pattern `v`; backward: covariance at `v⁻¹`
    obtain ⟨K, hK, hKcov⟩ := hinvar.invariance v
    obtain ⟨K', hK', hK'cov⟩ := hinvar.invariance (fun j => (v j)⁻¹)
    refine ⟨K, K', hK, hK', ?_, ?_⟩
    · intro σ
      exact hKcov σ
    · intro σ
      -- `(⊗ⱼ prodRep (v j))ᴴ = ⊗ⱼ (W ((v j)⁻¹)).toOp = (⊗ⱼ (W ((v j)⁻¹)).toOp)ᴴᴴ`
      have hconv : ∀ g : G_A × G_B, (W (g⁻¹)).toOp = (prodRep πA πB g)ᴴ := fun g => by
        rw [hW_toOp, hπG.inv g]
      have e1 : (tensorFamily fun j => prodRep πA πB (v j))ᴴ =
          tensorFamily (fun j => (W ((v j)⁻¹)).toOp) := by
        rw [conjTranspose_tensorFamily]
        exact congrArg tensorFamily (funext fun j => (hconv (v j)).symm)
      have e2 : tensorFamily (fun j => prodRep πA πB (v j)) =
          (tensorFamily (fun j => (W ((v j)⁻¹)).toOp))ᴴ := by
        rw [conjTranspose_tensorFamily]
        exact congrArg tensorFamily (funext fun j => by
          rw [hconv (v j), Matrix.conjTranspose_conjTranspose])
      rw [e1, e2]
      exact hK'cov σ
  -- the `Fin k`-indexed family of round-pattern unitaries and the reindexed marginal
  set e := Fintype.equivFin (Fin n → G_A × G_B) with he
  set k := Fintype.card (Fin n → G_A × G_B) with hk
  have hpi : Nonempty (Fin n → G_A × G_B) := ⟨fun _ => (1, 1)⟩
  have hkne : NeZero k := ⟨Fintype.card_ne_zero⟩
  have hU_unit : ∀ i : Fin k,
      (tensorFamily (fun j => prodRep πA πB (e.symm i j)))ᴴ *
        tensorFamily (fun j => prodRep πA πB (e.symm i j)) = 1 ∧
      tensorFamily (fun j => prodRep πA πB (e.symm i j)) *
        (tensorFamily (fun j => prodRep πA πB (e.symm i j)))ᴴ = 1 :=
    fun i => ⟨conjTranspose_tensorFamily_mul_self fun j => hπG.2 (e.symm i j),
      tensorFamily_mul_conjTranspose_self fun j => mul_eq_one_comm.mpr (hπG.2 (e.symm i j))⟩
  have h_marg : partialTraceB Ψ.toOp =
      (1 / (k : ℂ)) • ∑ i : Fin k,
        tensorFamily (fun j => prodRep πA πB (e.symm i j)) * ρ.partialTraceB.toOp *
          (tensorFamily fun j => prodRep πA πB (e.symm i j))ᴴ := by
    rw [hΨ_marg]
    simp only [one_div]
    exact congrArg (fun s : Op ((dA * dB) ^ n) => ((k : ℕ) : ℂ)⁻¹ • s)
      (Equiv.sum_comp e.symm fun v : Fin n → G_A × G_B =>
        tensorFamily (fun j => prodRep πA πB (v j)) * ρ.partialTraceB.toOp *
          (tensorFamily fun j => prodRep πA πB (v j))ᴴ).symm
  exact Quantum.Channels.purification_bound_of_family_twirl Δ
    (fun i : Fin k => tensorFamily (fun j => prodRep πA πB (e.symm i j)))
    hU_unit (fun i => hΔ_cov (e.symm i)) ρ Ψ hΨ_pure h_marg

/-- **Round-wise Alice marginal of the group twirl.** If `M` on the
round-grouped register `(dA·dB)^n` has round-wise Alice marginal `(σA^{⊗n}).toOp`, then its
group twirl over the round patterns `v : Fin n → G_A × G_B` (through `prodRep πA πB`) has the
same marginal. Each summand transports by `roundwiseAliceMarginal_conj` to the conjugation of
`(σA^{⊗n}).toOp` by `⊗ⱼ πA ((v j).1)` — the `B`-half `πB ((v j).2)` cancels under the partial
trace — which fixes the tensor power because `σA` is `πA`-invariant
(`isIIDGroupInvariant_tensorPowGen_iff`). Hence every summand has the same marginal and the
uniform average collapses. -/
lemma roundwiseAliceMarginal_groupTwirl
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (σA : DensityOp dA) (hσinv : IsGroupInvariantState πA σA)
    (M : Op ((dA * dB) ^ n))
    (hmarg : partialTraceB (Matrix.reindex (roundGroupEquiv dA dB n)
        (roundGroupEquiv dA dB n) M) = (σA.tensorPowGen n).toOp) :
    partialTraceB (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        (((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
          ∑ v : Fin n → G_A × G_B,
            tensorFamily (fun j => prodRep πA πB (v j)) * M *
              (tensorFamily fun j => prodRep πA πB (v j))ᴴ))
      = (σA.tensorPowGen n).toOp := by
  have : Nonempty (Fin n → G_A × G_B) := ⟨fun _ => (1, 1)⟩
  have hcard_ne : ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Fin n → G_A × G_B)
  -- push `reindex` through the scalar multiple and the finite sum (entrywise)
  have hpush : Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        (((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
          ∑ v : Fin n → G_A × G_B,
            tensorFamily (fun j => prodRep πA πB (v j)) * M *
              (tensorFamily fun j => prodRep πA πB (v j))ᴴ)
      = ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
        ∑ v : Fin n → G_A × G_B,
          Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
            (tensorFamily (fun j => prodRep πA πB (v j)) * M *
              (tensorFamily fun j => prodRep πA πB (v j))ᴴ) := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  rw [hpush, partialTraceB_smul, partialTraceB_finset_sum]
  -- `σA^{⊗n}` is IID-`πA`-invariant because `σA` is `πA`-invariant
  have hiid : IsIIDGroupInvariant πA (σA.tensorPowGen n) :=
    (isIIDGroupInvariant_tensorPowGen_iff πA hπA σA).2 hσinv
  -- each summand has marginal `(σA^{⊗n}).toOp`: the `B`-unitary cancels under the
  -- partial trace and the `A`-conjugation fixes the tensor power
  have hterm : ∀ v : Fin n → G_A × G_B,
      partialTraceB (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
        (tensorFamily (fun j => prodRep πA πB (v j)) * M *
          (tensorFamily fun j => prodRep πA πB (v j))ᴴ)) = (σA.tensorPowGen n).toOp := by
    intro v
    have h1 := roundwiseAliceMarginal_conj (fun j => πA ((v j).1)) (fun j => πB ((v j).2))
      (fun j => hπB.2 ((v j).2)) M
    rw [hmarg] at h1
    exact h1.trans (hiid (fun j => (v j).1))
  simp_rw [hterm]
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ _ _, smul_smul, Finset.card_univ,
    inv_mul_cancel₀ hcard_ne, one_smul]

/-- **The round-grouped group twirl of a density state, as a density operator:**
`(1/|G|ⁿ) • ∑_v (⊗ⱼ prodRep πA πB (v j)) σ (⊗ⱼ prodRep πA πB (v j))ᴴ`. Each summand is a
unitary conjugate of `σ` (Hermitian, PSD, trace one), so the uniform average is again a
density operator; the unitarity of the pattern unitaries comes from `IsUnitaryRep.2` of
`prodRep` through `conjTranspose_tensorFamily_mul_self`. -/
def groupTwirlDensity {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (σ : DensityOp ((dA * dB) ^ n)) : DensityOp ((dA * dB) ^ n) where
  toOp := ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
    ∑ v : Fin n → G_A × G_B,
      tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
        (tensorFamily fun j => prodRep πA πB (v j))ᴴ
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
    -- the scalar is real, so it is fixed by the star
    have hsc : star (((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹) =
        ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ := by
      rw [RCLike.star_def, Complex.conj_inv, Complex.conj_natCast]
    have hσherm : (σ.toOp)ᴴ = σ.toOp := σ.toPosSemidefOp.toHermitianOp.isHermitian
    rw [hsc]
    congr 1
    exact Finset.sum_congr rfl fun v _ => by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hσherm, mul_assoc]
  pos_semidef := by
    intro x
    have hσpsd : σ.toOp.PosSemidef := posSemidefOp_implies_mathlib σ.toPosSemidefOp
    -- each conjugate sandwich is PSD; a sum of PSD matrices is PSD, and a
    -- nonnegative-real scaling preserves PSD (same pattern as `twirlFamily_posSemidef`)
    have hpsd := Quantum.Operators.posSemidef_smul_of_nonneg_re
      (((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹)
      (∑ v : Fin n → G_A × G_B,
        tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
          (tensorFamily fun j => prodRep πA πB (v j))ᴴ)
      (Finset.sum_induction
        (fun (v : Fin n → G_A × G_B) =>
          tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
            (tensorFamily fun j => prodRep πA πB (v j))ᴴ)
        Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add) Matrix.PosSemidef.zero
        (fun v _ => hσpsd.mul_mul_conjTranspose_same
          (tensorFamily fun j => prodRep πA πB (v j)))) ?_ ?_
    · exact posSemidef_re_quadraticForm_nonneg hpsd x
    · rw [Complex.inv_re, Complex.natCast_re]
      exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
    · rw [Complex.inv_im, Complex.natCast_im, neg_zero, zero_div]
  trace_one := by
    have hπG : IsUnitaryRep (prodRep πA πB) := prodRep_isUnitaryRep πA hπA πB hπB
    have hcard_ne : ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero (α := Fin n → G_A × G_B)
    rw [Matrix.trace_smul, Matrix.trace_sum]
    -- each summand is a unitary conjugate of `σ`, hence has the same trace
    have hterm : ∀ v : Fin n → G_A × G_B,
        (tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
            (tensorFamily fun j => prodRep πA πB (v j))ᴴ).trace = σ.toOp.trace := by
      intro v
      rw [Matrix.trace_mul_cycle, conjTranspose_tensorFamily_mul_self
        (fun j => hπG.2 (v j)), Matrix.one_mul]
    simp only [hterm]
    rw [σ.trace_one, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ _ _, smul_smul,
      Finset.card_univ, inv_mul_cancel₀ hcard_ne, one_smul]

omit [NeZero dA] [NeZero dB] [NeZero n] in
/-- The underlying operator of the group twirl is the uniform average of the round-pattern
unitary conjugates (definitional). -/
lemma groupTwirlDensity_toOp {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A]
    [Fintype G_B] (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) (σ : DensityOp ((dA * dB) ^ n)) :
    (groupTwirlDensity πA hπA πB hπB σ).toOp =
      ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
        ∑ v : Fin n → G_A × G_B,
          tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
            (tensorFamily fun j => prodRep πA πB (v j))ᴴ := rfl

omit [NeZero dA] [NeZero dB] [NeZero n] in
/-- **The group twirl is IID-`G`-invariant.** Conjugating the twirl by the pattern
unitary `⊗ⱼ prodRep πA πB (w j)` pushes inside the sum (scalars and sums commute with matrix
products), turning each summand into the summand at the pointwise product pattern `w * v`
(`tensorFamily_mul` + multiplicativity `IsUnitaryRep.1` of `prodRep`); the pattern change
`v ↦ w * v` is a bijection (inverse `u ↦ w⁻¹ * u`), so the sum reindexes back. -/
lemma isIIDGroupInvariant_groupTwirlDensity
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (σ : DensityOp ((dA * dB) ^ n)) :
    IsIIDGroupInvariant (prodRep πA πB) (groupTwirlDensity πA hπA πB hπB σ) := by
  have hπG : IsUnitaryRep (prodRep πA πB) := prodRep_isUnitaryRep πA hπA πB hπB
  -- the pattern unitaries multiply pointwise: `U v · U w' = U (v · w')`
  have hUmul : ∀ v w' : Fin n → G_A × G_B,
      tensorFamily (fun j => prodRep πA πB (v j)) *
        tensorFamily (fun j => prodRep πA πB (w' j)) =
        tensorFamily (fun j => prodRep πA πB (v j * w' j)) := fun v w' => by
    rw [tensorFamily_mul]
    exact congrArg tensorFamily (funext fun j => (hπG.1 (v j) (w' j)).symm)
  -- conjugating a summand by `U w` is the summand at the pointwise product pattern `w · v`
  have key : ∀ (w v : Fin n → G_A × G_B),
      tensorFamily (fun j => prodRep πA πB (w j)) *
        (tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
          (tensorFamily fun j => prodRep πA πB (v j))ᴴ) *
        (tensorFamily fun j => prodRep πA πB (w j))ᴴ
      = tensorFamily (fun j => prodRep πA πB (w j * v j)) * σ.toOp *
          (tensorFamily fun j => prodRep πA πB (w j * v j))ᴴ := by
    intro w v
    -- reassociate: `U w · (U v M U vᴴ) · U wᴴ = (U w · U v) M (U w · U v)ᴴ`
    have hassoc : tensorFamily (fun j => prodRep πA πB (w j)) *
        (tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
          (tensorFamily fun j => prodRep πA πB (v j))ᴴ) *
        (tensorFamily fun j => prodRep πA πB (w j))ᴴ
      = (tensorFamily (fun j => prodRep πA πB (w j)) *
          tensorFamily (fun j => prodRep πA πB (v j))) * σ.toOp *
        (tensorFamily (fun j => prodRep πA πB (w j)) *
          tensorFamily (fun j => prodRep πA πB (v j)))ᴴ := by
      simp only [mul_assoc, Matrix.conjTranspose_mul]
    rw [hassoc, hUmul w v]
  intro w
  -- unfold the twirl to its defining operator average
  change tensorFamily (fun j => prodRep πA πB (w j)) *
        (((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
          ∑ v : Fin n → G_A × G_B,
            tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
              (tensorFamily fun j => prodRep πA πB (v j))ᴴ) *
        (tensorFamily fun j => prodRep πA πB (w j))ᴴ
      = (((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
          ∑ v : Fin n → G_A × G_B,
            tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
              (tensorFamily fun j => prodRep πA πB (v j))ᴴ)
  -- fold the scalar into the conjugation and push `U w` inside the sum
  have hstep : tensorFamily (fun j => prodRep πA πB (w j)) *
        (((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
          ∑ v : Fin n → G_A × G_B,
            tensorFamily (fun j => prodRep πA πB (v j)) * σ.toOp *
              (tensorFamily fun j => prodRep πA πB (v j))ᴴ) *
        (tensorFamily fun j => prodRep πA πB (w j))ᴴ
      = ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
        ∑ v : Fin n → G_A × G_B,
          tensorFamily (fun j => prodRep πA πB (w j * v j)) * σ.toOp *
            (tensorFamily fun j => prodRep πA πB (w j * v j))ᴴ := by
    rw [mul_smul_comm, ← smul_mul_assoc, Matrix.mul_sum, Finset.sum_mul]
    -- push the scalar out of each summand (`smul` then `key`), pull it out of the sum
    have hterm : ∀ i : Fin n → G_A × G_B,
        (((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
            tensorFamily (fun j => prodRep πA πB (w j)) *
              (tensorFamily (fun j => prodRep πA πB (i j)) * σ.toOp *
                (tensorFamily fun j => prodRep πA πB (i j))ᴴ) *
          (tensorFamily fun j => prodRep πA πB (w j))ᴴ)
      = ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ •
          (tensorFamily (fun j => prodRep πA πB (w j * i j)) * σ.toOp *
            (tensorFamily fun j => prodRep πA πB (w j * i j))ᴴ) := by
      intro i
      rw [smul_mul_assoc, smul_mul_assoc, key w i]
    simp only [hterm]
    rw [← Finset.smul_sum]
  rw [hstep]
  -- reindex the patterns `v ↦ w · v` (bijection with inverse `u ↦ w⁻¹ · u`)
  exact congrArg (fun s : Op ((dA * dB) ^ n) =>
      ((Fintype.card (Fin n → G_A × G_B) : ℕ) : ℂ)⁻¹ • s)
    (Equiv.sum_comp
      { toFun := fun v => w * v
        invFun := fun u => w⁻¹ * u
        left_inv := fun v => by funext j; simp
        right_inv := fun u => by funext j; simp }
      (fun u : Fin n → G_A × G_B =>
        tensorFamily (fun j => prodRep πA πB (u j)) * σ.toOp *
          (tensorFamily fun j => prodRep πA πB (u j))ᴴ))

end InfoTheory.Postselection
