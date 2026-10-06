import QCryptLean.InfoTheory.Postselection.FixedMarginalDeFinetti
import QCryptLean.Quantum.TensorProducts.RoundRegrouping
import QCryptLean.InfoTheory.Postselection.MapSymmetry
import QCryptLean.InfoTheory.Postselection.PairedBlockedOperators
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction

/-!
# QKD postselection — fixed-marginal de Finetti trace-norm reduction (Nahar et al. Lemma 3)

Faithful transcription of the **fixed-marginal** de Finetti trace-norm reduction of
Nahar–Tupkary–Zhao–Lütkenhaus–Tan 2024 (arXiv:2403.11851), **Lemma 3 / main.tex:430–:432 (unlabeled;
inside `\label{lemma:endOfStepOne}` :427–:433, Lemma 3) and `\label{eq:incor2.1}`
(main.tex:502–:505, inside `\label{cor:liftToCoherent}` :495–:499)**
(the "CKR de Finetti reduction" step of Corollary 3.1).

This turns the fixed-marginal *operator* inequality of
`InfoTheory.Postselection.deFinetti_fixedMarginal_op_le` (Nahar et al. Corollary 1.1) into the
*trace-norm* domination

  `‖(Δ ⊗ id_{R''}) ρ‖₁ ≤ g_{n,x} · ‖(Δ ⊗ id_R) τ_R‖₁`,   `x = d_A² d_B²`,

for a permutation-invariant (covariant) map `Δ`, an **arbitrary purifying ancilla `R''`**,
and any input `ρ` whose round-wise Alice marginal is `σ̂A^{⊗n}` (fixed marginal). The
reference `τ_R = deFinettiMixturePurification` is Nahar et al.'s fixed-marginal de Finetti
purification (main.tex:483–:486 (unlabeled; the `\tau_{A^nB^n}` mixture inside
`\label{thm:maintheorem}` :481–:491) / main.tex:575–:578 (unlabeled; the `\tau_{A^nB^n}` mixture
inside `\label{thm:maintheoremvar}` :573–:590)), with Alice marginal `σ̂A`.

Unlike the universal CKR route (`Quantum.Channels.ckr_per_operator_bound_paired_core`),
this reduction never touches the
diamond norm / Kitaev–Watrous maximization: the arbitrary ancilla `R''` is handled *natively*
by the substate-extraction engine (`traceNorm_mapTensorId_substate_bound`), exactly as Nahar et
al.'s
Lemma 3 is native for an arbitrary purifying register.

## Main statements
- `InfoTheory.Postselection.roundwiseAliceMarginal_symmetrize` : symmetrization over the round
  permutations preserves the round-wise Alice marginal `σ̂A^{⊗n}`.
- `InfoTheory.Postselection.deFinetti_fixedMarginal_traceNorm_le` : Nahar et al. Lemma 3 /
main.tex:430–:432 (unlabeled; inside `\label{lemma:endOfStepOne}` :427–:433, Lemma 3) and
`\label{eq:incor2.1}` (main.tex:502–:505, inside `\label{cor:liftToCoherent}` :495–:499),
  the fixed-marginal de Finetti trace-norm reduction.

## Route

Given `ρ_{AⁿBⁿR''}` (arbitrary ancilla `R''`) with round-wise Alice marginal `σ̂A^{⊗n}`:
1. reduce the arbitrary ancilla `R''` to the square ancilla by dominating `ρ` with a
   purification `Ψ₀` of its marginal `σ = Tr_{R''}ρ` (`traceNorm_mapTensorId_substate_bound`
   at `α = 1`, marginal domination `σ − σ = 0 ⪰ 0`);
2. block-diagonal permutation averaging (`block_diagonal_purification_bound`, using
   permutation-covariance of `Δ`) replaces `Ψ₀` by a symmetric purification `Ψ_sym` of the
   symmetrized marginal `symmetrize σ`, preserving the trace norm;
3. the fixed-marginal operator inequality `deFinetti_fixedMarginal_op_le` applied to the
   permutation-invariant `symmetrize σ` (whose round-wise Alice marginal is still `σ̂A^{⊗n}`
   by `roundwiseAliceMarginal_symmetrize`) yields the domination
   `g · τ − symmetrize σ ⪰ 0`, so the final substate bound
   (`traceNorm_mapTensorId_substate_bound` at `α = g`) gives the `g`-factor against `τ_R`.
-/

open Equiv

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts Quantum.Symmetry
open InfoTheory.DeFinetti Math.RepresentationTheory
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-- **Symmetrization preserves the round-wise Alice marginal.**

    If a state `σ` on the round-grouped register `(d_A d_B)^n` has round-wise Alice marginal
    `Tr_{Bⁿ}σ = σ̂A^{⊗n}`, then so does its permutation symmetrization
    `symmetrize σ = (1/n!)∑_π P_π σ P_π†`. The round permutation `P_π` acts on the
    `(d_A d_B)^n` register by the site permutation `π`, which under the round-regrouping
    `roundGroupEquiv` splits as the simultaneous `Aⁿ`/`Bⁿ` block permutation; tracing out
    `Bⁿ` therefore intertwines `P_π` with the Alice-side permutation `P_π^{A}`, and
    `σ̂A^{⊗n}` (a tensor power) is fixed by every `P_π^{A}`. -/
theorem roundwiseAliceMarginal_symmetrize
    (σ : DensityOp ((dA * dB) ^ n)) (σA : DensityOp dA)
    (hmarg : roundwiseAliceMarginal σ = σA.tensorPowGen n) :
    roundwiseAliceMarginal (symmetrize σ) = σA.tensorPowGen n := by
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero (dA ^ n) := ⟨pow_ne_zero n (NeZero.ne dA)⟩
  set e := roundGroupEquiv dA dB n with he
  -- Per-permutation covariance of the round-wise Alice marginal.
  have hcov : ∀ π : Equiv.Perm (Fin n),
      partialTraceB (Matrix.reindex e e
          (permutationRepresentation (dA * dB) n π * σ.toOp *
            (permutationRepresentation (dA * dB) n π)ᴴ)) =
        permutationRepresentation dA n π * (σA.tensorPowGen n).toOp *
          (permutationRepresentation dA n π)ᴴ := by
    intro π
    have hmul : Matrix.reindex e e
          (permutationRepresentation (dA * dB) n π * σ.toOp *
            (permutationRepresentation (dA * dB) n π)ᴴ) =
        Op.tensor (permutationRepresentation dA n π) (permutationRepresentation dB n π) *
          Matrix.reindex e e σ.toOp *
          (Op.tensor (permutationRepresentation dA n π)
            (permutationRepresentation dB n π))ᴴ := by
      rw [← Matrix.reindexAlgEquiv_apply ℂ ℂ, map_mul, map_mul,
        Matrix.reindexAlgEquiv_apply, Matrix.reindexAlgEquiv_apply,
        Matrix.reindexAlgEquiv_apply, he, reindex_roundGroupEquiv_permRep,
        ← Matrix.conjTranspose_reindex, reindex_roundGroupEquiv_permRep]
    rw [hmul, Op.tensor_conjTranspose,
      partialTraceB_sandwich_tensor_unitary
        (permutationRepresentation dA n π) (permutationRepresentation dA n π)ᴴ
        (permutationRepresentation dB n π) (permutationRepresentation_unitary dB n π).1]
    congr 2
    change (roundwiseAliceMarginal σ).toOp = (σA.tensorPowGen n).toOp
    rw [hmarg]
  apply DensityOp.ext
  change partialTraceB (Matrix.reindex e e (symmetrize σ).toOp) = (σA.tensorPowGen n).toOp
  rw [symmetrize_toOp]
  have hpush : Matrix.reindex e e
        ((1 / (Nat.factorial n : ℂ)) • ∑ π : Equiv.Perm (Fin n),
          permutationRepresentation (dA * dB) n π * σ.toOp *
            (permutationRepresentation (dA * dB) n π)ᴴ) =
      (1 / (Nat.factorial n : ℂ)) • ∑ π : Equiv.Perm (Fin n),
        Matrix.reindex e e (permutationRepresentation (dA * dB) n π * σ.toOp *
          (permutationRepresentation (dA * dB) n π)ᴴ) := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  rw [hpush, partialTraceB_smul, partialTraceB_finset_sum]
  simp_rw [hcov]
  rw [← symmetrize_toOp (σA.tensorPowGen n),
    symmetrize_invariant _ (tensorPow_isPermutationInvariant σA)]

/-- **Nahar et al. Lemma 3 (main.tex:430–:432 (unlabeled; inside `\label{lemma:endOfStepOne}`
:427–:433, Lemma 3) and `\label{eq:incor2.1}` (main.tex:502–:505, inside
`\label{cor:liftToCoherent}` :495–:499)) — fixed-marginal de Finetti trace-norm reduction.**

    Let `d_A, d_B, n ≥ 1`, `x := d_A² d_B²`, `g := deFinettiPrefactor x n`. Let
    `σA : DensityOp d_A` be full rank (`hσA`), `Δ : Op ((d_A d_B)^n) → Op dimOut` be
    permutation-invariant (covariant, `hΔ_cov`); Hermiticity-preservation of `Δ` is not needed.
    For any Eve ancilla `eveDim` and input `ρ_{AⁿBⁿEⁿ}` whose round-wise Alice marginal is
    `σ̂A^{⊗n}` (`hmarg`), there is a fixed-marginal de Finetti measure `μ` with

    `‖(Δ ⊗ id_{Eⁿ}) ρ‖₁ ≤ g · ‖(Δ ⊗ id_R) τ_R‖₁`,

    where `τ_R = deFinettiMixturePurification d_A d_B n μ` is Nahar et al.'s fixed-marginal de
    Finetti
    purification (Alice marginal `σ̂A`).

    Proven from the fixed-marginal operator inequality (`deFinetti_fixedMarginal_op_le`,
    Nahar et al. Cor. 1.1) via the generic substate-extraction / block-diagonal engine
    (`traceNorm_mapTensorId_substate_bound`, `block_diagonal_purification_bound`), with the
    fixed-marginal reference in place of the universal `ckrDeFinettiState`. The arbitrary
    ancilla is handled natively (no diamond norm / Kitaev–Watrous). -/
theorem deFinetti_fixedMarginal_traceNorm_le
    {dimOut eveDim : ℕ} [NeZero dimOut] [NeZero eveDim]
    (Δ : Op ((dA * dB) ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ_cov : IsPermutationInvariantMap Δ)
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (ρ : DensityOp ((dA * dB) ^ n * eveDim))
    (hmarg : roundwiseAliceMarginal ρ.partialTraceB = σA.tensorPowGen n) :
    ∃ μ : DensityMeasure (dA * dB), IsFixedMarginalMeasure σA μ ∧
      traceNorm (mapTensorId Δ ρ.toOp) ≤
        (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ) *
          traceNorm (mapTensorId Δ (deFinettiMixturePurification dA dB n μ).toOp) := by
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  set g : ℝ := (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ) with hg_def
  -- the round-grouped marginal of `ρ` over the ancilla `Eⁿ`
  set σnorm : DensityOp ((dA * dB) ^ n) := ρ.partialTraceB with hσnorm_def
  -- its permutation symmetrization is permutation-invariant with the same round Alice marginal
  set σsym : DensityOp ((dA * dB) ^ n) := symmetrize σnorm with hσsym_def
  have hσsym_inv : IsPermutationInvariant σsym := symmetrize_isPermutationInvariant σnorm
  have hσsym_marg : roundwiseAliceMarginal σsym = σA.tensorPowGen n :=
    roundwiseAliceMarginal_symmetrize σnorm σA hmarg
  -- fixed-marginal operator inequality (Nahar et al. Cor. 1.1): `g · τ − σsym ⪰ 0`
  obtain ⟨μ, hμ_marg, hμ_op⟩ :=
    deFinetti_fixedMarginal_op_le σA hσA σsym hσsym_inv hσsym_marg
  refine ⟨μ, hμ_marg, ?_⟩
  -- the fixed-marginal de Finetti reference purification `τ_R`
  set τR : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n) :=
    deFinettiMixturePurification dA dB n μ with hτR_def
  have hτR_pure : τR.IsPure := purificationDensityOp_isPure _
  have hτR_marg : τR.partialTraceB = deFinettiMixtureFixedMarginal dA dB n μ :=
    deFinettiMixturePurification_partialTraceB dA dB n μ
  -- symmetric purification `Ψ_sym` of `σsym`
  obtain ⟨Ψsym, hΨsym_pure, _hΨsym_paired, _hΨsym_supp, hΨsym_marg⟩ :=
    symmetric_purification_with_pure σsym hσsym_inv
  -- purification `Ψ₀` of `σnorm` (to fold the arbitrary ancilla into the square ancilla)
  set Ψ0 : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n) := purificationDensityOp σnorm with hΨ0_def
  have hΨ0_pure : Ψ0.IsPure := purificationDensityOp_isPure _
  have hΨ0_marg : Ψ0.partialTraceB = σnorm := purificationDensityOp_partialTraceB _
  -- `partialTraceB (·.toOp)` of a `DensityOp.partialTraceB`
  have hσnorm_toOp : partialTraceB ρ.toOp = σnorm.toOp := rfl
  have hΨ0_ptB_toOp : partialTraceB Ψ0.toOp = σnorm.toOp :=
    congrArg (fun d => d.toOp) hΨ0_marg
  have hΨsym_toOp : partialTraceB Ψsym.toOp = σsym.toOp := hΨsym_marg
  have hτR_ptB_toOp : partialTraceB τR.toOp = (deFinettiMixtureFixedMarginal dA dB n μ).toOp :=
    congrArg (fun d => d.toOp) hτR_marg
  -- STEP 1: fold the arbitrary ancilla `eveDim` into the square-ancilla purification `Ψ₀`
  have step1 : traceNorm (mapTensorId Δ ρ.toOp) ≤ traceNorm (mapTensorId Δ Ψ0.toOp) := by
    have h_dom : (((1 : ℝ) : ℂ) • Ψ0.partialTraceB.toOp - partialTraceB ρ.toOp).PosSemidef := by
      have : Ψ0.partialTraceB.toOp = partialTraceB ρ.toOp := by
        rw [hσnorm_toOp]
        exact congrArg (fun d => d.toOp) hΨ0_marg
      rw [Complex.ofReal_one, one_smul, this, sub_self]
      exact Matrix.PosSemidef.zero
    have h := traceNorm_mapTensorId_substate_bound Δ ρ.toOp
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp) Ψ0 hΨ0_pure 1 one_pos h_dom
    simpa using h
  -- STEP 2: block-diagonal permutation averaging → symmetric purification `Ψ_sym`
  have step2 : traceNorm (mapTensorId Δ Ψ0.toOp) ≤ traceNorm (mapTensorId Δ Ψsym.toOp) := by
    have hΨ0_nz : Ψ0.toOp ≠ 0 := by
      intro h
      have := Ψ0.trace_one
      rw [h] at this
      simp at this
    have hΨ0_trace : Ψ0.toOp.trace.re ≤ 1 := by rw [Ψ0.trace_one]; simp
    have hσnorm_rel : σnorm.toOp = (1 / Ψ0.toOp.trace) • partialTraceB Ψ0.toOp := by
      rw [hΨ0_ptB_toOp, Ψ0.trace_one]; simp
    have hΨsym_marg_sym : partialTraceB Ψsym.toOp = (symmetrize σnorm).toOp := by
      rw [hΨsym_toOp, hσsym_def]
    exact block_diagonal_purification_bound Δ hΔ_cov.covariance Ψ0.toOp
      (posSemidefOp_implies_mathlib Ψ0.toPosSemidefOp) hΨ0_trace hΨ0_nz
      σnorm hσnorm_rel Ψsym hΨsym_pure hΨsym_marg_sym
  -- STEP 3: substate bound against the fixed-marginal reference `τ_R` with `α = g`
  have hg_pos : 0 < g := by
    rw [hg_def]
    exact_mod_cast Nat.choose_pos (by omega)
  have step3 : traceNorm (mapTensorId Δ Ψsym.toOp) ≤ g * traceNorm (mapTensorId Δ τR.toOp) := by
    have h_dom : (((g : ℝ) : ℂ) • τR.partialTraceB.toOp - partialTraceB Ψsym.toOp).PosSemidef := by
      rw [hΨsym_toOp]
      have hcast : ((g : ℝ) : ℂ) = (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℂ) := by
        rw [hg_def]; push_cast; ring
      rw [hcast]
      have hτR_toOp : τR.partialTraceB.toOp = (deFinettiMixtureFixedMarginal dA dB n μ).toOp :=
        congrArg (fun d => d.toOp) hτR_marg
      rw [hτR_toOp]
      exact hμ_op
    exact traceNorm_mapTensorId_substate_bound Δ Ψsym.toOp
      (posSemidefOp_implies_mathlib Ψsym.toPosSemidefOp) τR hτR_pure g hg_pos h_dom
  calc traceNorm (mapTensorId Δ ρ.toOp)
      ≤ traceNorm (mapTensorId Δ Ψ0.toOp) := step1
    _ ≤ traceNorm (mapTensorId Δ Ψsym.toOp) := step2
    _ ≤ g * traceNorm (mapTensorId Δ τR.toOp) := step3

end InfoTheory.Postselection

end
