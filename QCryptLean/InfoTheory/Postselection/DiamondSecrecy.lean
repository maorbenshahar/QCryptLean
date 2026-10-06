import QCryptLean.InfoTheory.Postselection.Lift
import QCryptLean.Quantum.Channels.CPTP.DiamondNormAncilla

/-!
# The diamond-norm criterion implies Nahar et al. Definition 4

The companion `Protocol.lean` file's module docstring records that Nahar et al.'s fixed-marginal
secrecy
(Definition 4, arXiv:2403.11851, `main.tex:401` `\label{def:epsSecPromise}`, equation at
`main.tex:404` `\label{eq:epsSec}`) is *weaker* than the diamond-norm criterion
`½‖E − E_ideal‖_◇ ≤ ε`, because Definition 4 restricts the input to the fixed-marginal set
`Tr_{BⁿEⁿ} ρ = σ̂A^{⊗n}` while the diamond norm ranges over all inputs. This file proves that
sentence, as `PMQKDProtocol.isSecretAt_of_roundDifferenceMap_diamondNorm_le`.

Both sides carry the same `½`: `IsFixedMarginalSecret` bakes the factor of Nahar et al.'s
`main.tex:404` into its definition, and the hypothesis here is stated in the
same `½` convention, so composing the two does not halve twice.

The hypothesis is stated on the **round-grouped** map `P.roundDifferenceMap l'` (register
`(d_A d_B)^n`), not on `P.differenceMap l'` (register `d_A^n d_B^n`). The two are related by the
round-regrouping relabelling `roundGroupEquiv` and carry the same trace norms; the round-grouped
form is the one channel constructions are typed at, so it is the form a concrete instantiation can
supply directly.

**What this route does not do.** It reaches Definition 4 without Nahar et al.'s Theorem 3
(`main.tex:481` `\label{thm:maintheorem}`) and Corollary 3.1 (`main.tex:495`
`\label{cor:liftToCoherent}`): those derive Definition 4 from the IID security-proof conditions
`main.tex:452`/`main.tex:462` `\label{eq:condLHL}` and pay the de Finetti prefactor `g_{n,x}` for
the lift. A caller that already holds a diamond-norm bound has paid that lift inside its own
budget, and must not pay it again here — the conclusion carries exactly the `ε` of the hypothesis.
-/

open Equiv

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-- **Nahar et al. Definition 4 from a diamond-norm bound** (`main.tex:401`
`\label{def:epsSecPromise}`, equation `main.tex:404` `\label{eq:epsSec}`).

If half the diamond norm of the round-grouped difference map `P.roundDifferenceMap l'` is at most
`ε`, then the length-`l'` variant of `P` is `ε`-secret with fixed marginal `σA` — for *every*
`σA`, since the diamond norm does not see the marginal constraint.

Two steps. (i) The Definition-4 input `ρ` on `AⁿBⁿ ⊗ Eⁿ` is relabelled to the round-grouped
register `(AB)^{⊗n} ⊗ Eⁿ` along `Equiv.finProdCongrExt (roundGroupEquiv d_A d_B n) eveDim`, under
which
`(Δ_round ⊗ id)(ρ_round)` and `(Δ ⊗ id)(ρ)` are the same matrix (the identical step (b) of
`permInvariant_postselection_security_of_referenceBound`). (ii) Definition 4's Eve register `Eⁿ` is
of arbitrary dimension while `diamondNorm`'s defining supremum pins the ancilla to the input
dimension; `Quantum.Channels.traceNorm_mapTensorId_le_diamondNorm` closes that gap.

The fixed-marginal hypothesis of Definition 4 is not used: the bound obtained is the stronger
all-input one. -/
theorem PMQKDProtocol.isSecretAt_of_roundDifferenceMap_diamondNorm_le
    (P : PMQKDProtocol dA dB n) (l' : ℕ) (σA : DensityOp dA) (ε : ℝ)
    (h :
      haveI := P.keyDim_neZero
      haveI := P.annDim_neZero
      haveI : NeZero (P.keyDim * P.annDim) :=
        ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
      haveI : NeZero ((dA * dB) ^ n) :=
        ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
      (1 / 2 : ℝ) * diamondNorm (P.roundDifferenceMap l') ≤ ε) :
    P.IsSecretAt l' σA ε := by
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  haveI : NeZero (P.keyDim * P.annDim) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  set e := roundGroupEquiv dA dB n with he_def
  set Δ := P.roundDifferenceMap l' with hΔ_def
  intro eveDim _ ρ _
  -- (i) The round-grouped avatar of the Definition-4 input.
  set ρround : DensityOp ((dA * dB) ^ n * eveDim) :=
    densityOp_reindex (Equiv.finProdCongrExt e eveDim).symm ρ with hρround_def
  have hρround_toOp : ρround.toOp =
      Matrix.reindex (Equiv.finProdCongrExt e eveDim).symm
        (Equiv.finProdCongrExt e eveDim).symm ρ.toOp := rfl
  have hround : mapTensorId Δ ρround.toOp = mapTensorId (P.differenceMap l') ρ.toOp := by
    rw [hρround_toOp, hΔ_def, PMQKDProtocol.roundDifferenceMap,
      ← mapTensorId_comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap (P.differenceMap l'),
      mapTensorId_reindexLinearEquiv]
    congr 1
    ext p q
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
  -- (ii) The arbitrary Eve ancilla is dominated by the diamond norm.
  have hle : traceNorm (mapTensorId Δ ρround.toOp) ≤ diamondNorm Δ :=
    traceNorm_mapTensorId_le_diamondNorm (d := dA * dB) (n := n) Δ ρround
  rw [hround] at hle
  change (1 / 2 : ℝ) * traceNorm (mapTensorId (P.differenceMap l') ρ.toOp) ≤ ε
  linarith

end InfoTheory.Postselection

end
