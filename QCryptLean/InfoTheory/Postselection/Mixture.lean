import QCryptLean.InfoTheory.DeFinetti.Measure
import QCryptLean.InfoTheory.DeFinetti.Purification
import QCryptLean.InfoTheory.DeFinetti.PurificationAncillaEmbed
import QCryptLean.Quantum.Metrics.TraceNormIntegral

/-!
# QKD postselection — de Finetti mixture `τ` and its purification `τ_R`

Faithful transcription of the de Finetti state `τ_{AⁿBⁿ}` of
Nahar–Tupkary–Zhao–Lütkenhaus–Tan 2024 (arXiv:2403.11851), main.tex:483–:486 (unlabeled; the
`\tau_{A^nB^n}` mixture inside `\label{thm:maintheorem}` :481–:491) (lines 536–541)
and main.tex:575–:578 (unlabeled; the `\tau_{A^nB^n}` mixture inside `\label{thm:maintheoremvar}`
:573–:590), together with a purification `τ_{AⁿBⁿR}`.

Nahar et al. main.tex:483–:486 (unlabeled; the `\tau_{A^nB^n}` mixture inside
`\label{thm:maintheorem}` :481–:491):  `τ_{AⁿBⁿ} = ∫ σ_AB^{⊗n} dσ_AB`, where `dσ_AB` is a
probability measure
on the non-negative extensions `σ_AB` of the fixed marginal `σ̂A`
(`Tr_B σ_AB = σ̂A`). The single-round joint system `AB` has dimension `dA * dB`, so the
mixture is `integralTensorPower n μ : DensityOp ((dA*dB)^n)` for a
`μ : DensityMeasure (dA*dB)`. This is the general **HS-mixture** de Finetti state (over
density operators), distinct from the Haar-pure `deFinettiState` and the paired
`ckrDeFinettiState`.

The purification `τ_{AⁿBⁿR}` is the canonical `(√τ ⊗ 𝟙)|Ω⟩` purification with reference
register `R` of equal dimension.

## Main definitions
- `InfoTheory.Postselection.deFinettiMixtureFixedMarginal` : the mixture `τ = ∫ σ_AB^{⊗n} dσ`.
- `InfoTheory.Postselection.deFinettiMixturePurification` : the canonical purification `τ_R`.
- `InfoTheory.Postselection.IsFixedMarginalMeasure` : `μ` is supported on extensions of `σ̂A`
  (`Tr_B σ = σ̂A` for `μ`-a.e. `σ`).

## Main statements
- `InfoTheory.Postselection.deFinettiMixturePurification_partialTraceB` : tracing out the
  reference `R` recovers the mixture `τ` (so `τ_R` is a purification of `τ`).
-/

open Quantum.Operators Quantum.TensorProducts InfoTheory.DeFinetti MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

variable (dA dB n : ℕ) [NeZero dA] [NeZero dB] [NeZero n]

/-- Positivity of `dA * dB`. -/
private theorem neZero_pairDim : NeZero (dA * dB) :=
  ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩

omit [NeZero n] in
/-- Positivity of `(dA * dB) ^ n`. -/
private theorem neZero_pairPow : NeZero ((dA * dB) ^ n) :=
  ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩

/-- **Nahar et al. main.tex:483–:486 (unlabeled; the `\tau_{A^nB^n}` mixture inside
`\label{thm:maintheorem}` :481–:491) mixture** `τ_{AⁿBⁿ} = ∫ σ_AB^{⊗n} dσ_AB` over a probability
measure `μ`
    on density operators on the single-round joint system `AB` (dimension `dA * dB`).

    This is the HS-mixture de Finetti state: an integral of tensor powers of single-round
    states, distinct from the Haar-pure `deFinettiState` and the paired `ckrDeFinettiState`. -/
def deFinettiMixtureFixedMarginal (μ : DensityMeasure (dA * dB)) :
    DensityOp ((dA * dB) ^ n) :=
  haveI := neZero_pairDim dA dB
  haveI := neZero_pairPow dA dB n
  integralTensorPower n μ

/-- **Nahar et al. purification** `τ_{AⁿBⁿR}` of the main.tex:483–:486 (unlabeled; the
`\tau_{A^nB^n}` mixture inside `\label{thm:maintheorem}` :481–:491) mixture: the canonical
    `(√τ ⊗ 𝟙)|Ω⟩` purification with reference register `R` of equal dimension. -/
def deFinettiMixturePurification (μ : DensityMeasure (dA * dB)) :
    DensityOp ((dA * dB) ^ n * (dA * dB) ^ n) :=
  haveI := neZero_pairDim dA dB
  haveI := neZero_pairPow dA dB n
  purificationDensityOp (deFinettiMixtureFixedMarginal dA dB n μ)

/-- The single-round bipartite states extending the fixed Alice marginal. -/
def fixedMarginalSet {dA dB : ℕ} (σA : DensityOp dA) : Set (DensityOp (dA * dB)) :=
  {σ | σ.partialTraceB = σA}

/-- **Fixed-marginal support** (Nahar et al. main.tex:483–:486 (unlabeled; the `\tau_{A^nB^n}`
mixture inside `\label{thm:maintheorem}` :481–:491), "extensions `σ_AB` of `σ̂A`"): the measure
    `μ` is supported on states whose Alice marginal is `σ̂A`, i.e. `Tr_B σ = σ̂A` for
    `μ`-almost every `σ`. -/
def IsFixedMarginalMeasure {dA dB : ℕ} (σA : DensityOp dA)
    (μ : DensityMeasure (dA * dB)) : Prop :=
  ∀ᵐ σ ∂μ.measure, DensityOp.partialTraceB σ = σA

/-- Tracing out the reference register `R` of the purification recovers the mixture `τ`,
    so `deFinettiMixturePurification` is a purification of `deFinettiMixtureFixedMarginal`. -/
theorem deFinettiMixturePurification_partialTraceB (μ : DensityMeasure (dA * dB)) :
    (deFinettiMixturePurification dA dB n μ).partialTraceB =
      deFinettiMixtureFixedMarginal dA dB n μ := by
  haveI := neZero_pairDim dA dB
  haveI := neZero_pairPow dA dB n
  exact purificationDensityOp_partialTraceB (deFinettiMixtureFixedMarginal dA dB n μ)

/-- Pure extension of the fixed-marginal de Finetti mixture at any register size: for any
nonempty additional register dimension `r`, the mixture `deFinettiMixtureFixedMarginal dA dB n μ`
has a *pure* extension on `((dA·dB)^n) ⊗ ((dA·dB)^n ⊗ r)`: purify the mixture canonically
(`deFinettiMixturePurification`, pure with marginal the mixture) and zero-pad the second factor
from `(dA·dB)^n` to `(dA·dB)^n · r` (`padDensityOpAncillaB`); padding preserves purity and does
not change the partial trace. -/
theorem exists_pure_extension_fixedMarginal {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (μ : DensityMeasure (dA * dB)) (r : ℕ) [NeZero r] :
    ∃ τ : DensityOp ((dA * dB) ^ n * ((dA * dB) ^ n * r)),
      τ.IsPure ∧ τ.partialTraceB = deFinettiMixtureFixedMarginal dA dB n μ := by
  haveI hABn : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  haveI hABn2 : NeZero ((dA * dB) ^ n * (dA * dB) ^ n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne ((dA * dB) ^ n)) (NeZero.ne ((dA * dB) ^ n))⟩
  haveI hABnr : NeZero ((dA * dB) ^ n * r) :=
    ⟨Nat.mul_ne_zero (NeZero.ne ((dA * dB) ^ n)) (NeZero.ne r)⟩
  -- pad the canonical purification's reference register from `(dA·dB)^n` to `(dA·dB)^n · r`
  have hle : (dA * dB) ^ n ≤ (dA * dB) ^ n * r :=
    Nat.le_mul_of_pos_right _ (NeZero.pos r)
  refine ⟨padDensityOpAncillaB hle (deFinettiMixturePurification dA dB n μ),
    padDensityOpAncillaB_isPure hle
      (purificationDensityOp_isPure (deFinettiMixtureFixedMarginal dA dB n μ)), ?_⟩
  apply DensityOp.ext
  change partialTraceB
    (padDensityOpAncillaB hle (deFinettiMixturePurification dA dB n μ)).toOp =
    (deFinettiMixtureFixedMarginal dA dB n μ).toOp
  exact (padDensityOpAncillaB_partialTraceB hle (deFinettiMixturePurification dA dB n μ)).trans
    (congrArg (fun d : DensityOp ((dA * dB) ^ n) => d.toOp)
      (deFinettiMixturePurification_partialTraceB dA dB n μ))

end InfoTheory.Postselection

end
