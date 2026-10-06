import QCryptLean.InfoTheory.QuantumLHL.SeedKeyOperatorBlock
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.SingularReferenceTransfer

/-!
# Dominating references for leftover hashing

A positive-definite dominating reference transfers operator coefficients and the resulting smooth
hashing bounds. Real logarithmic charges remain signed until the entropy floor is converted with
`ENNReal.ofReal`.
-/

open Quantum.Operators Quantum.Metrics Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- Seed-visible hashing transfers along reference domination without a weight floor. -/
theorem
    traceDistanceGen_seedKeyExtractorOutput_uniformOutput_le_of_minEntropy_of_posDef_dominating
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ σ' : SubDensityOp n)
    (hdom : opLe σ.toOp σ'.toOp)
    (hσ'_pd : σ'.toOp.PosDef)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) := by
  exact traceDistanceGen_seedKeyExtractorOutput_uniformOutput_le_of_minEntropy
    H hH ρ σ' hσ'_pd k
    (hk.trans (conditionalMinEntropy_le_of_isFeasible_imp ρ ρ σ σ'
      (fun _ ht => isFeasible_of_opLe ρ σ' σ hdom ht)))

/-- Reference domination transfers extended smooth operator blocks without ball guards. -/
theorem quantum_seedKey_LHL_smooth_operatorBlock_of_posDef_dominating
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ σ' : SubDensityOp n)
    (hdom : opLe σ.toOp σ'.toOp)
    (hσ'_pd : σ'.toOp.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    ∃ ρReal_acc ρReal_resid ρIdeal_acc ρIdeal_resid : Op (n * Fintype.card (S × Z)),
      (seedKeyExtractorOutputState H ρ).toJointDensity.toOp = ρReal_acc + ρReal_resid ∧
        (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp =
            ρIdeal_acc + ρIdeal_resid ∧
          ((1 / 2) * traceNorm ρReal_resid + (1 / 2) * traceNorm ρIdeal_resid ≤ 2 * ε) ∧
            traceDistanceGen ρReal_acc ρIdeal_acc ≤
              (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) := by
  exact quantum_seedKey_LHL_smooth_operatorBlock H hH ρ σ' hσ'_pd ε hε k
    (hk.trans (smoothMinEntropy_antitone_sigma ε ρ σ σ' hdom))

/-- Rescaled reference domination transfers extended operator blocks with logarithmic cost.
The coefficient satisfies `c ≤ 1`, so a clipped zero floor cannot produce a positive target rate. -/
theorem quantum_seedKey_LHL_smooth_operatorBlock_of_smul_opLe
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ σ' : SubDensityOp n)
    (c : ℝ) (hc : 0 < c) (hc_le : c ≤ 1)
    (hdom : ∀ v : Fin n → ℂ,
      (quadraticForm ((c : ℂ) • σ.toOp) v).re ≤ (quadraticForm σ'.toOp v).re)
    (hσ'_pd : σ'.toOp.PosDef)
    (ε : ℝ) (hε : 0 ≤ ε)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    ∃ ρReal_acc ρReal_resid ρIdeal_acc ρIdeal_resid : Op (n * Fintype.card (S × Z)),
      (seedKeyExtractorOutputState H ρ).toJointDensity.toOp = ρReal_acc + ρReal_resid ∧
        (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp =
            ρIdeal_acc + ρIdeal_resid ∧
          ((1 / 2) * traceNorm ρReal_resid + (1 / 2) * traceNorm ρIdeal_resid ≤ 2 * ε) ∧
            traceDistanceGen ρReal_acc ρIdeal_acc ≤
              (1 / 2) *
                Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-(k + Real.log c / Real.log 2))) := by
  exact quantum_seedKey_LHL_smooth_operatorBlock H hH ρ σ' hσ'_pd ε hε
    (k + Real.log c / Real.log 2)
    (smoothMinEntropy_ge_of_smul_opLe_of_floor ε ρ σ σ' c hc hc_le hdom k hk)


/-- A signed conditional min-entropy floor transfers from a feasible reference to a dominating
positive-definite reference for a state of positive weight. -/
lemma conditionalMinEntropyReal_floor_transfer_of_posDef_dominating
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ σ' : SubDensityOp n)
    (hdom : opLe σ.toOp σ'.toOp)
    (hσ'_pd : σ'.toOp.PosDef)
    (hfeasσ : hasFeasibleLambda ρ σ)
    (hρ_weight_pos : 0 < ∑ x : X, (ρ.stateMap x).trace)
    (k : ℝ) (hk : k ≤ conditionalMinEntropyReal ρ σ) :
    k ≤ conditionalMinEntropyReal ρ σ' := by
  have hpos' : 0 < minFeasibleLambda ρ σ' :=
    minFeasibleLambda_pos_of_posDef_of_weight_pos ρ σ' hσ'_pd hρ_weight_pos
  exact hk.trans (conditionalMinEntropyReal_antitone_sigma ρ σ' σ hdom hfeasσ hpos')

end InfoTheory.QuantumLHL

end -- noncomputable section
