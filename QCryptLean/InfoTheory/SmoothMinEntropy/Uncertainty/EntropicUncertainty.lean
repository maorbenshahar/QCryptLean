import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MaxEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MaxEntropyFidelity
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Entropic Uncertainty Relations for CQ States — Berta pairs and operational bridges

This file packages the abstract Berta–Christandl–Colbeck–Renes–Renner (2010)
entropic uncertainty relation (EUR) at the level of optimized conditional
min-entropy and max-entropy for CQ states.

## Main definitions

- `BertaMeasurementPair`: the data witnessing that two CQ states on the same
  quantum register arise from a common bipartite state via two measurements
  with a specified elementwise overlap bound.
- `BertaOperationalBridge`: the explicit guessing-vs-fidelity premise needed
  for the same-memory abstract interface.

## Main statements

- `hminReal_plus_fidelity_hmax_ge_log_overlap_inv`: bridge-based abstract Berta EUR
  over the fidelity-based conditional max-entropy interface.
- `hminReal_plus_hmax_ge_log_overlap_inv`: abstract Berta EUR over the public
  optimized conditional min-entropy and max-entropy interfaces.

## References

- Berta, Christandl, Colbeck, Renes & Renner (2010). The uncertainty principle
  in the presence of quantum memory. Nature Physics 6(9), 659–662. Theorem 1,
  Eq. (2).
- Tomamichel (2016). Quantum Information Processing with Finite Resources.
  Springer. Theorem 6.19.
- Tomamichel & Renner (2011). Uncertainty Relation for Smooth Entropies.
  Phys. Rev. Lett. 106, 110506.
-/

open Quantum.Operators Quantum.TensorProducts Real
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## Berta EUR hypothesis structure

The structure below records the common-source measurement data used by Berta
EUR applications: two CQ states arise from the same bipartite state ρ_{AE} via
two measurements P and M on system A, with overlap

  c = max_{z,x} ‖P_z M_x‖²_{op}.

The same-memory entropy inequality in this file is intentionally stated with
the extra `BertaOperationalBridge` premise; the origin and overlap fields alone
do not provide that bridge.
-/

/-- The data witnessing that two CQ states `ρ_Z` (classical register Z, quantum
register E of dimension `n`) and `ρ_X` (classical register X, same quantum register
E) arise from a common bipartite state on Alice's system A (dimension `m`) tensored
with E, via two measurements on A with max elementwise overlap at most `c`.

Fields `meas_Z` and `meas_X` are the measurement operators on Alice's system.
Fields `rho_Z_weight_eq_one` and `rho_X_weight_eq_one` assert that both
post-measurement CQ states are normalized. Field `source` is the bipartite
state on A⊗E.
Fields `origin_Z` and `origin_X` assert the post-measurement CQ state equations:
  (ρ_Z.stateMap z).toOp = Tr_A[(meas_Z z ⊗ I_E) · source · (meas_Z z ⊗ I_E)]
  (ρ_X.stateMap x).toOp = Tr_A[(meas_X x ⊗ I_E) · source · (meas_X x ⊗ I_E)]
(Berta 2010, §Methods; Tomamichel 2016, Definition before Theorem 6.19.)

Field `overlap_bound` asserts the max elementwise overlap condition
  ∀ z x, ‖meas_Z z · meas_X x‖²_{op} ≤ c
using the L2 operator norm on finite matrices. -/
structure BertaMeasurementPair
    (Z X : Type*) [Fintype Z] [Fintype X] (m n : ℕ) (c : ℝ) where
  /-- The first CQ state (post-measurement under meas_Z), classical register Z. -/
  ρ_Z : CQState Z n
  /-- The second CQ state (post-measurement under meas_X), classical register X. -/
  ρ_X : CQState X n
  /-- The Z-side post-measurement CQ state is normalized. -/
  rho_Z_weight_eq_one : ∑ z : Z, (ρ_Z.stateMap z).trace = 1
  /-- The X-side post-measurement CQ state is normalized. -/
  rho_X_weight_eq_one : ∑ x : X, (ρ_X.stateMap x).trace = 1
  /-- The first measurement operators on Alice's system of dimension m. -/
  meas_Z : Z → Op m
  /-- The second measurement operators on Alice's system of dimension m. -/
  meas_X : X → Op m
  /-- The source bipartite state on Alice ⊗ Eve (Op (m * n)). -/
  source : SubDensityOp (m * n)
  /-- ρ_Z's blocks are the partial-trace–sandwiched blocks of source under meas_Z:
  (Berta 2010 §Methods; Tomamichel 2016 before Theorem 6.19.) -/
  origin_Z : ∀ z : Z,
    (ρ_Z.stateMap z).toOp =
      partialTraceA
        (Op.tensor (meas_Z z) (1 : Op n) * source.toOp *
         Op.tensor (meas_Z z) (1 : Op n))
  /-- ρ_X's blocks are the partial-trace–sandwiched blocks of source under meas_X:
  (Berta 2010 §Methods; Tomamichel 2016 before Theorem 6.19.) -/
  origin_X : ∀ x : X,
    (ρ_X.stateMap x).toOp =
      partialTraceA
        (Op.tensor (meas_X x) (1 : Op n) * source.toOp *
         Op.tensor (meas_X x) (1 : Op n))
  /-- Max elementwise overlap bound: for every z and x,
  the L2 operator-norm squared ‖meas_Z z · meas_X x‖²_{op} ≤ c. -/
  overlap_bound : ∀ (z : Z) (x : X),
    ‖meas_Z z * meas_X x‖ ^ 2 ≤ c

/-- The operational bridge needed by the same-memory abstract Berta interface.

The source/origin/overlap fields of `BertaMeasurementPair` do not by themselves
prove this statement for a common memory register.  We therefore expose the
bridge as an explicit mathematical premise: the optimized Z-side guessing
probability is controlled by one normalized reference state in the X-side
fidelity max-entropy expression. -/
def BertaOperationalBridge
    (Z X : Type*) [Fintype Z] [Fintype X] [Nonempty Z] [Nonempty X]
    {m n : ℕ} [NeZero m] [NeZero n]
    {c : ℝ} (pair : BertaMeasurementPair Z X m n c) : Prop := by
  classical
  exact ∃ σ : DensityOp n,
    povmGuessingProb pair.ρ_Z ≤
      c *
        (Quantum.Metrics.fidelity pair.ρ_X.toJointDensity.toPosSemidefOp
          (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)) ^ 2

/-- A positive-fidelity reference value is bounded by the optimized max-entropy
for every CQ state of positive weight. -/
lemma conditionalMaxEntropyFidelityReal_le_optReal_of_normalized
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ : 0 < ∑ x, ρ.classicalMarginal x) (σ : DensityOp n)
    (hF : 0 < Quantum.Metrics.fidelity
      (@CQState.toJointDensity X _ (Classical.decEq X) n ρ).toPosSemidefOp
      (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)) :
    conditionalMaxEntropyFidelityReal ρ σ hF ≤
      conditionalMaxEntropyFidelityOptReal ρ hρ := by
  unfold conditionalMaxEntropyFidelityOptReal
  refine le_csSup ?_ ⟨σ, hF, rfl⟩
  refine ⟨classicalMarginalMaxEntropyReal ρ hρ, ?_⟩
  rintro b ⟨τ, hτ, rfl⟩
  exact conditionalMaxEntropyFidelityReal_le_classicalMarginalMaxEntropy_of_normalized
    ρ hρ τ hτ

/-- A bound `Pg ≤ c * F²` gives the fixed-reference min/max entropy
uncertainty inequality. -/
lemma log_overlap_inv_le_hminReal_add_fidelity_hmax_of_guess_le
    (Z X : Type*) [Fintype Z] [Fintype X] [Nonempty Z] [Nonempty X]
    {n : ℕ} [NeZero n] {c : ℝ} (hc_pos : 0 < c)
    (ρ_Z : CQState Z n) (ρ_X : CQState X n) (σ : DensityOp n)
    (hPg_pos : 0 < povmGuessingProb ρ_Z)
    (hguess : povmGuessingProb ρ_Z ≤
      c *
        (Quantum.Metrics.fidelity
          (@CQState.toJointDensity X _ (Classical.decEq X) n ρ_X).toPosSemidefOp
          (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)) ^ 2) :
    Real.log (1 / c) / Real.log 2 ≤
      conditionalMinEntropyOptReal ρ_Z +
        conditionalMaxEntropyFidelityReal ρ_X σ (by
          have hpos := lt_of_lt_of_le hPg_pos hguess
          have hnonneg := Quantum.Metrics.fidelity_nonneg_posSemidefOp
            (@CQState.toJointDensity X _ (Classical.decEq X) n ρ_X).toPosSemidefOp
            (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)
          exact lt_of_le_of_ne hnonneg (by
            intro hzero
            simp [← hzero] at hpos)) := by
  let : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  let : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  let F : ℝ :=
    Quantum.Metrics.fidelity
      (@CQState.toJointDensity X _ (Classical.decEq X) n ρ_X).toPosSemidefOp
      (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)
  let F2 : ℝ := F ^ 2
  have hF2_pos : 0 < F2 := by
    have hcF_pos : 0 < c * F2 := by
      exact lt_of_lt_of_le hPg_pos (by simpa [F, F2] using hguess)
    nlinarith [hc_pos]
  have hlog_guess_le : Real.log (povmGuessingProb ρ_Z) ≤ Real.log c + Real.log F2 := by
    have hlog_le :
        Real.log (povmGuessingProb ρ_Z) ≤ Real.log (c * F2) :=
      Real.log_le_log hPg_pos (by simpa [F, F2] using hguess)
    simpa [Real.log_mul hc_pos.ne' hF2_pos.ne'] using hlog_le
  have hnum :
      Real.log (1 / c) ≤ -Real.log (povmGuessingProb ρ_Z) + Real.log F2 := by
    rw [one_div, Real.log_inv]
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hdiv :
      Real.log (1 / c) / Real.log 2 ≤
        (-Real.log (povmGuessingProb ρ_Z) + Real.log F2) / Real.log 2 :=
    div_le_div_of_nonneg_right hnum hlog2_pos.le
  rw [conditionalMinEntropyReal_cq_guess_eq ρ_Z]
  unfold conditionalMaxEntropyFidelityReal
  simpa [add_div, F2, F] using hdiv

/-- Abstract Berta EUR (Berta–Christandl–Colbeck–Renes–Renner 2010, Theorem 1, Eq. (2);
Tomamichel 2016, Theorem 6.19):

For two CQ states encoded by a `BertaMeasurementPair` with overlap `c ∈ (0, 1]`,

  H_min(Z|E)_{ρ_Z} + H_max(X|E)_{ρ_X} ≥ log₂(1/c).

`hc_pos` and `hc_le_one` are required for `log(1/c) ≥ 0`.  The separate
`BertaOperationalBridge` premise is the operational guessing-vs-fidelity input;
this theorem only performs the logarithmic entropy arithmetic and optimization
lift. -/
theorem hminReal_plus_fidelity_hmax_ge_log_overlap_inv
    (Z X : Type*) [Fintype Z] [Fintype X] [Nonempty Z] [Nonempty X]
    {m n : ℕ} [NeZero m] [NeZero n]
    {c : ℝ} (hc_pos : 0 < c) (_hc_le_one : c ≤ 1)
    (pair : BertaMeasurementPair Z X m n c)
    (h_bridge : BertaOperationalBridge Z X pair) :
    conditionalMinEntropyOptReal pair.ρ_Z + conditionalMaxEntropyFidelityOptReal pair.ρ_X
        (by simp [CQState.classicalMarginal, pair.rho_X_weight_eq_one]) ≥
      Real.log (1 / c) / Real.log 2 := by
  let ρZN : NormalizedCQState Z n :=
    { pair.ρ_Z with
      weight_eq_one := pair.rho_Z_weight_eq_one }
  have hPg_pos : 0 < povmGuessingProb pair.ρ_Z := by
    simpa [ρZN] using povmGuessingProb_pos_of_normalizedCQState ρZN
  obtain ⟨σ, hguess⟩ := h_bridge
  have hρX : 0 < ∑ x, pair.ρ_X.classicalMarginal x := by
    simp [CQState.classicalMarginal, pair.rho_X_weight_eq_one]
  have hF : 0 < Quantum.Metrics.fidelity
      (@CQState.toJointDensity X _ (Classical.decEq X) n pair.ρ_X).toPosSemidefOp
      (conditionalMaxEntropyFidelityReferenceOp (X := X) σ) := by
    have hpos := lt_of_lt_of_le hPg_pos hguess
    have hnonneg := Quantum.Metrics.fidelity_nonneg_posSemidefOp
      (@CQState.toJointDensity X _ (Classical.decEq X) n pair.ρ_X).toPosSemidefOp
      (conditionalMaxEntropyFidelityReferenceOp (X := X) σ)
    exact lt_of_le_of_ne hnonneg (by
      intro hzero
      simp [← hzero] at hpos)
  have hfixed :
      Real.log (1 / c) / Real.log 2 ≤
        conditionalMinEntropyOptReal pair.ρ_Z +
          conditionalMaxEntropyFidelityReal pair.ρ_X σ hF := by
    exact log_overlap_inv_le_hminReal_add_fidelity_hmax_of_guess_le
      Z X hc_pos pair.ρ_Z pair.ρ_X σ hPg_pos hguess
  have hmax_ge_fixed :
      conditionalMaxEntropyFidelityReal pair.ρ_X σ hF ≤
        conditionalMaxEntropyFidelityOptReal pair.ρ_X hρX := by
    exact conditionalMaxEntropyFidelityReal_le_optReal_of_normalized
      pair.ρ_X hρX σ hF
  linarith

/-- Public form of the abstract Berta EUR, stated over `conditionalMaxEntropyOptReal`.

The public max-entropy name unfolds to the fidelity-based optimized
max-entropy, so this theorem is just the stable interface restatement of
`hminReal_plus_fidelity_hmax_ge_log_overlap_inv`. -/
theorem hminReal_plus_hmax_ge_log_overlap_inv
    (Z X : Type*) [Fintype Z] [Fintype X] [Nonempty Z] [Nonempty X]
    {m n : ℕ} [NeZero m] [NeZero n]
    {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    (pair : BertaMeasurementPair Z X m n c)
    (h_bridge : BertaOperationalBridge Z X pair) :
    conditionalMinEntropyOptReal pair.ρ_Z + conditionalMaxEntropyOptReal pair.ρ_X
        (by simp [CQState.classicalMarginal, pair.rho_X_weight_eq_one]) ≥
      Real.log (1 / c) / Real.log 2 := by
  simpa [conditionalMaxEntropyOptReal] using
    hminReal_plus_fidelity_hmax_ge_log_overlap_inv Z X hc_pos hc_le_one pair h_bridge

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
