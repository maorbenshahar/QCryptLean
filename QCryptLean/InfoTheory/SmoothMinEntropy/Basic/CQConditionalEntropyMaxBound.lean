import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQJointEntropyLowerBound
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.Concavity

/-!
# CQ conditional von Neumann entropy is bounded by the classical max-entropy

For a normalized classical–quantum state `ρ : CQState X n` with block-diagonal
joint state `ρ_XB = ρ.toJointDensityOp` and quantum marginal
`ρ_B = ρ.quantumMarginalDensityOp`, the conditional von Neumann entropy
`H(X|B) = S(ρ_XB) − S(ρ_B)` (in nats) is bounded by the classical max-entropy of
the classical register:

    S(ρ_XB) − S(ρ_B)  ≤  H(X)  ≤  log (classicalRank ρ),

where `H(X) = ∑ x, entropyTerm (ρ.classicalMarginal x)` is the Shannon entropy of
the classical marginal and `classicalRank ρ = #{x : Tr(ρ.stateMap x) > 0}` is the
support size of the classical distribution (Renner's `rank(ρ_A)`).

The classical register `X` is a general `Fintype`, so the Shannon entropy is the
explicit sum `∑ x : X, entropyTerm (ρ.classicalMarginal x)`, agreeing with
`Math.ClassicalEntropy.shannonEntropy` when `X = Fin n`. Both bounds hold
unconditionally for every normalized CQ state: no reference operator,
invertibility, or feasibility assumption is needed.

## Main statements

- `CQState.cqConditional_vonNeumann_le_shannon_classicalMarginal` (the quantum
  step): `S(ρ_XB) − S(ρ_B) ≤ ∑ x, entropyTerm (ρ.classicalMarginal x)`.
- `CQState.shannonEntropy_classicalMarginal_le_log_classicalRank` (the classical
  max-entropy step): `∑ x, entropyTerm (ρ.classicalMarginal x) ≤ log (classicalRank ρ)`.
- `CQState.cqConditional_vonNeumann_le_log_classicalRank`: the composition of the
  two steps above.

## References

- R. Renner, *Security of Quantum Key Distribution* (PhD thesis), `main.tex:2711`
  (`H_max(ρ_A) = log rank(ρ_A)`).
- Tomamichel (2016), *Quantum Information Processing with Finite Resources*, §4.3.
-/

open Quantum.Operators Matrix
open Math.ClassicalEntropy
open InfoTheory.VonNeumannEntropy
open scoped ComplexOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Pointwise scaling rule for `entropyTerm`.** For `p > 0` and `l ≥ 0`,
`p · entropyTerm (l / p) = entropyTerm l + l · log p`. This is the per-coordinate
form of the Shannon chain rule `entropyTerm (l) = entropyTerm (p·(l/p))`. -/
lemma entropyTerm_smul_div {p l : ℝ} (hp : 0 < p) (hl : 0 ≤ l) :
    p * entropyTerm (l / p) = entropyTerm l + l * Real.log p := by
  rcases eq_or_lt_of_le hl with hl0 | hlpos
  · simp [← hl0, entropyTerm_zero]
  · rw [entropyTerm_eq_neg_mul_log (l / p), entropyTerm_eq_neg_mul_log l,
        Real.log_div (ne_of_gt hlpos) (ne_of_gt hp)]
    field_simp
    ring

/-- **Shannon chain rule (grouped-distribution equality).** For a nonnegative
weight vector `lam : Fin n → ℝ` with total mass `p = ∑ lam`, the entropy of the
fine weights equals the entropy of the total plus `p` times the entropy of the
normalized distribution `lam / p`:

    `∑_i entropyTerm (lam i) = entropyTerm p + p · shannonEntropy (lam / p)`.

For `p = 0` all `lam i = 0` and both sides vanish; for `p > 0` it is the sum of
the pointwise rule `entropyTerm_smul_div`. -/
lemma entropyTerm_chain_rule {n : ℕ} (lam : Fin n → ℝ) (p : ℝ)
    (hnn : ∀ i, 0 ≤ lam i) (hp : ∑ i, lam i = p) :
    ∑ i, entropyTerm (lam i)
      = entropyTerm p + p * shannonEntropy (fun i => lam i / p) := by
  have hp_nonneg : 0 ≤ p := hp ▸ Finset.sum_nonneg (fun i _ => hnn i)
  rcases eq_or_lt_of_le hp_nonneg with hp0 | hppos
  · -- p = 0: every `lam i = 0`
    have hp0' : p = 0 := hp0.symm
    have hlam0 : ∀ i ∈ (Finset.univ : Finset (Fin n)), lam i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp (by rw [hp]; exact hp0')
    rw [hp0']
    simp only [entropyTerm_zero, zero_mul, add_zero]
    exact Finset.sum_eq_zero (fun i hi => by rw [hlam0 i hi, entropyTerm_zero])
  · -- p > 0: sum of the pointwise scaling rule
    simp only [shannonEntropy]
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => entropyTerm_smul_div hppos (hnn i))]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, entropyTerm_eq_neg_mul_log]
    ring

/-- The classical-marginal-weighted block entropy of a CQ state,
`∑_x p(x) · S(τ_x)`, where `p(x) = ρ.classicalMarginal x` and
`fun i => ρ.blockEigenvalues x i / p(x)` is the eigenvalue spectrum of the
normalized conditional state `τ_x`. Blocks with `p(x) = 0` contribute `0`: the
`p(x)` prefactor cancels the `0/0` in the normalization, and every eigenvalue of
a trace-zero PSD block is `0`. -/
noncomputable def CQState.weightedBlockEntropy
    {X : Type*} [Fintype X] {n : ℕ} (ρ : CQState X n) : ℝ :=
  ∑ x : X, ρ.classicalMarginal x *
    shannonEntropy (fun i => ρ.blockEigenvalues x i / ρ.classicalMarginal x)

/-- **Block-diagonal entropy split.** For a normalized CQ state, the joint
von Neumann entropy decomposes as

    `S(ρ_XB) = H(X) + ∑_x p(x)·S(τ_x)`,

where `H(X) = ∑_x entropyTerm (p(x))` is the classical Shannon entropy and
`∑_x p(x)·S(τ_x) = ρ.weightedBlockEntropy` is the weighted block entropy. -/
theorem CQState.vonNeumannEntropy_toJointDensityOp_eq_classicalShannon_add_weightedBlockEntropy
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
      = (∑ x : X, entropyTerm (ρ.classicalMarginal x)) + ρ.weightedBlockEntropy := by
  classical
  -- S(ρ_XB) = H(jointEigenvalues)
  rw [vonNeumannEntropy_eq_shannonEntropy (ρ.toJointDensityOp hρ_norm) ρ.jointEigenvalues
        (ρ.isEigenvalueSpectrum_toJointDensityOp_jointEigenvalues hρ_norm)]
  -- regroup the fine spectrum by the classical index
  set e := cqJointEquiv X n with he
  have hreindex : shannonEntropy ρ.jointEigenvalues
      = ∑ x : X, ∑ i : Fin n, entropyTerm (ρ.blockEigenvalues x i) := by
    have h1 : shannonEntropy ρ.jointEigenvalues
        = ∑ p : Fin n × X, entropyTerm (ρ.blockEigenvalues p.2 p.1) := by
      unfold shannonEntropy
      exact Fintype.sum_equiv e.symm (fun k => entropyTerm (ρ.jointEigenvalues k))
        (fun p : Fin n × X => entropyTerm (ρ.blockEigenvalues p.2 p.1)) (fun k => rfl)
    rw [h1, Fintype.sum_prod_type_right]
  rw [hreindex, CQState.weightedBlockEntropy, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact entropyTerm_chain_rule (ρ.blockEigenvalues x) (ρ.classicalMarginal x)
    (fun i => ρ.blockEigenvalues_nonneg x i)
    (ρ.sum_blockEigenvalues_eq_classicalMarginal x)

/-- The normalized conditional state `τ_x = ρ.stateMap x / p(x)` of a CQ state,
viewed as a `DensityOp n`. For `p(x) = 0` blocks (which carry no information) we
fall back to an arbitrary fixed pure state; the `p(x)` prefactor cancels the
fallback wherever it is used. -/
noncomputable def CQState.conditionalState
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (x : X) : DensityOp n :=
  if h : 0 < ρ.classicalMarginal x then
    Quantum.Metrics.normalizePosSemidefOp (ρ.stateMap x).toPosSemidefOp h
  else
    DensityOp.fromPure (stdKet n default) (stdKet_IsNormalized default)

/-- The weighted conditional block recovers the original block:
`p(x) · τ_x = ρ.stateMap x` as operators (for `p(x) = 0` both sides vanish). -/
lemma CQState.smul_conditionalState_toOp
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (x : X) :
    ((ρ.classicalMarginal x : ℝ) : ℂ) • (ρ.conditionalState x).toOp
      = (ρ.stateMap x).toOp := by
  unfold CQState.conditionalState
  by_cases h : 0 < ρ.classicalMarginal x
  · rw [dif_pos h, Quantum.Metrics.normalizePosSemidefOp_toOp]
    have htr : (Matrix.trace ((ρ.stateMap x).toPosSemidefOp.toOp)).re
        = ρ.classicalMarginal x := rfl
    rw [htr, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt h),
        Complex.ofReal_one, one_smul]
  · rw [dif_neg h]
    have hp0 : ρ.classicalMarginal x = 0 :=
      le_antisymm (not_lt.mp h) (ρ.classicalMarginal_nonneg x)
    have hpsd : Matrix.PosSemidef (ρ.stateMap x).toOp :=
      Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
    have htr0 : (ρ.stateMap x).toOp.trace = 0 := by
      rw [(ρ.stateMap x).trace_complex_eq,
        show (ρ.stateMap x).trace = ρ.classicalMarginal x from rfl, hp0,
        Complex.ofReal_zero]
    have hzero : (ρ.stateMap x).toOp = 0 := hpsd.trace_eq_zero_iff.mp htr0
    rw [hp0, hzero]
    simp

/-- On the positive-weight support, the normalized eigenvalue distribution
`λ_{x,·}/p(x)` of the block `ρ.stateMap x` is the eigenvalue spectrum of the
conditional state `τ_x = ρ.stateMap x / p(x)`. -/
lemma CQState.conditionalState_isEigenvalueSpectrum
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (x : X) (h : 0 < ρ.classicalMarginal x) :
    IsEigenvalueSpectrum (ρ.conditionalState x)
      (fun i => ρ.blockEigenvalues x i / ρ.classicalMarginal x) := by
  set a := ρ.classicalMarginal x with ha
  set H := (ρ.stateMap x).isHermitian with hH
  -- toOp of the conditional state is the rescaled block
  have hcond_toOp : (ρ.conditionalState x).toOp
      = ((a⁻¹ : ℝ) : ℂ) • (ρ.stateMap x).toOp := by
    have hare : (Matrix.trace (ρ.stateMap x).toOp).re = a := rfl
    unfold CQState.conditionalState
    rw [dif_pos h, Quantum.Metrics.normalizePosSemidefOp_toOp, hare]
  -- spectral decomposition of the block
  let U : Op n := (H.eigenvectorUnitary.val : Op n)
  have h_spec : (ρ.stateMap x).toOp
      = U * Matrix.diagonal (fun i => (ρ.blockEigenvalues x i : ℂ)) * star U := by
    have h := H.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have h_star_mul : star U * U = 1 := Unitary.coe_star_mul_self H.eigenvectorUnitary
  have h_mul_star : U * star U = 1 := by
    have h := Unitary.coe_mul_star_self H.eigenvectorUnitary
    simp only [Unitary.coe_star] at h
    exact h
  -- nonnegativity / sum=1 / ≤1
  have hnn : ∀ i, 0 ≤ ρ.blockEigenvalues x i / a :=
    fun i => div_nonneg (ρ.blockEigenvalues_nonneg x i) h.le
  have hsum : ∑ i, ρ.blockEigenvalues x i / a = 1 := by
    rw [← Finset.sum_div, ρ.sum_blockEigenvalues_eq_classicalMarginal x, ← ha,
        div_self (ne_of_gt h)]
  refine ⟨hnn, hsum, ?_, ?_⟩
  · intro i
    calc ρ.blockEigenvalues x i / a ≤ ∑ j, ρ.blockEigenvalues x j / a :=
          Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
      _ = 1 := hsum
  · -- spectral decomposition for the scaled operator
    refine ⟨star U, ?_, ?_, ?_⟩
    · simp only [← Matrix.star_eq_conjTranspose, star_star]; exact h_mul_star
    · simp only [← Matrix.star_eq_conjTranspose, star_star]; exact h_star_mul
    · simp only [← Matrix.star_eq_conjTranspose, star_star]
      rw [hcond_toOp, h_spec]
      have hD : ((a⁻¹ : ℝ) : ℂ) • Matrix.diagonal (fun i => (ρ.blockEigenvalues x i : ℂ))
          = Matrix.diagonal (fun i => ((ρ.blockEigenvalues x i / a : ℝ) : ℂ)) := by
        rw [← Matrix.diagonal_smul]
        congr 1
        funext i
        rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_inv,
          div_eq_inv_mul]
      set D : Matrix (Fin n) (Fin n) ℂ :=
        Matrix.diagonal (fun i => (ρ.blockEigenvalues x i : ℂ)) with hDdef
      calc ((a⁻¹ : ℝ) : ℂ) • (U * D * star U)
          = U * (((a⁻¹ : ℝ) : ℂ) • D) * star U := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
        _ = U * Matrix.diagonal (fun i => ((ρ.blockEigenvalues x i / a : ℝ) : ℂ)) * star U := by
            rw [hD]

/-- On the positive-weight support, the von-Neumann entropy of the conditional
state `τ_x` is the Shannon entropy of its normalized eigenvalue distribution
`λ_{x,·}/p(x)`; weighting by `p(x)` (which kills the `p(x) = 0` blocks) gives the
per-block summand of `ρ.weightedBlockEntropy`. -/
lemma CQState.classicalMarginal_mul_vonNeumannEntropy_conditionalState
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (x : X) :
    ρ.classicalMarginal x * vonNeumannEntropy (ρ.conditionalState x)
      = ρ.classicalMarginal x *
          shannonEntropy (fun i => ρ.blockEigenvalues x i / ρ.classicalMarginal x) := by
  by_cases h : 0 < ρ.classicalMarginal x
  · congr 1
    rw [vonNeumannEntropy_eq_shannonEntropy (ρ.conditionalState x)
          (fun i => ρ.blockEigenvalues x i / ρ.classicalMarginal x)
          (ρ.conditionalState_isEigenvalueSpectrum x h)]
  · have hp0 : ρ.classicalMarginal x = 0 :=
      le_antisymm (not_lt.mp h) (ρ.classicalMarginal_nonneg x)
    rw [hp0]; ring

/-- The weighted block entropy is bounded by the von Neumann entropy of the quantum
marginal:

    `∑_x p(x)·S(τ_x) ≤ S(ρ_B)`.

This is concavity of the von Neumann entropy: `ρ_B = ρ.quantumMarginalDensityOp`
is the `p(x)`-weighted ensemble average of the conditional states `τ_x`. -/
theorem CQState.weightedBlockEntropy_le_vonNeumannEntropy_quantumMarginal
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    ρ.weightedBlockEntropy ≤ vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm) := by
  classical
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  set e := Fintype.equivFin X with he
  set probs : Fin (Fintype.card X) → ℝ :=
    fun i => ρ.classicalMarginal (e.symm i) with hprobs
  set states : Fin (Fintype.card X) → DensityOp n :=
    fun i => ρ.conditionalState (e.symm i) with hstates
  have hprobs_nonneg : ∀ i, 0 ≤ probs i := fun i => ρ.classicalMarginal_nonneg _
  have hprobs_sum : ∑ i, probs i = 1 := by
    simp only [hprobs]
    rw [Equiv.sum_comp e.symm (fun y => ρ.classicalMarginal y)]
    simpa [CQState.classicalMarginal] using hρ_norm
  -- ρ_B is the ensemble average of the conditional states
  have hbridge :
      InfoTheory.Measurement.DensityOp.fromEnsemble probs states hprobs_nonneg hprobs_sum
        = ρ.quantumMarginalDensityOp hρ_norm := by
    apply DensityOp.ext
    change (∑ i, (probs i : ℂ) • (states i).toOp) = ρ.quantumMarginalOp
    simp only [hprobs, hstates]
    rw [Equiv.sum_comp e.symm
      (fun y => ((ρ.classicalMarginal y : ℝ) : ℂ) • (ρ.conditionalState y).toOp)]
    simp only [ρ.smul_conditionalState_toOp]
    rfl
  have hconc := InfoTheory.RelativeEntropy.vonNeumannEntropy_concave
    probs states hprobs_nonneg hprobs_sum
  rw [hbridge] at hconc
  -- the weighted block entropy is exactly the ensemble's average conditional entropy
  have hweq : ρ.weightedBlockEntropy = ∑ i, probs i * vonNeumannEntropy (states i) := by
    rw [CQState.weightedBlockEntropy]
    simp only [hprobs, hstates]
    rw [Equiv.sum_comp e.symm
      (fun y => ρ.classicalMarginal y * vonNeumannEntropy (ρ.conditionalState y))]
    exact Finset.sum_congr rfl
      (fun x _ => (ρ.classicalMarginal_mul_vonNeumannEntropy_conditionalState x).symm)
  rw [hweq]
  exact hconc

/-- **The quantum step `H(X|B) ≤ H(X)`.**

For a normalized CQ state `ρ`, the conditional von Neumann entropy (in nats) is
bounded by the Shannon entropy of the classical marginal:

    S(ρ_XB) − S(ρ_B) ≤ ∑_x entropyTerm (ρ.classicalMarginal x).

Equivalently `H(X|B) = H(X) − χ ≤ H(X)`, i.e. the Holevo quantity `χ` of the CQ
ensemble is nonnegative. -/
theorem CQState.cqConditional_vonNeumann_le_shannon_classicalMarginal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)
      ≤ ∑ x : X, entropyTerm (ρ.classicalMarginal x) := by
  -- S(ρ_XB) = H(X) + Σ p·S(τ), and Σ p·S(τ) ≤ S(ρ_B).
  have hsplit := ρ.vonNeumannEntropy_toJointDensityOp_eq_classicalShannon_add_weightedBlockEntropy
      hρ_norm
  have hconc := ρ.weightedBlockEntropy_le_vonNeumannEntropy_quantumMarginal hρ_norm
  rw [hsplit]
  linarith

/-- **Classical maximum-entropy bound over a general `Fintype`.** For a nonnegative
weight function `p : X → ℝ` summing to `1`, the Shannon entropy
`∑ x, entropyTerm (p x)` is at most `log` of the size of its positive support
`#{x : 0 < p x}` (the zero-weight outcomes contribute `entropyTerm 0 = 0`). -/
lemma sum_entropyTerm_le_log_card_support
    {X : Type*} [Fintype X] (p : X → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1) :
    ∑ x : X, entropyTerm (p x)
      ≤ Real.log ((Finset.univ.filter (fun x => 0 < p x)).card : ℝ) := by
  classical
  set S := Finset.univ.filter (fun x => 0 < p x) with hS
  -- outside the support, p x = 0 (nonneg + not positive)
  have hzero : ∀ x ∈ (Finset.univ : Finset X), x ∉ S → p x = 0 := by
    intro x _ hx
    have : ¬ (0 < p x) := by
      simpa [hS, Finset.mem_filter] using hx
    exact le_antisymm (not_lt.mp this) (hp_nonneg x)
  -- the support is nonempty since the weights sum to 1
  have hk_pos : 0 < S.card := by
    rw [Finset.card_pos]
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hsum0 : ∑ x : X, p x = 0 :=
      Finset.sum_eq_zero (fun x _ => hzero x (Finset.mem_univ x) (by simp [h]))
    rw [hp_sum] at hsum0
    exact one_ne_zero hsum0
  set k := S.card with hk
  haveI : NeZero k := ⟨hk_pos.ne'⟩
  -- reindex the support to `Fin k`
  set e := S.equivFin with he
  set q : Fin k → ℝ := fun j => p ↑(e.symm j) with hq
  -- the restricted entropy sum equals shannonEntropy q
  have hsum_eq : shannonEntropy q = ∑ x : X, entropyTerm (p x) := by
    unfold shannonEntropy
    simp only [hq]
    rw [Equiv.sum_comp e.symm (fun i : ↥S => entropyTerm (p ↑i)),
        Finset.sum_coe_sort S (fun x => entropyTerm (p x))]
    exact Finset.sum_subset (Finset.subset_univ S)
      (fun x hx hxs => by rw [hzero x hx hxs, entropyTerm_zero])
  -- the reindexed distribution is nonneg and sums to 1
  have hq_nonneg : ∀ j, 0 ≤ q j := fun j => hp_nonneg _
  have hq_sum : ∑ j, q j = 1 := by
    simp only [hq]
    rw [Equiv.sum_comp e.symm (fun i : ↥S => p ↑i),
        Finset.sum_coe_sort S (fun x => p x)]
    rw [Finset.sum_subset (Finset.subset_univ S)
          (fun x hx hxs => hzero x hx hxs), hp_sum]
  rw [← hsum_eq]
  exact shannonEntropy_le_log q hq_nonneg hq_sum

/-- **The classical max-entropy step.**

The Shannon entropy of the classical marginal is bounded by the log of the
support size (the classical rank):

    ∑ x, entropyTerm (ρ.classicalMarginal x) ≤ Real.log (classicalRank ρ).

This is the specialization of `sum_entropyTerm_le_log_card_support` to the
classical-marginal distribution, whose positive-probability support has
cardinality `ρ.classicalRank`. -/
theorem CQState.shannonEntropy_classicalMarginal_le_log_classicalRank
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    ∑ x : X, entropyTerm (ρ.classicalMarginal x) ≤ Real.log (ρ.classicalRank : ℝ) := by
  have h := sum_entropyTerm_le_log_card_support ρ.classicalMarginal
    (fun x => ρ.classicalMarginal_nonneg x)
    (by simpa [CQState.classicalMarginal] using hρ_norm)
  simpa [CQState.classicalRank, CQState.classicalMarginal] using h

/-- **Nat-level CQ conditional entropy bound.** For a normalized CQ state,
`S(ρ_XB) − S(ρ_B) ≤ log (classicalRank ρ)`. -/
theorem CQState.cqConditional_vonNeumann_le_log_classicalRank
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)
      ≤ Real.log (ρ.classicalRank : ℝ) :=
  le_trans
    (ρ.cqConditional_vonNeumann_le_shannon_classicalMarginal hρ_norm)
    (ρ.shannonEntropy_classicalMarginal_le_log_classicalRank hρ_norm)

end InfoTheory.SmoothMinEntropy

end
