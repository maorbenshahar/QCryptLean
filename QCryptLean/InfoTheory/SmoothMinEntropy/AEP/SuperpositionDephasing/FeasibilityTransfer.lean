import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SuperpositionDephasing.Basic
import QCryptLean.InfoTheory.DeFinetti.Purification

/-!
# Dephased-mixture feasibility transfer — operator positivity, λ-feasibility, min-entropy

Operator-positivity feasibility transfer for the dephased mixture `dephasedMixtureCQ`.
A single weighted conditional reference is Löwner-dominated by the dephased reference
`σ_dephased = Σ_{s'} weight s' • σ_cond s'`, and from this a common per-component
feasibility scalar transfers to the assembled mixture.  These results turn
per-component conditional-min-entropy lower bounds into a lower bound for the mixture.

**Textbook reference**: Renner, R. (2005). *Security of Quantum Key Distribution*.
PhD thesis, ETH Zürich. arXiv:quant-ph/0512258v2.

## Main statements
- `opLe_smul_cond_le_dephased`: a weighted conditional reference is `opLe`-dominated
  by the dephased reference.
- `isFeasible_dephasedMixtureCQ_of_components`: a commonly-feasible scalar transfers
  to the mixture.
- `minFeasibleLambda_dephasedMixtureCQ_le_of_components`: `minFeasibleLambda` of the
  mixture is bounded by any commonly-feasible scalar.
- `conditionalMinEntropyReal_dephasedMixtureCQ_ge_of_components`: a common
  per-component min-entropy lower bound lower bounds the mixture's real-valued
  conditional min-entropy.
-/

open Real Math.ClassicalEntropy
open Quantum.Operators
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open InfoTheory.SmoothMinEntropy

open Quantum.Operators in
/-- A single weighted conditional reference `weight s • σ_cond s` is dominated in
    the Löwner/`opLe` order by the dephased reference
    `σ_dephased = Σ_{s'∈S} weight s' • σ_cond s'`, because every other summand is
    PSD. -/
lemma opLe_smul_cond_le_dephased
    {n : ℕ}
    (S : Finset ℕ) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (σ_dephased : SubDensityOp n)
    (σ_cond : ℕ → SubDensityOp n)
    (hσ_dephased_pin : σ_dephased.toOp =
      ∑ s ∈ S, (weight s : ℂ) • (σ_cond s).toOp)
    {s : ℕ} (hs : s ∈ S) :
    opLe ((weight s : ℂ) • (σ_cond s).toOp) σ_dephased.toOp := by
  intro v
  rw [hσ_dephased_pin]
  have hqf_sum :
      (quadraticForm (∑ s' ∈ S, (weight s' : ℂ) • (σ_cond s').toOp) v).re
        = ∑ s' ∈ S, (quadraticForm ((weight s' : ℂ) • (σ_cond s').toOp) v).re := by
    unfold quadraticForm
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  rw [hqf_sum]
  refine Finset.single_le_sum
    (f := fun s' => (quadraticForm ((weight s' : ℂ) • (σ_cond s').toOp) v).re)
    (fun s' hs' => ?_) hs
  have hpsd : ((σ_cond s').toOp).PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib (σ_cond s').toPosSemidefOp
  exact InfoTheory.DeFinetti.quadraticForm_re_nonneg_of_nonnegReal_smul (weight s' : ℂ) ((σ_cond
      s').toOp) v hpsd
    (by rw [Complex.ofReal_re]; exact hweight_nonneg s' hs')
    (Complex.ofReal_im _)

/-- Feasibility transfer.  If a scalar `t ≥ 0` is feasible for every per-component
    problem `(comp s | σ_cond s)` (all `s ∈ S`), then `t` is feasible for the
    dephased mixture against `σ_dephased`. -/
lemma isFeasible_dephasedMixtureCQ_of_components
    {X : Type*} [Fintype X] {n : ℕ}
    (S : Finset ℕ) (comp : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (hweight_le_one : ∀ s ∈ S, weight s ≤ 1)
    (hweight_sum : ∑ s ∈ S, weight s ≤ 1)
    (σ_dephased : SubDensityOp n)
    (σ_cond : ℕ → SubDensityOp n)
    (hσ_dephased_pin : σ_dephased.toOp =
      ∑ s ∈ S, (weight s : ℂ) • (σ_cond s).toOp)
    {t : ℝ} (ht_nonneg : 0 ≤ t)
    (hcomp_feas : ∀ s ∈ S, isFeasible (comp s) (σ_cond s) t) :
    isFeasible
      (dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum)
      σ_dephased t := by
  refine ⟨ht_nonneg, fun p => ?_⟩
  obtain ⟨x, ⟨s, hs⟩⟩ := p
  -- the (x, ⟨s, hs⟩)-block is `weight s • (comp s).stateMap x`
  change opLe ((weight s : ℂ) • ((comp s).stateMap x).toOp)
    ((Complex.ofReal t) • σ_dephased.toOp)
  -- scale the per-component feasibility by `weight s ≥ 0`
  have hA := opLe_smul_nonneg (hweight_nonneg s hs) ((hcomp_feas s hs).2 x)
  -- scale the operator-positivity step by `t ≥ 0`
  have hstar := opLe_smul_cond_le_dephased S weight hweight_nonneg σ_dephased σ_cond
    hσ_dephased_pin hs
  have hB := opLe_smul_nonneg ht_nonneg hstar
  -- bridge A's RHS to B's LHS by commuting the two real scalings
  have hcomm :
      (Complex.ofReal (weight s)) • ((Complex.ofReal t) • (σ_cond s).toOp)
        = (Complex.ofReal t) • ((Complex.ofReal (weight s)) • (σ_cond s).toOp) :=
    smul_comm _ _ _
  rw [hcomm] at hA
  exact opLe_trans hA hB

/-- `minFeasibleLambda` of the mixture is bounded by any commonly-feasible scalar.
    If `t ≥ 0` is feasible for every per-component problem, then
    `minFeasibleLambda(ρ̃', σ_dephased) ≤ t`.  In particular, taking
    `t = max_{s∈S} minFeasibleLambda(comp s, σ_cond s)` gives the feasibility
    transfer. -/
lemma minFeasibleLambda_dephasedMixtureCQ_le_of_components
    {X : Type*} [Fintype X] {n : ℕ}
    (S : Finset ℕ) (comp : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (hweight_le_one : ∀ s ∈ S, weight s ≤ 1)
    (hweight_sum : ∑ s ∈ S, weight s ≤ 1)
    (σ_dephased : SubDensityOp n)
    (σ_cond : ℕ → SubDensityOp n)
    (hσ_dephased_pin : σ_dephased.toOp =
      ∑ s ∈ S, (weight s : ℂ) • (σ_cond s).toOp)
    {t : ℝ} (ht_nonneg : 0 ≤ t)
    (hcomp_feas : ∀ s ∈ S, isFeasible (comp s) (σ_cond s) t) :
    minFeasibleLambda
        (dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum)
        σ_dephased ≤ t :=
  minFeasibleLambda_le_of_isFeasible _ _
    (isFeasible_dephasedMixtureCQ_of_components S comp weight hweight_nonneg
      hweight_le_one hweight_sum σ_dephased σ_cond hσ_dephased_pin ht_nonneg hcomp_feas)

/-- Entropy-level feasibility transfer.  If `k` is a common per-component
    min-entropy lower bound (and each per-component problem is feasible), then `k`
    lower bounds the mixture's real-valued conditional min-entropy.

    The positivity hypothesis `hpos` on the mixture's optimum excludes the
    `−log₂ 0 = 0` sentinel; in the AEP application it holds because the smoothing
    candidates have support inside `σ_cond s`. -/
lemma conditionalMinEntropyReal_dephasedMixtureCQ_ge_of_components
    {X : Type*} [Fintype X] {n : ℕ}
    (S : Finset ℕ) (comp : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (hweight_le_one : ∀ s ∈ S, weight s ≤ 1)
    (hweight_sum : ∑ s ∈ S, weight s ≤ 1)
    (σ_dephased : SubDensityOp n)
    (σ_cond : ℕ → SubDensityOp n)
    (hσ_dephased_pin : σ_dephased.toOp =
      ∑ s ∈ S, (weight s : ℂ) • (σ_cond s).toOp)
    (k : ℝ)
    (hcomp_feas : ∀ s ∈ S, hasFeasibleLambda (comp s) (σ_cond s))
    (hcomp_ge : ∀ s ∈ S, k ≤ conditionalMinEntropyReal (comp s) (σ_cond s))
    (hpos : 0 < minFeasibleLambda
      (dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum)
      σ_dephased) :
    k ≤ conditionalMinEntropyReal
      (dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum)
      σ_dephased := by
  have ht_nonneg : (0 : ℝ) ≤ 2 ^ (-k) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hfeas_each : ∀ s ∈ S, isFeasible (comp s) (σ_cond s) (2 ^ (-k)) := by
    intro s hs
    have hlam_le :=
      minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le (comp s) (σ_cond s) k (hcomp_ge
          s hs)
    have hattain :=
      isFeasible_minFeasibleLambda_of_hasFeasibleLambda (comp s) (σ_cond s) (hcomp_feas s hs)
    exact isFeasible_mono_t hattain hlam_le
  have hmix_le := minFeasibleLambda_dephasedMixtureCQ_le_of_components S comp weight
    hweight_nonneg hweight_le_one hweight_sum σ_dephased σ_cond hσ_dephased_pin
    ht_nonneg hfeas_each
  exact conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k _ _ k hpos hmix_le

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
