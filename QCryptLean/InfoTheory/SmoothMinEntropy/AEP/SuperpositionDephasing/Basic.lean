import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Fidelity
import QCryptLean.Math.ClassicalEntropy.Entropy

/-!
# Dephased-mixture CQ data — `componentWeight`, `dephasedMixtureCQ`, weight/trace identities

Explicit dephasing data for the symmetric-subspace AEP (`thm:Renyisym`): the
dephased-mixture CQ state `dephasedMixtureCQ` built from a finite index family of
mutually orthogonal per-component CQ states, together with the per-component weight
`componentWeight = |γ_s|²` and the basic weight/trace identities.

**Textbook reference**: Renner, R. (2005). *Security of Quantum Key Distribution*.
PhD thesis, ETH Zürich. arXiv:quant-ph/0512258v2.

## Dephasing data

The dephased mixture is built explicitly from:
- a finite index set `S : Finset ℕ` (the dephasing register `S`),
- a family `comp : ℕ → CQState X n` of per-component CQ states (the `ρ̃^s_{AB}`),
- a weight `weight : ℕ → ℝ` with `weight s = |γ_s|²` (so `Σ_{s∈S} weight s = 1`).

The dephased mixture is the `CQState (X × {s // s ∈ S}) n` whose `(x, s)`-block is
`weight s • (comp s).stateMap x`.  This is `ρ̃_{ABS}` written as a CQ state whose
classical register is `X × S`; the per-`s` conditional operator is
`weight s • (comp s)`, and the cross terms between distinct `s` vanish by
construction (genuine mixture, no superposition off-diagonals).

## Main definitions
- `componentWeight`: the per-component weight `|γ_s|²` extracted from a coefficient.
- `dephasedMixtureCQ`: the dephased-mixture CQ state `ρ̃_{ABS}`.

## Main statements
- `dephasedMixtureCQ_stateMap`: the `(x, s)`-block is `weight s • (comp s).stateMap x`.
- `dephasedMixtureCQ_toJointDensity_trace`: the joint-density trace decomposes over
  the weights, `tr ρ̃_{ABS} = Σ_{s∈S} weight s · tr (comp s)`.
-/

open Real Math.ClassicalEntropy
open Quantum.Operators
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open InfoTheory.SmoothMinEntropy

/-- Per-component weight `weight s := |γ_s|²` extracted from a complex
    coefficient `γ_s`.  Nonnegative; bounded by `1` once the squared moduli sum
    to `1`. -/
def componentWeight (γ : ℂ) : ℝ := Complex.normSq γ

lemma componentWeight_nonneg (γ : ℂ) : 0 ≤ componentWeight γ :=
  Complex.normSq_nonneg γ

/-- If the squared moduli of a coefficient family sum to one, each individual
    squared modulus is at most one. -/
lemma componentWeight_le_one_of_sum_eq_one
    (S : Finset ℕ) (γ : ℕ → ℂ) (hsum : ∑ s ∈ S, Complex.normSq (γ s) = 1)
    (s : ℕ) (hs : s ∈ S) : componentWeight (γ s) ≤ 1 := by
  unfold componentWeight
  rw [← hsum]
  exact Finset.single_le_sum (fun t _ => Complex.normSq_nonneg (γ t)) hs

/-- **The dephased-mixture CQ state `ρ̃_{ABS}` (Renner main.tex:6184, the
    `ρ̃_{X^n B^n S}` of the AEP proof; general `lem:smoothHinfcondlowbound` form
    eq `rhobABEXdef`, main.tex:3259).**

    Built from a per-component CQ family `comp : ℕ → CQState X n` and a weight
    family `weight`, over the product classical register `X × {s // s ∈ S}`.
    The `(x, s)`-block is `weight s • (comp s).stateMap x`; the per-`s` conditional
    operator is `weight s • (comp s)`, and the cross terms between distinct `s`
    vanish by construction (genuine mixture).

    hweight_le_one is the per-block sub-normalization needed to scale each block
    by `weight s ≤ 1` (only required for `s ∈ S`, the indices that actually appear);
    `hweight_sum` certifies the overall weight `≤ 1`. -/
def dephasedMixtureCQ
    {X : Type*} [Fintype X] {n : ℕ}
    (S : Finset ℕ) (comp : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (hweight_le_one : ∀ s ∈ S, weight s ≤ 1)
    (hweight_sum : ∑ s ∈ S, weight s ≤ 1) :
    CQState (X × {s // s ∈ S}) n where
  stateMap := fun p =>
    (comp p.2.1).stateMap p.1 |>.smul (weight p.2.1)
      (hweight_nonneg p.2.1 p.2.2) (hweight_le_one p.2.1 p.2.2)
  weight_le_one := by
    calc ∑ p : X × {s // s ∈ S},
            (((comp p.2.1).stateMap p.1).smul (weight p.2.1)
              (hweight_nonneg p.2.1 p.2.2) (hweight_le_one p.2.1 p.2.2)).trace
        = ∑ p : X × {s // s ∈ S},
            weight p.2.1 * ((comp p.2.1).stateMap p.1).trace := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [SubDensityOp.smul_trace]
      _ = ∑ s : {s // s ∈ S}, weight s.1 *
            ∑ x : X, ((comp s.1).stateMap x).trace := by
          rw [Fintype.sum_prod_type_right]
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [Finset.mul_sum]
      _ ≤ ∑ s : {s // s ∈ S}, weight s.1 * 1 := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          exact mul_le_mul_of_nonneg_left (comp s.1).weight_le_one (hweight_nonneg s.1 s.2)
      _ = ∑ s ∈ S, weight s := by
          simp only [mul_one]; exact Finset.sum_attach S weight
      _ ≤ 1 := hweight_sum

/-- The `(x, s)`-block of the dephased mixture is `weight s • (comp s).stateMap x`. -/
@[simp] lemma dephasedMixtureCQ_stateMap
    {X : Type*} [Fintype X] {n : ℕ}
    (S : Finset ℕ) (comp : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (hweight_le_one : ∀ s ∈ S, weight s ≤ 1)
    (hweight_sum : ∑ s ∈ S, weight s ≤ 1)
    (p : X × {s // s ∈ S}) :
    (dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum).stateMap p =
      ((comp p.2.1).stateMap p.1).smul (weight p.2.1)
        (hweight_nonneg p.2.1 p.2.2) (hweight_le_one p.2.1 p.2.2) :=
  rfl

/-- The joint-density trace of the dephased mixture decomposes over the weights:
    `tr ρ̃_{ABS} = Σ_{s∈S} weight s · tr (comp s)`. -/
lemma dephasedMixtureCQ_toJointDensity_trace
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (S : Finset ℕ) (comp : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hweight_nonneg : ∀ s ∈ S, 0 ≤ weight s)
    (hweight_le_one : ∀ s ∈ S, weight s ≤ 1)
    (hweight_sum : ∑ s ∈ S, weight s ≤ 1) :
    (dephasedMixtureCQ S comp weight hweight_nonneg hweight_le_one hweight_sum).toJointDensity.trace
      = ∑ s ∈ S, weight s * (comp s).toJointDensity.trace := by
  rw [CQState.toJointDensity_trace_eq_sum]
  simp only [dephasedMixtureCQ_stateMap, SubDensityOp.smul_trace]
  rw [Fintype.sum_prod_type_right]
  rw [← Finset.sum_attach S (fun s => weight s * (comp s).toJointDensity.trace)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [CQState.toJointDensity_trace_eq_sum, Finset.mul_sum]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
