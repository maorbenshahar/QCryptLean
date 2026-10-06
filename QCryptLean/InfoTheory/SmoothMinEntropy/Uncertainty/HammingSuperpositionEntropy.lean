import QCryptLean.Math.Analysis.LogBounds
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.SuperpositionPenalty
import QCryptLean.Quantum.Bases.WalshHadamard
import QCryptLean.Math.ClassicalEntropy.HammingBall

/-!
# Bouman–Fehr Corollary 1: conjugate-basis min-entropy of a Hamming-bounded superposition

This module is the capstone of the sampling layer.  It assembles

* the superposition penalty `H_min(ρ^mix|E) ≤ H_min(ρ|E) + log₂|J|`
  (`QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.SuperpositionPenalty`),
* flatness of the `n`-qubit Walsh–Hadamard basis against the computational basis
  (`QCryptLean.Quantum.Bases.WalshHadamard`), and
* the Hamming-ball counting bound `|J| ≤ 2^{n·h(p)}`
  (`QCryptLean.Math.ClassicalEntropy.HammingBall`)

into the conditional statement of Bouman–Fehr, *Sampling in a Quantum Population, and
Applications*, [arXiv:0907.4246v5](https://arxiv.org/abs/0907.4246), Corollary 1 (§4.3):

> for `|φ_AE⟩ = ∑_{b ∈ J} |b⟩|φ^b_E⟩` a superposition of computational strings of relative
> Hamming weight at most `p ≤ 1/2`, measuring `A` in the Hadamard basis yields an outcome `X`
> with `H_min(X|E) ≥ n − h(p)·n`.

It is written additively, `n ≤ H_min(X|E) + h(p)·n`, to avoid truncated `ENNReal` subtraction.

## Why the ingredients combine

Measuring `A` in the Hadamard basis sends the coherent state to the hybrid state whose block at
outcome `w` is the rank-one operator of `∑_{b ∈ J} ⟨w|b⟩_H · φ^b_E`, and the *dephased* state to
the block `∑_{b ∈ J} |⟨w|b⟩_H|² |φ^b_E⟩⟨φ^b_E|`.  Flatness makes every `|⟨w|b⟩_H|²` equal to
`2^{-n}`, so the dephased block is *exactly* `2^{-n}` times the branch reference
`σ = ∑_{b ∈ J} |φ^b_E⟩⟨φ^b_E|`: the dephased outcome is uniformly random given `E`, worth `n`
bits.  That is the content of "measuring qubits within a state `|b⟩` in the Hadamard basis
produces uniformly random bits" (paper, §4.3).  The penalty then costs at most `log₂|J|` bits,
and Hamming counting bounds `log₂|J|` by `n·h(p)`.

Both CQ states are *constructed*, not assumed: `walshSuperpositionMixture` builds them from the
Eve-side branch vectors alone.  The coherent state's total weight is computed by Parseval against
the complete Walsh basis (`Quantum.Operators.sum_normSq_bra_mul_of_complete`), so the only input
is the honest normalization `∑_{b ∈ J} ‖φ^b‖² ≤ 1` of the underlying pure state.

## Scope

`H_min(·|E)` is `conditionalMinEntropyOpt`, the optimized min-entropy: the supremum of
`H_min(·|σ)` over the *feasible* references `σ`, which is how the library reads the paper's
`sup_{σ_E}`.  This is not a *smooth* min-entropy statement, and nothing here concerns a
QKD protocol: the input is a pure state with bounded-weight support and the output is an entropy
bound.  The paper's general `H^θ` version for an arbitrary basis string `θ` is the unitary
relabelling of this statement and is not formalized.

## Main definitions

* `InfoTheory.SmoothMinEntropy.branchReference` — the branch reference `∑_{b ∈ J} |φ^b⟩⟨φ^b|`.
* `InfoTheory.SmoothMinEntropy.walshBranchVec` — the Eve-side branch vector `⟨w|b⟩_H · φ^b`.
* `InfoTheory.SmoothMinEntropy.walshSuperpositionMixture` — the constructed hybrid pair.

## Main statements

* `isFeasible_walshMixture_branchReference` — the dephased state is feasible at `2^{-n}`.
* `ofReal_le_conditionalMinEntropyOpt_walshSuperposition_add_logb_card` —
  `n ≤ H_min(X|E) + log₂|J|`.
* `ofReal_le_conditionalMinEntropyOpt_walshSuperposition_add_binaryEntropy` — **Corollary 1**:
  `n ≤ H_min(X|E) + n·h(p)` for a support inside a Hamming ball of relative radius `p ≤ 1/2`.
-/

open Quantum.Operators Quantum.Bases Math.ClassicalEntropy Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

variable {n dE : ℕ}

/-! ## The branch reference -/

/-- **The branch reference** `σ = ∑_{b ∈ J} |φ^b⟩⟨φ^b|`: the Eve-side operator of the dephased
state, and the reference against which its min-entropy is computed.  The hypothesis is the
honest normalization of the underlying pure state `|φ_AE⟩ = ∑_{b ∈ J} |b⟩|φ^b_E⟩`. -/
def branchReference {ι : Type*} (J : Finset ι) (φ : ι → Fin dE → ℂ)
    (hφ : ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) ≤ 1) : SubDensityOp dE :=
  SubDensityOp.ofPosSemidef
    (Matrix.posSemidef_sum J fun b _ => Matrix.posSemidef_vecMulVec_self_star (φ b))
    (by
      refine le_trans (le_of_eq ?_) hφ
      rw [Matrix.trace_sum, Complex.re_sum]
      exact Finset.sum_congr rfl fun b _ => trace_re_vecMulVec_self_star (φ b))

@[simp] lemma branchReference_toOp {ι : Type*} (J : Finset ι) (φ : ι → Fin dE → ℂ)
    (hφ : ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) ≤ 1) :
    (branchReference J φ hφ).toOp = ∑ b ∈ J, Matrix.vecMulVec (φ b) (star (φ b)) := rfl

/-! ## The measured branch vectors -/

/-- **The Eve-side branch vector of a Hadamard measurement:** `⟨w|_H |b⟩ · φ^b_E`, the component
of the post-measurement state at Walsh outcome `w` contributed by the computational branch `b`. -/
def walshBranchVec (φ : (Fin n → Bool) → Fin dE → ℂ) (w b : Fin n → Bool) : Fin dE → ℂ :=
  ((walshKet w).dag * stdKet (2 ^ n) ((bitIndex n).symm b) : ℂ) • φ b

/-- Flatness of the Hadamard measurement in the form used below: every branch overlap has
squared modulus `2^{-n}`. -/
lemma normSq_walshOverlap (w b : Fin n → Bool) :
    Complex.normSq ((walshKet w).dag * stdKet (2 ^ n) ((bitIndex n).symm b) : ℂ) =
      1 / ((2 ^ n : ℕ) : ℝ) :=
  (stdKet_walshKet_mutuallyUnbiased n).symm w ((bitIndex n).symm b)

/-- The computational kets, re-indexed by bit strings, are orthonormal. -/
lemma stdKet_bitIndex_orthonormal (b b' : Fin n → Bool) :
    ((stdKet (2 ^ n) ((bitIndex n).symm b)).dag * stdKet (2 ^ n) ((bitIndex n).symm b') : ℂ) =
      if b = b' then 1 else 0 := by
  rw [stdKet_braket]
  by_cases h : b = b'
  · rw [ite_eq_left h, ite_eq_left (congrArg (bitIndex n).symm h)]
  · rw [ite_eq_right h, ite_eq_right fun hs => h ((bitIndex n).symm.injective hs)]

/-! ## The two total weights -/

/-- **The dephased total weight is the pure state's squared norm.**  Flatness contributes
`2^{-n}` per branch and there are `2^n` Walsh outcomes, so the factors cancel exactly. -/
lemma sum_normSq_walshBranchVec (J : Finset (Fin n → Bool)) (φ : (Fin n → Bool) → Fin dE → ℂ) :
    (∑ _w : Fin n → Bool, ∑ b ∈ J, ∑ j, Complex.normSq (walshBranchVec φ _w b j)) =
      ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) := by
  have h2n : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  have hinner : ∀ w : Fin n → Bool,
      (∑ b ∈ J, ∑ j, Complex.normSq (walshBranchVec φ w b j)) =
        (1 / ((2 ^ n : ℕ) : ℝ)) * ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) := by
    intro w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [walshBranchVec, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
      normSq_walshOverlap]
  rw [Finset.sum_congr rfl fun w _ => hinner w, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    hcard, ← mul_assoc, mul_one_div, div_self h2n, one_mul]

/-- **The coherent total weight is also the pure state's squared norm.**  For each Eve coordinate
`j` the amplitudes `w ↦ ⟨w|_H ψ_j⟩` are the Walsh-basis amplitudes of the computational-basis
combination `ψ_j = ∑_{b ∈ J} φ^b_j |b⟩`, so Parseval against the complete Walsh basis and
orthonormality of the computational basis give the claim. -/
lemma sum_normSq_sum_walshBranchVec (J : Finset (Fin n → Bool))
    (φ : (Fin n → Bool) → Fin dE → ℂ) :
    (∑ _w : Fin n → Bool, ∑ j, Complex.normSq ((∑ b ∈ J, walshBranchVec φ _w b) j)) =
      ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) := by
  classical
  -- Coordinate `j` of the coherent branch sum is the Walsh amplitude of the computational
  -- combination `ψ_j = ∑_{b ∈ J} φ^b_j |b⟩`.
  have hcoord : ∀ (w : Fin n → Bool) (j : Fin dE),
      (∑ b ∈ J, walshBranchVec φ w b) j =
        ((walshKet w).dag * Ket.combination J (fun b => φ b j)
          (fun b => stdKet (2 ^ n) ((bitIndex n).symm b)) : ℂ) := by
    intro w j
    rw [bra_mul_combination, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => by
      simp only [walshBranchVec, Pi.smul_apply, smul_eq_mul]
      ring
  -- Parseval against the complete Walsh basis, then Bessel equality on the support.
  have hparseval : ∀ j : Fin dE,
      (∑ w : Fin n → Bool, Complex.normSq ((walshKet w).dag * Ket.combination J (fun b => φ b j)
        (fun b => stdKet (2 ^ n) ((bitIndex n).symm b)) : ℂ)) =
        ∑ b ∈ J, Complex.normSq (φ b j) := by
    intro j
    have hP := sum_normSq_bra_mul_of_complete (walshKet (n := n)) walshKet_complete
      (Ket.combination J (fun b => φ b j) (fun b => stdKet (2 ^ n) ((bitIndex n).symm b)))
    have hB := Ket.combination_inner_self_of_orthonormalOn J (fun b => φ b j)
      (fun b => stdKet (2 ^ n) ((bitIndex n).symm b))
      (fun b _ b' _ => stdKet_bitIndex_orthonormal b b')
    exact_mod_cast hP.trans hB
  calc (∑ _w : Fin n → Bool, ∑ j, Complex.normSq ((∑ b ∈ J, walshBranchVec φ _w b) j))
      = ∑ w : Fin n → Bool, ∑ j, Complex.normSq ((walshKet w).dag *
          Ket.combination J (fun b => φ b j)
            (fun b => stdKet (2 ^ n) ((bitIndex n).symm b)) : ℂ) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => by rw [hcoord w j]
    _ = ∑ j, ∑ w : Fin n → Bool, Complex.normSq ((walshKet w).dag *
          Ket.combination J (fun b => φ b j)
            (fun b => stdKet (2 ^ n) ((bitIndex n).symm b)) : ℂ) := Finset.sum_comm
    _ = ∑ j, ∑ b ∈ J, Complex.normSq (φ b j) := Finset.sum_congr rfl fun j _ => hparseval j
    _ = ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) := Finset.sum_comm

/-! ## The constructed hybrid pair -/

/-- **The Hadamard-measured superposition/mixture pair** of a computational-basis superposition
`|φ_AE⟩ = ∑_{b ∈ J} |b⟩|φ^b_E⟩`.  Both CQ states are built from the branch vectors; the two
normalization obligations are discharged by `sum_normSq_sum_walshBranchVec` (Parseval) and
`sum_normSq_walshBranchVec` (flatness plus outcome counting), so the sole hypothesis is the
subnormalization of the pure state. -/
def walshSuperpositionMixture (J : Finset (Fin n → Bool)) (φ : (Fin n → Bool) → Fin dE → ℂ)
    (hφ : ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) ≤ 1) :
    SuperpositionMixture (Fin n → Bool) dE (Fin n → Bool) :=
  SuperpositionMixture.ofVectors J (walshBranchVec φ)
    (by rw [sum_normSq_sum_walshBranchVec]; exact hφ)
    (by rw [sum_normSq_walshBranchVec]; exact hφ)

/-! ## The dephased floor -/

/-- **The dephased Hadamard measurement is uniformly random given `E`.**  Every block of the
dephased state equals `2^{-n}` times the branch reference, so `2^{-n}` is feasible — the exact
statement that the outcome carries `n` bits of min-entropy conditioned on Eve. -/
theorem isFeasible_walshMixture_branchReference (J : Finset (Fin n → Bool))
    (φ : (Fin n → Bool) → Fin dE → ℂ) (hφ : ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) ≤ 1) :
    isFeasible (walshSuperpositionMixture J φ hφ).mixture (branchReference J φ hφ)
      (1 / ((2 ^ n : ℕ) : ℝ)) := by
  refine ⟨by positivity, fun w => ?_⟩
  have hblock : ((walshSuperpositionMixture J φ hφ).mixture.stateMap w).toOp =
      (Complex.ofReal (1 / ((2 ^ n : ℕ) : ℝ))) • (branchReference J φ hφ).toOp := by
    rw [(walshSuperpositionMixture J φ hφ).mixture_stateMap w, branchReference_toOp,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (walshSuperpositionMixture J φ hφ).vec w b = walshBranchVec φ w b from rfl,
      walshBranchVec, vecMulVec_smul_self_star, normSq_walshOverlap]
  rw [hblock]
  exact fun v => le_refl _

/-! ## The conditional min-entropy bounds -/

/-- **The `n`-bit floor plus the superposition penalty.**  For the Hadamard measurement of a
computational-basis superposition supported on `J`,

  `n ≤ H_min(X|E) + log₂ |J|`,

with `H_min` the optimized conditional min-entropy.  No positivity or nondegeneracy side
condition is needed: the `ENNReal` forms handle the boundaries. -/
theorem ofReal_le_conditionalMinEntropyOpt_walshSuperposition_add_logb_card
    (J : Finset (Fin n → Bool)) (φ : (Fin n → Bool) → Fin dE → ℂ)
    (hφ : ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) ≤ 1) :
    ENNReal.ofReal (n : ℝ) ≤
      conditionalMinEntropyOpt (walshSuperpositionMixture J φ hφ).superposition +
        ENNReal.ofReal (Real.logb 2 (J.card : ℝ)) := by
  have hfeas := isFeasible_walshMixture_branchReference J φ hφ
  have hfloor := ofReal_neg_logb_le_conditionalMinEntropy
    (walshSuperpositionMixture J φ hφ).mixture (branchReference J φ hφ) hfeas
  have hlog : -Real.logb 2 (1 / ((2 ^ n : ℕ) : ℝ)) = (n : ℝ) := by
    rw [one_div, Real.logb_inv, neg_neg,
      show ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n by push_cast; ring,
      Real.logb_self_pow (by norm_num) (by norm_num)]
  rw [hlog] at hfloor
  refine le_trans hfloor ?_
  refine le_trans (conditionalMinEntropy_le_conditionalMinEntropyOpt _ _ ⟨_, hfeas⟩) ?_
  exact (walshSuperpositionMixture J φ
    hφ).conditionalMinEntropyOpt_mixture_le_superposition_add_logb_card

/-- **Bouman–Fehr Corollary 1** (arXiv:0907.4246v5, §4.3).  Let `|φ_AE⟩ = ∑_{b ∈ J} |b⟩|φ^b_E⟩`
be a subnormalized superposition of computational `n`-bit strings all lying within Hamming
distance `r` of a centre `c`, and let `p ∈ [0, 1/2]` satisfy `r ≤ p·n`.  Measuring `A` in the
Hadamard basis produces an outcome `X` with

  `n ≤ H_min(X|E) + h(p)·n`,

i.e. `H_min(X|E) ≥ (1 − h(p))·n` bits of conditional min-entropy.  The centre `c` is arbitrary;
only the *volume* of the ball enters.  At `p = 0` the support is a single string and the bound is
the full `n` bits; it degrades to nothing as `p → 1/2`. -/
theorem ofReal_le_conditionalMinEntropyOpt_walshSuperposition_add_binaryEntropy
    {r : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp_half : p ≤ 1 / 2) (hr : (r : ℝ) ≤ p * (n : ℝ))
    (c : Fin n → Bool) (J : Finset (Fin n → Bool)) (hJ : ∀ b ∈ J, hammingDist c b ≤ r)
    (φ : (Fin n → Bool) → Fin dE → ℂ)
    (hφ : ∑ b ∈ J, ∑ j, Complex.normSq (φ b j) ≤ 1) :
    ENNReal.ofReal (n : ℝ) ≤
      conditionalMinEntropyOpt (walshSuperpositionMixture J φ hφ).superposition +
        ENNReal.ofReal ((n : ℝ) * binaryEntropyBits p) := by
  classical
  refine le_trans (ofReal_le_conditionalMinEntropyOpt_walshSuperposition_add_logb_card J φ hφ) ?_
  refine add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal ?_)
  have hent_nonneg : 0 ≤ (n : ℝ) * binaryEntropyBits p :=
    mul_nonneg (Nat.cast_nonneg n) (binaryEntropyBits_nonneg p hp0 (by linarith))
  rcases Nat.eq_zero_or_pos J.card with hJ0 | hJpos
  · rw [hJ0]
    simpa using hent_nonneg
  · have hsub : J ⊆ Finset.univ.filter fun y : Fin n → Bool => hammingDist c y ≤ r :=
      fun b hb => Finset.mem_filter.mpr ⟨Finset.mem_univ b, hJ b hb⟩
    have hcard : (J.card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits p) := by
      have hle : (J.card : ℝ) ≤
          ((Finset.univ.filter fun y : Fin n → Bool => hammingDist c y ≤ r).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hball := card_filter_hammingDist_le_two_pow_of_le (ι := Fin n) c hp0 hp_half
        (by simpa using hr)
      exact hle.trans (by simpa using hball)
    have hJR : (0 : ℝ) < (J.card : ℝ) := by exact_mod_cast hJpos
    have hmono := Real.logb_le_logb_of_le one_lt_two hJR hcard
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at hmono

end InfoTheory.SmoothMinEntropy

end
