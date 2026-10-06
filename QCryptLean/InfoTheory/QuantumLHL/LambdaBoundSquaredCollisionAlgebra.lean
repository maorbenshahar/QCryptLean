import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundSingleSigma
import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundTwoUniversal
import QCryptLean.InfoTheory.QuantumLHL.ScalarTwoUniversalL2

/-!
# Squared-sandwich seed-collision algebra

This module contains the low-level finite-sum conversion from seed-averaged
collisions to the variance-pair inequality, specialized to the squared sandwich
kernel.  It is kept separate from `LambdaBoundSquaredCollision.lean` so the
main δ-squared helper remains small and responsive to interactive tooling.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- Bilinearity of the squared sandwich kernel. -/
private lemma sum_pair_tr_SMzSsq_eq_marginal_sq_collision_aux
    {X : Type*} [Fintype X] {n : ℕ} (S : Op n) (R : X → Op n) :
    ∑ x : X, ∑ x' : X, ((S * R x * S) * (S * R x' * S)).trace.re =
      ((S * (∑ x : X, R x) * S) * (S * (∑ x : X, R x) * S)).trace.re := by
  have h := sum_pair_tr_S_RR_S_eq_marginal_sq
    (1 : Op n) (fun x : X => S * R x * S)
  have hsum : (∑ x : X, S * R x * S) = S * (∑ x : X, R x) * S := by
    rw [← Finset.sum_mul, ← Matrix.mul_sum]
  simpa [hsum, Matrix.one_mul, Matrix.mul_one] using h

/-- Seed-collision sums can be rewritten as pair sums with filter-card
coefficients. -/
private lemma seed_collision_sum_eq_filter_pair_sum
    {Seed X Z : Type*} [Fintype Seed] [Fintype X] [DecidableEq Z]
    (H : QuantumHashFamily Seed X Z) (K : X → X → ℝ) :
    (1 / (Fintype.card Seed : ℝ)) *
        ∑ s : Seed, ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then K x x' else 0) =
      ∑ x : X, ∑ x' : X,
        ((1 / (Fintype.card Seed : ℝ)) *
          ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ)) *
        K x x' := by
  have hSwap :
      (∑ s : Seed, ∑ x : X, ∑ x' : X,
        (if H.hash s x = H.hash s x' then K x x' else 0)) =
      ∑ x : X, ∑ x' : X,
        ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ) *
          K x x' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    exact Finset.sum_ite_const_eq_filter_card_mul_real
      (fun s : Seed => H.hash s x = H.hash s x') (K x x')
  rw [hSwap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- Pure real algebra: a variance-pair bound implies the corresponding
uncentered pair bound with a full-pair correction. -/
private lemma pair_sum_le_diag_add_c_pair_sum_of_variance
    {X : Type*} [Fintype X] (tau K : X → X → ℝ) (c : ℝ)
    (hVar :
      (∑ x : X, ∑ x' : X, (tau x x' - c) * K x x') ≤
        ∑ x : X, K x x) :
    (∑ x : X, ∑ x' : X, tau x x' * K x x') ≤
      (∑ x : X, K x x) + c * (∑ x : X, ∑ x' : X, K x x') := by
  have hTauSplit :
      (∑ x : X, ∑ x' : X, tau x x' * K x x') =
        (∑ x : X, ∑ x' : X, (tau x x' - c) * K x x') +
          c * (∑ x : X, ∑ x' : X, K x x') := by
    calc
      (∑ x : X, ∑ x' : X, tau x x' * K x x') =
          ∑ x : X, ∑ x' : X, ((tau x x' - c) * K x x' + c * K x x') := by
            refine Finset.sum_congr rfl fun x _ => ?_
            refine Finset.sum_congr rfl fun x' _ => ?_
            ring
      _ = (∑ x : X, ∑ x' : X, (tau x x' - c) * K x x') +
          (∑ x : X, ∑ x' : X, c * K x x') := by
            simp_rw [Finset.sum_add_distrib]
      _ = (∑ x : X, ∑ x' : X, (tau x x' - c) * K x x') +
          c * (∑ x : X, ∑ x' : X, K x x') := by
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
  rw [hTauSplit]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right hVar (c * (∑ x : X, ∑ x' : X, K x x'))

/-- Hermitian sandwich of a PSD operator is PSD. -/
private lemma hermitian_sandwich_posSemidef
    {n : ℕ} {S A : Op n} (hS : S.IsHermitian) (hA : A.PosSemidef) :
    (S * A * S).PosSemidef := by
  rw [show S * A * S = S.conjTranspose * A * S from by rw [hS.eq]]
  exact hA.conjTranspose_mul_mul_same S

/-- The squared-sandwich 2-universality bound: the centred pair sum is bounded by
the diagonal.  Direct proof via off-diagonal non-positivity and diagonal contraction;
uses the squared-sandwich expression directly. -/
private lemma squared_sandwich_variance_pair_bound
    {Seed X Z : Type*} [Fintype Seed] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (S : Op n) (hS : S.IsHermitian)
    (H : QuantumHashFamily Seed X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n) :
    ∑ x : X, ∑ x' : X,
      ((1 / (Fintype.card Seed : ℝ)) *
        ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ) -
        (1 / (Fintype.card Z : ℝ))) *
      ((S * (ρ.stateMap x).toOp * S) *
        (S * (ρ.stateMap x').toOp * S)).trace.re ≤
    ∑ x : X,
      ((S * (ρ.stateMap x).toOp * S) *
        (S * (ρ.stateMap x).toOp * S)).trace.re := by
  classical
  -- Abbreviations.
  let Q : X → Op n := fun x => S * (ρ.stateMap x).toOp * S
  -- (1) Q x is PSD for every x.
  have hQ_psd : ∀ x : X, (Q x).PosSemidef := fun x =>
    hermitian_sandwich_posSemidef hS
      (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)
  -- (2) K(x,x') := (Q x * Q x').trace.re is non-negative.
  -- `tr_prod_sandwich_re_nonneg` with T = 1 gives
  --   `0 ≤ ((1 * (Q x) * 1) * (1 * (Q x') * 1)).trace.re = (Q x * Q x').trace.re`.
  have hK_nonneg' : ∀ x x' : X,
      0 ≤ ((S * (ρ.stateMap x).toOp * S) * (S * (ρ.stateMap x').toOp * S)).trace.re :=
    fun x x' => by
      have h := tr_prod_sandwich_re_nonneg Matrix.isHermitian_one (hQ_psd x) (hQ_psd x')
      simpa using h
  -- (3) Off-diagonal coefficient is non-positive for x ≠ x' (by 2-universality).
  have hOffdiag_coeff : ∀ x x' : X, x ≠ x' →
      (1 / (Fintype.card Seed : ℝ)) *
        ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ) -
        (1 / (Fintype.card Z : ℝ)) ≤ 0 :=
    fun x x' hne => quantumHash_offdiag_coeff_nonpos H hH hne
  -- (4) Diagonal coefficient: τ(x,x) = 1, so coefficient = 1 - 1/|Z| ≤ 1.
  haveI : Nonempty Seed := H.seedNonempty
  haveI : Nonempty Z := H.outputNonempty
  have hSeed_pos : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hSeed_ne : (Fintype.card Seed : ℝ) ≠ 0 := ne_of_gt hSeed_pos
  have hZ_pos : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have hZ_ne : (Fintype.card Z : ℝ) ≠ 0 := ne_of_gt hZ_pos
  have hDiag_coeff : ∀ x : X,
      (1 / (Fintype.card Seed : ℝ)) *
        ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x)).card : ℝ) -
        (1 / (Fintype.card Z : ℝ)) = 1 - 1 / (Fintype.card Z : ℝ) := by
    intro x
    have hfilter : (Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x)) =
        Finset.univ := Finset.filter_true_of_mem (fun _ _ => rfl)
    rw [hfilter, Finset.card_univ]
    field_simp
  -- (5) Split LHS into diagonal and off-diagonal.
  have hLHS_split :
      ∑ x : X, ∑ x' : X,
          ((1 / (Fintype.card Seed : ℝ)) *
              ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ) -
              (1 / (Fintype.card Z : ℝ))) *
            ((S * (ρ.stateMap x).toOp * S) *
              (S * (ρ.stateMap x').toOp * S)).trace.re =
        (∑ x : X,
            ((1 / (Fintype.card Seed : ℝ)) *
                ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x)).card : ℝ) -
                (1 / (Fintype.card Z : ℝ))) *
              ((S * (ρ.stateMap x).toOp * S) *
                (S * (ρ.stateMap x).toOp * S)).trace.re) +
          ∑ x : X, ∑ x' : X,
            if x ≠ x' then
              ((1 / (Fintype.card Seed : ℝ)) *
                  ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ) -
                  (1 / (Fintype.card Z : ℝ))) *
                ((S * (ρ.stateMap x).toOp * S) *
                  (S * (ρ.stateMap x').toOp * S)).trace.re
            else 0 := by
      rw [Finset.sum_sum_eq_diag_add_offdiag
          (fun x x' => ((1 / (Fintype.card Seed : ℝ)) *
              ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ) -
              (1 / (Fintype.card Z : ℝ))) *
            ((S * (ρ.stateMap x).toOp * S) *
              (S * (ρ.stateMap x').toOp * S)).trace.re)]
  rw [hLHS_split]
  -- (6) Diagonal sum ≤ ∑ x, K(x,x).
  have hDiag_le : ∑ x : X,
        ((1 / (Fintype.card Seed : ℝ)) *
            ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x)).card : ℝ) -
            (1 / (Fintype.card Z : ℝ))) *
          ((S * (ρ.stateMap x).toOp * S) *
            (S * (ρ.stateMap x).toOp * S)).trace.re ≤
      ∑ x : X,
          ((S * (ρ.stateMap x).toOp * S) *
            (S * (ρ.stateMap x).toOp * S)).trace.re := by
    apply Finset.sum_le_sum
    intro x _
    rw [hDiag_coeff x]
    have hKxx : 0 ≤ ((S * (ρ.stateMap x).toOp * S) *
          (S * (ρ.stateMap x).toOp * S)).trace.re := hK_nonneg' x x
    have hZ_inv_nonneg : 0 ≤ 1 / (Fintype.card Z : ℝ) := by positivity
    nlinarith
  -- (7) Off-diagonal sum ≤ 0.
  have hOffdiag_le : ∑ x : X, ∑ x' : X,
      (if x ≠ x' then
        ((1 / (Fintype.card Seed : ℝ)) *
            ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ) -
            (1 / (Fintype.card Z : ℝ))) *
          ((S * (ρ.stateMap x).toOp * S) *
            (S * (ρ.stateMap x').toOp * S)).trace.re
       else 0) ≤ 0 := by
    apply Finset.sum_nonpos
    intro x _
    apply Finset.sum_nonpos
    intro x' _
    by_cases hxx' : x ≠ x'
    · rw [if_pos hxx']
      exact mul_nonpos_of_nonpos_of_nonneg (hOffdiag_coeff x x' hxx') (hK_nonneg' x x')
    · rw [if_neg hxx']
  linarith

/-- Pair-sum form of the squared sandwich marginal. -/
private lemma squared_sandwich_pair_sum_eq_marginal
    {X : Type*} [Fintype X] {n : ℕ} (S : Op n) (ρ : CQState X n) :
    ∑ x : X, ∑ x' : X,
      ((S * (ρ.stateMap x).toOp * S) *
        (S * (ρ.stateMap x').toOp * S)).trace.re =
      ((S * ρ.quantumMarginalOp * S) *
        (S * ρ.quantumMarginalOp * S)).trace.re := by
  simpa [CQState.quantumMarginalOp] using
    sum_pair_tr_SMzSsq_eq_marginal_sq_collision_aux
      S (fun x : X => (ρ.stateMap x).toOp)

/-- Convert the variance-pair inequality into the squared-sandwich combined
seed-collision bound. -/
lemma seed_avg_collision_sum_sq_le_diag_plus_c_marginalSq_algebra
    {Seed X Z : Type*} [Fintype Seed] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (S : Op n) (hS : S.IsHermitian)
    (H : QuantumHashFamily Seed X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n) :
    (1 / (Fintype.card Seed : ℝ)) *
      ∑ s : Seed, ∑ x : X, ∑ x' : X,
        (if H.hash s x = H.hash s x' then
          ((S * (ρ.stateMap x).toOp * S) *
            (S * (ρ.stateMap x').toOp * S)).trace.re
         else 0) ≤
      (∑ x : X,
          ((S * (ρ.stateMap x).toOp * S) *
            (S * (ρ.stateMap x).toOp * S)).trace.re) +
      (1 / (Fintype.card Z : ℝ)) *
        ((S * ρ.quantumMarginalOp * S) *
          (S * ρ.quantumMarginalOp * S)).trace.re := by
  let K : X → X → ℝ := fun x x' =>
    ((S * (ρ.stateMap x).toOp * S) *
      (S * (ρ.stateMap x').toOp * S)).trace.re
  let tau : X → X → ℝ := fun x x' =>
    (1 / (Fintype.card Seed : ℝ)) *
      ((Finset.univ.filter (fun s : Seed => H.hash s x = H.hash s x')).card : ℝ)
  let c : ℝ := 1 / (Fintype.card Z : ℝ)
  have hVar :
      (∑ x : X, ∑ x' : X, (tau x x' - c) * K x x') ≤
        ∑ x : X, K x x := by
    simpa [K, tau, c] using
      squared_sandwich_variance_pair_bound S hS H hH ρ
  have hSeedAvg :
      (1 / (Fintype.card Seed : ℝ)) *
        ∑ s : Seed, ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then K x x' else 0) =
      ∑ x : X, ∑ x' : X, tau x x' * K x x' := by
    simpa [tau] using seed_collision_sum_eq_filter_pair_sum H K
  have hMarg :
      (∑ x : X, ∑ x' : X, K x x') =
        ((S * ρ.quantumMarginalOp * S) *
          (S * ρ.quantumMarginalOp * S)).trace.re := by
    simpa [K] using squared_sandwich_pair_sum_eq_marginal S ρ
  have hPairBound :
      (∑ x : X, ∑ x' : X, tau x x' * K x x') ≤
        (∑ x : X, K x x) + c * (∑ x : X, ∑ x' : X, K x x') :=
    pair_sum_le_diag_add_c_pair_sum_of_variance tau K c hVar
  change
      (1 / (Fintype.card Seed : ℝ)) *
        ∑ s : Seed, ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then K x x' else 0) ≤
      (∑ x : X, K x x) +
        c * ((S * ρ.quantumMarginalOp * S) *
          (S * ρ.quantumMarginalOp * S)).trace.re
  rw [hSeedAvg, ← hMarg]
  exact hPairBound

end InfoTheory.QuantumLHL

end -- noncomputable section
