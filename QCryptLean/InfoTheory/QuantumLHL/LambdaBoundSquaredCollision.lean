import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundSquaredCollisionAlgebra

/-!
# Squared-sandwich collision helpers

This module keeps the low-level squared-sandwich Jensen and seed-collision
algebra out of `LambdaBoundCore.lean`.  The high-level λ\*-bound assembly imports
these helpers and performs only the centering/cancellation step locally.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- **Jensen + per-seed collision expansion for the squared sandwich kernel.**

For any Hermitian sandwich operator `S`, convexity of `A ↦ Tr(A²)` applied to
`S · extractorWeightedOp H ρ z · S` gives the seed-averaged collision form with
kernel `((S·ρ_x·S)·(S·ρ_x'·S)).trace.re`. -/
lemma sum_tr_SMzSsq_le_seed_avg_collision_sum
    {Seed X Z : Type*} [Fintype Seed] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (S : Op n) (hS : S.IsHermitian)
    (H : QuantumHashFamily Seed X Z)
    (ρ : CQState X n) :
    (∑ z : Z,
        ((S * extractorWeightedOp H ρ z * S) *
          (S * extractorWeightedOp H ρ z * S)).trace.re) ≤
      (1 / (Fintype.card Seed : ℝ)) *
        ∑ s : Seed, ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then
            ((S * (ρ.stateMap x).toOp * S) *
              (S * (ρ.stateMap x').toOp * S)).trace.re
           else 0) := by
  by_cases hSeed : Nonempty Seed
  · have := hSeed
    let E : Seed → Z → Op n := fun s z =>
      ∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0
    let A : Seed → Z → Op n := fun s z => S * E s z * S
    let R : X → Op n := fun x => S * (ρ.stateMap x).toOp * S
    have hρ_herm : ∀ x : X, ((ρ.stateMap x).toOp).IsHermitian := fun x =>
      (Quantum.Operators.posSemidefOp_implies_mathlib
        (ρ.stateMap x).toPosSemidefOp).isHermitian
    have hE_herm : ∀ s z, (E s z).IsHermitian := by
      intros s z
      change (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0).IsHermitian
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : H.hash s x = z <;> simp [hx, (hρ_herm x).eq]
    have hA_herm : ∀ s z, (A s z).IsHermitian := by
      intros s z
      change (S * E s z * S).IsHermitian
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq,
        (hE_herm s z).eq, Matrix.mul_assoc]
    have hSand : ∀ z : Z,
        S * extractorWeightedOp H ρ z * S =
          (1 / (Fintype.card Seed : ℝ)) • ∑ s, A s z := by
      intro z
      unfold extractorWeightedOp
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
    have hLHS_rewrite :
        (∑ z : Z,
            ((S * extractorWeightedOp H ρ z * S) *
              (S * extractorWeightedOp H ρ z * S)).trace.re) =
        ∑ z : Z,
            (((1 / (Fintype.card Seed : ℝ)) • ∑ s, A s z) *
              ((1 / (Fintype.card Seed : ℝ)) • ∑ s, A s z)).trace.re := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [hSand z]
    rw [hLHS_rewrite]
    have hPerZ : ∀ z : Z,
        (((1 / (Fintype.card Seed : ℝ)) • ∑ s, A s z) *
            ((1 / (Fintype.card Seed : ℝ)) • ∑ s, A s z)).trace.re ≤
          (1 / (Fintype.card Seed : ℝ)) *
            ∑ s, (A s z * A s z).trace.re := fun z =>
      Quantum.Operators.tr_smul_avg_sq_re_le_avg_tr_sq_re (A · z) (fun s => hA_herm s z)
    have hSumZ :
        ∑ z : Z,
            (((1 / (Fintype.card Seed : ℝ)) • ∑ s, A s z) *
              ((1 / (Fintype.card Seed : ℝ)) • ∑ s, A s z)).trace.re ≤
          ∑ z : Z,
            (1 / (Fintype.card Seed : ℝ)) *
              ∑ s, (A s z * A s z).trace.re :=
      Finset.sum_le_sum fun z _ => hPerZ z
    refine hSumZ.trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hA_eq : ∀ s z, A s z = ∑ x : X, if H.hash s x = z then R x else 0 := by
      intros s z
      change S * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) * S = _
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : H.hash s x = z <;> simp [hx, R]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum fun s _ => ?_
    have hCollision := per_seed_collision_identity_single (1 : Op n) R (H.hash s)
    exact le_of_eq (by
      simpa [Matrix.one_mul, Matrix.mul_one, hA_eq s, R] using hCollision)
  · rw [not_nonempty_iff] at hSeed
    have := hSeed
    have hMz : ∀ z : Z, extractorWeightedOp H ρ z = 0 := by
      intro z
      unfold extractorWeightedOp
      have : (∑ s : Seed, ∑ x : X,
          if H.hash s x = z then (ρ.stateMap x).toOp else 0) = 0 := by
        rw [Finset.univ_eq_empty (α := Seed)]
        simp
      rw [this, smul_zero]
    simp [hMz]

end InfoTheory.QuantumLHL

end -- noncomputable section
