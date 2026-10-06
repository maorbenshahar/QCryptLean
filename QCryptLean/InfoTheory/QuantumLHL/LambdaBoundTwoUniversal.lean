import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.Quantum.Operators.InverseSqrt
import QCryptLean.Quantum.Operators.HermitianTraceSq

/-!
# 2-universality collision bound — Jensen, seed averaging, and off-diagonal PSD bounds

This helper module isolates the three analytic/combinatorial sub-steps that
constitute Tomamichel 2016 eq. 7.38–7.40 (the stochastic half of Prop 7.1).
The final gluing into the seed-averaged squared-domination inequality
(in `LambdaBound.lean`) is proved by linear arithmetic once the three
pieces are in hand.

## Main statements

- `sum_tr_SMzS_sq_le_seed_avg_collision_sum`: convexity of `A ↦ Tr(A²)` applied along
  the `(1/|S|)∑_s` factorization of `extractorWeightedOp`, combined with the per-seed
  collision expansion
  `∑_z Tr((∑_{x: h(s,x)=z} R_x)²) = ∑_{x,x': h(s,x)=h(s,x')} Tr(R_x R_{x'})`.
- `seed_avg_collision_sum_le_diag_plus_offdiag`: splits the collision sum into
  `x = x'` (diagonal) and `x ≠ x'` (off-diagonal) parts, bounding the off-diagonal
  collision count using the 2-universality property `H.isUniversal`.
- `sum_offdiag_tr_prod_sandwich_le_sq_marginal`: bounds the off-diagonal cross-term sum
  by the marginal square `Tr((S ρ_A S)²)` using `∑_x ρ.stateMap x = ρ.quantumMarginalOp`
  and the non-negativity of the diagonal `Tr((S ρ_x S)²) ≥ 0`.

## References

Tomamichel 2016, Prop 7.1, eq. 7.38–7.40.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- `∑ s, (if P s then c else 0) = |{s : P s}| * c` (ℝ-valued). -/
lemma Finset.sum_ite_const_eq_filter_card_mul_real
    {S : Type*} [Fintype S] (P : S → Prop) [DecidablePred P] (c : ℝ) :
    (∑ s : S, (if P s then c else 0)) =
      ((Finset.univ.filter P).card : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- A double sum over a finite type splits as its diagonal plus the
off-diagonal indicator sum:
`∑ x, ∑ x', f x x' = ∑ x, f x x + ∑ x, ∑ x', [x ≠ x'] f x x'`. -/
lemma Finset.sum_sum_eq_diag_add_offdiag
    {α β : Type*} [AddCommMonoid β] [DecidableEq α] [Fintype α] (f : α → α → β) :
    (∑ x : α, ∑ x' : α, f x x') =
      (∑ x : α, f x x) +
        (∑ x : α, ∑ x' : α, (if x ≠ x' then f x x' else 0)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdiag : f x x = ∑ x' : α, if x = x' then f x x' else 0 := by
    rw [Finset.sum_ite_eq Finset.univ x (fun x' => f x x'),
      if_pos (Finset.mem_univ x)]
  rw [hdiag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x' _ => ?_
  by_cases h : x = x' <;> simp [h]

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- Collapse of the double-condition indicator sum over `Z`:
`∑ z, [h(s,x)=z ∧ h(s,x')=z] · f = [h(s,x)=h(s,x')] · f`. -/
private lemma sum_z_collapse_double_iff
    {Z : Type*} [Fintype Z] [DecidableEq Z] {α : Type*} [AddCommMonoid α]
    (z1 z2 : Z) (f : α) :
    ∑ z : Z, (if z1 = z ∧ z2 = z then f else 0) =
      (if z1 = z2 then f else 0) := by
  by_cases h : z1 = z2
  · -- exactly one nonzero term at z = z1 = z2
    subst h
    rw [if_pos rfl]
    have : (∑ z : Z, (if z1 = z ∧ z1 = z then f else 0)) =
        ∑ z : Z, if z1 = z then f else 0 := by
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : z1 = z <;> simp [hz]
    rw [this, Finset.sum_ite_eq Finset.univ z1 (fun _ => f),
      if_pos (Finset.mem_univ z1)]
  · -- conjunction is never true
    rw [if_neg h]
    apply Finset.sum_eq_zero
    intro z _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (h1.trans h2.symm)

/-- **PSD sandwich trace positivity.**

If `T` is Hermitian and `A, B` are positive semidefinite, the real part of the
trace of `(TAT)(TBT)` is non-negative. Proof: `T A T` and `T B T` are PSD by
`Matrix.PosSemidef.conjTranspose_mul_mul_same`, and the cyclic trace identity
`trace(P Q) = trace(√P Q √P)` lets us apply `PosSemidef.trace_nonneg`. -/
lemma tr_prod_sandwich_re_nonneg
    {n : ℕ} {T A B : Op n} (hT : T.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((T * A * T) * (T * B * T)).trace.re := by
  have hT_cT : T.conjTranspose = T := hT.eq
  have hP_psd : (T * A * T).PosSemidef := by
    have heq : T * A * T = T.conjTranspose * A * T := by rw [hT_cT]
    rw [heq]
    exact hA.conjTranspose_mul_mul_same T
  have hQ_psd : (T * B * T).PosSemidef := by
    have heq : T * B * T = T.conjTranspose * B * T := by rw [hT_cT]
    rw [heq]
    exact hB.conjTranspose_mul_mul_same T
  set P : Op n := T * A * T
  set Q : Op n := T * B * T
  set R : Op n := CFC.sqrt P with hR_def
  have hR_psd : R.PosSemidef := (CFC.sqrt_nonneg (a := P)).posSemidef
  have hR_herm_eq : R.conjTranspose = R := hR_psd.isHermitian.eq
  have hRR_eq_P : R * R = P := CFC.sqrt_mul_sqrt_self P hP_psd.nonneg
  -- trace(P Q) = trace(R Q R) by cyclicity
  have hcyc : (P * Q).trace = (R * Q * R).trace := by
    rw [← hRR_eq_P, Matrix.mul_assoc, Matrix.trace_mul_comm]
  have hRQR_psd : (R * Q * R).PosSemidef := by
    have heq : R * Q * R = R.conjTranspose * Q * R := by rw [hR_herm_eq]
    rw [heq]
    exact hQ_psd.conjTranspose_mul_mul_same R
  have htr_nonneg : (0 : ℂ) ≤ (R * Q * R).trace := hRQR_psd.trace_nonneg
  rw [hcyc]
  exact (Complex.nonneg_iff.mp htr_nonneg).1

/-- **Jensen + per-seed collision expansion** — nonempty-seed version. -/
private lemma sum_tr_SMzS_sq_le_seed_avg_collision_sum_of_nonempty
    {S X Z : Type*} [Fintype S] [Nonempty S] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) {σ : Op n} (hσ : σ.PosDef) :
    (∑ z : Z,
        ((hσ.inverseSqrt * extractorWeightedOp H ρ z * hσ.inverseSqrt) *
          (hσ.inverseSqrt * extractorWeightedOp H ρ z * hσ.inverseSqrt)).trace.re) ≤
      (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then
            ((hσ.inverseSqrt * (ρ.stateMap x).toOp * hσ.inverseSqrt) *
              (hσ.inverseSqrt * (ρ.stateMap x').toOp * hσ.inverseSqrt)).trace.re
           else 0) := by
  -- Abbreviations.
  set T : Op n := hσ.inverseSqrt with hT_def
  -- `R x = T · ρ_x · T` is the σ-sandwich of each branch state.
  set R : X → Op n := fun x => T * (ρ.stateMap x).toOp * T with hR_def
  -- `E s z = ∑_{x : h(s,x)=z} ρ_x` (unnormalized per-seed block at output z).
  let E : S → Z → Op n := fun s z =>
    ∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0
  -- `A s z = T · E s z · T`.
  let A : S → Z → Op n := fun s z => T * E s z * T
  have hT_herm : T.IsHermitian := hσ.inverseSqrt_isHermitian
  have hρ_herm : ∀ x : X, ((ρ.stateMap x).toOp).IsHermitian := fun x =>
    (Quantum.Operators.posSemidefOp_implies_mathlib
      (ρ.stateMap x).toPosSemidefOp).isHermitian
  -- Hermiticity of `E s z`.
  have hE_herm : ∀ s z, (E s z).IsHermitian := by
    intros s z
    change (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0).IsHermitian
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : H.hash s x = z <;> simp [hx, (hρ_herm x).eq]
  -- Hermiticity of `A s z = T · E s z · T`.
  have hA_herm : ∀ s z, (A s z).IsHermitian := by
    intros s z
    change (T * E s z * T).IsHermitian
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hT_herm.eq,
      (hE_herm s z).eq, Matrix.mul_assoc]
  -- Sandwich linearity: T * M_z * T = (1/|S|) • ∑ s, A s z.
  have hSand : ∀ z : Z,
      T * extractorWeightedOp H ρ z * T =
        (1 / (Fintype.card S : ℝ)) • ∑ s, A s z := by
    intro z
    unfold extractorWeightedOp
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
  -- Rewrite LHS using hSand.
  have hLHS_rewrite :
      (∑ z : Z,
          ((T * extractorWeightedOp H ρ z * T) *
            (T * extractorWeightedOp H ρ z * T)).trace.re) =
      ∑ z : Z,
          (((1 / (Fintype.card S : ℝ)) • ∑ s, A s z) *
            ((1 / (Fintype.card S : ℝ)) • ∑ s, A s z)).trace.re := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hSand z]
  rw [hLHS_rewrite]
  -- Per-z Jensen bound.
  have hPerZ : ∀ z : Z,
      (((1 / (Fintype.card S : ℝ)) • ∑ s, A s z) *
          ((1 / (Fintype.card S : ℝ)) • ∑ s, A s z)).trace.re ≤
        (1 / (Fintype.card S : ℝ)) * ∑ s, (A s z * A s z).trace.re := fun z =>
    Quantum.Operators.tr_smul_avg_sq_re_le_avg_tr_sq_re (A · z) (fun s => hA_herm s z)
  have hSumZ :
      ∑ z : Z,
          (((1 / (Fintype.card S : ℝ)) • ∑ s, A s z) *
            ((1 / (Fintype.card S : ℝ)) • ∑ s, A s z)).trace.re ≤
        ∑ z : Z,
          (1 / (Fintype.card S : ℝ)) * ∑ s, (A s z * A s z).trace.re :=
    Finset.sum_le_sum fun z _ => hPerZ z
  refine hSumZ.trans ?_
  -- Now reorganize: ∑_z (1/|S|) * ∑_s = (1/|S|) * ∑_s ∑_z.
  rw [← Finset.mul_sum, Finset.sum_comm]
  -- Rewrite each `A s z` as a sum of σ-sandwiched branches `R x` indexed by
  -- those `x` hashing to `z`.
  have hA_eq : ∀ s z, A s z = ∑ x : X, if H.hash s x = z then R x else 0 := by
    intros s z
    change T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) * T = _
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : H.hash s x = z <;> simp [hx, hR_def]
  -- Per-(s,z) expansion of Tr((A s z)²).re.
  have hExpand : ∀ s z,
      (A s z * A s z).trace.re =
        ∑ x : X, ∑ x' : X,
          (if H.hash s x = z ∧ H.hash s x' = z then
            ((R x) * (R x')).trace.re
           else 0) := by
    intros s z
    rw [hA_eq s z]
    -- (∑ x, f x) * (∑ x', g x') = ∑ x, ∑ x', f x * g x'
    rw [Finset.sum_mul_sum]
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    -- (if p then R x else 0) * (if q then R x' else 0) = if p ∧ q then R x * R x' else 0
    by_cases hx : H.hash s x = z <;> by_cases hx' : H.hash s x' = z <;>
      simp [hx, hx']
  -- Goal: (1/N) * ∑_s ∑_z Tr((A s z)²).re
  --     ≤ (1/N) * ∑_s ∑_x ∑_x' [h(s,x)=h(s,x')] Tr(R_x R_{x'}).re.
  -- (Note: `T * (ρ.stateMap x).toOp * T = R x` definitionally.)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum fun s _ => ?_
  -- Per-s: ∑_z Tr((A s z)²).re = ∑_x ∑_x' [h(s,x)=h(s,x')] Tr(R_x R_{x'}).re.
  have hSwap :
      ∑ z : Z, (A s z * A s z).trace.re =
        ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then
            ((R x) * (R x')).trace.re else 0) := by
    simp_rw [hExpand s]
    -- ∑_z ∑_x ∑_x' (if ∧ then f else 0) = ∑_x ∑_x' ∑_z (if ∧ then f else 0)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    exact sum_z_collapse_double_iff _ _ _
  exact le_of_eq hSwap

/-- **Jensen + per-seed collision expansion.**

Convexity of `A ↦ Tr(A²)` on Hermitian operators (= squared Hilbert–Schmidt
norm) combined with the `(1/|S|) ∑_s` factorization of
`extractorWeightedOp H ρ z` and the expansion
`(∑_{x: h(s,x)=z} R_x)² = ∑_{x,x': h(s,x)=h(s,x')=z} R_x R_{x'}` yields

  `∑_z Tr((S · E_z · S)²) ≤ (1/|S|) ∑_s ∑_{x,x'} [h(s,x)=h(s,x')] · Tr((S ρ_x S)(S ρ_{x'} S))`.

The inner indicator is the `ite` form used in Lean. -/
lemma sum_tr_SMzS_sq_le_seed_avg_collision_sum
    {S X Z : Type*} [Fintype S] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) {σ : Op n} (hσ : σ.PosDef) :
    (∑ z : Z,
        ((hσ.inverseSqrt * extractorWeightedOp H ρ z * hσ.inverseSqrt) *
          (hσ.inverseSqrt * extractorWeightedOp H ρ z * hσ.inverseSqrt)).trace.re) ≤
      (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then
            ((hσ.inverseSqrt * (ρ.stateMap x).toOp * hσ.inverseSqrt) *
              (hσ.inverseSqrt * (ρ.stateMap x').toOp * hσ.inverseSqrt)).trace.re
           else 0) := by
  -- Case-split on emptiness of S; both sides collapse to 0 when S is empty.
  by_cases hS : Nonempty S
  · haveI := hS
    exact sum_tr_SMzS_sq_le_seed_avg_collision_sum_of_nonempty H ρ hσ
  · rw [not_nonempty_iff] at hS
    haveI := hS
    have hMz : ∀ z : Z, extractorWeightedOp H ρ z = 0 := by
      intro z
      unfold extractorWeightedOp
      have : (∑ s : S, ∑ x : X,
          if H.hash s x = z then (ρ.stateMap x).toOp else 0) = 0 := by
        rw [Finset.univ_eq_empty (α := S)]
        simp
      rw [this, smul_zero]
    simp [hMz]

/-- **2-universality split of the seed-averaged collision sum.**

Split the collision sum by `x = x'` vs `x ≠ x'`. The diagonal contribution
`(1/|S|) ∑_s ∑_x 1 · Tr((S ρ_x S)²) = ∑_x Tr((S ρ_x S)²)` is seed-independent.
The off-diagonal contribution satisfies, for each pair `x ≠ x'`,

  `(1/|S|) · #{s : H.hash s x = H.hash s x'} ≤ 1/|Z|`  (Tomamichel eq. 7.31).

Since each `Tr((S ρ_x S)(S ρ_{x'} S)) ≥ 0` (trace of a product of PSDs), we get:

  `(1/|S|) ∑_s ∑_{x,x'} [h(s,x)=h(s,x')] · Tr(...) ≤
     ∑_x Tr((S ρ_x S)²) + (1/|Z|) ∑_{x≠x'} Tr((S ρ_x S)(S ρ_{x'} S))`. -/
lemma seed_avg_collision_sum_le_diag_plus_offdiag
    {S X Z : Type*} [Fintype S] [Fintype X] [DecidableEq X]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S X Z) (hH : H.isUniversal)
    (ρ : CQState X n) {σ : Op n} (hσ : σ.PosDef) :
    (1 / (Fintype.card S : ℝ)) *
      ∑ s : S, ∑ x : X, ∑ x' : X,
        (if H.hash s x = H.hash s x' then
          ((hσ.inverseSqrt * (ρ.stateMap x).toOp * hσ.inverseSqrt) *
            (hσ.inverseSqrt * (ρ.stateMap x').toOp * hσ.inverseSqrt)).trace.re
         else 0) ≤
      (∑ x : X,
          ((hσ.inverseSqrt * (ρ.stateMap x).toOp * hσ.inverseSqrt) *
            (hσ.inverseSqrt * (ρ.stateMap x).toOp * hσ.inverseSqrt)).trace.re) +
      (1 / (Fintype.card Z : ℝ)) *
        ∑ x : X, ∑ x' : X,
          (if x ≠ x' then
            ((hσ.inverseSqrt * (ρ.stateMap x).toOp * hσ.inverseSqrt) *
              (hσ.inverseSqrt * (ρ.stateMap x').toOp * hσ.inverseSqrt)).trace.re
           else 0) := by
  -- Abbreviations
  set T : Op n := hσ.inverseSqrt with hT_def
  set M : X → X → ℝ := fun x x' =>
    ((T * (ρ.stateMap x).toOp * T) * (T * (ρ.stateMap x').toOp * T)).trace.re
    with hM_def
  set cardf : X → X → ℝ := fun x x' =>
    ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
    with hcardf_def
  have hT_herm : T.IsHermitian := hσ.inverseSqrt_isHermitian
  have hρ_psd : ∀ x : X, ((ρ.stateMap x).toOp).PosSemidef := fun x =>
    Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  have hM_nonneg : ∀ x x' : X, 0 ≤ M x x' := fun x x' =>
    tr_prod_sandwich_re_nonneg hT_herm (hρ_psd x) (hρ_psd x')
  -- Positive cardinalities.
  haveI := H.seedNonempty
  haveI := H.outputNonempty
  have hS_pos : (0 : ℝ) < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have hZ_pos : (0 : ℝ) < (Fintype.card Z : ℝ) := by exact_mod_cast Fintype.card_pos
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  -- Restate the goal using the M abbreviation (definitional equality).
  change (1 / (Fintype.card S : ℝ)) *
      (∑ s : S, ∑ x : X, ∑ x' : X,
        (if H.hash s x = H.hash s x' then M x x' else 0)) ≤
      (∑ x : X, M x x) +
        (1 / (Fintype.card Z : ℝ)) *
          ∑ x : X, ∑ x' : X, (if x ≠ x' then M x x' else 0)
  -- Step 1: Swap ∑_s to innermost and collapse via filter-card identity.
  have hSwap :
      (∑ s : S, ∑ x : X, ∑ x' : X,
        (if H.hash s x = H.hash s x' then M x x' else 0)) =
        ∑ x : X, ∑ x' : X, cardf x x' * M x x' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    exact Finset.sum_ite_const_eq_filter_card_mul_real _ _
  rw [hSwap]
  -- Step 2: diagonal/off-diagonal split of the double sum.
  rw [Finset.sum_sum_eq_diag_add_offdiag (fun x x' => cardf x x' * M x x')]
  -- Step 3: Diagonal simplification — cardf x x = |S|.
  have hDiag_eq : ∀ x : X, cardf x x = (Fintype.card S : ℝ) := by
    intro x
    have hfilter :
        Finset.univ.filter (fun s : S => H.hash s x = H.hash s x) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intros s _; rfl
    change ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x)).card : ℝ) =
        (Fintype.card S : ℝ)
    rw [hfilter]; rfl
  have hDiagSum :
      (∑ x : X, cardf x x * M x x) =
        (Fintype.card S : ℝ) * ∑ x : X, M x x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [hDiag_eq]
  rw [hDiagSum]
  -- Step 4: Distribute (1/|S|) and cancel with |S|.
  rw [mul_add, ← mul_assoc, one_div_mul_cancel hS_ne, one_mul]
  -- Step 5: Bound the off-diagonal scaled sum pointwise.
  refine add_le_add (le_refl _) ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x' _
  by_cases hxx' : x ≠ x'
  · rw [if_pos hxx', if_pos hxx']
    -- Goal: (1/|S|) * (cardf x x' * M x x') ≤ (1/|Z|) * M x x'.
    have hU := hH x x' hxx'
    have hM := hM_nonneg x x'
    have h1 : (1 / (Fintype.card S : ℝ)) * (cardf x x' * M x x') =
        (cardf x x' / (Fintype.card S : ℝ)) * M x x' := by ring
    rw [h1]
    have h2 : cardf x x' / (Fintype.card S : ℝ) ≤ 1 / (Fintype.card Z : ℝ) := by
      rw [div_le_div_iff₀ hS_pos hZ_pos, one_mul, mul_comm]
      calc (Fintype.card Z : ℝ) * cardf x x'
          ≤ (Fintype.card Z : ℝ) *
              ((Fintype.card S : ℝ) / (Fintype.card Z : ℝ)) :=
            mul_le_mul_of_nonneg_left hU hZ_pos.le
        _ = (Fintype.card S : ℝ) := by
            field_simp
    exact mul_le_mul_of_nonneg_right h2 hM
  · rw [if_neg hxx', if_neg hxx']
    simp

/-- **Off-diagonal pair sum bounded by marginal square.**

Since the full pair sum `∑_{x,x'} Tr((Sρ_x S)(Sρ_{x'} S)) = Tr((Sρ_A S)²)` (by
bilinearity of the trace-product and `∑_x ρ_x = ρ_A = quantumMarginalOp`), and
the diagonal contributions `Tr((Sρ_x S)²) ≥ 0` (trace of squared PSD), dropping
the diagonal yields

  `∑_{x≠x'} Tr((Sρ_x S)(Sρ_{x'} S)) ≤ Tr((S ρ_A S)²)`. -/
lemma sum_offdiag_tr_prod_sandwich_le_sq_marginal
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) {σ : Op n} (hσ : σ.PosDef) :
    (∑ x : X, ∑ x' : X,
        (if x ≠ x' then
          ((hσ.inverseSqrt * (ρ.stateMap x).toOp * hσ.inverseSqrt) *
            (hσ.inverseSqrt * (ρ.stateMap x').toOp * hσ.inverseSqrt)).trace.re
         else 0)) ≤
      ((hσ.inverseSqrt * ρ.quantumMarginalOp * hσ.inverseSqrt) *
          (hσ.inverseSqrt * ρ.quantumMarginalOp * hσ.inverseSqrt)).trace.re := by
  -- Abbreviations
  set S : Op n := hσ.inverseSqrt with hS_def
  let R : X → Op n := fun x => S * (ρ.stateMap x).toOp * S
  -- Sum identity: ∑_x R x = S * ρ_A * S
  have hSumR : ∑ x : X, R x = S * ρ.quantumMarginalOp * S := by
    change ∑ x : X, S * (ρ.stateMap x).toOp * S = S * ρ.quantumMarginalOp * S
    rw [CQState.quantumMarginalOp, ← Finset.sum_mul, ← Finset.mul_sum]
  -- Full pair-product-trace
  have hFull :
      (∑ x : X, ∑ x' : X, ((R x) * (R x')).trace.re) =
        ((S * ρ.quantumMarginalOp * S) * (S * ρ.quantumMarginalOp * S)).trace.re := by
    rw [← hSumR, Finset.sum_mul_sum]
    simp_rw [Matrix.trace_sum, Complex.re_sum]
  -- Each R x is PSD
  have hR_psd : ∀ x : X, (R x).PosSemidef := by
    intro x
    have hS_herm : S.conjTranspose = S := hσ.inverseSqrt_isHermitian.eq
    change (S * (ρ.stateMap x).toOp * S).PosSemidef
    have hρx_psd : ((ρ.stateMap x).toOp).PosSemidef :=
      Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
    have key : S * (ρ.stateMap x).toOp * S =
        S.conjTranspose * (ρ.stateMap x).toOp * S := by rw [hS_herm]
    rw [key]
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same hρx_psd S
  -- Each diagonal term is nonneg
  have hDiag_nonneg : ∀ x : X, 0 ≤ (R x * R x).trace.re := by
    intro x
    have hRx := hR_psd x
    have hRx_herm : (R x).conjTranspose = R x := hRx.isHermitian.eq
    have hRR : ((R x) * (R x)).PosSemidef := by
      have h1 := Matrix.posSemidef_conjTranspose_mul_self (R x)
      rwa [hRx_herm] at h1
    have htr : 0 ≤ (R x * R x).trace := hRR.trace_nonneg
    exact (Complex.nonneg_iff.mp htr).1
  -- Full = diagonal + off-diagonal
  have hSplit :
      (∑ x : X, ∑ x' : X, ((R x) * (R x')).trace.re) =
        (∑ x : X, ((R x) * (R x)).trace.re) +
        (∑ x : X, ∑ x' : X, (if x ≠ x' then ((R x) * (R x')).trace.re else 0)) :=
    Finset.sum_sum_eq_diag_add_offdiag (fun x x' => ((R x) * (R x')).trace.re)
  have hDiagSum_nonneg : 0 ≤ ∑ x : X, ((R x) * (R x)).trace.re :=
    Finset.sum_nonneg fun x _ => hDiag_nonneg x
  -- Combine
  have hTarget :
      (∑ x : X, ∑ x' : X,
        (if x ≠ x' then
          ((S * (ρ.stateMap x).toOp * S) *
            (S * (ρ.stateMap x').toOp * S)).trace.re
         else 0)) =
      (∑ x : X, ∑ x' : X, (if x ≠ x' then ((R x) * (R x')).trace.re else 0)) := rfl
  rw [hTarget]
  linarith

end InfoTheory.QuantumLHL

end -- noncomputable section
