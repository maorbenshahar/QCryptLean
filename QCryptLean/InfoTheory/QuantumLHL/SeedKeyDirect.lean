import QCryptLean.InfoTheory.QuantumLHL.SeedKeyContractivity
import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundCore
import QCryptLean.InfoTheory.QuantumLHL.SmoothingSideConditions

/-!
# Direct seed-visible quantum leftover hashing

Centering and collision estimates bound the public-seed extractor by a feasible coefficient or
a fixed-reference min-entropy floor. The output factor is `|Z|`, independent of the public seed
alphabet. Zero floors use a blockwise triangle estimate valid for every hash family.
-/

open Quantum.Operators Quantum.Metrics Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

private lemma seed_uniform_scalar_eq
    {S Z : Type*} [Fintype S] [Fintype Z] [Nonempty S] [Nonempty Z] :
    (((1 / (Fintype.card (S × Z) : ℝ) : ℝ) : ℂ)) =
      (((1 / (Fintype.card S : ℝ) : ℝ) : ℂ)) *
        (((1 / (Fintype.card Z : ℝ) : ℝ) : ℂ)) := by
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := S)
  have hZ_ne : (Fintype.card Z : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Z)
  have hcard :
      (Fintype.card (S × Z) : ℝ) =
        (Fintype.card S : ℝ) * (Fintype.card Z : ℝ) := by
    exact_mod_cast Fintype.card_prod S Z
  have hR :
      (1 / (Fintype.card (S × Z) : ℝ) : ℝ) =
        (1 / (Fintype.card S : ℝ)) * (1 / (Fintype.card Z : ℝ)) := by
    rw [hcard]
    field_simp [hS_ne, hZ_ne]
  exact_mod_cast hR

private lemma sum_unscaled_seed_blocks_eq_quantumMarginalOp
    {S X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (H : QuantumHashFamily S X Z) (ρ : CQState X n) (s : S) :
    ∑ z : Z, (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) =
      ρ.quantumMarginalOp := by
  unfold CQState.quantumMarginalOp
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have := Finset.sum_ite_eq (Finset.univ : Finset Z) (H.hash s x)
    (fun _ => (ρ.stateMap x).toOp)
  rw [this]
  simp

/-- Centering identity for one fixed public seed. -/
private lemma seed_visible_centering_per_seed
    {S X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (T : Op n) (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) (s : S) :
    ∑ z : Z,
        ((T *
            ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            T) *
          (T *
            ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            T)).trace.re =
      (∑ z : Z,
        ((T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) * T) *
          (T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) *
            T)).trace.re) -
        ((1 : ℝ) / (Fintype.card Z : ℝ)) *
          ((T * ρ.quantumMarginalOp * T) *
            (T * ρ.quantumMarginalOp * T)).trace.re := by
  exact sum_tr_SMzSsq_centering T ρ.quantumMarginalOp
    (fun z : Z => ∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0)
    (sum_unscaled_seed_blocks_eq_quantumMarginalOp H ρ s)

/-- Averaging the per-seed centering identity over public seeds. -/
lemma seed_visible_avg_centering_eq
    {S X Z : Type*} [Fintype S] [Nonempty S] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (T : Op n) (H : QuantumHashFamily S X Z) (ρ : CQState X n) :
    (1 / (Fintype.card S : ℝ)) *
      ∑ s : S, ∑ z : Z,
        ((T *
            ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            T) *
          (T *
            ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            T)).trace.re =
      (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ z : Z,
          ((T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) * T) *
            (T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) *
              T)).trace.re -
        ((1 : ℝ) / (Fintype.card Z : ℝ)) *
          ((T * ρ.quantumMarginalOp * T) *
            (T * ρ.quantumMarginalOp * T)).trace.re := by
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- Averaging a per-seed identity `f s = g s - a` over the seeds keeps the constant `a`.
  have avg : ∀ (f g : S → ℝ) (a : ℝ), (∀ s, f s = g s - a) →
      (1 / (Fintype.card S : ℝ)) * ∑ s, f s = (1 / (Fintype.card S : ℝ)) * ∑ s, g s - a := by
    intro f g a h
    rw [Finset.sum_congr rfl (fun s _ => h s), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_sub, ← mul_assoc, one_div_mul_cancel hS_ne, one_mul]
  exact avg _ _ _ (seed_visible_centering_per_seed T H ρ)

/-- Expanding the seed-visible uncentered collision sum into seed-conditioned
hash collisions. -/
lemma seed_visible_uncentered_collision_sum_eq_pair_sum
    {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (T : Op n) (H : QuantumHashFamily S X Z) (ρ : CQState X n) :
    (1 / (Fintype.card S : ℝ)) *
      ∑ s : S, ∑ z : Z,
        ((T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) * T) *
          (T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) *
            T)).trace.re =
      (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then
            ((T * (ρ.stateMap x).toOp * T) *
              (T * (ρ.stateMap x').toOp * T)).trace.re
           else 0) := by
  classical
  let R : X → Op n := fun x => T * (ρ.stateMap x).toOp * T
  congr 1
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have hper :=
    per_seed_collision_identity_single (1 : Op n) R (H.hash s)
  have hE_sand : ∀ z : Z,
      T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) * T =
        ∑ x : X, if H.hash s x = z then R x else 0 := by
    intro z
    dsimp [R]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : H.hash s x = z <;> simp [hx]
  simpa [R, Matrix.one_mul, Matrix.mul_one, hE_sand] using hper

/-- Seed-averaged squared centered collision bound for public seeds. -/
lemma seed_visible_sum_tr_centered_sq_le_sum_tr_SrhoxSsq
    {S X Z : Type*} [Fintype S] [Nonempty S] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (T : Op n) (hT : T.IsHermitian)
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n) :
    (1 / (Fintype.card S : ℝ)) *
      ∑ s : S, ∑ z : Z,
        ((T *
            ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            T) *
          (T *
            ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
              (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
            T)).trace.re ≤
    ∑ x : X,
        ((T * (ρ.stateMap x).toOp * T) *
          (T * (ρ.stateMap x).toOp * T)).trace.re := by
  classical
  let c : ℝ := (1 : ℝ) / (Fintype.card Z : ℝ)
  let KR : ℝ :=
    ((T * ρ.quantumMarginalOp * T) *
      (T * ρ.quantumMarginalOp * T)).trace.re
  have hAvgCenter := seed_visible_avg_centering_eq T H ρ
  have hCollisionLe :
      (1 / (Fintype.card S : ℝ)) *
          ∑ s : S, ∑ z : Z,
            ((T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) * T) *
              (T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) *
                T)).trace.re ≤
        (∑ x : X,
          ((T * (ρ.stateMap x).toOp * T) *
            (T * (ρ.stateMap x).toOp * T)).trace.re) +
          c * KR := by
    rw [seed_visible_uncentered_collision_sum_eq_pair_sum T H ρ]
    exact InfoTheory.QuantumLHL.seed_avg_collision_sum_sq_le_diag_plus_c_marginalSq_algebra
      T hT H hH ρ
  calc
    (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ z : Z,
          ((T *
              ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
                (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
              T) *
            (T *
              ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
                (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
              T)).trace.re
      = (1 / (Fintype.card S : ℝ)) *
          ∑ s : S, ∑ z : Z,
            ((T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) * T) *
              (T * (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) *
                T)).trace.re - c * KR := hAvgCenter
    _ ≤ ∑ x : X,
          ((T * (ρ.stateMap x).toOp * T) *
            (T * (ρ.stateMap x).toOp * T)).trace.re := sub_le_iff_le_add.mpr hCollisionLe

/-- Hermitianness of the unweighted seed-output block centered by the
output-uniform marginal. -/
lemma seed_unscaled_block_sub_uniform_isHermitian
    {S X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} (H : QuantumHashFamily S X Z) (ρ : CQState X n) (s : S) (z : Z) :
    ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
        (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp).IsHermitian := by
  have hE :
      (∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : H.hash s x = z
    · simp only [hx, ↓reduceIte]
      exact (ρ.stateMap x).isHermitian
    · simp only [hx, ↓reduceIte, Matrix.conjTranspose_zero]
  have hsa : IsSelfAdjoint ((((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ)) :=
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp)
  have hU :
      ((((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) •
        ρ.quantumMarginalOp).IsHermitian := by
    change (((((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) •
      ρ.quantumMarginalOp).conjTranspose =
        (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp)
    rw [Matrix.conjTranspose_smul, hsa, ρ.quantumMarginalOp_isHermitian]
  exact Matrix.IsHermitian.sub hE hU

/-- The seed-visible block difference is the seed weight times the unweighted
centered seed-output block. -/
lemma seed_visible_stateMap_sub_uniform_toOp_eq
    {S X Z : Type*} [Fintype S] [Nonempty S] [Fintype X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} (H : QuantumHashFamily S X Z) (ρ : CQState X n) (sz : S × Z) :
    ((seedKeyExtractorOutputState H ρ).stateMap sz).toOp -
        ((seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).stateMap sz).toOp =
      (1 / (Fintype.card S : ℝ)) •
        ((∑ x : X, if H.hash sz.1 x = sz.2 then (ρ.stateMap x).toOp else 0) -
          (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) := by
  change seedPerSeedWeightedOp H ρ sz.1 sz.2 -
      ((seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).stateMap sz).toOp =
    (1 / (Fintype.card S : ℝ)) •
      ((∑ x : X, if H.hash sz.1 x = sz.2 then (ρ.stateMap x).toOp else 0) -
        (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp)
  unfold seedPerSeedWeightedOp
  have hUblock :
      ((seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).stateMap sz).toOp =
        (((1 / (Fintype.card (S × Z) : ℝ) : ℝ) : ℂ)) • ρ.quantumMarginalOp := by
    change ((uniformCQState (X := S × Z) ρ.quantumMarginal :
      CQState (S × Z) n).stateMap sz).toOp =
        (((1 / (Fintype.card (S × Z) : ℝ) : ℝ) : ℂ)) • ρ.quantumMarginalOp
    exact uniformOutput_stateMap_toOp (Z := S × Z) ρ.quantumMarginal sz
  rw [hUblock, smul_sub]
  congr 1
  have hsc := seed_uniform_scalar_eq (S := S) (Z := Z)
  ext i j
  rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply]
  simp only [Complex.real_smul, smul_eq_mul]
  rw [hsc]
  ring_nf
  rw [Complex.ofReal_inv]
  rw [Complex.ofReal_inv]
  ring_nf
  norm_num

/-- Cauchy-Schwarz for a seed average over a seed-output product register. -/
lemma sq_seed_average_sum_le_card_output_mul_seed_average_sum_sq
    {S Z : Type*} [Fintype S] [Nonempty S] [Fintype Z] (a : S × Z → ℝ) :
    ((1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, a sz) ^ 2 ≤
      (Fintype.card Z : ℝ) *
        ((1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, (a sz) ^ 2) := by
  have hS_pos : (0 : ℝ) < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (S × Z))) (f := a)
  have hcard :
      (Fintype.card (S × Z) : ℝ) =
        (Fintype.card S : ℝ) * (Fintype.card Z : ℝ) := by
    exact_mod_cast Fintype.card_prod S Z
  rw [Finset.card_univ] at hcs
  rw [hcard] at hcs
  field_simp [hS_ne]
  nlinarith [hcs, hS_pos]

/-- The seed average of squared centered block trace norms is bounded by
`minFeasibleLambda`. -/
lemma seed_visible_average_traceNorm_sq_le_minFeasibleLambda
    {S X Z : Type*} [Fintype S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (hfeas : hasFeasibleLambda ρ σ) :
    (1 / (Fintype.card S : ℝ)) *
      ∑ sz : S × Z,
        (Quantum.Metrics.traceNorm
          ((∑ x : X, if H.hash sz.1 x = sz.2 then (ρ.stateMap x).toOp else 0) -
            (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp)) ^ 2 ≤
      minFeasibleLambda ρ σ := by
  set lam := minFeasibleLambda ρ σ
  have hlam_nn : 0 ≤ lam := minFeasibleLambda_nonneg ρ σ
  have hσtr_nn : (0 : ℝ) ≤ σ.toOp.trace.re := σ.trace_nonneg
  have hσtr_le : σ.toOp.trace.re ≤ 1 := σ.trace_le_one
  let D : S × Z → Op n := fun sz =>
    (∑ x : X, if H.hash sz.1 x = sz.2 then (ρ.stateMap x).toOp else 0) -
      (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp
  let a : S × Z → ℝ := fun sz => Quantum.Metrics.traceNorm (D sz)
  have h_herm : ∀ sz : S × Z, (D sz).IsHermitian := by
    intro sz
    dsimp [D]
    exact seed_unscaled_block_sub_uniform_isHermitian H ρ sz.1 sz.2
  have h_alpha : ∀ sz : S × Z, (a sz) ^ 2 ≤
      σ.toOp.trace.re *
        ((hσ_pd.inverseFourthRoot * D sz * hσ_pd.inverseFourthRoot) *
          (hσ_pd.inverseFourthRoot * D sz * hσ_pd.inverseFourthRoot)).trace.re :=
    fun sz => traceNorm_sq_le_trsig_squared hσ_pd (h_herm sz)
  have h_center :=
    seed_visible_sum_tr_centered_sq_le_sum_tr_SrhoxSsq
      hσ_pd.inverseFourthRoot hσ_pd.inverseFourthRoot_isHermitian H hH ρ
  have h_epsilon := sum_tr_SrhoxSsq_le_lambda_subNorm ρ σ hσ_pd hfeas
  have h_sum_sq_le_lam :
      (1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, (a sz) ^ 2 ≤ lam := by
    calc
      (1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, (a sz) ^ 2
          ≤ (1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z,
              σ.toOp.trace.re *
                ((hσ_pd.inverseFourthRoot * D sz * hσ_pd.inverseFourthRoot) *
                  (hσ_pd.inverseFourthRoot * D sz * hσ_pd.inverseFourthRoot)).trace.re := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum (fun sz _ => h_alpha sz)) (by positivity)
      _ = σ.toOp.trace.re *
            ((1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z,
                ((hσ_pd.inverseFourthRoot * D sz * hσ_pd.inverseFourthRoot) *
                  (hσ_pd.inverseFourthRoot * D sz * hσ_pd.inverseFourthRoot)).trace.re) := by
            rw [← Finset.mul_sum]
            ring
      _ = σ.toOp.trace.re *
            ((1 / (Fintype.card S : ℝ)) * ∑ s : S, ∑ z : Z,
                ((hσ_pd.inverseFourthRoot *
                    ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
                      (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
                    hσ_pd.inverseFourthRoot) *
                  (hσ_pd.inverseFourthRoot *
                    ((∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0) -
                      (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp) *
                    hσ_pd.inverseFourthRoot)).trace.re) := by
            congr 1
            congr 1
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ ≤ σ.toOp.trace.re *
            ∑ x : X,
              ((hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp *
                  hσ_pd.inverseFourthRoot) *
                (hσ_pd.inverseFourthRoot * (ρ.stateMap x).toOp *
                  hσ_pd.inverseFourthRoot)).trace.re :=
            mul_le_mul_of_nonneg_left h_center hσtr_nn
      _ ≤ σ.toOp.trace.re * lam :=
            mul_le_mul_of_nonneg_left h_epsilon hσtr_nn
      _ ≤ 1 * lam := mul_le_mul_of_nonneg_right hσtr_le hlam_nn
      _ = lam := one_mul lam
  simpa [a, D, lam] using h_sum_sq_le_lam

/-- Public-seed direct LHL block-sum bound with the `|Z|` output factor. -/
lemma joint_traceNorm_seedKey_sum_blocks_le_sqrt_card_mul_lambda_subNorm
    {S X Z : Type*} [Fintype S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (hfeas : hasFeasibleLambda ρ σ) :
    ∑ sz : S × Z, Quantum.Metrics.traceNorm
        (((seedKeyExtractorOutputState H ρ).stateMap sz).toOp -
          ((seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).stateMap sz).toOp) ≤
      Real.sqrt ((Fintype.card Z : ℝ) * minFeasibleLambda ρ σ) := by
  classical
  set lam := minFeasibleLambda ρ σ
  have hcardZ_nn : (0 : ℝ) ≤ (Fintype.card Z : ℝ) := Nat.cast_nonneg _
  let D : S × Z → Op n := fun sz =>
    (∑ x : X, if H.hash sz.1 x = sz.2 then (ρ.stateMap x).toOp else 0) -
      (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • ρ.quantumMarginalOp
  let a : S × Z → ℝ := fun sz => Quantum.Metrics.traceNorm (D sz)
  have h_block_diff : ∀ sz : S × Z,
      ((seedKeyExtractorOutputState H ρ).stateMap sz).toOp -
          ((seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).stateMap sz).toOp =
        (1 / (Fintype.card S : ℝ)) • D sz := by
    intro sz
    dsimp [D]
    exact seed_visible_stateMap_sub_uniform_toOp_eq H ρ sz
  have h_block_sum :
      ∑ sz : S × Z, Quantum.Metrics.traceNorm
        (((seedKeyExtractorOutputState H ρ).stateMap sz).toOp -
          ((seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).stateMap sz).toOp) =
        (1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, a sz := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun sz _ => ?_)
    rw [h_block_diff sz, traceNorm_real_smul]
    simp [a]
  rw [h_block_sum]
  have h_sum_sq_le_lam :
      (1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, (a sz) ^ 2 ≤ lam := by
    simpa [a, D, lam] using
      seed_visible_average_traceNorm_sq_le_minFeasibleLambda H hH ρ σ hσ_pd hfeas
  have h_card_sum_sq :
      ((1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, a sz) ^ 2 ≤
        (Fintype.card Z : ℝ) *
          ((1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, (a sz) ^ 2) := by
    exact sq_seed_average_sum_le_card_output_mul_seed_average_sum_sq (S := S) (Z := Z) a
  have h_sq :
      ((1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, a sz) ^ 2 ≤
        (Fintype.card Z : ℝ) * lam :=
    h_card_sum_sq.trans (mul_le_mul_of_nonneg_left h_sum_sq_le_lam hcardZ_nn)
  simpa [lam] using Real.le_sqrt_of_sq_le h_sq

/-- Direct seed-visible hashing from an exponential or arbitrary feasible coefficient. -/
lemma quantum_seedKey_LHL_of_isFeasible
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (t : ℝ)
    (ht : isFeasible ρ σ t) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        ((seedKeyExtractorOutputState H ρ).toJointDensity.toOp -
          (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp) ≤
      Real.sqrt ((Fintype.card Z : ℝ) * t) := by
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  rw [cqState_joint_traceNorm_eq_sum_blocks]
  exact (joint_traceNorm_seedKey_sum_blocks_le_sqrt_card_mul_lambda_subNorm
    H hH ρ σ hσ_pd ⟨t, ht⟩).trans (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (minFeasibleLambda_le_of_isFeasible ρ σ ht)
        (Nat.cast_nonneg _)))

/-- Every hash family satisfies the seed-visible zero-floor bound. -/
lemma quantum_seedKey_LHL_zero_floor
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        ((seedKeyExtractorOutputState H ρ).toJointDensity.toOp -
          (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp) ≤
      Real.sqrt ((Fintype.card Z : ℝ)) := by
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  let A (s : S) (z : Z) : Op n :=
    ∑ x : X, if H.hash s x = z then (ρ.stateMap x).toOp else 0
  have hA (s : S) (z : Z) : (A s z).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro x _
    split_ifs
    · exact posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
    · exact Matrix.PosSemidef.zero
  have hsum (s : S) : ∑ z, A s z = ρ.quantumMarginal.toOp :=
    sum_unscaled_seed_blocks_eq_quantumMarginalOp H ρ s
  have htrace (s : S) : ∑ z, (A s z).trace.re = ρ.quantumMarginal.trace := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, hsum]
    rfl
  have hseed (s : S) :
      ∑ z, traceNorm (A s z - (1 / (Fintype.card Z : ℝ)) • ρ.quantumMarginal.toOp) ≤
        2 * (1 - 1 / (Fintype.card Z : ℝ)) * ρ.quantumMarginal.trace := by
    simpa only [hsum, htrace] using sum_traceNorm_sub_uniform_le (A s) (hA s)
  rw [cqState_joint_traceNorm_eq_sum_blocks]
  simp only [seed_visible_stateMap_sub_uniform_toOp_eq, traceNorm_real_smul,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 / Fintype.card S by positivity)]
  rw [← Finset.mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  have hbound :
      (1 / (Fintype.card S : ℝ)) * ∑ s : S, ∑ z : Z,
        traceNorm (A s z - (1 / (Fintype.card Z : ℝ)) • ρ.quantumMarginal.toOp) ≤
      2 * (1 - 1 / (Fintype.card Z : ℝ)) * ρ.quantumMarginal.trace := by
    calc
      _ ≤ (1 / (Fintype.card S : ℝ)) * ∑ _s : S,
          (2 * (1 - 1 / (Fintype.card Z : ℝ)) * ρ.quantumMarginal.trace) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => hseed s) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hm : (1 : ℝ) ≤ Fintype.card Z := by exact_mod_cast Fintype.card_pos (α := Z)
  have hc : 1 / (Fintype.card Z : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num) hm
  have hweight := mul_le_mul_of_nonneg_left ρ.quantumMarginal.trace_le_one
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sub_nonneg.mpr hc))
  have hfinal := hbound.trans (hweight.trans
    (by simpa using two_mul_one_sub_inv_le_sqrt_card (Fintype.card Z) Fintype.card_pos))
  simp only [← Complex.ofReal_div, Complex.coe_smul]
  exact hfinal

/-- Direct seed-visible hashing from a clipped extended entropy floor, including zero. -/
lemma quantum_seedKey_LHL_subNormalized
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceNorm
        ((seedKeyExtractorOutputState H ρ).toJointDensity.toOp -
          (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp) ≤
      Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) := by
  by_cases hkpos : 0 < k
  · exact quantum_seedKey_LHL_of_isFeasible H hH ρ σ hσ_pd _
      (isFeasible_of_ofReal_le_conditionalMinEntropy ρ σ hkpos hk)
  · exact (quantum_seedKey_LHL_zero_floor H ρ).trans
      (sqrt_card_le_sqrt_card_mul_two_pow_neg_k (le_of_not_gt hkpos))

/-- Generalized-distance seed-visible hashing from an extended entropy floor. -/
lemma traceDistanceGen_seedKeyExtractorOutput_uniformOutput_le_of_minEntropy
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {n : ℕ} [NeZero n]
    (H : QuantumHashFamily S X Z)
    (hH : H.isUniversal)
    (ρ : CQState X n)
    (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef)
    (k : ℝ)
    (hk : ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ) :
    haveI : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
    haveI : NeZero (n * Fintype.card (S × Z)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
    Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState H ρ).toJointDensity.toOp
        (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp ≤
      (1 / 2) * Real.sqrt ((Fintype.card Z : ℝ) * 2 ^ (-k)) := by
  have : NeZero (Fintype.card (S × Z)) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card (S × Z)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) Fintype.card_ne_zero⟩
  have htr_E :=
    seedKeyExtractorOutputState_joint_trace_eq_quantumMarginal_trace H ρ
  have htr_U :=
    seedUniformOutputState_joint_trace_eq_quantumMarginal_trace
      (S := S) (Z := Z) ρ.quantumMarginal
  have htr_eq :
      ((seedKeyExtractorOutputState H ρ).toJointDensity.toOp).trace.re =
        (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal :
          CQState (S × Z) n).toJointDensity.toOp.trace.re :=
    htr_E.trans htr_U.symm
  rw [Quantum.Metrics.traceDistanceGen_eq_traceDistance _ _ htr_eq]
  unfold Quantum.Metrics.traceDistance
  have h_tn :=
    quantum_seedKey_LHL_subNormalized H hH ρ σ hσ_pd k hk
  linarith

end InfoTheory.QuantumLHL

end -- noncomputable section
