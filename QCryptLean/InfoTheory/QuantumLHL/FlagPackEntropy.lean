import QCryptLean.InfoTheory.QuantumLHL.FlagPackCoarsening
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.DimensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct

/-!
# Entropy of flagged blocks

Reference blocks are weighted by signed real entropy floors. Operator domination yields a packed
conditional entropy floor, and nearby feasible block witnesses yield a packed smooth entropy
floor. The real exponential sums are formed before conversion to `ENNReal`, so negative component
rates retain their meaning.
-/

open Quantum.Operators Quantum.Metrics Matrix
open InfoTheory.QuantumLHL
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- **A block-diagonal matrix with positive-definite blocks is positive definite.**  Strict sibling
of
`Matrix.posSemidef_blockDiagonal`: any nonzero vector has a nonzero component on some block `k`,
whose
quadratic form is strictly positive while the others are nonnegative. -/
lemma Matrix.posDef_blockDiagonal {n : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    {M : o → Matrix (Fin n) (Fin n) ℂ} (h : ∀ i, (M i).PosDef) :
    (Matrix.blockDiagonal M).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.posSemidef_blockDiagonal (fun i => (h i).posSemidef)).isHermitian ?_
  intro x hx
  have hsum : star x ⬝ᵥ (Matrix.blockDiagonal M *ᵥ x)
      = ∑ k : o, star (fun b => x (b, k)) ⬝ᵥ (M k *ᵥ (fun b => x (b, k))) := by
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, blockDiagonal_mulVec_apply]
    rw [Finset.sum_comm]
  rw [hsum]
  obtain ⟨⟨a, k⟩, hp⟩ := Function.ne_iff.mp hx
  refine Finset.sum_pos'
    (fun k' _ => (h k').posSemidef.dotProduct_mulVec_nonneg (fun b => x (b, k')))
    ⟨k, Finset.mem_univ k, ?_⟩
  refine (h k).dotProduct_mulVec_pos (fun hzero => hp ?_)
  exact congrFun hzero a

namespace InfoTheory.SmoothMinEntropy

/-!
## The `λ`/feasibility transfer for flag-packed states
-/

/-- **Blockwise feasibility lift.** If, for every flag block `c` and classical outcome `x`, the
packed
block `(blocks c).stateMap x` is dominated by `t · (ref.stateMap c)` in the semidefinite order, then
the
scalar `t` is feasible for the flag-packed state against the block-diagonal reference
ref.toJointDensity.

The packed block `(flagPack blocks hjoint).stateMap x` is the reindexed `blockDiagonal` over `C` of
the
per-flag blocks, and so is ref.toJointDensity; the domination lifts through
`CQState.toJointDensity_opLe_of_forall`. -/
theorem isFeasible_flagPack_of_forall_opLe
    {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (ref : CQState C nE) {t : ℝ} (ht : 0 ≤ t)
    (hdom : ∀ (c : C) (x : X),
      opLe ((blocks c).stateMap x).toOp ((Complex.ofReal t) • (ref.stateMap c).toOp)) :
    isFeasible (CQState.flagPack blocks hjoint) ref.toJointDensity t := by
  refine ⟨ht, fun x => ?_⟩
  have h := CQState.toJointDensity_opLe_of_forall
    (CQState.pointBlock blocks hjoint x) ref ht (fun c => by simpa using hdom c x)
  simpa [CQState.flagPack_stateMap] using h

/-- **`minFeasibleLambda` transfer.** The feasible-lambda optimum of the flag-packed state against
the
block-diagonal reference is at most any scalar feasible blockwise. -/
theorem minFeasibleLambda_flagPack_le
    {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (ref : CQState C nE) {t : ℝ} (ht : 0 ≤ t)
    (hdom : ∀ (c : C) (x : X),
      opLe ((blocks c).stateMap x).toOp ((Complex.ofReal t) • (ref.stateMap c).toOp)) :
    minFeasibleLambda (CQState.flagPack blocks hjoint) ref.toJointDensity ≤ t :=
  minFeasibleLambda_le_of_isFeasible _ _
    (isFeasible_flagPack_of_forall_opLe blocks hjoint ref ht hdom)

/-- The total weight of a flag-packed state is the joint normalization `∑_c ∑_x tr`. -/
lemma flagPack_sum_stateMap_trace
    {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) :
    ∑ x : X, ((CQState.flagPack blocks hjoint).stateMap x).trace
      = ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace := by
  have hx : ∀ x : X, ((CQState.flagPack blocks hjoint).stateMap x).trace
      = ∑ c : C, ((blocks c).stateMap x).trace := by
    intro x
    change ((CQState.pointBlock blocks hjoint x).toJointDensity).trace = _
    rw [CQState.toJointDensity_trace_eq_sum]
    rfl
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_comm]

/-!
## The optimally weighted block-diagonal reference and the joint exponent
-/

/-- The exponential mass `∑_c 2^(-(k c))`.  Its negative base-2 logarithm `-log₂ (∑_c 2^(-(k c)))`
is the certified joint min-entropy exponent — the value for which `2^(-H_joint) = ∑_c 2^(-H_c)`. -/
noncomputable def packExpSum {C : Type*} [Fintype C] (k : C → ℝ) : ℝ :=
  ∑ c : C, (2 : ℝ) ^ (-(k c))

lemma packExpSum_nonneg {C : Type*} [Fintype C] (k : C → ℝ) : 0 ≤ packExpSum k :=
  Finset.sum_nonneg (fun c _ => Real.rpow_nonneg (by norm_num) _)

lemma packExpSum_pos {C : Type*} [Fintype C] [Nonempty C] (k : C → ℝ) : 0 < packExpSum k :=
  Finset.sum_pos (fun c _ => Real.rpow_pos_of_pos (by norm_num) _) Finset.univ_nonempty

/-- The optimal per-block weight `q_c = 2^(-(k c)) / ∑_{c'} 2^(-(k c'))`. -/
noncomputable def packQ {C : Type*} [Fintype C] (k : C → ℝ) (c : C) : ℝ :=
  (2 : ℝ) ^ (-(k c)) / packExpSum k

lemma packQ_nonneg {C : Type*} [Fintype C] (k : C → ℝ) (c : C) : 0 ≤ packQ k c :=
  div_nonneg (Real.rpow_nonneg (by norm_num) _) (packExpSum_nonneg k)

lemma packQ_pos {C : Type*} [Fintype C] [Nonempty C] (k : C → ℝ) (c : C) : 0 < packQ k c :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (packExpSum_pos k)

lemma packQ_le_one {C : Type*} [Fintype C] [Nonempty C] (k : C → ℝ) (c : C) : packQ k c ≤ 1 := by
  rw [packQ, div_le_one (packExpSum_pos k)]
  change (2 : ℝ) ^ (-(k c)) ≤ ∑ c' : C, (2 : ℝ) ^ (-(k c'))
  exact Finset.single_le_sum (f := fun c' => (2 : ℝ) ^ (-(k c')))
    (fun c' _ => Real.rpow_nonneg (by norm_num) _) (Finset.mem_univ c)

lemma packExpSum_mul_packQ {C : Type*} [Fintype C] [Nonempty C] (k : C → ℝ) (c : C) :
    packExpSum k * packQ k c = (2 : ℝ) ^ (-(k c)) := by
  rw [packQ, mul_div_assoc', mul_comm, mul_div_assoc, div_self (packExpSum_pos k).ne', mul_one]

lemma sum_packQ_eq_one {C : Type*} [Fintype C] [Nonempty C] (k : C → ℝ) :
    ∑ c : C, packQ k c = 1 := by
  simp only [packQ, ← Finset.sum_div]
  exact div_self (packExpSum_pos k).ne'

/-- **The optimally weighted block-diagonal reference.** The CQ state over the flag register `C`
whose
`c`-block is `q_c σ_c` with `q_c ∝ 2^(-(k c))`.  Its joint density is the block-diagonal reference
`blockdiag_c (q_c σ_c)` against which the flag-packed joint min-entropy is certified. -/
noncomputable def flagPackRef {C : Type*} [Fintype C] [Nonempty C] {nE : ℕ}
    (σ : C → SubDensityOp nE) (k : C → ℝ) : CQState C nE where
  stateMap c := (σ c).smul (packQ k c) (packQ_nonneg k c) (packQ_le_one k c)
  weight_le_one := by
    calc ∑ c : C, ((σ c).smul (packQ k c) (packQ_nonneg k c) (packQ_le_one k c)).trace
        = ∑ c : C, packQ k c * (σ c).trace :=
          Finset.sum_congr rfl (fun c _ =>
            SubDensityOp.smul_trace (σ c) (packQ k c) (packQ_nonneg k c) (packQ_le_one k c))
      _ ≤ ∑ c : C, packQ k c * 1 :=
          Finset.sum_le_sum (fun c _ =>
            mul_le_mul_of_nonneg_left (σ c).trace_le_one (packQ_nonneg k c))
      _ = ∑ c : C, packQ k c := by simp
      _ = 1 := sum_packQ_eq_one k

@[simp] lemma flagPackRef_stateMap_toOp {C : Type*} [Fintype C] [Nonempty C] {nE : ℕ}
    (σ : C → SubDensityOp nE) (k : C → ℝ) (c : C) :
    ((flagPackRef σ k).stateMap c).toOp = (Complex.ofReal (packQ k c)) • (σ c).toOp := rfl

/-- **Blockwise domination at the optimal weighting.** Each packed block `(blocks c).stateMap x` is
dominated by `(∑_{c'} 2^(-(k c'))) · (q_c σ_c)`: the per-block domination
`(blocks c).stateMap x ≤ 2^(-(k c)) σ_c` (from `k c ≤ H_min((blocks c)|σ c)`) rescales through
`q_c = 2^(-(k c)) / ∑ 2^(-·)` to the single packed scalar `∑_{c'} 2^(-(k c'))`. -/
lemma flagPack_blocks_opLe_packExpSum_smul_refReal
    {X C : Type*} [Fintype X] [Fintype C] [Nonempty C] {nE : ℕ}
    (blocks : C → CQState X nE) (σ : C → SubDensityOp nE) (k : C → ℝ)
    (hfeas : ∀ c : C, hasFeasibleLambda (blocks c) (σ c))
    (hk : ∀ c : C, k c ≤ conditionalMinEntropyReal (blocks c) (σ c))
    (c : C) (x : X) :
    opLe ((blocks c).stateMap x).toOp
      ((Complex.ofReal (packExpSum k)) • ((flagPackRef σ k).stateMap c).toOp) := by
  have hpb := stateMap_opLe_pow_neg_of_conditionalMinEntropyReal_le_of_hasFeasibleLambda
    (blocks c) (σ c) (hfeas c) (hk c) x
  rw [flagPackRef_stateMap_toOp, smul_smul, ← Complex.ofReal_mul, packExpSum_mul_packQ]
  exact hpb

/-- A CQ joint density is positive-definite when every classical block is. -/
lemma CQState.toJointDensity_posDef_of_forall {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) (h : ∀ x : X, (ρ.stateMap x).toOp.PosDef) :
    ρ.toJointDensity.toOp.PosDef := by
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal, Matrix.reindex_apply]
  exact (Matrix.posDef_blockDiagonal h).submatrix (Equiv.injective _)

/-- **The optimally weighted block-diagonal reference is positive-definite** when the per-block
references are.  This is the positive-definiteness side condition consumed by the union-event
leftover-hashing bound. -/
lemma flagPackRef_toJointDensity_posDef {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C] {nE :
    ℕ}
    (σ : C → SubDensityOp nE) (k : C → ℝ) (hσ : ∀ c : C, (σ c).toOp.PosDef) :
    (flagPackRef σ k).toJointDensity.toOp.PosDef := by
  refine CQState.toJointDensity_posDef_of_forall _ (fun c => ?_)
  rw [flagPackRef_stateMap_toOp]
  exact (hσ c).smul (Complex.zero_lt_real.mpr (packQ_pos k c))

/-!
## Witness assembly: the packed smoothing radius from per-block radii
-/

/-- **The flag-packed generalized trace distance is subadditive over the flag.** The packed trace
norm
is the block sum `∑_c ‖·‖₁` (`traceNorm_flagPack_diff_eq_sum` + `traceNorm_joint_diff_eq_sum`) and
the
packed trace gap is `|∑_c Δ_c| ≤ ∑_c |Δ_c|` (the block traces add), so the two `traceDistanceGen`
contributions are each subadditive over `C`. -/
lemma traceDistanceGen_flagPack_toJointDensity_le_sum
    {X C : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ} [NeZero nE]
    (blocks blocks' : C → CQState X nE)
    (hj : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (hj' : ∑ c : C, ∑ x : X, ((blocks' c).stateMap x).trace ≤ 1) :
    haveI : NeZero (nE * Fintype.card C) :=
      ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
    traceDistanceGen (CQState.flagPack blocks hj).toJointDensity.toOp
        (CQState.flagPack blocks' hj').toJointDensity.toOp
      ≤ ∑ c : C, traceDistanceGen (blocks c).toJointDensity.toOp (blocks' c).toJointDensity.toOp :=
          by
  haveI : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (nE * Fintype.card C) :=
    ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
  have hTN : traceNorm ((CQState.flagPack blocks hj).toJointDensity.toOp
        - (CQState.flagPack blocks' hj').toJointDensity.toOp)
      = ∑ c : C, traceNorm ((blocks c).toJointDensity.toOp - (blocks' c).toJointDensity.toOp) := by
    rw [traceNorm_flagPack_diff_eq_sum blocks blocks' hj hj', Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => (traceNorm_joint_diff_eq_sum (blocks c) (blocks'
        c)).symm)
  have htrL : (CQState.flagPack blocks hj).toJointDensity.toOp.trace.re
      = ∑ c : C, (blocks c).toJointDensity.toOp.trace.re := by
    calc (CQState.flagPack blocks hj).toJointDensity.toOp.trace.re
        = ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace := flagPack_toJointDensity_trace blocks hj
      _ = ∑ c : C, (blocks c).toJointDensity.toOp.trace.re :=
          Finset.sum_congr rfl (fun c _ => (CQState.toJointDensity_trace_eq_sum (blocks c)).symm)
  have htrL' : (CQState.flagPack blocks' hj').toJointDensity.toOp.trace.re
      = ∑ c : C, (blocks' c).toJointDensity.toOp.trace.re := by
    calc (CQState.flagPack blocks' hj').toJointDensity.toOp.trace.re
        = ∑ c : C, ∑ x : X, ((blocks' c).stateMap x).trace := flagPack_toJointDensity_trace blocks'
            hj'
      _ = ∑ c : C, (blocks' c).toJointDensity.toOp.trace.re :=
          Finset.sum_congr rfl (fun c _ => (CQState.toJointDensity_trace_eq_sum (blocks' c)).symm)
  have hTrGap :
      |((CQState.flagPack blocks hj).toJointDensity.toOp.trace
          - (CQState.flagPack blocks' hj').toJointDensity.toOp.trace).re|
        ≤ ∑ c : C, |((blocks c).toJointDensity.toOp.trace
            - (blocks' c).toJointDensity.toOp.trace).re| := by
    have heq : ((CQState.flagPack blocks hj).toJointDensity.toOp.trace
          - (CQState.flagPack blocks' hj').toJointDensity.toOp.trace).re
        = ∑ c : C, ((blocks c).toJointDensity.toOp.trace
            - (blocks' c).toJointDensity.toOp.trace).re := by
      rw [Complex.sub_re, htrL, htrL', ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun c _ => (Complex.sub_re _ _).symm)
    rw [heq]
    exact Finset.abs_sum_le_sum_abs _ _
  calc traceDistanceGen (CQState.flagPack blocks hj).toJointDensity.toOp
          (CQState.flagPack blocks' hj').toJointDensity.toOp
      = (1 / 2) * (∑ c : C, traceNorm ((blocks c).toJointDensity.toOp - (blocks'
          c).toJointDensity.toOp))
          + (1 / 2) * |((CQState.flagPack blocks hj).toJointDensity.toOp.trace
              - (CQState.flagPack blocks' hj').toJointDensity.toOp.trace).re| := by
        rw [Quantum.Metrics.traceDistanceGen, hTN]
    _ ≤ (1 / 2) * (∑ c : C, traceNorm ((blocks c).toJointDensity.toOp - (blocks'
        c).toJointDensity.toOp))
          + (1 / 2) * (∑ c : C, |((blocks c).toJointDensity.toOp.trace
              - (blocks' c).toJointDensity.toOp.trace).re|) := by
        gcongr
    _ = ∑ c : C, traceDistanceGen (blocks c).toJointDensity.toOp (blocks' c).toJointDensity.toOp :=
        by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        rfl

/-- **The packed smoothing radius from per-block radii (Fuchs–van-de-Graaf).** The purified distance
of
two flag-packs is bounded by `√(2 ∑_c P(blocks c, blocks' c))`: the packed generalized trace
distance is
subadditive over the flag (`traceDistanceGen_flagPack_toJointDensity_le_sum`), bounded per block by
the
per-block purified distance (`traceDistanceGen_le_purifiedDistance`), and `P ≤ √(2 D)`
(`purifiedDistance_le_sqrt_two_mul_traceDistanceGen`).  This is the deficit-robust witness-assembly
radius: it needs no alignment of the per-block sub-normalizations (unlike the sharper Pythagorean
`√(∑_c P_c²)`). -/
theorem flagPack_purifiedDistance_le_sqrt_two_sum
    {X C : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ} [NeZero nE]
    (blocks blocks' : C → CQState X nE)
    (hj : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (hj' : ∑ c : C, ∑ x : X, ((blocks' c).stateMap x).trace ≤ 1) :
    haveI : NeZero (nE * Fintype.card C) :=
      ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
    CQState.purifiedDistance (CQState.flagPack blocks hj) (CQState.flagPack blocks' hj')
      ≤ Real.sqrt (2 * ∑ c : C, CQState.purifiedDistance (blocks c) (blocks' c)) := by
  haveI : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (nE * Fintype.card C) :=
    ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
  have hstep :
      traceDistanceGen (CQState.flagPack blocks hj).toJointDensity.toOp
          (CQState.flagPack blocks' hj').toJointDensity.toOp
        ≤ ∑ c : C, CQState.purifiedDistance (blocks c) (blocks' c) := by
    refine le_trans (traceDistanceGen_flagPack_toJointDensity_le_sum blocks blocks' hj hj') ?_
    exact Finset.sum_le_sum (fun c _ =>
      traceDistanceGen_le_purifiedDistance (blocks c).toJointDensity (blocks' c).toJointDensity)
  refine le_trans (purifiedDistance_le_sqrt_two_mul_traceDistanceGen
    (CQState.flagPack blocks hj).toJointDensity (CQState.flagPack blocks' hj').toJointDensity) ?_
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hstep (by norm_num))

/-- Per-block extended entropy floors certify the packed positive-part entropy.
A nonpositive packed exponent is automatic; a positive exponent forces every block rate positive. -/
theorem flagPack_conditionalMinEntropy_ge_of_blocks
    {X C : Type*} [Fintype X] [Nonempty X]
    [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (σ : C → SubDensityOp nE) (k : C → ℝ)
    (hk : ∀ c, ENNReal.ofReal (k c) ≤ conditionalMinEntropy (blocks c) (σ c)) :
    ENNReal.ofReal (-Real.logb 2 (packExpSum k)) ≤
      conditionalMinEntropy (CQState.flagPack blocks hjoint) (flagPackRef σ k).toJointDensity := by
  by_cases hpos : 0 < -Real.logb 2 (packExpSum k)
  · have hZpos := packExpSum_pos k
    have hZlt : packExpSum k < 1 := by
      rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hZpos]
      exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    have hkpos : ∀ c, 0 < k c := by
      intro c
      have hsum : (2 : ℝ) ^ (-k c) ≤ packExpSum k := by
        unfold packExpSum
        exact Finset.single_le_sum
          (fun c _ => show 0 ≤ (2 : ℝ) ^ (-k c) from Real.rpow_nonneg (by norm_num) _)
          (Finset.mem_univ c)
      have hexp : (2 : ℝ) ^ (-k c) < 2 ^ (0 : ℝ) := by
        simpa only [Real.rpow_zero] using hsum.trans_lt hZlt
      have := (Real.rpow_lt_rpow_left_iff one_lt_two).mp hexp
      linarith
    apply ofReal_le_conditionalMinEntropy_of_isFeasible
    rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num) hZpos]
    apply isFeasible_flagPack_of_forall_opLe blocks hjoint (flagPackRef σ k) hZpos.le
    intro c x
    rw [flagPackRef_stateMap_toOp, smul_smul, ← Complex.ofReal_mul, packExpSum_mul_packQ]
    exact (isFeasible_of_ofReal_le_conditionalMinEntropy (blocks c) (σ c)
      (hkpos c) (hk c)).2 x
  · simp [ENNReal.ofReal_of_nonpos (le_of_not_gt hpos)]

/-- Packed extended entropy floors hold at every nonnegative smoothing radius. -/
theorem flagPack_smoothMinEntropy_ge_of_blocks
    {X C : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ} [NeZero nE]
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (σ : C → SubDensityOp nE) (k : C → ℝ)
    (hk : ∀ c, ENNReal.ofReal (k c) ≤ conditionalMinEntropy (blocks c) (σ c))
    (ε : ℝ) (hε : 0 ≤ ε) :
    ENNReal.ofReal (-Real.logb 2 (packExpSum k)) ≤
      smoothMinEntropy ε (CQState.flagPack blocks hjoint) (flagPackRef σ k).toJointDensity := by
  haveI : NeZero (nE * Fintype.card C) :=
    ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
  exact (flagPack_conditionalMinEntropy_ge_of_blocks blocks hjoint σ k hk).trans
    (smoothMinEntropy_ge_conditionalMinEntropy hε _ _)

/-- Per-block smoothing witnesses give the packed extended floor at radius `sqrt (2 * ∑ radii)`.
Zero witness weight and balls containing zero need no separate boundedness premise. -/
theorem flagPack_smoothMinEntropy_ge_of_block_witnesses
    {X C : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ} [NeZero nE]
    (blocks τ : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (hτjoint : ∑ c : C, ∑ x : X, ((τ c).stateMap x).trace ≤ 1)
    (σ : C → SubDensityOp nE) (k : C → ℝ)
    (hk : ∀ c, ENNReal.ofReal (k c) ≤ conditionalMinEntropy (τ c) (σ c))
    (radii : C → ℝ)
    (hball : ∀ c, CQState.purifiedDistance (blocks c) (τ c) ≤ radii c) :
    ENNReal.ofReal (-Real.logb 2 (packExpSum k)) ≤
      smoothMinEntropy (Real.sqrt (2 * ∑ c, radii c))
        (CQState.flagPack blocks hjoint) (flagPackRef σ k).toJointDensity := by
  haveI : NeZero (nE * Fintype.card C) :=
    ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
  apply smoothMinEntropy_ge_of_hmin_approx _ (CQState.flagPack τ hτjoint)
  · exact (flagPack_purifiedDistance_le_sqrt_two_sum blocks τ hjoint hτjoint).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun c _ => hball c)) (by norm_num)))
  · exact flagPack_conditionalMinEntropy_ge_of_blocks τ hτjoint σ k hk

/-- Packing classical flags preserves the signed floor `-logb 2 (packExpSum k)` against
`flagPackRef σ k` when the packed state has positive weight. -/
theorem flagPack_conditionalMinEntropyReal_ge_of_blocks
    {X C : Type*} [Fintype X] [Nonempty X] [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (σ : C → SubDensityOp nE) (k : C → ℝ)
    (hfeas : ∀ c : C, hasFeasibleLambda (blocks c) (σ c))
    (hk : ∀ c : C, k c ≤ conditionalMinEntropyReal (blocks c) (σ c))
    (hweight : 0 < ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace) :
    -Real.logb 2 (packExpSum k)
      ≤ conditionalMinEntropyReal (CQState.flagPack blocks hjoint) (flagPackRef σ k).toJointDensity
          := by
  have hZpos := packExpSum_pos k
  have hdom := flagPack_blocks_opLe_packExpSum_smul_refReal blocks σ k hfeas hk
  have hlam_le :
      minFeasibleLambda (CQState.flagPack blocks hjoint) (flagPackRef σ k).toJointDensity
        ≤ packExpSum k :=
    minFeasibleLambda_flagPack_le blocks hjoint (flagPackRef σ k) hZpos.le hdom
  have hfeas_packed :
      hasFeasibleLambda (CQState.flagPack blocks hjoint) (flagPackRef σ k).toJointDensity :=
    ⟨packExpSum k, isFeasible_flagPack_of_forall_opLe blocks hjoint (flagPackRef σ k) hZpos.le hdom⟩
  have hweight_packed :
      0 < ∑ x : X, ((CQState.flagPack blocks hjoint).stateMap x).trace := by
    rw [flagPack_sum_stateMap_trace]; exact hweight
  have hlam_pos :
      0 < minFeasibleLambda (CQState.flagPack blocks hjoint) (flagPackRef σ k).toJointDensity :=
    minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos _ _ hweight_packed hfeas_packed
  refine conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k
    _ _ (-Real.logb 2 (packExpSum k)) hlam_pos ?_
  rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num) hZpos]
  exact hlam_le

/-- The packed blocks retain the signed floor `-logb 2 (packExpSum k)` throughout a smoothing
ball below the stated weight threshold. -/
theorem flagPack_smoothMinEntropyReal_ge_of_blocks
    {X C : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ} [NeZero nE]
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (σ : C → SubDensityOp nE) (k : C → ℝ)
    (hfeas : ∀ c : C, hasFeasibleLambda (blocks c) (σ c))
    (hk : ∀ c : C, k c ≤ conditionalMinEntropyReal (blocks c) (σ c))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hweight : 2 * ε < ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace) :
    -Real.logb 2 (packExpSum k)
      ≤ smoothMinEntropyReal ε (CQState.flagPack blocks hjoint)
        (flagPackRef σ k).toJointDensity := by
  haveI : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (nE * Fintype.card C) := ⟨Nat.mul_ne_zero (NeZero.ne nE) (NeZero.ne _)⟩
  have hweight_pos : 0 < ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace := by linarith
  have hcond :=
    flagPack_conditionalMinEntropyReal_ge_of_blocks blocks hjoint σ k hfeas hk hweight_pos
  have hsum : ∑ x : X, ((CQState.flagPack blocks hjoint).stateMap x).trace
      = ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace :=
    flagPack_sum_stateMap_trace blocks hjoint
  have hbdd :
      BddAbove (setOf (isInSmoothedSetReal ε (CQState.flagPack blocks hjoint)
        (flagPackRef σ k).toJointDensity)) :=
    (fun ε η hη ρ hρ σ =>
      smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη ρ σ
        (fun _ hd => CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ hd)) ε
      ((∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace) - 2 * ε) (by linarith)
      (CQState.flagPack blocks hjoint) (by rw [hsum]; linarith)
      (flagPackRef σ k).toJointDensity
  exact smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove ε (CQState.flagPack blocks hjoint)
    (flagPackRef σ k).toJointDensity (-Real.logb 2 (packExpSum k))
    (CQState.flagPack blocks hjoint) hbdd
    (by rw [CQState.purifiedDistance_self_zero]; exact hε) hcond

/-- Packing block witnesses gives the signed floor `-logb 2 (packExpSum k)` at radius `sqrt (2 *
∑ c, radii c)`. -/
theorem flagPack_smoothMinEntropyReal_ge_of_block_witnesses
    {X C : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ} [NeZero nE]
    (blocks τ : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (hτjoint : ∑ c : C, ∑ x : X, ((τ c).stateMap x).trace ≤ 1)
    (σ : C → SubDensityOp nE) (k : C → ℝ)
    (hfeas : ∀ c : C, hasFeasibleLambda (τ c) (σ c))
    (hk : ∀ c : C, k c ≤ conditionalMinEntropyReal (τ c) (σ c))
    (hτweight : 0 < ∑ c : C, ∑ x : X, ((τ c).stateMap x).trace)
    (radii : C → ℝ)
    (hball : ∀ c : C, CQState.purifiedDistance (blocks c) (τ c) ≤ radii c)
    (hbudget : 2 * Real.sqrt (2 * ∑ c : C, radii c)
      < ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace) :
    -Real.logb 2 (packExpSum k)
      ≤ smoothMinEntropyReal (Real.sqrt (2 * ∑ c : C, radii c))
          (CQState.flagPack blocks hjoint) (flagPackRef σ k).toJointDensity := by
  haveI : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (nE * Fintype.card C) :=
    ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
  set r : ℝ := Real.sqrt (2 * ∑ c : C, radii c) with hr
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hcond :=
    flagPack_conditionalMinEntropyReal_ge_of_blocks τ hτjoint σ k hfeas hk hτweight
  have hdist : CQState.purifiedDistance (CQState.flagPack blocks hjoint)
      (CQState.flagPack τ hτjoint) ≤ r := by
    refine le_trans (flagPack_purifiedDistance_le_sqrt_two_sum blocks τ hjoint hτjoint) ?_
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun c _ => hball c)) (by norm_num))
  have hsum : ∑ x : X, ((CQState.flagPack blocks hjoint).stateMap x).trace
      = ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace :=
    flagPack_sum_stateMap_trace blocks hjoint
  have hbdd :
      BddAbove (setOf (isInSmoothedSetReal r (CQState.flagPack blocks hjoint)
        (flagPackRef σ k).toJointDensity)) :=
    (fun ε η hη ρ hρ σ =>
      smoothMinEntropyReal_bddAbove_of_candidate_weight_floor ε η hη ρ σ
        (fun _ hd => CQState.sum_stateMap_trace_ge_of_purifiedDistance_of_weight_lower hρ hd)) r
      ((∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace) - 2 * r) (by linarith)
      (CQState.flagPack blocks hjoint) (by rw [hsum]; linarith)
      (flagPackRef σ k).toJointDensity
  exact smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove r (CQState.flagPack blocks hjoint)
    (flagPackRef σ k).toJointDensity (-Real.logb 2 (packExpSum k))
    (CQState.flagPack τ hτjoint) hbdd hdist hcond

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
