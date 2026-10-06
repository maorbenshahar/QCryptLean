import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Instrument
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyExtractor

/-!
# The blockwise good/bad split of the seed-visible leftover-hashing pair

The linear (`√`-free) accept-split route charges the accept-tail residual at the **output** of
privacy amplification, in trace norm, instead of enlarging the smoothing radius by `√(2·ε_AT)`.
Operationally it needs exactly two register-generic facts about a blockwise Löwner split
`ρ_mix = ρ_good + ρ_bad` of a CQ state:

* `cqStateSubOfOpLe` — the residual `ρ_mix − ρ_good` is itself a CQ state whenever `ρ_good` is
  blockwise Löwner-dominated by `ρ_mix` (`opLe` blockwise).  Every block is positive
  semidefinite, which is what makes its trace norm equal to its trace downstream;
* `seedKeyExtractor_seedUniform_toJointDensity_add_of_split` — both the seed-visible extractor
  output `seedKeyExtractorOutputState` and the seed-visible ideal `seedUniformOutputState` are
  finite `ℂ`-linear in the input blocks, so the split propagates to their joint-density
  operators.  This is the additivity `traceDistanceGen_le_acceptSplit` consumes.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`), App. B, the
accept-block split `\label{eq:tausplit}` (`main.tex:1356`–`:1361`)
and the leftover-hashing step (`main.tex:1406`–`:1416`); Christandl-König-Renner 2009
(`arXiv:0809.3019`),
`\label{lem:extractpart}` (`main.tex:319`–`:328`).
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- The real-minus-uniform block for a public seed and hashed key, for any
complex module of raw-key blocks. -/
def hashDifferenceBlock {S X Z E : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] [AddCommGroup E] [Module ℂ E]
    (H : QuantumHashFamily S X Z) (f : X → E) (sz : S × Z) : E :=
  (1 / (Fintype.card S : ℂ)) • (∑ x, if H.hash sz.1 x = sz.2 then f x else 0) -
    (1 / (Fintype.card (S × Z) : ℂ)) • ∑ x, f x

/-- Any complex-linear map commutes with the real-minus-uniform hash blocks. -/
lemma map_hashDifferenceBlock {S X Z E F : Type*}
    [Fintype S] [Fintype X] [Fintype Z] [DecidableEq Z]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (H : QuantumHashFamily S X Z) (T : E →ₗ[ℂ] F) (f : X → E) (sz : S × Z) :
    T (hashDifferenceBlock H f sz) = hashDifferenceBlock H (fun x => T (f x)) sz := by
  simp only [hashDifferenceBlock, map_sub, map_smul, map_sum, apply_ite, map_zero]

/-- Seed-visible real-minus-ideal hashing is the joint diagonal embedding of
the corresponding linear combinations of raw-key blocks. -/
lemma hashDifferenceBlock_joint {S X Z : Type*}
    [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X] [Fintype Z] [DecidableEq Z] [Nonempty Z] {b : ℕ}
    (H : QuantumHashFamily S X Z) (ρ : CQState X b) :
    (seedKeyExtractorOutputState H ρ).toJointDensity.toOp -
        (seedUniformOutputState (S := S) (Z := Z) ρ.quantumMarginal).toJointDensity.toOp =
      cqJointLinearMap (S × Z) b (hashDifferenceBlock H (fun x => (ρ.stateMap x).toOp)) := by
  rw [CQState.toJointDensity_toOp_eq_cqJointLinearMap,
    CQState.toJointDensity_toOp_eq_cqJointLinearMap, ← map_sub]
  congr 1
  funext sz
  simp only [Pi.sub_apply, seedKeyExtractorOutputState_stateMap_toOp,
    seedUniformOutputState_stateMap_toOp]
  simp only [hashDifferenceBlock, ← Complex.coe_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast]
  rfl

/-- **The blockwise operator difference `big − small` of two CQ states with `small ⪯ big`.**

The bad branch of the linear accept-split.  Each block is positive semidefinite by the blockwise
`opLe` domination, and sub-normalized because `big` is; the total weight is `big`'s weight minus
`small`'s, hence still at most one. -/
def cqStateSubOfOpLe {X : Type*} [Fintype X] {dE : ℕ}
    (big small : CQState X dE)
    (hle : ∀ x, opLe (small.stateMap x).toOp (big.stateMap x).toOp) :
    CQState X dE where
  stateMap x :=
    { toOp := (big.stateMap x).toOp - (small.stateMap x).toOp
      isHermitian := (big.stateMap x).isHermitian.sub (small.stateMap x).isHermitian
      pos_semidef := fun v => by
        have h := hle x v
        rw [quadraticForm_sub, Complex.sub_re]
        linarith
      trace_le_one := by
        rw [Matrix.trace_sub, Complex.sub_re]
        have h1 := (big.stateMap x).trace_le_one
        have h2 := (small.stateMap x).trace_nonneg
        change (big.stateMap x).toOp.trace.re - (small.stateMap x).toOp.trace.re ≤ 1
        have h2' : (0 : ℝ) ≤ (small.stateMap x).toOp.trace.re := h2
        linarith }
  weight_le_one := by
    have hterm : ∀ x : X, ((big.stateMap x).toOp - (small.stateMap x).toOp).trace.re
        = (big.stateMap x).trace - (small.stateMap x).trace := fun x => by
      rw [Matrix.trace_sub, Complex.sub_re]
      rfl
    change ∑ x : X, ((big.stateMap x).toOp - (small.stateMap x).toOp).trace.re ≤ 1
    simp only [hterm]
    rw [Finset.sum_sub_distrib]
    have hbig := big.weight_le_one
    have hsmall : (0 : ℝ) ≤ ∑ x : X, (small.stateMap x).trace :=
      Finset.sum_nonneg (fun x _ => (small.stateMap x).trace_nonneg)
    linarith

@[simp]
lemma cqStateSubOfOpLe_stateMap_toOp {X : Type*} [Fintype X] {dE : ℕ}
    (big small : CQState X dE)
    (hle : ∀ x, opLe (small.stateMap x).toOp (big.stateMap x).toOp) (x : X) :
    ((cqStateSubOfOpLe big small hle).stateMap x).toOp
      = (big.stateMap x).toOp - (small.stateMap x).toOp := rfl

/-- The total weight of the residual is the weight gap. -/
lemma cqStateSubOfOpLe_quantumMarginal_trace {X : Type*} [Fintype X] {dE : ℕ}
    (big small : CQState X dE)
    (hle : ∀ x, opLe (small.stateMap x).toOp (big.stateMap x).toOp) :
    (cqStateSubOfOpLe big small hle).quantumMarginal.trace
      = (∑ x : X, (big.stateMap x).trace) - (∑ x : X, (small.stateMap x).trace) := by
  change (cqStateSubOfOpLe big small hle).quantumMarginalOp.trace.re = _
  unfold CQState.quantumMarginalOp
  simp only [cqStateSubOfOpLe_stateMap_toOp]
  rw [Finset.sum_sub_distrib, Matrix.trace_sub, Complex.sub_re, Matrix.trace_sum,
    Matrix.trace_sum, Complex.re_sum, Complex.re_sum]
  rfl

/-- Blockwise additivity of a CQ state lifts to its block-diagonal joint-density operator. -/
theorem cqState_toJointDensity_toOp_add {X : Type*} [Fintype X] [DecidableEq X] {dE : ℕ}
    (a b c : CQState X dE)
    (h : ∀ x, (a.stateMap x).toOp = (b.stateMap x).toOp + (c.stateMap x).toOp) :
    a.toJointDensity.toOp = b.toJointDensity.toOp + c.toJointDensity.toOp := by
  simp_rw [CQState.toJointDensity_toOp_eq_cqJointLinearMap]
  rw [← map_add]
  congr 1
  funext x
  exact h x

/-- **Extractor/ideal additivity over a blockwise operator split** (Nahar et al. App. B, the
accept-block split `\label{eq:tausplit}` feeding the leftover-hashing step).

Both the seed-visible extractor output and the seed-visible ideal are finite `ℂ`-linear in the
input blocks, so a blockwise split `ρ_mix = ρ_good + ρ_bad` propagates to their joint-density
operators. -/
theorem seedKeyExtractor_seedUniform_toJointDensity_add_of_split
    {S X Z : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype X]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] {dE : ℕ}
    (H : QuantumHashFamily S X Z)
    (ρ_mix ρ_good ρ_bad : CQState X dE)
    (hsplit : ∀ x, (ρ_mix.stateMap x).toOp
      = (ρ_good.stateMap x).toOp + (ρ_bad.stateMap x).toOp) :
    (seedKeyExtractorOutputState H ρ_mix).toJointDensity.toOp
        = (seedKeyExtractorOutputState H ρ_good).toJointDensity.toOp
          + (seedKeyExtractorOutputState H ρ_bad).toJointDensity.toOp
      ∧ (seedUniformOutputState (S := S) (Z := Z) ρ_mix.quantumMarginal).toJointDensity.toOp
        = (seedUniformOutputState (S := S) (Z := Z) ρ_good.quantumMarginal).toJointDensity.toOp
          + (seedUniformOutputState (S := S) (Z := Z)
              ρ_bad.quantumMarginal).toJointDensity.toOp := by
  -- The quantum marginal splits (`quantumMarginalOp` is the sum of the blocks).
  have hqm : ρ_mix.quantumMarginal.toOp
      = ρ_good.quantumMarginal.toOp + ρ_bad.quantumMarginal.toOp := by
    change ρ_mix.quantumMarginalOp = ρ_good.quantumMarginalOp + ρ_bad.quantumMarginalOp
    unfold CQState.quantumMarginalOp
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => hsplit x)
  refine ⟨?_, ?_⟩
  · -- Extractor side: each seed block is a scaled sum of input blocks.
    refine cqState_toJointDensity_toOp_add _ _ _ (fun sz => ?_)
    change seedPerSeedWeightedOp H ρ_mix sz.1 sz.2
        = seedPerSeedWeightedOp H ρ_good sz.1 sz.2 + seedPerSeedWeightedOp H ρ_bad sz.1 sz.2
    unfold seedPerSeedWeightedOp
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs with hh
    · exact hsplit x
    · rw [add_zero]
  · -- Ideal side: each block is `(1/(|S|·|Z|)) • quantumMarginal`.
    refine cqState_toJointDensity_toOp_add _ _ _ (fun sz => ?_)
    simp only [seedUniformOutputState_stateMap_toOp]
    rw [hqm, smul_add]

end InfoTheory.QuantumLHL

end -- noncomputable section
