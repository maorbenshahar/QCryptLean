import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarseningTraceDistance
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyExtractor

/-!
# Flag-packed CQ states and flag-controlled classical coarsening

This file packages the "conditioning-flag absorption" construction for CQ states: a family of
CQ blocks indexed by a classical announcement register `C` is packed into a *single* CQ state by
moving `C` into the **quantum** register as a block-diagonal flag `Σ_c |c⟩⟨c| ⊗ ·`. This is the
generic library-grade infrastructure behind the union-event form of the discarded-position
leftover-hashing lemma (`QKD/ReviewGaps/DiscardedPositionUnion.lean`, [142] Lemma 4): absorbing the
announcement register `C̄` into the quantum side lets the stock seed-key leftover hashing lemma
`quantum_seedKey_LHL_smooth` apply verbatim with `C̄` as classical side information, so the exponent
is the genuine jointly-conditioned smooth min-entropy `H_min^ε(Z|C̄E)`.

The one substantive result is `traceDistanceGen_flagControlledCoarsen_le`: a **flag-controlled**
classical relabel family `g : C → X → Y` (a different classical map on each flag block) contracts
the
generalized trace distance of flag-packed states. This is the data-processing step of the union-form
proof, where the relabel `ℰ` reads the announcement `C̄` — now a quantum-side flag — and applies a
`C̄`-dependent classical map; it is not a plain `CQState.coarsen` (which uses one classical map), so
a
dedicated flag-aware contraction is needed.

## Main definitions
- `CQState.pointBlock` — for fixed classical outcome `x`, the CQ state over the flag register `C`
  whose `c`-block is `(blocks c).stateMap x`.
- `CQState.flagPack` — the flag-packed CQ state `X → SubDensityOp (nE * |C|)`,
  `stateMap x = Σ_c |c⟩⟨c| ⊗ (blocks c).stateMap x`, carrying the joint normalization
  `Σ_c Σ_x tr ≤ 1`.
- `CQState.flagMarginal` — the CQ state over `C` of per-block quantum marginals; its joint density
is
  the flag-packed quantum marginal (`ρ_{C̄E}`).
- `flagPackOp` — the block-diagonal packing `F ↦ reindex (blockDiagonal F)` of a `C`-family of
  operators into the flag-augmented register; the operator-level engine of `flagPack`.

## Main statements
- `flagPackOp_finsetSum`, `flagPackOp_smul`, `flagPackOp_ite`, `flagPackOp_zero` — linearity of
  the packing engine.
- `flagPack_stateMap_toOp` — the packed block equals `flagPackOp` of the per-flag blocks.
- `flagPack_quantumMarginalOp` / `flagPack_quantumMarginal` — the packed quantum marginal is the
  flag-packed marginal (`ρ_{C̄E}`).
- `flagPack_seedKeyExtractorOutput` / `flagPack_seedUniformOutput` — the seed-key extractor and its
  ideal uniform target commute with flag packing.
- `traceDistanceGen_flagControlledCoarsen_le` — flag-controlled classical relabels contract
  generalized trace distance on flag-packed states.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## The flag-indexed point block and the flag-packed CQ state
-/

/-- For a fixed classical outcome `x`, the CQ state over the flag register `C` whose `c`-block is
`(blocks c).stateMap x`. Its weight is `Σ_c tr((blocks c).stateMap x)`, bounded by the joint
normalization `Σ_c Σ_x tr ≤ 1` because dropping the sum over the other outcomes only removes
nonnegative terms. -/
def CQState.pointBlock {X C : Type*} [Fintype X] [Fintype C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (x : X) : CQState C nE where
  stateMap c := (blocks c).stateMap x
  weight_le_one := by
    calc ∑ c : C, ((blocks c).stateMap x).trace
        ≤ ∑ c : C, ∑ x' : X, ((blocks c).stateMap x').trace := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.single_le_sum
            (fun x' _ => ((blocks c).stateMap x').trace_nonneg) (Finset.mem_univ x)
      _ ≤ 1 := hjoint

@[simp] lemma CQState.pointBlock_stateMap {X C : Type*} [Fintype X] [Fintype C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) (x : X) (c : C) :
    (CQState.pointBlock blocks hjoint x).stateMap c = (blocks c).stateMap x := rfl

/-- **The flag-packed CQ state** ([142] Lemma 4, C̄-as-conditioning-flag construction).

Given a `C`-indexed family of CQ blocks over the classical register `X` with quantum side `E`
(dimension `nE`), the flag pack is the single CQ state over `X` with quantum register the
flag-augmented `C ⊗ E` (dimension `nE * |C|`) whose `x`-block is the block-diagonal
`Σ_c |c⟩⟨c| ⊗ (blocks c).stateMap x`. The joint normalization `Σ_c Σ_x tr ≤ 1` supplies the CQ
weight bound. Absorbing `C` into the quantum register is what lets a leftover-hashing lemma with a
single reference `σ` on the quantum side compute a jointly-`C`-conditioned entropy. -/
def CQState.flagPack {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) :
    CQState X (nE * Fintype.card C) where
  stateMap x := (CQState.pointBlock blocks hjoint x).toJointDensity
  weight_le_one := by
    have hx : ∀ x : X,
        ((CQState.pointBlock blocks hjoint x).toJointDensity).trace
          = ∑ c : C, ((blocks c).stateMap x).trace := by
      intro x
      rw [CQState.toJointDensity_trace_eq_sum]
      rfl
    calc ∑ x : X, ((CQState.pointBlock blocks hjoint x).toJointDensity).trace
        = ∑ x : X, ∑ c : C, ((blocks c).stateMap x).trace := by
          exact Finset.sum_congr rfl (fun x _ => hx x)
      _ = ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace := Finset.sum_comm
      _ ≤ 1 := hjoint

@[simp] lemma CQState.flagPack_stateMap {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C]
    {nE : ℕ} (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) (x : X) :
    (CQState.flagPack blocks hjoint).stateMap x = (CQState.pointBlock blocks hjoint
        x).toJointDensity :=
  rfl

/-- Flag packing depends only on the family, not on the joint-normalization proof: equal families
give equal flag packs. -/
lemma CQState.flagPack_congr {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C] {nE : ℕ}
    {blocks blocks' : C → CQState X nE} (hb : blocks = blocks')
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (hjoint' : ∑ c : C, ∑ x : X, ((blocks' c).stateMap x).trace ≤ 1) :
    CQState.flagPack blocks hjoint = CQState.flagPack blocks' hjoint' := by
  subst hb
  rfl

/-- The zero CQ state: every block is the zero sub-density operator. Used to zero out flag blocks
outside an event `Ω` while preserving subnormalization. -/
def CQState.zeroCQ {X : Type*} [Fintype X] {nE : ℕ} : CQState X nE where
  stateMap _ := 0
  weight_le_one := by
    have hz : (0 : SubDensityOp nE).trace = 0 := by
      change (0 : Matrix (Fin nE) (Fin nE) ℂ).trace.re = 0
      simp
    simp [hz]

@[simp] lemma CQState.zeroCQ_stateMap {X : Type*} [Fintype X] {nE : ℕ} (x : X) :
    (CQState.zeroCQ (X := X) (nE := nE)).stateMap x = 0 := rfl

/-- **The flag-packed quantum marginal.** The CQ state over the flag register `C` whose `c`-block is
`(blocks c).quantumMarginal`. Its joint density is `Σ_c |c⟩⟨c| ⊗ ρ_E(c) = ρ_{C̄E}`, the quantum
marginal of the flag pack (`flagPack_quantumMarginal`). -/
def CQState.flagMarginal {X C : Type*} [Fintype X] [Fintype C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) :
    CQState C nE where
  stateMap c := (blocks c).quantumMarginal
  weight_le_one := by
    have hc : ∀ c : C, ((blocks c).quantumMarginal).trace = ∑ x : X, ((blocks c).stateMap x).trace
        := by
      intro c
      change ((blocks c).quantumMarginalOp).trace.re = _
      unfold CQState.quantumMarginalOp
      rw [Matrix.trace_sum, Complex.re_sum]
      rfl
    calc ∑ c : C, ((blocks c).quantumMarginal).trace
        = ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace := Finset.sum_congr rfl (fun c _ => hc c)
      _ ≤ 1 := hjoint

end InfoTheory.SmoothMinEntropy

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-!
## The block-diagonal packing engine `flagPackOp` and its linearity

`flagPackOp F` reindexes `Matrix.blockDiagonal F` (over the flag register `C`) into the
quantum-first flag-augmented register `Fin (nE * |C|)`, using the same reindexing equivalence as
`CQState.toJointDensity` so that the packed block of `flagPack` is `flagPackOp` of the per-flag
blocks (`flagPack_stateMap_toOp`). The engine is additive, real-scalar-linear, and preserves the
zero and the fiber-indicator structure — this is everything needed to commute packing past the
finite linear operations of the leftover-hashing extractor.
-/

/-- The reindexing equivalence packing `Fin nE × C` into `Fin (nE * |C|)`, quantum index first —
identical to the equivalence used by `CQState.toJointDensity` for the classical register `C`. -/
def packEquivC (nE : ℕ) (C : Type*) [Fintype C] : Fin nE × C ≃ Fin (nE * Fintype.card C) :=
  (Equiv.prodCongr (Equiv.refl (Fin nE)) (Fintype.equivFin C)).trans finProdFinEquiv

/-- **Block-diagonal packing of a flag-indexed operator family** into the flag-augmented register:
`F ↦ reindex (blockDiagonal F)`. This is the operator-level engine underlying `CQState.flagPack`. -/
def flagPackOp {C : Type*} [Fintype C] [DecidableEq C] {nE : ℕ} (F : C → Op nE) :
    Op (nE * Fintype.card C) :=
  Matrix.reindex (packEquivC nE C) (packEquivC nE C) (Matrix.blockDiagonal F)

lemma flagPackOp_zero {C : Type*} [Fintype C] [DecidableEq C] {nE : ℕ} :
    flagPackOp (0 : C → Op nE) = 0 := by
  unfold flagPackOp
  simp [Matrix.blockDiagonal_zero]

/-- Packing distributes over finite sums of operator families. -/
lemma flagPackOp_finsetSum {C ι : Type*} [Fintype C] [DecidableEq C] {nE : ℕ}
    (s : Finset ι) (G : ι → C → Op nE) :
    flagPackOp (fun c => ∑ i ∈ s, G i c) = ∑ i ∈ s, flagPackOp (fun c => G i c) := by
  unfold flagPackOp
  have hfun : (fun c => ∑ i ∈ s, G i c) = ∑ i ∈ s, (fun c => G i c) := by
    funext c
    rw [Finset.sum_apply]
  rw [hfun, ← Matrix.blockDiagonalAddMonoidHom_apply, map_sum]
  simp only [Matrix.blockDiagonalAddMonoidHom_apply]
  rw [← Matrix.coe_reindexLinearEquiv ℂ ℂ, map_sum]

/-- Packing commutes with scalar multiplication (real or complex scalars). -/
lemma flagPackOp_smul {C : Type*} [Fintype C] [DecidableEq C] {nE : ℕ}
    {R : Type*} [SMulZeroClass R ℂ] (r : R) (F : C → Op nE) :
    flagPackOp (fun c => r • F c) = r • flagPackOp F := by
  unfold flagPackOp
  have hfun : (fun c => r • F c) = r • F := rfl
  rw [hfun, Matrix.blockDiagonal_smul, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_smul]
  rfl

/-- Packing commutes with a flag-independent fiber indicator. -/
lemma flagPackOp_ite {C : Type*} [Fintype C] [DecidableEq C] {nE : ℕ}
    (p : Prop) [Decidable p] (F : C → Op nE) :
    flagPackOp (fun c => if p then F c else 0) = if p then flagPackOp F else 0 := by
  by_cases h : p
  · simp only [if_pos h]
  · simp only [if_neg h]
    exact flagPackOp_zero

lemma flagPackOp_apply_eq_reindex {C : Type*} [Fintype C] [DecidableEq C] {nE : ℕ}
    (F : C → Op nE) :
    flagPackOp F = Matrix.reindex (packEquivC nE C) (packEquivC nE C) (Matrix.blockDiagonal F) :=
  rfl

/-- The packed block of `flagPack` is `flagPackOp` of the per-flag blocks. -/
lemma flagPack_stateMap_toOp {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) (x : X) :
    ((CQState.flagPack blocks hjoint).stateMap x).toOp
      = flagPackOp (fun c => ((blocks c).stateMap x).toOp) := by
  change ((CQState.pointBlock blocks hjoint x).toJointDensity).toOp = _
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  rfl

/-!
## The flag-packed trace, quantum marginal, and extractor commutations
-/

/-- The joint trace of a flag pack is the total joint normalization `Σ_c Σ_x tr`. -/
lemma flagPack_toJointDensity_trace {X C : Type*} [Fintype X] [DecidableEq X] [Fintype C]
    [DecidableEq C] {nE : ℕ} (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) :
    (CQState.flagPack blocks hjoint).toJointDensity.trace
      = ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace := by
  rw [CQState.toJointDensity_trace_eq_sum]
  have hx : ∀ x : X, ((CQState.flagPack blocks hjoint).stateMap x).trace
      = ∑ c : C, ((blocks c).stateMap x).trace := by
    intro x
    change ((CQState.pointBlock blocks hjoint x).toJointDensity).trace = _
    rw [CQState.toJointDensity_trace_eq_sum]
    rfl
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_comm]

/-- The quantum marginal operator of a flag pack is the packed operator of per-flag marginals. -/
lemma flagPack_quantumMarginalOp {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) :
    (CQState.flagPack blocks hjoint).quantumMarginalOp
      = flagPackOp (fun c => (blocks c).quantumMarginalOp) := by
  unfold CQState.quantumMarginalOp
  simp_rw [flagPack_stateMap_toOp]
  rw [← flagPackOp_finsetSum]

/-- **The flag-packed quantum marginal is `ρ_{C̄E}`.** The quantum marginal of the flag pack equals
the joint density of the per-block-marginal CQ state `flagMarginal` — the block-diagonal
`Σ_c |c⟩⟨c| ⊗ ρ_E(c)`. -/
lemma flagPack_quantumMarginal {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) :
    (CQState.flagPack blocks hjoint).quantumMarginal
      = (CQState.flagMarginal blocks hjoint).toJointDensity := by
  apply SubDensityOp.ext
  change (CQState.flagPack blocks hjoint).quantumMarginalOp = _
  rw [flagPack_quantumMarginalOp, CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  rfl

/-- The seed-visible weighted block of a flag pack is the packed operator of the per-block
weighted blocks: `seedPerSeedWeightedOp` commutes with flag packing. -/
lemma flagPack_seedPerSeedWeightedOp {S X Z C : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] [Fintype C] [DecidableEq C] {nE : ℕ}
    (H : QuantumHashFamily S X Z) (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) (s : S) (z : Z) :
    seedPerSeedWeightedOp H (CQState.flagPack blocks hjoint) s z
      = flagPackOp (fun c => seedPerSeedWeightedOp H (blocks c) s z) := by
  unfold seedPerSeedWeightedOp
  rw [flagPackOp_smul]
  congr 1
  rw [flagPackOp_finsetSum]
  apply Finset.sum_congr rfl
  intro x _
  rw [flagPackOp_ite]
  by_cases hp : H.hash s x = z
  · rw [if_pos hp, if_pos hp, flagPack_stateMap_toOp]
  · rw [if_neg hp, if_neg hp]

/-- **The seed-key extractor commutes with flag packing.** Applying a hash family to the classical
register of a flag pack equals flag-packing the per-block extractor outputs. The extractor acts by a
`1/|S|`-scaled fiber sum of the input blocks, and both operations commute with the block-diagonal
flag embedding. -/
lemma flagPack_seedKeyExtractorOutput {S X Z C : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] [Fintype C] [DecidableEq C] {nE : ℕ}
    (H : QuantumHashFamily S X Z) (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (hjoint' : ∑ c : C, ∑ sz : S × Z,
      ((seedKeyExtractorOutputState H (blocks c)).stateMap sz).trace ≤ 1) :
    seedKeyExtractorOutputState H (CQState.flagPack blocks hjoint)
      = CQState.flagPack (fun c => seedKeyExtractorOutputState H (blocks c)) hjoint' := by
  apply CQState.ext_stateMap
  funext sz
  apply SubDensityOp.ext
  obtain ⟨s, z⟩ := sz
  change seedPerSeedWeightedOp H (CQState.flagPack blocks hjoint) s z
    = ((CQState.flagPack (fun c => seedKeyExtractorOutputState H (blocks c)) hjoint').stateMap (s,
        z)).toOp
  rw [flagPack_seedPerSeedWeightedOp, flagPack_stateMap_toOp]
  rfl

/-- **The ideal uniform target commutes with flag packing.** The seed-visible uniform state built on
the flag-packed quantum marginal `ρ_{C̄E}` equals the flag pack of the per-block uniform targets. -/
lemma flagPack_seedUniformOutput {S Z X C : Type*} [Fintype S] [Nonempty S] [Fintype Z] [Nonempty Z]
    [Fintype X] [Fintype C] [DecidableEq C] {nE : ℕ}
    (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (hjoint' : ∑ c : C, ∑ sz : S × Z,
      ((seedUniformOutputState (S := S) (Z := Z) (blocks c).quantumMarginal).stateMap sz).trace ≤ 1)
          :
    seedUniformOutputState (S := S) (Z := Z) (CQState.flagPack blocks hjoint).quantumMarginal
      = CQState.flagPack (fun c => seedUniformOutputState (S := S) (Z := Z)
          (blocks c).quantumMarginal) hjoint' := by
  apply CQState.ext_stateMap
  funext sz
  apply SubDensityOp.ext
  obtain ⟨s, z⟩ := sz
  rw [flagPack_stateMap_toOp]
  have hL : ((seedUniformOutputState (S := S) (Z := Z)
        (CQState.flagPack blocks hjoint).quantumMarginal).stateMap (s, z)).toOp
      = ((1 / (Fintype.card (S × Z) : ℝ) : ℝ) : ℂ) •
          (CQState.flagPack blocks hjoint).quantumMarginalOp :=
    uniformOutput_stateMap_toOp (Z := S × Z) (CQState.flagPack blocks hjoint).quantumMarginal (s, z)
  rw [hL, flagPack_quantumMarginalOp]
  have hR : (fun c => ((seedUniformOutputState (S := S) (Z := Z)
        (blocks c).quantumMarginal).stateMap (s, z)).toOp)
      = (fun c => ((1 / (Fintype.card (S × Z) : ℝ) : ℝ) : ℂ) • (blocks c).quantumMarginalOp) := by
    funext c
    exact uniformOutput_stateMap_toOp (Z := S × Z) (blocks c).quantumMarginal (s, z)
  rw [hR, flagPackOp_smul]

/-- The total weight of a seed-key extractor output equals the input CQ state's total weight. -/
lemma sum_seedKeyExtractorOutputState_trace {S X Z : Type*} [Fintype S] [Fintype X] [Fintype Z]
    [DecidableEq Z] {nE : ℕ} (H : QuantumHashFamily S X Z) (ρ : CQState X nE) :
    ∑ sz : S × Z, ((seedKeyExtractorOutputState H ρ).stateMap sz).trace
      = ∑ x : X, (ρ.stateMap x).trace := by
  change ∑ sz : S × Z, (seedPerSeedWeightedOp H ρ sz.1 sz.2).trace.re = _
  rw [← Complex.re_sum, ← Matrix.trace_sum, sum_seedPerSeedWeightedOp_eq_quantumMarginalOp]
  unfold CQState.quantumMarginalOp
  rw [Matrix.trace_sum, Complex.re_sum]
  rfl

/-- The total weight of a seed-visible uniform target equals the underlying operator's weight. -/
lemma sum_seedUniformOutputState_trace {S Z : Type*} [Fintype S] [Nonempty S] [Fintype Z]
    [Nonempty Z] {nE : ℕ} (σ : SubDensityOp nE) :
    ∑ sz : S × Z, ((seedUniformOutputState (S := S) (Z := Z) σ).stateMap sz).trace = σ.trace := by
  classical
  rw [← uniformCQState_toJointDensity_trace (X := S × Z) σ, CQState.toJointDensity_trace_eq_sum]
  rfl

/-- The trace of a quantum marginal is the total weight of the CQ state. -/
lemma quantumMarginal_trace_eq_sum {X : Type*} [Fintype X] {nE : ℕ} (ρ : CQState X nE) :
    ρ.quantumMarginal.trace = ∑ x : X, (ρ.stateMap x).trace := by
  change (ρ.quantumMarginalOp).trace.re = _
  unfold CQState.quantumMarginalOp
  rw [Matrix.trace_sum, Complex.re_sum]
  rfl

/-!
## Flag-controlled classical coarsening contracts generalized trace distance

The data-processing step of the union-form leftover-hashing proof. A *flag-controlled* relabel
family `g : C → X → Y` applies a different classical map `g c` on each flag block `c`; on the flag
pack this is realised by coarsening each block before packing. Because the trace-norm of a
flag-packed difference is the double sum `Σ_x Σ_c ‖·‖₁` (block-diagonal in both the classical
register `X` and the flag `C`), and the total trace is preserved per flag block, the standard
per-block coarsening contraction (`CQState.sum_traceNorm_coarsen_stateMap_diff_le`) lifts to the
flag-packed states.
-/

/-- Coarsening each flag block preserves the joint normalization of the flag pack. -/
lemma flagPack_coarsen_weight_le_one {X Y C : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype C] {nE : ℕ} (g : C → X → Y) (blocks : C → CQState X nE)
    (hjoint : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1) :
    ∑ c : C, ∑ y : Y, ((CQState.coarsen (g c) (blocks c)).stateMap y).trace ≤ 1 := by
  refine le_trans (le_of_eq ?_) hjoint
  apply Finset.sum_congr rfl
  intro c _
  exact CQState.sum_coarsen_stateMap_trace_eq (g c) (blocks c)

/-- **The flag-packed trace norm is a double sum.** The trace norm of a flag-packed difference is
the sum, over the classical register `X` and the flag register `C`, of the per-block trace-norm
differences — block-diagonal both in `X` (via `toJointDensity`) and in `C` (via the flag). -/
lemma traceNorm_flagPack_diff_eq_sum {X C : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ} [NeZero nE]
    (blocks blocks' : C → CQState X nE)
    (hj : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (hj' : ∑ c : C, ∑ x : X, ((blocks' c).stateMap x).trace ≤ 1) :
    haveI : NeZero (nE * Fintype.card C) :=
      ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
    traceNorm ((CQState.flagPack blocks hj).toJointDensity.toOp
        - (CQState.flagPack blocks' hj').toJointDensity.toOp)
      = ∑ x : X, ∑ c : C,
          traceNorm (((blocks c).stateMap x).toOp - ((blocks' c).stateMap x).toOp) := by
  haveI : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (nE * Fintype.card C) :=
    ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
  rw [traceNorm_joint_diff_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  change traceNorm ((CQState.pointBlock blocks hj x).toJointDensity.toOp
      - (CQState.pointBlock blocks' hj' x).toJointDensity.toOp) = _
  rw [traceNorm_joint_diff_eq_sum]
  rfl

/-- **Flag-controlled classical coarsening contracts generalized trace distance.**

For a flag-controlled classical relabel family `g : C → X → Y` (a distinct classical map on each
flag block), coarsening each block before flag packing contracts the generalized trace distance:

  `D(pack (coarsen g blocks), pack (coarsen g blocks')) ≤ D(pack blocks, pack blocks')`.

This is the data-processing inequality of [142] Lemma 4's union form, where the paper's controlled
channel `ℰ` reads the announcement register `C̄` — here absorbed as a quantum-side flag — and
applies
a `C̄`-dependent classical relabel. It is proved by reducing the flag-packed trace norm to the
double
sum `Σ_x Σ_c ‖·‖₁`, applying the per-block coarsening contraction of
`CQState.sum_traceNorm_coarsen_stateMap_diff_le`, and observing that coarsening preserves the joint
trace per flag block. -/
theorem traceDistanceGen_flagControlledCoarsen_le {X Y C : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype C] [DecidableEq C] [Nonempty C] {nE : ℕ} [NeZero nE]
    (blocks blocks' : C → CQState X nE) (g : C → X → Y)
    (hj : ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace ≤ 1)
    (hj' : ∑ c : C, ∑ x : X, ((blocks' c).stateMap x).trace ≤ 1) :
    haveI : NeZero (nE * Fintype.card C) :=
      ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
    haveI : NeZero ((nE * Fintype.card C) * Fintype.card Y) :=
      ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero) Fintype.card_ne_zero⟩
    haveI : NeZero ((nE * Fintype.card C) * Fintype.card X) :=
      ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero) Fintype.card_ne_zero⟩
    traceDistanceGen
        (CQState.flagPack (fun c => CQState.coarsen (g c) (blocks c))
            (flagPack_coarsen_weight_le_one g blocks hj)).toJointDensity.toOp
        (CQState.flagPack (fun c => CQState.coarsen (g c) (blocks' c))
            (flagPack_coarsen_weight_le_one g blocks' hj')).toJointDensity.toOp ≤
      traceDistanceGen
        (CQState.flagPack blocks hj).toJointDensity.toOp
        (CQState.flagPack blocks' hj').toJointDensity.toOp := by
  haveI : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (nE * Fintype.card C) :=
    ⟨Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero⟩
  haveI : NeZero ((nE * Fintype.card C) * Fintype.card Y) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero) Fintype.card_ne_zero⟩
  haveI : NeZero ((nE * Fintype.card C) * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne nE) Fintype.card_ne_zero) Fintype.card_ne_zero⟩
  apply traceDistanceGen_le_of_traceNorm_sub_le_of_trace_re_sub_eq
  · rw [traceNorm_flagPack_diff_eq_sum, traceNorm_flagPack_diff_eq_sum,
      Finset.sum_comm, Finset.sum_comm (γ := X)]
    apply Finset.sum_le_sum
    intro c _
    exact CQState.sum_traceNorm_coarsen_stateMap_diff_le (g c) (blocks c) (blocks' c)
  · have hcoarsenL : (CQState.flagPack (fun c => CQState.coarsen (g c) (blocks c))
          (flagPack_coarsen_weight_le_one g blocks hj)).toJointDensity.toOp.trace.re
        = ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace := by
      have h := flagPack_toJointDensity_trace (fun c => CQState.coarsen (g c) (blocks c))
        (flagPack_coarsen_weight_le_one g blocks hj)
      refine h.trans ?_
      apply Finset.sum_congr rfl
      intro c _
      exact CQState.sum_coarsen_stateMap_trace_eq (g c) (blocks c)
    have hcoarsenL' : (CQState.flagPack (fun c => CQState.coarsen (g c) (blocks' c))
          (flagPack_coarsen_weight_le_one g blocks' hj')).toJointDensity.toOp.trace.re
        = ∑ c : C, ∑ x : X, ((blocks' c).stateMap x).trace := by
      have h := flagPack_toJointDensity_trace (fun c => CQState.coarsen (g c) (blocks' c))
        (flagPack_coarsen_weight_le_one g blocks' hj')
      refine h.trans ?_
      apply Finset.sum_congr rfl
      intro c _
      exact CQState.sum_coarsen_stateMap_trace_eq (g c) (blocks' c)
    have hRblocks : (CQState.flagPack blocks hj).toJointDensity.toOp.trace.re
        = ∑ c : C, ∑ x : X, ((blocks c).stateMap x).trace :=
      flagPack_toJointDensity_trace blocks hj
    have hRblocks' : (CQState.flagPack blocks' hj').toJointDensity.toOp.trace.re
        = ∑ c : C, ∑ x : X, ((blocks' c).stateMap x).trace :=
      flagPack_toJointDensity_trace blocks' hj'
    rw [Complex.sub_re, Complex.sub_re, hcoarsenL, hcoarsenL', hRblocks, hRblocks']

end InfoTheory.QuantumLHL

end -- noncomputable section
