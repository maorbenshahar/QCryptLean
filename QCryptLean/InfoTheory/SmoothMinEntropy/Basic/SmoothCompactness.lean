import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.PovmCompactness
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.SmoothPartialTrace
import QCryptLean.Quantum.Metrics.TraceNormIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact smooth-entropy witnesses

The CQ purified-distance ball is compact. For positive-definite references, a bounded signed real
entropy objective attains its supremum. A positive canonical smooth floor therefore has an exact
exponential feasibility witness; when the ball reaches zero, the zero state provides the witness.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Entrywise topology on `CQState X n`, induced by the map sending a CQ state to its family of
block matrices `x ↦ (ρ.stateMap x).toOp : X → Op n` (with the Pi topology of the matrix entrywise
topology).  This mirrors `instTopologicalSpaceDensityOp`. -/
noncomputable instance instTopologicalSpaceCQState
    {X : Type*} [Fintype X] {n : ℕ} : TopologicalSpace (CQState X n) :=
  TopologicalSpace.induced
    (fun ρ : CQState X n => (fun x => (ρ.stateMap x).toOp : X → Op n)) inferInstance

/-! ## Ambient compactness of `CQState`

The entrywise topology on `CQState X n` is the topology induced by the block-matrix
coordinate map `cqIncl : τ ↦ (x ↦ (τ.stateMap x).toOp)`.  Its range is the closed set of
PSD block families of total real trace at most one, which sits inside a compact entry box;
hence the whole space is compact (`cqState_univ_isCompact`).  This mirrors
`povmFeasibleHerm_isCompact`. -/

/-- The block-matrix coordinate map underlying `instTopologicalSpaceCQState`. -/
def cqIncl {X : Type*} [Fintype X] {n : ℕ} (τ : CQState X n) : X → Op n :=
  fun x => (τ.stateMap x).toOp

/-- `cqIncl` exhibits `instTopologicalSpaceCQState` as an induced topology. -/
lemma isInducing_cqIncl {X : Type*} [Fintype X] {n : ℕ} :
    Topology.IsInducing (cqIncl : CQState X n → (X → Op n)) := ⟨rfl⟩

/-- The block coordinate `τ ↦ (τ.stateMap x).toOp` is continuous. -/
lemma continuous_cqIncl_apply {X : Type*} [Fintype X] {n : ℕ} (x : X) :
    Continuous (fun τ : CQState X n => (τ.stateMap x).toOp) :=
  (continuous_apply x).comp isInducing_cqIncl.continuous

/-- The range of `cqIncl` is exactly the set of PSD block families whose total real trace is
at most one. -/
lemma range_cqIncl {X : Type*} [Fintype X] {n : ℕ} :
    Set.range (cqIncl : CQState X n → (X → Op n)) =
      Set.ofPred (fun M : X → Op n => (∀ x, (M x).PosSemidef) ∧ ∑ x, (M x).trace.re ≤ 1) := by
  ext M
  constructor
  · rintro ⟨τ, rfl⟩
    refine ⟨fun x => posSemidefOp_implies_mathlib (τ.stateMap x).toPosSemidefOp, ?_⟩
    simpa [cqIncl, SubDensityOp.trace] using τ.weight_le_one
  · rintro ⟨hPSD, hsum⟩
    have htr_nonneg : ∀ x : X, 0 ≤ (M x).trace.re := fun x =>
      (Complex.nonneg_iff.mp (hPSD x).trace_nonneg).1
    have htr_le_one : ∀ x : X, (M x).trace.re ≤ 1 := fun x =>
      le_trans (Finset.single_le_sum (fun y _ => htr_nonneg y) (Finset.mem_univ x)) hsum
    refine ⟨⟨fun x => ⟨⟨⟨M x, (hPSD x).isHermitian⟩,
        fun v => posSemidef_re_quadraticForm_nonneg (hPSD x) v⟩, htr_le_one x⟩, ?_⟩, ?_⟩
    · simpa [SubDensityOp.trace] using hsum
    · funext x; rfl

/-- **Ambient compactness of `CQState X n`.**  In the entrywise topology the whole space is
compact: its image under `cqIncl` is the closed set of PSD block families with total real
trace at most one, contained in a compact entry box.  This mirrors
`povmFeasibleHerm_isCompact`. -/
lemma cqState_univ_isCompact {X : Type*} [Fintype X] {n : ℕ} :
    IsCompact (Set.univ : Set (CQState X n)) := by
  classical
  rw [isInducing_cqIncl.isCompact_iff, Set.image_univ, range_cqIncl]
  have hBox : IsCompact (Set.univ.pi (fun _ : X =>
      Set.univ.pi (fun _ : Fin n =>
        Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1))) : Set (X → Op n)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ =>
      isCompact_univ_pi (fun _ => ProperSpace.isCompact_closedBall (0 : ℂ) 1)))
  refine hBox.of_isClosed_subset ?_ ?_
  · -- closedness of the PSD / trace-bounded family
    have h_psd : ∀ x : X, IsClosed (Set.ofPred (fun M : X → Op n => (M x).PosSemidef)) := by
      intro x
      simpa only [Set.preimage, Set.mem_ofPred_eq] using
        IsClosed.preimage (f := fun M : X → Op n => M x)
          (continuous_apply x) (isClosed_setOf_posSemidef (n := n))
    have h_trace : IsClosed (Set.ofPred (fun M : X → Op n => ∑ x, (M x).trace.re ≤ 1)) := by
      apply isClosed_le ?_ continuous_const
      exact continuous_finsetSum _ (fun x _ =>
        Complex.continuous_re.comp (continuous_apply x).matrix_trace)
    have hEq : Set.ofPred (fun M : X → Op n => (∀ x, (M x).PosSemidef) ∧ ∑ x, (M x).trace.re ≤ 1) =
        (⋂ x, Set.ofPred (fun M : X → Op n => (M x).PosSemidef)) ∩
          Set.ofPred (fun M : X → Op n => ∑ x, (M x).trace.re ≤ 1) := by
      ext M; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [hEq]
    exact (isClosed_iInter h_psd).inter h_trace
  · -- containment in the compact entry box
    intro M hM x _ i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    have htr_nonneg : ∀ y : X, 0 ≤ (M y).trace.re := fun y =>
      (Complex.nonneg_iff.mp (hM.1 y).trace_nonneg).1
    have htr : (M x).trace.re ≤ 1 :=
      le_trans (Finset.single_le_sum (fun y _ => htr_nonneg y) (Finset.mem_univ x)) hM.2
    exact posSemidef_trace_le_one_entry_norm_le_one (hM.1 x) htr i j

/-- The joint-density block matrix `τ ↦ τ.toJointDensity.toOp` is continuous in the entrywise
topology: it is the block-diagonal of the (continuous) `cqIncl` coordinates, reindexed by a fixed
equivalence. -/
lemma continuous_cqState_toJointDensity_toOp
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} :
    Continuous (fun τ : CQState X n => τ.toJointDensity.toOp) := by
  simp only [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal, Matrix.reindex_apply]
  exact (isInducing_cqIncl.continuous.matrix_blockDiagonal).matrix_submatrix _ _

/-- **Continuity of the CQ purified distance.**

`τ ↦ P(ρ, τ)` is continuous in the entrywise topology.  Instead of relying on continuity of the
Uhlmann/generalized fidelity (operator square root), we use that the purified distance is a metric
on CQ states (`CQState.purifiedDistance_triangle`/`_symm`) and that it is squeezed by the continuous
generalized trace distance via the proved Fuchs–van-de-Graaf bound
`P ≤ √(2·D)` (`purifiedDistance_le_sqrt_two_mul_traceDistanceGen`).  The joint density
`τ ↦ τ.toJointDensity.toOp` is a continuous reindex of the block-diagonal of the `cqIncl`
coordinates (`continuous_cqState_toJointDensity_toOp`), so the squeezing majorant is continuous and
vanishes at the base point.  (Renner 2005 §5.5; Tomamichel 2016 §6.2.2.) -/
lemma continuous_cqState_purifiedDistance
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) :
    Continuous (fun τ : CQState X n => CQState.purifiedDistance ρ τ) := by
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have hJcont : Continuous (fun τ : CQState X n => τ.toJointDensity.toOp) :=
    continuous_cqState_toJointDensity_toOp
  rw [continuous_iff_continuousAt]
  intro τ₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  -- Squeezing majorant `g τ = √(2·D(Jτ, Jτ₀))`.
  have hg_cont : Continuous (fun τ : CQState X n =>
      Real.sqrt (2 * Quantum.Metrics.traceDistanceGen τ.toJointDensity.toOp
        τ₀.toJointDensity.toOp)) := by
    refine Real.continuous_sqrt.comp (continuous_const.mul ?_)
    unfold Quantum.Metrics.traceDistanceGen
    refine Continuous.add (continuous_const.mul ?_) (continuous_const.mul ?_)
    · exact Quantum.Metrics.traceNorm_continuous.comp (hJcont.sub continuous_const)
    · exact continuous_abs.comp (Complex.continuous_re.comp
        (hJcont.matrix_trace.sub continuous_const))
  have hg0 : Real.sqrt (2 * Quantum.Metrics.traceDistanceGen τ₀.toJointDensity.toOp
      τ₀.toJointDensity.toOp) = 0 := by
    rw [Quantum.Metrics.traceDistanceGen_self_zero]; simp
  refine squeeze_zero (fun τ => dist_nonneg) (fun τ => ?_) (hg0 ▸ hg_cont.tendsto τ₀)
  -- `dist (P ρ τ) (P ρ τ₀) = |P ρ τ - P ρ τ₀| ≤ P τ τ₀ ≤ √(2·D)`.
  rw [Real.dist_eq]
  have hrev : |CQState.purifiedDistance ρ τ - CQState.purifiedDistance ρ τ₀| ≤
      CQState.purifiedDistance τ τ₀ := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · have h := CQState.purifiedDistance_triangle ρ τ₀ τ
      have hs := CQState.purifiedDistance_symm τ₀ τ
      linarith
    · have h := CQState.purifiedDistance_triangle ρ τ τ₀
      linarith
  refine hrev.trans ?_
  unfold CQState.purifiedDistance
  exact purifiedDistance_le_sqrt_two_mul_traceDistanceGen τ.toJointDensity τ₀.toJointDensity

/-- **Compactness of the purified-distance ε-ball of CQ states.**

The ε-ball `{ρ̃ | P(ρ, ρ̃) ≤ ε}` is a closed subset of the compact ambient `CQState X n`
(Renner 2005 §5.5; Tomamichel 2016 §6.2.2).  Closedness follows from continuity of
`τ ↦ CQState.purifiedDistance ρ τ` (`continuous_cqState_purifiedDistance`), which is proved by
squeezing the purified distance between the continuous generalized trace distance via the
Fuchs–van-de-Graaf bound `P ≤ √(2·D)` (`purifiedDistance_le_sqrt_two_mul_traceDistanceGen`).
Ambient compactness is `cqState_univ_isCompact`, proved via the entrywise PSD box of
`PovmCompactness.lean`. -/
theorem cqEpsilonBall_isCompact
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (ε : ℝ) :
    IsCompact (Set.ofPred (fun τ : CQState X n => CQState.purifiedDistance ρ τ ≤ ε)) := by
  have hclosed : IsClosed (Set.ofPred (fun τ : CQState X n => CQState.purifiedDistance ρ τ ≤ ε)) :=
    isClosed_Iic.preimage (continuous_cqState_purifiedDistance ρ)
  exact cqState_univ_isCompact.of_isClosed_subset hclosed (Set.subset_univ _)

/-- For a Hermitian operator `H`, the trace norm scalar `‖H‖₁` dominates `H` in the
operator-semidefinite order: `H ≼ ‖H‖₁ · 1`.  Each eigenvalue `λᵢ` of `H` satisfies
`λᵢ ≤ |λᵢ| ≤ ∑ⱼ |λⱼ| = ‖H‖₁`, so `cfc (‖H‖₁ - ·) H = ‖H‖₁·1 - H` is PSD. -/
lemma opLe_traceNorm_smul_one_of_isHermitian {n : ℕ} [NeZero n] {H : Op n}
    (hH : H.IsHermitian) :
    opLe H ((Complex.ofReal (Quantum.Metrics.traceNorm H) : ℂ) • (1 : Op n)) := by
  apply Quantum.Operators.opLe_of_posSemidef_sub
  set c := Quantum.Metrics.traceNorm H with hc_def
  have h_eig_le : ∀ i, hH.eigenvalues i ≤ c := by
    intro i
    rw [hc_def, Quantum.Metrics.traceNorm_hermitian_eq H hH]
    calc hH.eigenvalues i ≤ |hH.eigenvalues i| := le_abs_self _
      _ ≤ ∑ j, |hH.eigenvalues j| :=
          Finset.single_le_sum (f := fun j => |hH.eigenvalues j|)
            (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      _ = Quantum.Metrics.traceNormHermitian H hH := rfl
  have h_spec : ∀ x ∈ spectrum ℝ H, 0 ≤ c - x := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i, rfl⟩; linarith [h_eig_le i]
  have h_eq : cfc (fun x : ℝ => c - x) H
      = (Complex.ofReal c : ℂ) • (1 : Op n) - H := by
    have hfg : (fun x : ℝ => c - x) = fun x => (fun _ : ℝ => c) x - id x := by ext x; simp
    rw [hfg, cfc_sub (fun _ => c) id H, cfc_const c H, cfc_id ℝ H]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  have h0 : (0 : Op n) ≤ cfc (fun x : ℝ => c - x) H := cfc_nonneg h_spec
  rw [h_eq] at h0
  simpa using Matrix.le_iff.mp h0

/-- **Continuity of `minFeasibleLambda` in the CQ state.**

With `σ ≻ 0`, the map `τ ↦ minFeasibleLambda τ σ` is continuous (Tomamichel 2016 §6.2.2).  The
proof uses a global two-sided Lipschitz bound in the block trace norms: for Löwner constant `C`
with `1 ⪯ C·σ`, `minFeasibleLambda τ σ ≤ minFeasibleLambda τ' σ + C · ∑ₓ ‖(τ.stateMap x).toOp
- (τ'.stateMap x).toOp‖₁`.  The right-hand side is continuous in the `cqIncl` coordinates
(`traceNorm_continuous`) and vanishes at `τ' = τ`, so `squeeze_zero` gives continuity. -/
lemma continuous_minFeasibleLambda_of_posDef
    {X : Type*} [Fintype X] {n : ℕ}
    (σ : SubDensityOp n) (hσ_pd : σ.toOp.PosDef) :
    Continuous (fun τ : CQState X n => minFeasibleLambda τ σ) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- Degenerate dimension `n = 0`: every scalar `t ≥ 0` is feasible, so
    -- `minFeasibleLambda · σ` is the constant `0`.
    subst hn
    have hconst : (fun τ : CQState X 0 => minFeasibleLambda τ σ) = fun _ => 0 := by
      funext τ
      have hset : Set.ofPred (isFeasible τ σ) = Set.Ici (0 : ℝ) := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_Ici, isFeasible]
        refine ⟨fun h => h.1, fun ht => ⟨ht, fun x v => ?_⟩⟩
        simp [quadraticForm, dotProduct]
      rw [minFeasibleLambda, hset, csInf_Ici]
    rw [hconst]; exact continuous_const
  · have : NeZero n := ⟨hn.ne'⟩
    -- A fixed Löwner constant `C ≥ 0` with `1 ⪯ C·σ` (from `σ ≻ 0`).
    obtain ⟨C, hC0, hC1⟩ :=
      Matrix.PosDef.exists_smul_opLe_of_posSemidef hσ_pd (Matrix.PosSemidef.one (n := Fin n))
    -- Scalar monotonicity of `t ↦ t·σ`.
    have hsmul_mono : ∀ a b : ℝ, a ≤ b →
        opLe ((Complex.ofReal a) • σ.toOp) ((Complex.ofReal b) • σ.toOp) := by
      intro a b hab v
      simp only [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_right hab (σ.pos_semidef v)
    -- Neg-invariance of the trace norm of a difference.
    have htn_symm : ∀ A B : Op n,
        Quantum.Metrics.traceNorm (A - B) = Quantum.Metrics.traceNorm (B - A) := by
      intro A B
      have hAB : A - B = (-1 : ℂ) • (B - A) := by rw [neg_one_smul, neg_sub]
      rw [hAB, Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]; simp
    -- Global Lipschitz estimate in the block coordinates.
    have hlip : ∀ τ τ' : CQState X n,
        minFeasibleLambda τ σ ≤ minFeasibleLambda τ' σ +
          (∑ x : X, Quantum.Metrics.traceNorm
            ((τ.stateMap x).toOp - (τ'.stateMap x).toOp)) * C := by
      intro τ τ'
      have hm'_nn : 0 ≤ minFeasibleLambda τ' σ := minFeasibleLambda_nonneg τ' σ
      have hs_nn : 0 ≤ ∑ x : X,
          Quantum.Metrics.traceNorm ((τ.stateMap x).toOp - (τ'.stateMap x).toOp) :=
        Finset.sum_nonneg (fun x _ => Quantum.Metrics.traceNorm_nonneg _)
      have hfeas : isFeasible τ σ (minFeasibleLambda τ' σ +
          (∑ x : X, Quantum.Metrics.traceNorm
            ((τ.stateMap x).toOp - (τ'.stateMap x).toOp)) * C) := by
        refine ⟨add_nonneg hm'_nn (mul_nonneg hs_nn hC0), fun x => ?_⟩
        set Hx := (τ.stateMap x).toOp - (τ'.stateMap x).toOp with hHx
        have hHx_herm : Hx.IsHermitian :=
          (τ.stateMap x).isHermitian.sub (τ'.stateMap x).isHermitian
        have htn_nn : 0 ≤ Quantum.Metrics.traceNorm Hx := Quantum.Metrics.traceNorm_nonneg _
        have htn_le_s : Quantum.Metrics.traceNorm Hx ≤
            ∑ y : X, Quantum.Metrics.traceNorm ((τ.stateMap y).toOp - (τ'.stateMap y).toOp) :=
          Finset.single_le_sum
            (f := fun y => Quantum.Metrics.traceNorm ((τ.stateMap y).toOp - (τ'.stateMap y).toOp))
            (fun y _ => Quantum.Metrics.traceNorm_nonneg _) (Finset.mem_univ x)
        have h1 := opLe_traceNorm_smul_one_of_isHermitian hHx_herm
        have h2 := opLe_smul_nonneg (A := (1 : Op n)) (B := (Complex.ofReal C) • σ.toOp) htn_nn hC1
        rw [smul_smul, ← Complex.ofReal_mul] at h2
        have hHx_bound : opLe Hx
            ((Complex.ofReal (Quantum.Metrics.traceNorm Hx * C)) • σ.toOp) := opLe_trans h1 h2
        have hbump : opLe ((Complex.ofReal (Quantum.Metrics.traceNorm Hx * C)) • σ.toOp)
            ((Complex.ofReal ((∑ y : X, Quantum.Metrics.traceNorm
              ((τ.stateMap y).toOp - (τ'.stateMap y).toOp)) * C)) • σ.toOp) :=
          hsmul_mono _ _ (mul_le_mul_of_nonneg_right htn_le_s hC0)
        have hHx_final := opLe_trans hHx_bound hbump
        have hfeas' := (isFeasible_minFeasibleLambda_of_posDef τ' σ hσ_pd).2 x
        have hsum := opLe_add hfeas' hHx_final
        have hLHS : (τ'.stateMap x).toOp + Hx = (τ.stateMap x).toOp := by rw [hHx]; abel
        have hRHS : (Complex.ofReal (minFeasibleLambda τ' σ)) • σ.toOp +
            (Complex.ofReal ((∑ y : X, Quantum.Metrics.traceNorm
              ((τ.stateMap y).toOp - (τ'.stateMap y).toOp)) * C)) • σ.toOp =
            (Complex.ofReal (minFeasibleLambda τ' σ +
              (∑ y : X, Quantum.Metrics.traceNorm
                ((τ.stateMap y).toOp - (τ'.stateMap y).toOp)) * C)) • σ.toOp := by
          rw [← add_smul, ← Complex.ofReal_add]
        rw [hLHS, hRHS] at hsum
        exact hsum
      exact minFeasibleLambda_le_of_isFeasible τ σ hfeas
    -- Continuity from the two-sided Lipschitz bound.
    rw [continuous_iff_continuousAt]
    intro τ₀
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    have hmaj_cont : Continuous (fun τ : CQState X n =>
        (∑ x : X, Quantum.Metrics.traceNorm
          ((τ.stateMap x).toOp - (τ₀.stateMap x).toOp)) * C) := by
      refine (continuous_finsetSum _ (fun x _ => ?_)).mul continuous_const
      exact Quantum.Metrics.traceNorm_continuous.comp
        ((continuous_cqIncl_apply x).sub continuous_const)
    have htend : Filter.Tendsto (fun τ : CQState X n =>
        (∑ x : X, Quantum.Metrics.traceNorm
          ((τ.stateMap x).toOp - (τ₀.stateMap x).toOp)) * C) (nhds τ₀) (nhds 0) := by
      have h0 := hmaj_cont.tendsto τ₀
      simpa [sub_self, Quantum.Channels.traceNorm_zero] using h0
    refine squeeze_zero (fun τ => dist_nonneg) (fun τ => ?_) htend
    rw [Real.dist_eq, abs_sub_le_iff]
    refine ⟨by linarith [hlip τ τ₀], ?_⟩
    have h := hlip τ₀ τ
    have hsymm : (∑ x : X, Quantum.Metrics.traceNorm
          ((τ₀.stateMap x).toOp - (τ.stateMap x).toOp)) =
        ∑ x : X, Quantum.Metrics.traceNorm ((τ.stateMap x).toOp - (τ₀.stateMap x).toOp) :=
      Finset.sum_congr rfl (fun x _ => htn_symm _ _)
    rw [hsymm] at h
    linarith [h]

/-- **Positive total weight on the smoothing ε-ball.**

If the smooth min-entropy optimization set is bounded above (with `σ ≻ 0` and `0 < ε`), then
the purified-distance ε-ball contains no zero-weight (hence no zero) state — equivalently
`tr ρ > ε²` — so every `τ` in the ball has strictly positive total weight.  If `tr ρ ≤ ε²`,
scaling small witnesses toward zero produces ball states with arbitrarily large min-entropy,
contradicting `BddAbove` (`smoothedSetReal_not_bddAbove_of_weight_le_eps_sq_of_posDef`); hence
`ε² < tr ρ`, whence the explicit `purifiedDistanceWeightFloor` is a positive lower bound on the
total weight of every ball member.

The hypothesis `0 < ε` is necessary: at `ε = 0` the ball collapses to `{ρ}` and the statement
fails for `ρ` the zero CQ state.  (Renner 2005 §5.5; Tomamichel 2016 §6.2.2.) -/
lemma weight_pos_on_ball_of_bddAboveReal
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ_pd : σ.toOp.PosDef) (ε : ℝ) (hε_pos : 0 < ε)
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ σ)))
    {τ : CQState X n} (hτ : CQState.purifiedDistance ρ τ ≤ ε) :
    0 < ∑ x : X, (τ.stateMap x).trace := by
  -- Boundedness of the smoothed set forces `ε² < weight(ρ)`.
  have hgt : ε ^ 2 < ∑ x : X, (ρ.stateMap x).trace := by
    by_contra hle
    push Not at hle
    exact smoothedSetReal_not_bddAbove_of_weight_le_eps_sq_of_posDef ρ σ hσ_pd ε hε_pos hle hbdd
  -- The explicit purified-distance weight floor is then a positive lower bound on `τ`'s weight.
  have hfloor_pos : 0 < purifiedDistanceWeightFloor ε (∑ x : X, (ρ.stateMap x).trace) :=
    purifiedDistanceWeightFloor_pos (le_of_lt hε_pos) ρ.weight_le_one hgt
  have hfloor_le : purifiedDistanceWeightFloor ε (∑ x : X, (ρ.stateMap x).trace) ≤
      ∑ x : X, (τ.stateMap x).trace :=
    CQState.sum_stateMap_trace_ge_purifiedDistanceWeightFloor (le_of_lt hε_pos) hgt hτ
  linarith

/-- **Continuity of the min-entropy objective on the ε-ball (finite-supremum case).**

With `σ ≻ 0` and a finite smoothing supremum (`BddAbove`), `τ ↦ conditionalMinEntropyReal τ σ` is
continuous on the purified-distance ε-ball (Tomamichel 2016 §6.2.2).  Two cases:
* `0 < ε`: `continuous_minFeasibleLambda_of_posDef` (global Lipschitz in block trace norms) gives
  continuity of `τ ↦ minFeasibleLambda τ σ`; `BddAbove` forces a positive total-weight floor on
  the ball (`weight_pos_on_ball_of_bddAboveReal`), keeping `minFeasibleLambda` strictly positive, so
  `conditionalMinEntropyReal = -log(minFeasibleLambda)/log 2` is continuous there.
* `ε ≤ 0`: the purified distance is non-negative, so the ball collapses to `{ρ}`; the objective is
  constant on it, hence trivially continuous. -/
theorem continuousOn_conditionalMinEntropyReal_of_bddAbove
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : SubDensityOp n) (hσ_pd : σ.toOp.PosDef) (ε : ℝ)
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ σ))) :
    ContinuousOn (fun τ : CQState X n => conditionalMinEntropyReal τ σ)
      (Set.ofPred (fun τ : CQState X n => CQState.purifiedDistance ρ τ ≤ ε)) := by
  by_cases hε_pos : 0 < ε
  · -- `conditionalMinEntropyReal τ σ = -log (minFeasibleLambda τ σ) / log 2`.
    have hg_cont : Continuous (fun τ : CQState X n => minFeasibleLambda τ σ) :=
      continuous_minFeasibleLambda_of_posDef σ hσ_pd
    -- `minFeasibleLambda` is strictly positive on the ball (positive weight + `σ ≻ 0`).
    have hpos : ∀ τ ∈ Set.ofPred (fun τ : CQState X n => CQState.purifiedDistance ρ τ ≤ ε),
        0 < minFeasibleLambda τ σ := by
      intro τ hτ
      exact minFeasibleLambda_pos_of_posDef_of_weight_pos τ σ hσ_pd
        (weight_pos_on_ball_of_bddAboveReal ρ σ hσ_pd ε hε_pos hbdd hτ)
    -- `log ∘ minFeasibleLambda` is continuous on the ball (image avoids `0`).
    have hlog : ContinuousOn (fun τ : CQState X n => Real.log (minFeasibleLambda τ σ))
        (Set.ofPred (fun τ : CQState X n => CQState.purifiedDistance ρ τ ≤ ε)) := by
      refine Real.continuousOn_log.comp hg_cont.continuousOn ?_
      intro τ hτ
      exact Set.mem_compl_singleton_iff.mpr (hpos τ hτ).ne'
    -- Finish: negate and divide by the constant `log 2`.
    exact hlog.neg.div_const (Real.log 2)
  · -- `ε ≤ 0`: the ball forces `P(ρ, τ) = 0`, so the objective is constant on it.
    push Not at hε_pos
    have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
    have : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
    have heqon : Set.EqOn (fun τ : CQState X n => conditionalMinEntropyReal τ σ)
        (fun _ : CQState X n => conditionalMinEntropyReal ρ σ)
        (Set.ofPred (fun τ : CQState X n => CQState.purifiedDistance ρ τ ≤ ε)) := by
      intro τ hτ
      simp only [Set.mem_ofPred_eq] at hτ
      have hP_nn : 0 ≤ CQState.purifiedDistance ρ τ := by
        unfold CQState.purifiedDistance
        exact purifiedDistance_nonneg ρ.toJointDensity τ.toJointDensity
      have hP_zero : CQState.purifiedDistance ρ τ = 0 :=
        le_antisymm (le_trans hτ hε_pos) hP_nn
      have hJoint : ρ.toJointDensity = τ.toJointDensity :=
        (purifiedDistance_eq_zero_iff ρ.toJointDensity τ.toJointDensity).mp hP_zero
      exact (conditionalMinEntropyReal_congr_toJointDensity σ hJoint).symm
    exact continuousOn_const.congr heqon

/-- The image of the min-entropy objective over the ε-ball is exactly the smooth min-entropy
optimization set.  This is the definitional unfolding of `isInSmoothedSetReal`. -/
lemma conditionalMinEntropyReal_image_epsilonBall_eq
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : SubDensityOp n) (ε : ℝ) :
    (fun τ : CQState X n => conditionalMinEntropyReal τ σ) ''
        (Set.ofPred (fun τ : CQState X n => CQState.purifiedDistance ρ τ ≤ ε))
      = Set.ofPred (isInSmoothedSetReal ε ρ σ) := by
  ext h
  simp only [Set.mem_image, Set.mem_ofPred_eq, isInSmoothedSetReal]
  constructor
  · rintro ⟨τ, hd, hval⟩
    exact ⟨τ, hval.symm, hd⟩
  · rintro ⟨τ, hval, hd⟩
    exact ⟨τ, hd, hval.symm⟩

/-- **Attainment of the smooth min-entropy supremum.**

When the smooth min-entropy optimization set is bounded above (equivalently, the supremum is a
genuine finite maximum rather than the unbounded `sSup = 0` sentinel), the defining supremum
`smoothMinEntropyReal ε ρ σ` is **attained** at a single CQ state `ρ'` inside the purified-distance
ε-ball.  This is the boundary content of Tomamichel 2016, Definition 6.5 / Corollary 7.1: the smooth
min-entropy is a `max`.

Combines compactness of the ε-ball (`cqEpsilonBall_isCompact`), continuity of the objective
(`continuousOn_conditionalMinEntropyReal_of_bddAbove`), and `IsCompact.exists_sSup_image_eq`. -/
theorem smoothMinEntropyReal_sSup_attained_of_bddAbove
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε : 0 ≤ ε) (ρ : CQState X n) (σ : SubDensityOp n) (hσ_pd : σ.toOp.PosDef)
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ σ))) :
    ∃ ρ' : CQState X n,
      CQState.purifiedDistance ρ ρ' ≤ ε ∧
        conditionalMinEntropyReal ρ' σ = smoothMinEntropyReal ε ρ σ := by
  have hne : ((Set.ofPred (fun τ : CQState X n => CQState.purifiedDistance ρ τ ≤ ε))).Nonempty := by
    refine ⟨ρ, ?_⟩
    change CQState.purifiedDistance ρ ρ ≤ ε
    rw [CQState.purifiedDistance_self_zero]
    exact hε
  obtain ⟨ρ', hρ'_mem, hsup⟩ :=
    (cqEpsilonBall_isCompact ρ ε).exists_sSup_image_eq hne
      (continuousOn_conditionalMinEntropyReal_of_bddAbove ρ σ hσ_pd ε hbdd)
  refine ⟨ρ', hρ'_mem, ?_⟩
  rw [smoothMinEntropyReal, ← conditionalMinEntropyReal_image_epsilonBall_eq ρ σ ε]
  exact hsup.symm

/-- A positive extended smooth floor has an exact exponential feasibility witness.
At the infinite boundary the witness is zero; otherwise compactness attains the finite floor. -/
theorem smoothMinEntropy_exists_approx_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (ε : ℝ) (hε : 0 ≤ ε) (ρ : CQState X n) (σ : SubDensityOp n)
    (hσ : σ.toOp.PosDef) (k : ℝ) (hkpos : 0 < k)
    (hk : ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ) :
    ∃ τ : CQState X n, CQState.purifiedDistance ρ τ ≤ ε ∧
      isFeasible τ σ (2 ^ (-k)) := by
  by_cases hw : ∑ x, (ρ.stateMap x).trace ≤ ε ^ 2
  · refine ⟨zeroCQ, ?_, isFeasible_zeroCQ σ (Real.rpow_nonneg (by norm_num) _)⟩
    rw [CQState.purifiedDistance_zeroCQ]
    exact Real.sqrt_le_iff.mpr ⟨hε, hw⟩
  · have hw' := lt_of_not_ge hw
    rw [smoothMinEntropy_eq_ofReal_of_eps_sq_lt_weight hε ρ σ hw'] at hk
    have hkreal : k ≤ smoothMinEntropyReal ε ρ σ :=
      (ENNReal.ofReal_le_ofReal_iff'.mp hk).resolve_right (not_le_of_gt hkpos)
    obtain ⟨τ, hd, hτ⟩ := smoothMinEntropyReal_sSup_attained_of_bddAbove ε hε ρ σ hσ
      (smoothMinEntropyReal_bddAbove_of_eps_sq_lt_weight ε hε ρ σ hw')
    refine ⟨τ, hd, ?_⟩
    exact ⟨Real.rpow_nonneg (by norm_num) _,
      stateMap_opLe_pow_neg_of_conditionalMinEntropyReal_le τ σ hσ (hτ ▸ hkreal)⟩

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
