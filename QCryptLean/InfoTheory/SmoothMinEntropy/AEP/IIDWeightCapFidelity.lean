import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCap
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCapVectorFamily
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistance
import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionFiberWitness
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState

/-!
# Weight-cap fidelity lower bound (Renner `thm:Hmincondrep`, main.tex:4671–4706)

This module supplies the genuinely-new fidelity / trace-gap content for the
weight-cap purified-distance route.  The weight-cap smoothed state `ρ̄ =
W.smoothedState` is *not* operator-dominated by the tensor-power state `R =
iidAEPTensorState ρ n_copies` (the cap redistributes spectral mass across
the non-commuting cumulative projectors `B_z`), so the `opLe` route is dead.
Instead the purified distance is controlled through a direct lower bound on the
generalized fidelity of the joint densities:

  `1 − (tr R − tr ρ̄) ≤ fidelityGen R.toJointDensity ρ̄.toJointDensity`.

This is the hard analytic core (Renner's Fuchs–van de Graaf / Jensen argument
applied to external-flag purifications built from the spectral pairs `(x, z)`),
and is stated here as a named lemma so that the bit-normalized main theorem
can stay a thin reduction.

The reference spectral decomposition `hreference` and the weight-cap pin `hpin`
are load-bearing: without `hpin` the free `smoothedState` field admits
adversarial values, and without `hreference`'s idempotency/self-adjointness of
`B_z` the overlap collapse `⟨x|B_z|x⟩ = ‖B_z|x⟩‖²` fails.
-/

open Quantum.Operators Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy

noncomputable section

namespace InfoTheory.SmoothMinEntropy

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  {n : ℕ} [NeZero n]

omit [Nonempty X] in
/-- **Trace ordering for the weight-cap state.** The joint trace of the
weight-cap smoothed state never exceeds that of the tensor-power state, i.e. the
trace defect is nonnegative.  This uses only the weight-cap pin `hpin`
(identifying each smoothed block with `weightCapBlockOp`) together with the
spectral decomposition `hreference` (which makes the `B_z` genuine projectors, so
each capped block `B_z|x⟩⟨x|B_z` has trace `≤ p_x`). -/
theorem iidAEP_weightCap_toJointDensity_trace_le
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    [NeZero (n ^ n_copies * Fintype.card (Fin n_copies → X))]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hpin : iidAEPIsWeightCapSmoothedState ρ n_copies W) :
    W.smoothedState.toJointDensity.trace ≤
      (iidAEPTensorState ρ n_copies).toJointDensity.trace := by
  rw [CQState.toJointDensity_trace_eq_sum, CQState.toJointDensity_trace_eq_sum]
  refine Finset.sum_le_sum (fun xs _ => ?_)
  have heq : (W.smoothedState.stateMap xs).trace
      = (weightCapBlockOp ρ n_copies W xs).trace.re := by
    unfold SubDensityOp.trace
    rw [hpin xs]
  rw [heq]
  exact weightCapBlockOp_trace_re_le ρ n_copies σ W hreference xs

omit [Nonempty X] in
/-- **Live-fidelity Uhlmann lower bound (the hard core).** The trace of the
weight-cap smoothed state `ρ̄` is at most the (live, non-generalized) fidelity of
the joint densities of the tensor-power state `R` and `ρ̄`:

  `tr ρ̄ ≤ fidelity R.toJointDensity.toPosSemidefOp ρ̄.toJointDensity.toPosSemidefOp`.

Renner's route (main.tex:4671–4706): represent `R` and `ρ̄` as sum-of-ketbra over
a *shared* label set indexed by the spectral triples `(xs, x, z)` with `z` ranging
over the **extended** index set `Z^n ∪ {∞}` (main.tex:4631–4633).  The extra `∞`
discard label is load-bearing: the finite split coefficients sum to only
`Σ_z p_{x,z}(xs) = min(p_x(xs), λ q_max)`, which is *strictly below* the eigenvalue
`p_x(xs)` whenever `p_x > λ q_max`, so the finite family `√(p_{x,z})·|x⟩` alone
reproduces `Σ_x min(p_x, λ q_max)|x⟩⟨x|`, **not** `R`'s block `Σ_x p_x|x⟩⟨x|`.  The
discard slot carries the residual mass `p_{x,∞}(xs) = p_x − Σ_z p_{x,z}` (the
nonnegative `weightCapDiscardCoefficient`, with
`sum_splitCoefficient_add_discardCoefficient_eq_blockEigenvalue`).  The vectors are
`v_{xs,x,z} = √(p_{x,z}(xs))·|x⟩_{block xs}` for finite `z`,
`v_{xs,x,∞} = √(p_{x,∞}(xs))·|x⟩_{block xs}`,
`w_{xs,x,z} = √(p_{x,z}(xs))·(B_z|x⟩)_{block xs}` for finite `z`, and
`w_{xs,x,∞} = 0`, so that `R.toJointDensity.toOp = Σ v v†` (now exact, via the
extended-sum identity) and `ρ̄.toJointDensity.toOp = Σ w w†` (via `hpin` identifying
each block with `weightCapBlockOp`).  The family-wise overlap collapses to
`Σ_{xs,x,z finite} p_{x,z}(xs) ⟨x|B_z|x⟩ = Σ p_{x,z} ‖B_z|x⟩‖² = tr ρ̄` (the `∞`
slot contributes `0` since `w_{xs,x,∞} = 0`), using the idempotency
`B_z·B_z = B_z` and self-adjointness `B_z† = B_z` from `hreference`.
The domination-free vector-family Uhlmann tool
`InfoTheory.SmoothMinEntropy.SubDensityOp.sum_re_inner_le_fidelity_of_sumKetbra`
(`UhlmannVectorFamily.lean`, built on the generic kernel
`Quantum.TensorProducts.purifyVectorFamily`) then upgrades the overlap sum to the
fidelity lower bound.  No operator domination (`opLe`) is used: `ρ̄ ⋠ R`.

The concrete family construction (sum-of-ketbra identities for the two joint
densities and the overlap-equals-trace computation) feeding that bridge is
discharged here via the embedded vector families `V`/`Wv` over the extended label
set, the block-embedding helper `reindex_blockDiagonal_eq_sum_blockKetInclusion_ketbra`,
the per-block ketbra identities `weightCapVBlock_sum_ketbra` / `weightCapWBlock_sum_ketbra`,
and the overlap collapse `weightCapVBlock_dag_mul_weightCapWBlock_sum`. -/
theorem iidAEP_weightCap_trace_le_fidelity
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    [NeZero (n ^ n_copies * Fintype.card (Fin n_copies → X))]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hpin : iidAEPIsWeightCapSmoothedState ρ n_copies W) :
    W.smoothedState.toJointDensity.trace ≤
      Quantum.Metrics.fidelity
        (iidAEPTensorState ρ n_copies).toJointDensity.toPosSemidefOp
        W.smoothedState.toJointDensity.toPosSemidefOp := by
  classical
  -- Spectral-data facts extracted from the reference decomposition.
  obtain ⟨hq_nn, _hincr, _haction, hcum⟩ := hreference
  have hmono : Monotone W.referenceEigenvalue :=
    referenceEigenvalue_monotone_of_cumulativeResolution σ n_copies W hcum
  obtain ⟨_, _, hBidem, hBherm, _, _, _⟩ := hcum
  -- The block-diagonal reindexing equivalence used by `CQState.toJointDensity`.
  set e :
      (Fin (n ^ n_copies) × (Fin n_copies → X)) ≃
        Fin (n ^ n_copies * Fintype.card (Fin n_copies → X)) :=
    (Equiv.prodCongr (Equiv.refl (Fin (n ^ n_copies)))
      (Fintype.equivFin (Fin n_copies → X))).trans finProdFinEquiv with he
  haveI : Nonempty (Fin (n ^ n_copies)) := ⟨0⟩
  haveI : Nonempty (Fin (n ^ n_copies + 1)) := ⟨0⟩
  haveI : Nonempty ((Fin n_copies → X) × Fin (n ^ n_copies) × Fin (n ^ n_copies + 1)) :=
    ⟨(Classical.arbitrary _, (0, 0))⟩
  -- The two embedded vector families over the label set
  -- `L = (block) × (eigenindex) × (cumulative-index ∪ {∞})`.
  set V : ((Fin n_copies → X) × Fin (n ^ n_copies) × Fin (n ^ n_copies + 1)) →
      Ket (n ^ n_copies * Fintype.card (Fin n_copies → X)) :=
    fun l => blockKetInclusion e l.1 (weightCapVBlock ρ n_copies W l.1 l.2.1 l.2.2) with hV
  set Wv : ((Fin n_copies → X) × Fin (n ^ n_copies) × Fin (n ^ n_copies + 1)) →
      Ket (n ^ n_copies * Fintype.card (Fin n_copies → X)) :=
    fun l => blockKetInclusion e l.1 (weightCapWBlock ρ n_copies W l.1 l.2.1 l.2.2) with hWv
  -- `R` is the joint sum-of-ketbra over `V`.
  have hRrepr : (iidAEPTensorState ρ n_copies).toJointDensity.toOp
      = ∑ l, (V l) * (V l).dag := by
    rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal, ← he]
    have hblk : (fun xs : Fin n_copies → X =>
          ((iidAEPTensorState ρ n_copies).stateMap xs).toOp)
        = fun xs => ∑ k : Fin (n ^ n_copies) × Fin (n ^ n_copies + 1),
            (weightCapVBlock ρ n_copies W xs k.1 k.2) *
              (weightCapVBlock ρ n_copies W xs k.1 k.2).dag := by
      funext xs
      rw [← weightCapVBlock_sum_ketbra ρ n_copies W hmono hq_nn xs]
      simp only [Fintype.sum_prod_type]
    rw [hblk, reindex_blockDiagonal_eq_sum_blockKetInclusion_ketbra e
        (fun (xs : Fin n_copies → X) (k : Fin (n ^ n_copies) × Fin (n ^ n_copies + 1)) =>
          weightCapVBlock ρ n_copies W xs k.1 k.2)]
    simp only [hV, Fintype.sum_prod_type]
  -- `ρ̄` is the joint sum-of-ketbra over `Wv`.
  have hSrepr : W.smoothedState.toJointDensity.toOp
      = ∑ l, (Wv l) * (Wv l).dag := by
    rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal, ← he]
    have hblk : (fun xs : Fin n_copies → X => (W.smoothedState.stateMap xs).toOp)
        = fun xs => ∑ k : Fin (n ^ n_copies) × Fin (n ^ n_copies + 1),
            (weightCapWBlock ρ n_copies W xs k.1 k.2) *
              (weightCapWBlock ρ n_copies W xs k.1 k.2).dag := by
      funext xs
      rw [hpin xs, ← weightCapWBlock_sum_ketbra ρ n_copies W hBherm hmono hq_nn xs]
      simp only [Fintype.sum_prod_type]
    rw [hblk, reindex_blockDiagonal_eq_sum_blockKetInclusion_ketbra e
        (fun (xs : Fin n_copies → X) (k : Fin (n ^ n_copies) × Fin (n ^ n_copies + 1)) =>
          weightCapWBlock ρ n_copies W xs k.1 k.2)]
    simp only [hWv, Fintype.sum_prod_type]
  -- The family overlap collapses to the sum of weight-cap block traces.
  have hoverlap : (∑ l, ((V l).dag * (Wv l) : ℂ))
      = ∑ xs : Fin n_copies → X, (weightCapBlockOp ρ n_copies W xs).trace := by
    simp only [hV, hWv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun xs _ => ?_)
    rw [show (∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies + 1),
              ((blockKetInclusion e xs (weightCapVBlock ρ n_copies W xs x z)).dag *
                (blockKetInclusion e xs (weightCapWBlock ρ n_copies W xs x z)) : ℂ))
          = ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies + 1),
              ((weightCapVBlock ρ n_copies W xs x z).dag *
                weightCapWBlock ρ n_copies W xs x z : ℂ) from
        Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ =>
          blockKetInclusion_dag_mul_same e xs _ _))]
    exact weightCapVBlock_dag_mul_weightCapWBlock_sum ρ n_copies W hBherm hBidem hmono hq_nn xs
  -- The weight-cap smoothed trace equals the real part of that overlap sum.
  have htr : W.smoothedState.toJointDensity.trace
      = (∑ xs : Fin n_copies → X, (weightCapBlockOp ρ n_copies W xs).trace).re := by
    rw [CQState.toJointDensity_trace_eq_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun xs _ => ?_)
    unfold SubDensityOp.trace
    rw [hpin xs]
  -- Feed the domination-free vector-family Uhlmann bound.
  have hfid := SubDensityOp.sum_re_inner_le_fidelity_of_sumKetbra_fintype
    (iidAEPTensorState ρ n_copies).toJointDensity W.smoothedState.toJointDensity
    V Wv hRrepr hSrepr
  rw [hoverlap] at hfid
  rw [htr]
  exact hfid

/-- **Domination-free fidelity / trace-gap arithmetic core.** From the trace
ordering `tr τ ≤ tr ρ` and the live (non-generalized) fidelity lower bound
`tr τ ≤ fidelity ρ τ`, the generalized fidelity is at least the complement of
the trace gap.  This is the fidelity-input analogue of
`fidelityGen_ge_one_sub_trace_gap_of_opLe`, valid even when `τ ⋠ ρ`. -/
theorem fidelityGen_ge_one_sub_trace_gap_of_trace_le_fidelity
    {m : ℕ} [NeZero m] (ρ τ : SubDensityOp m)
    (htrace_le : τ.trace ≤ ρ.trace)
    (hF_ge : τ.trace ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp) :
    1 - (ρ.trace - τ.trace) ≤ fidelityGen ρ τ := by
  have hcorr_ge :
      1 - ρ.trace ≤ Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) := by
    have hρ_gap_nonneg : 0 ≤ 1 - ρ.trace := ρ.one_sub_trace_nonneg
    have hsq_le : (1 - ρ.trace) ^ 2 ≤ (1 - ρ.trace) * (1 - τ.trace) := by
      nlinarith
    calc
      1 - ρ.trace = Real.sqrt ((1 - ρ.trace) ^ 2) := by
        rw [Real.sqrt_sq hρ_gap_nonneg]
      _ ≤ Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) :=
        Real.sqrt_le_sqrt hsq_le
  unfold fidelityGen
  linarith

omit [Nonempty X] in
/-- **Weight-cap fidelity lower bound.** The generalized fidelity of the joint
densities of the tensor-power state `R` and the weight-cap smoothed state `ρ̄` is
at least the complement of their trace gap:

  `1 − (tr R − tr ρ̄) ≤ fidelityGen R.toJointDensity ρ̄.toJointDensity`.

This feeds the *domination-free* inputs into the arithmetic core
`fidelityGen_ge_one_sub_trace_gap_of_trace_le_fidelity`: the trace ordering
`tr ρ̄ ≤ tr R` from `iidAEP_weightCap_toJointDensity_trace_le`, and the
live-fidelity bound `tr ρ̄ ≤ fidelity R ρ̄` from
`iidAEP_weightCap_trace_le_fidelity`.  No operator domination is used. -/
theorem iidAEP_weightCap_one_sub_traceGap_le_fidelityGen
    (ρ : CQState X n) (σ : DensityOp n)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (n ^ n_copies)]
    [Nonempty (Fin n_copies → X)]
    [NeZero (n ^ n_copies * Fintype.card (Fin n_copies → X))]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hreference : iidAEPReferenceSpectralDecomposition σ n_copies W)
    (hpin : iidAEPIsWeightCapSmoothedState ρ n_copies W) :
    1 - ((iidAEPTensorState ρ n_copies).toJointDensity.trace
          - W.smoothedState.toJointDensity.trace)
      ≤ fidelityGen (iidAEPTensorState ρ n_copies).toJointDensity
          W.smoothedState.toJointDensity := by
  set R := (iidAEPTensorState ρ n_copies).toJointDensity with hR
  set S := W.smoothedState.toJointDensity with hS
  have htrace_le : S.trace ≤ R.trace :=
    iidAEP_weightCap_toJointDensity_trace_le ρ σ n_copies W hreference hpin
  have hF_ge :
      S.trace ≤ Quantum.Metrics.fidelity R.toPosSemidefOp S.toPosSemidefOp :=
    iidAEP_weightCap_trace_le_fidelity ρ σ n_copies W hreference hpin
  exact fidelityGen_ge_one_sub_trace_gap_of_trace_le_fidelity R S htrace_le hF_ge

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
