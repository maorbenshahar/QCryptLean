import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernel

/-!
# Block references for classical announcements

Block-diagonal references encode per-announcement feasible coefficients. Nearby feasible witnesses
give canonical smooth entropy floors without positive-weight or boundedness guards.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The reference that is classical on the announced register -/

/-- `Σ_p |p⟩⟨p| ⊗ ν_p` on the joint register `C ⊗ E`: the reference operator that is **classical on
the announced register** `C` in its computational basis, with an arbitrary sub-normalised block
`ν p` on `E` for each announced value.

`Op.tensor` places its left argument in the high digit, matching `CQState.tensorLeftKernel`, so the
announced register sits in the high digits here too. -/
def blockDiagRefOp {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE) : Op (dC * dE) :=
  ∑ p : Fin dC, Op.tensor (stdKet dC p * (stdKet dC p).dag) (ν p).toOp

/-- The `(k, ·), (k, ·)` block of `|k⟩⟨k| ⊗ A` is `A` itself. -/
lemma stdKetProj_tensor_apply_diagBlock {dE dC : ℕ} (A : Op dE) (k : Fin dC) (i j : Fin dE) :
    Op.tensor (stdKet dC k * (stdKet dC k).dag) A
        (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j)) = A i j := by
  rw [Op_tensor_apply_finProd]
  simp [ket_mul_bra_apply, Ket.dag_vec]

/-- The `(k, ·), (k, ·)` block of the classical block-diagonal reference is `ν k`: the off-diagonal
announcement blocks contribute nothing, which is exactly the orthogonality of the `|z⟩` in Renner
2005 (arXiv:quant-ph/0512258v2) `main.tex:2917`, `\label{lem:Hminclasscondr}`. -/
lemma blockDiagRefOp_apply_diagBlock {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE)
    (k : Fin dC) (i j : Fin dE) :
    blockDiagRefOp ν (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j)) = (ν k).toOp i j := by
  rw [blockDiagRefOp, Matrix.sum_apply, Finset.sum_eq_single k]
  · exact stdKetProj_tensor_apply_diagBlock (ν k).toOp k i j
  · intro p _ hp
    rw [Op_tensor_apply_finProd]
    simp [ket_mul_bra_apply, Ket.dag_vec, hp]
  · intro h
    exact absurd (Finset.mem_univ k) h

lemma blockDiagRefOp_isHermitian {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE) :
    (blockDiagRefOp ν).IsHermitian := by
  unfold Matrix.IsHermitian blockDiagRefOp
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Quantum.TensorProducts.Op.tensor_conjTranspose, ketbra_hermitian, (ν p).isHermitian]

lemma blockDiagRefOp_posSemidef {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE) :
    (blockDiagRefOp ν).PosSemidef := by
  rw [blockDiagRefOp]
  refine Matrix.posSemidef_sum _ (fun p _ => ?_)
  exact Op.tensor_posSemidef_mathlib (ketbra_posSemidef _)
    (posSemidefOp_implies_mathlib (ν p).toPosSemidefOp)

/-- The reference carries exactly the total weight of its block family. -/
lemma blockDiagRefOp_trace {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE) :
    (blockDiagRefOp ν).trace = ∑ p : Fin dC, (ν p).toOp.trace := by
  rw [blockDiagRefOp, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Quantum.TensorProducts.Op.trace_tensor,
    trace_ketbra_normalized _ (stdKet_braket_self p), one_mul]

/-- **The reference that is classical on the announced register**, `Σ_p |p⟩⟨p| ⊗ ν_p`.

`hν` is the sub-normalisation the `SubDensityOp` carrier demands, and it is the only constraint the
block family must satisfy: the blocks are otherwise arbitrary sub-normalised operators on `E`, in
particular they may be `ν_p = q_p · σ` for the announcement law `q` and a common `σ`, which is the
shape in which a decoupled announcement enters.

This is the sibling of `SubDensityOp.maxMixedTensor` (`ClassicalAnnounceKernel.lean`) with the flat
announcement block `1/d_C · 1` replaced by the announcement's own law.  Renner 2005
(arXiv:quant-ph/0512258v2) `main.tex:2917`, `\label{lem:Hminclasscondr}`, calls this the reference
being classical with respect to the same basis. -/
def blockDiagRef {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE)
    (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) : SubDensityOp (dC * dE) where
  toOp := blockDiagRefOp ν
  isHermitian := blockDiagRefOp_isHermitian ν
  pos_semidef := fun v => posSemidef_re_quadraticForm_nonneg (blockDiagRefOp_posSemidef ν) v
  trace_le_one := by
    rw [blockDiagRefOp_trace, Complex.re_sum]
    exact hν

@[simp] lemma blockDiagRef_toOp {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE)
    (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) :
    (blockDiagRef ν hν).toOp = blockDiagRefOp ν := rfl

lemma blockDiagRef_trace {dE dC : ℕ} (ν : Fin dC → SubDensityOp dE)
    (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) :
    (blockDiagRef ν hν).trace = ∑ p : Fin dC, (ν p).trace := by
  change (blockDiagRefOp ν).trace.re = _
  rw [blockDiagRefOp_trace, Complex.re_sum]
  rfl

/-! ## Renner's classical-conditioning equivalence -/

/-- The quadratic form written out as a double sum over matrix entries. -/
private lemma quadraticForm_eq_double_sum {n : ℕ} (M : Op n) (v : Fin n → ℂ) :
    quadraticForm M v = ∑ i : Fin n, ∑ j : Fin n, star (v i) * M i j * v j := by
  simp only [quadraticForm, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, ← mul_assoc]

/-- **Renner's classical-conditioning equivalence** — arXiv:quant-ph/0512258v2 `main.tex:2936`,
`\label{eq:classcondeq}`.

For an operator supported in the single announcement block `p` and a reference that is classical on
the announcement register, Löwner domination against the whole reference is *equivalent* to Löwner
domination against that one block:

  `|p⟩⟨p| ⊗ A ≼ t · Σ_q |q⟩⟨q| ⊗ ν_q   ⟺   A ≼ t · ν_p`.

Forward: test on vectors supported in block `p`, where the off-diagonal announcement blocks drop
out.  Backward: the difference splits as `|p⟩⟨p| ⊗ (t·ν_p − A) + Σ_{q ≠ p} |q⟩⟨q| ⊗ (t·ν_q)`, a sum
of positive semidefinite terms.

No dimension factor enters in either direction; this is the whole reason the announcement is free
when the reference keeps it classical. -/
theorem opLe_stdKetProj_tensor_blockDiagRefOp_iff {dE dC : ℕ}
    (ν : Fin dC → SubDensityOp dE) (p : Fin dC) {A : Op dE} (hA : A.IsHermitian)
    {t : ℝ} (ht : 0 ≤ t) :
    opLe (Op.tensor (stdKet dC p * (stdKet dC p).dag) A)
        (Complex.ofReal t • blockDiagRefOp ν)
      ↔ opLe A (Complex.ofReal t • (ν p).toOp) := by
  constructor
  · intro h v
    have h1 := h (leftBlockVector p v)
    rw [quadraticForm_leftBlockVector_eq_sum, quadraticForm_leftBlockVector_eq_sum] at h1
    have hL : ∀ i j : Fin dE,
        Op.tensor (stdKet dC p * (stdKet dC p).dag) A
            (finProdFinEquiv (p, i)) (finProdFinEquiv (p, j)) = A i j :=
      fun i j => stdKetProj_tensor_apply_diagBlock A p i j
    have hR : ∀ i j : Fin dE,
        (Complex.ofReal t • blockDiagRefOp ν)
            (finProdFinEquiv (p, i)) (finProdFinEquiv (p, j))
          = (Complex.ofReal t • (ν p).toOp) i j := by
      intro i j
      rw [Matrix.smul_apply, Matrix.smul_apply, blockDiagRefOp_apply_diagBlock]
    simp only [hL, hR] at h1
    rw [quadraticForm_eq_double_sum, quadraticForm_eq_double_sum]
    exact h1
  · intro h
    apply opLe_of_posSemidef_sub
    have hsm : (Complex.ofReal t • blockDiagRefOp ν)
        = ∑ q : Fin dC, Op.tensor (stdKet dC q * (stdKet dC q).dag)
            (Complex.ofReal t • (ν q).toOp) := by
      rw [blockDiagRefOp, Finset.smul_sum]
      exact Finset.sum_congr rfl fun q _ =>
        (Quantum.TensorProducts.Op.tensor_smul_right _ _ _).symm
    have hsplit :
        (Complex.ofReal t • blockDiagRefOp ν)
            - Op.tensor (stdKet dC p * (stdKet dC p).dag) A
          = Op.tensor (stdKet dC p * (stdKet dC p).dag)
                ((Complex.ofReal t • (ν p).toOp) - A)
            + ∑ q ∈ Finset.univ.erase p,
                Op.tensor (stdKet dC q * (stdKet dC q).dag)
                  (Complex.ofReal t • (ν q).toOp) := by
      rw [hsm, ← Finset.add_sum_erase _ _ (Finset.mem_univ p),
        Quantum.TensorProducts.Op.tensor_sub_right]
      abel
    rw [hsplit]
    have hνp : ((Complex.ofReal t • (ν p).toOp)).PosSemidef :=
      (posSemidefOp_implies_mathlib (ν p).toPosSemidefOp).smul (Complex.zero_le_real.mpr ht)
    refine Matrix.PosSemidef.add ?_ ?_
    · exact Op.tensor_posSemidef_mathlib (ketbra_posSemidef _)
        (opLe.posSemidef_sub hA hνp.isHermitian h)
    · refine Matrix.posSemidef_sum _ (fun q _ => ?_)
      exact Op.tensor_posSemidef_mathlib (ketbra_posSemidef _)
        ((posSemidefOp_implies_mathlib (ν q).toPosSemidefOp).smul (Complex.zero_le_real.mpr ht))

/-! ## The announce kernel of a deterministic classical announcement -/

/-- The announce-kernel hypothesis used below is satisfiable: the computational-basis projector
carries it definitionally.  The library carrier is `stdProj`, defined elsewhere and not imported
here so that this module stays free of
the BB84 tower; a consumer discharges the hypothesis with `stdProj_toOp`. -/
example {dC : ℕ} (p : Fin dC) :
    (DensityOp.toSubDensityOp (DensityOp.fromPure (stdKet dC p) (stdKet_braket_self p))).toOp
      = stdKet dC p * (stdKet dC p).dag := rfl

/-- A block that is a computational-basis projector is normalised. -/
lemma trace_eq_one_of_toOp_eq_stdKetProj {dC : ℕ} {K : SubDensityOp dC} {p : Fin dC}
    (hK : K.toOp = stdKet dC p * (stdKet dC p).dag) : K.trace = 1 := by
  change K.toOp.trace.re = 1
  rw [hK, trace_ketbra_normalized _ (stdKet_braket_self p), Complex.one_re]

/-- **The announcement costs nothing, at the level of the min-entropy SDP.**

The announced pair `(ρ ⊗ K, Σ_p |p⟩⟨p| ⊗ ν_p)` and the family of per-block conditions
`ρ_x ≼ t · ν_{ann x}` have literally the **same** set of feasible scalars `t`.  This is Renner 2005
(arXiv:quant-ph/0512258v2) `main.tex:2936`, `\label{eq:classcondeq}`, in the CQ encoding: the
classical register `Z` of that lemma is the announcement register `C` here, its conditional
operators `ρ^z_{AB}` are the blocks with `ann x = z`, and its `A` register is the CQ label `X`.

`K` is an arbitrary announce kernel that happens to be the deterministic classical announcement
`|ann x⟩⟨ann x|`; the hypothesis is stated on `toOp` so any library carrier of that projector
discharges it. -/
theorem isFeasible_tensorLeftKernel_blockDiagRef_iff
    {X : Type*} [Fintype X] {dE dC : ℕ}
    (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (t : ℝ) :
    isFeasible (ρ.tensorLeftKernel K) (blockDiagRef ν hν) t
      ↔ 0 ≤ t ∧ ∀ x : X, opLe (ρ.stateMap x).toOp (Complex.ofReal t • (ν (ann x)).toOp) := by
  have hblk : ∀ x : X,
      ((ρ.tensorLeftKernel K).stateMap x).toOp
        = Op.tensor (stdKet dC (ann x) * (stdKet dC (ann x)).dag) (ρ.stateMap x).toOp := by
    intro x
    rw [CQState.tensorLeftKernel_stateMap,
      show ((K x).tensor (ρ.stateMap x)).toOp
          = Op.tensor (K x).toOp (ρ.stateMap x).toOp from rfl, hK x]
  constructor
  · rintro ⟨ht, hx⟩
    refine ⟨ht, fun x => ?_⟩
    have h := hx x
    rw [hblk x, blockDiagRef_toOp] at h
    exact (opLe_stdKetProj_tensor_blockDiagRefOp_iff ν (ann x)
      (ρ.stateMap x).isHermitian ht).mp h
  · rintro ⟨ht, hx⟩
    refine ⟨ht, fun x => ?_⟩
    rw [hblk x, blockDiagRef_toOp]
    exact (opLe_stdKetProj_tensor_blockDiagRefOp_iff ν (ann x)
      (ρ.stateMap x).isHermitian ht).mpr (hx x)

/-- **The charge is exactly zero.**

The optimum of the announced min-entropy SDP equals the optimum of the per-block problem, so no
constant — in particular no `log₂ d_C` — separates them.  Contrast
`conditionalMinEntropyReal_tensorLeftKernel_ge_sub_log` (`ClassicalAnnounceKernel.lean`), where the
reference has been flattened to `1/d_C · 1 ⊗ σ` and the optimum is multiplied by the domination
constant.  That is the flattened-reference mechanism of Renner 2005 (arXiv:quant-ph/0512258v2)
`main.tex:3791`, `\label{lem:Halphachainsmooth}` — reference `σ_B ⊗ σ_C`, charge `Hmax(ρ_B)`, which
for a classical register is `log|C|` — and not `\label{lem:Hminclasscondr}`. -/
theorem minFeasibleLambda_tensorLeftKernel_blockDiagRef_eq
    {X : Type*} [Fintype X] {dE dC : ℕ}
    (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) :
    minFeasibleLambda (ρ.tensorLeftKernel K) (blockDiagRef ν hν)
      = sInf (Set.ofPred (fun t : ℝ => 0 ≤ t ∧
          ∀ x : X, opLe (ρ.stateMap x).toOp (Complex.ofReal t • (ν (ann x)).toOp))) := by
  unfold minFeasibleLambda
  congr 1
  ext t
  exact isFeasible_tensorLeftKernel_blockDiagRef_iff ρ ann K hK ν hν t

/-! ## The entropy bounds -/

/-- **The unsmoothed zero-charge announce bound** — Renner 2005 (arXiv:quant-ph/0512258v2)
`main.tex:2917`, `\label{lem:Hminclasscondr}`.

A per-block domination `ρ_x ≼ 2^(−k) · ν_{ann x}` at a single scalar gives
`k ≤ H_min(X | C E)_{ρ ⊗ K | Σ_p |p⟩⟨p| ⊗ ν_p}` — with **nothing subtracted**.

`hweight` rules out the `minFeasibleLambda = 0` sentinel of `conditionalMinEntropyReal`, exactly as
in the signed logarithm formula; no positive-definiteness of
the reference is needed because feasibility is supplied by `hblock` rather than derived. -/
theorem conditionalMinEntropyReal_tensorLeftKernel_blockDiagRef_ge
    {X : Type*} [Fintype X] [Nonempty X] {dE dC : ℕ}
    (ρ : CQState X dE) (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (k : ℝ)
    (hweight : 0 < ∑ x : X, (ρ.stateMap x).trace)
    (hblock : ∀ x : X,
      opLe (ρ.stateMap x).toOp (Complex.ofReal ((2 : ℝ) ^ (-k)) • (ν (ann x)).toOp)) :
    k ≤ conditionalMinEntropyReal (ρ.tensorLeftKernel K) (blockDiagRef ν hν) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-k) := Real.rpow_pos_of_pos (by norm_num) _
  have hfeas : isFeasible (ρ.tensorLeftKernel K) (blockDiagRef ν hν) ((2 : ℝ) ^ (-k)) :=
    (isFeasible_tensorLeftKernel_blockDiagRef_iff ρ ann K hK ν hν _).mpr ⟨hpow.le, hblock⟩
  have hlam_le := minFeasibleLambda_le_of_isFeasible _ _ hfeas
  have hw : 0 < ∑ x : X, ((ρ.tensorLeftKernel K).stateMap x).trace := by
    rw [CQState.tensorLeftKernel_weight ρ K
      (fun x => trace_eq_one_of_toOp_eq_stdKetProj (hK x))]
    exact hweight
  have hpos := minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos _ _ hw ⟨_, hfeas⟩
  exact conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k _ _ k hpos hlam_le

/-- A single ball witness with per-block domination certifies an extended smooth floor
against the announced block reference, including zero witnesses. -/
theorem smoothMinEntropy_tensorLeftKernel_blockDiagRef_ge_of_ballWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {dE dC : ℕ}
    [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    (ε : ℝ) (ρ ρbar : CQState X dE) (hball : CQState.purifiedDistance ρ ρbar ≤ ε)
    (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (k : ℝ)
    (hblock : ∀ x : X,
      opLe (ρbar.stateMap x).toOp (Complex.ofReal ((2 : ℝ) ^ (-k)) • (ν (ann x)).toOp)) :
    ENNReal.ofReal k ≤
      smoothMinEntropy ε (ρ.tensorLeftKernel K) (blockDiagRef ν hν) := by
  apply smoothMinEntropy_ge_of_isFeasible _ (ρbar.tensorLeftKernel K)
  · exact (CQState.purifiedDistance_tensorLeftKernel_le ρ ρbar K
      (fun x => trace_eq_one_of_toOp_eq_stdKetProj (hK x))).trans hball
  · exact (isFeasible_tensorLeftKernel_blockDiagRef_iff ρbar ann K hK ν hν _).mpr
      ⟨Real.rpow_nonneg (by norm_num) _, hblock⟩


/-- A positive-weight ball witness with block domination gives the signed smooth floor `k`
against the block-diagonal announcement reference. -/
theorem smoothMinEntropyReal_tensorLeftKernel_blockDiagRef_ge_of_ballWitness
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {dE dC : ℕ}
    [NeZero dE] [NeZero dC] [NeZero (dC * dE)]
    (ε : ℝ) (ρ ρbar : CQState X dE) (hball : CQState.purifiedDistance ρ ρbar ≤ ε)
    (ann : X → Fin dC) (K : X → SubDensityOp dC)
    (hK : ∀ x, (K x).toOp = stdKet dC (ann x) * (stdKet dC (ann x)).dag)
    (ν : Fin dC → SubDensityOp dE) (hν : ∑ p : Fin dC, (ν p).trace ≤ 1) (k : ℝ)
    (hweight : 0 < ∑ x : X, (ρbar.stateMap x).trace)
    (hblock : ∀ x : X,
      opLe (ρbar.stateMap x).toOp (Complex.ofReal ((2 : ℝ) ^ (-k)) • (ν (ann x)).toOp))
    (hbdd : BddAbove
      (Set.ofPred (isInSmoothedSetReal ε (ρ.tensorLeftKernel K) (blockDiagRef ν hν)))) :
    k ≤ smoothMinEntropyReal ε (ρ.tensorLeftKernel K) (blockDiagRef ν hν) := by
  have hKtr : ∀ x, (K x).trace = 1 := fun x => trace_eq_one_of_toOp_eq_stdKetProj (hK x)
  have hmem : isInSmoothedSetReal ε (ρ.tensorLeftKernel K) (blockDiagRef ν hν)
      (conditionalMinEntropyReal (ρbar.tensorLeftKernel K) (blockDiagRef ν hν)) :=
    ⟨ρbar.tensorLeftKernel K, rfl,
      le_trans (CQState.purifiedDistance_tensorLeftKernel_le ρ ρbar K hKtr) hball⟩
  refine le_trans ?_ (le_csSup hbdd hmem)
  exact conditionalMinEntropyReal_tensorLeftKernel_blockDiagRef_ge ρbar ann K hK ν hν k
    hweight hblock

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
