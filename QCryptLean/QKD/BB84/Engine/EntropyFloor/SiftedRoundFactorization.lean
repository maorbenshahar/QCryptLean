import QCryptLean.QKD.BB84.Engine.EntropyFloor.SiftedRoundFactorizationReferee
import QCryptLean.QKD.BB84.Engine.InnerBudget.SiftedPassSupport

/-!
# Genuine-LOCC per-round factorization of the trivial-attack sifted τ-block

The genuine-LOCC counterpart of `SiftedRoundFactorizationReferee.lean`, at the LOCAL sift
`bb84SiftedSinglePairOp (peSel a) (xSel a)` (`H ⊗ H` on rounds that are both PE- and
X-designated, identity elsewhere) in place of the referee Bell rotation
`bb84RefereeSiftedSinglePairOp (peSel a)`.  Most of its `m = ⌈n/2⌉` declarations mirror a
declaration of `SiftedRoundFactorizationReferee.lean`; the referee declarations are untouched.
(The general-`m` declarations of the last section are the split-point-parametrised forms of the
`m = ⌈n/2⌉` accept-test decls.)  Two declarations have no referee analogue:
`bb84SiftedSinglePairOp_of_not_xTest` and `bb84SiftedSingleRoundRefBlock_eq_of_not_xTest`, which
state that on a non-X-test round (`b && x = false`, i.e. every key round and every Z-test PE round)
the local sift collapses to the identity and the block collapses to the referee key-round
block — a fact the referee construction has no need for, since its single Bell rotation never
varies with an X-test flag.

## Why a native construction is needed

The real/ideal difference channel is supported on the accept event, so the per-Carathéodory
floor argument that consumes the factorization must run on a `bb84SiftedRotation`-conjugated
state (`SiftedPassSupport.lean` module docstring).

## What the keystone delivers

`bb84_siftedUnitRegisterEmbed_tauConditioned_eq_tensorFinProd`: at the trivial attack and
`τ = densityOp_reindex (interleavingEquiv 4 n).symm (ψ.tensorPowGen n)`, the outcome-conditioned
Eve/reference block is a **tensor product over rounds**, each factor carrying its own reference
block.  It is that product structure — not round-disjointness, which is provably insufficient —
that makes the labeled-announce block a key-independent operator at a Carathéodory point.

## Main definitions
- `bb84SiftedConditionOp`, `bb84SiftedSingleRoundRefBlock`: the per-round conditioning
  projector `P_{b,x,k} = Vᴴ|k⟩⟨k|V` at `V = bb84SiftedSinglePairOp b x`, and the single-round
  reference block it cuts out of a paired state `ψ` on `A ⊗ R₀ = ℂ⁴ ⊗ ℂ⁴`.
- `bb84SiftedPEPass`: the PE-pass verdict read off the sorted PE-round outcomes.
- `bb84SiftedPERoundProd`: the PE-pass-filtered finite tensor product of the PE-round reference
  blocks over the sorted PE rounds.
- `bb84SiftedPEPass`, `bb84SiftedPERoundProd`: the same two objects at a **general
  test-set size `m`**, over the split-point-parametrised round partition
  (`bb84KeyRoundCount`, `bb84PERoundIdx`, `bb84PartEquiv`).

## Main statements
- `bb84_siftedUnitRegisterEmbed_tauConditioned_eq_tensorFinProd`: the keystone factorization.
- `bb84SiftedLocalPETestPassed_key_indep`, `bb84SiftedLocalPETestPassed_eq_pePass`: the
  fail-closed LOCC two-basis test depends only on the PE-round outcomes, hence factors through the
  sorted PE-round restriction.
- `bb84SiftedLocalPETestPassed_eq_pePass`: the same factorization at a general `m`, under
  `hcount : bb84KeyCount n m peSel`.  Substituting `m := ⌈n/2⌉` into the general-`m` forms
  `bb84SiftedPEPass` and `bb84SiftedPERoundProd` recovers the `m = ⌈n/2⌉` ones definitionally.
- `bb84SiftedSingleRoundRefBlock_eq_of_not_xTest`: on every round that is not an X-test round
  (key rounds and Z-test PE rounds) the block **is** the referee key-round block
  (`bb84SiftedSingleRoundRefBlock ψ b x k = bb84RefereeSiftedSingleRoundRefBlock ψ false k`, a block
  identity). This is what a consumer needs to reuse the Devetak–Winter / AEP rate layer built on
  `bb84RefereeSiftedSingleRoundRefBlock ψ false` — the identity is what this theorem proves; the
  reuse itself is a downstream consumer's obligation, not established here.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B main.tex:1341–:1413
(Appendix B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}`
(main.tex:1356–:1362), the Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed
min-entropy bound `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting
step `\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413); Renner 2005
(arXiv:quant-ph/0512258v2) §5/§6.5. -/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti Math.RepresentationTheory Quantum.Symmetry
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## The single-round sifted conditioning projector `P_{b,x,k} = Vᴴ |k⟩⟨k| V` -/

/-- The single-round sifted conditioning operator: rotate the computational projector `|k⟩⟨k|`
by the per-round sift `bb84SiftedSinglePairOp b x` (`H ⊗ H` on an X-test PE round, `1`
otherwise).  Explicit; no `Classical.choose`. -/
def bb84SiftedConditionOp (b x : Bool) (k : Fin signalDim) : Op signalDim :=
  (bb84SiftedSinglePairOp b x)ᴴ * bb84ComputationalPOVM k * bb84SiftedSinglePairOp b x

/-- `bb84SiftedConditionOp` is Hermitian. -/
lemma bb84SiftedConditionOp_isHermitian (b x : Bool) (k : Fin signalDim) :
    (bb84SiftedConditionOp b x k)ᴴ = bb84SiftedConditionOp b x k := by
  unfold bb84SiftedConditionOp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (bb84ComputationalPOVM_isHermitian k).eq, Matrix.mul_assoc]

/-- The per-round sift satisfies `V Vᴴ = 1` (from `Vᴴ V = 1` on a square matrix). -/
lemma bb84SiftedSinglePairOp_mul_conjTranspose (b x : Bool) :
    bb84SiftedSinglePairOp b x * (bb84SiftedSinglePairOp b x)ᴴ = (1 : Op signalDim) :=
  mul_eq_one_comm.mp (bb84SiftedSinglePairOp_unitary b x)

/-- `bb84SiftedConditionOp` is idempotent. -/
lemma bb84SiftedConditionOp_idem (b x : Bool) (k : Fin signalDim) :
    bb84SiftedConditionOp b x k * bb84SiftedConditionOp b x k = bb84SiftedConditionOp b x k := by
  unfold bb84SiftedConditionOp
  calc (bb84SiftedSinglePairOp b x)ᴴ * bb84ComputationalPOVM k * bb84SiftedSinglePairOp b x *
          ((bb84SiftedSinglePairOp b x)ᴴ * bb84ComputationalPOVM k * bb84SiftedSinglePairOp b x)
         = (bb84SiftedSinglePairOp b x)ᴴ * bb84ComputationalPOVM k *
          (bb84SiftedSinglePairOp b x * (bb84SiftedSinglePairOp b x)ᴴ) *
          (bb84ComputationalPOVM k * bb84SiftedSinglePairOp b x) := by
        simp only [Matrix.mul_assoc]
    _ = (bb84SiftedSinglePairOp b x)ᴴ * bb84ComputationalPOVM k *
          (bb84ComputationalPOVM k * bb84SiftedSinglePairOp b x) := by
        rw [bb84SiftedSinglePairOp_mul_conjTranspose, Matrix.mul_one]
    _ = (bb84SiftedSinglePairOp b x)ᴴ * (bb84ComputationalPOVM k * bb84ComputationalPOVM k) *
          bb84SiftedSinglePairOp b x := by
        simp only [Matrix.mul_assoc]
    _ = (bb84SiftedSinglePairOp b x)ᴴ * bb84ComputationalPOVM k * bb84SiftedSinglePairOp b x := by
        rw [bb84ComputationalPOVM_isProjection]

/-! ## The single-round sifted reference block -/

/-- **Single-round sifted-measured reference block of a paired state `ψ` on `A⊗R₀ = ℂ⁴⊗ℂ⁴`**:
rotate the signal by the per-round sift `bb84SiftedSinglePairOp b x`, project the signal onto
the computational `|k⟩`, trace out the signal. -/
noncomputable def bb84SiftedSingleRoundRefBlock
    (ψ : DensityOp (signalDim * signalDim)) (b x : Bool) (k : Fin signalDim) :
    SubDensityOp signalDim where
  toOp :=
    partialTraceA (Op.tensor (bb84SiftedConditionOp b x k) (1 : Op signalDim) * ψ.toOp
      * Op.tensor (bb84SiftedConditionOp b x k) (1 : Op signalDim))
  isHermitian :=
    partialTraceA_projector_sandwich_isHermitian (bb84SiftedConditionOp b x k) ψ.toOp
      (bb84SiftedConditionOp_isHermitian b x k)
      (posSemidefOp_implies_mathlib ψ.toPosSemidefOp).isHermitian
  pos_semidef :=
    partialTraceA_projector_sandwich_quadraticForm_re_nonneg (bb84SiftedConditionOp b x k) ψ.toOp
      (bb84SiftedConditionOp_isHermitian b x k)
      (posSemidefOp_implies_mathlib ψ.toPosSemidefOp)
  trace_le_one := by
    refine le_trans (trace_partialTraceA_projector_sandwich_le (bb84SiftedConditionOp b x k) ψ.toOp
      (bb84SiftedConditionOp_idem b x k) (bb84SiftedConditionOp_isHermitian b x k)
      (posSemidefOp_implies_mathlib ψ.toPosSemidefOp)) ?_
    rw [ψ.trace_one]; simp

/-- Underlying operator of the single-round block. -/
@[simp] lemma bb84SiftedSingleRoundRefBlock_toOp
    (ψ : DensityOp (signalDim * signalDim)) (b x : Bool) (k : Fin signalDim) :
    (bb84SiftedSingleRoundRefBlock ψ b x k).toOp =
      partialTraceA (Op.tensor (bb84SiftedConditionOp b x k) (1 : Op signalDim) * ψ.toOp
        * Op.tensor (bb84SiftedConditionOp b x k) (1 : Op signalDim)) := rfl

/-- **Entry formula for the single-round sifted reference block**:
`Block_{r,r'} = ∑_{t,t'} C_{t',t} · ψ_{(t,r),(t',r')}` with `C = Vᴴ|k⟩⟨k|V` at the sift. -/
lemma bb84SiftedSingleRoundRefBlock_toOp_entry
    (ψ : DensityOp (signalDim * signalDim)) (b x : Bool) (k r r' : Fin signalDim) :
    (bb84SiftedSingleRoundRefBlock ψ b x k).toOp r r' =
      ∑ t : Fin signalDim, ∑ t' : Fin signalDim,
        bb84SiftedConditionOp b x k t' t *
          ψ.toOp (finProdFinEquiv (t, r)) (finProdFinEquiv (t', r')) := by
  rw [bb84SiftedSingleRoundRefBlock_toOp]
  simp only [partialTraceA, Matrix.of_apply]
  simp_rw [Quantum.TensorProducts.tensor_one_mul_mul_tensor_one_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hstep : ∀ y : Fin signalDim,
      bb84SiftedConditionOp b x k y a *
          ψ.toOp (finProdFinEquiv (a, r)) (finProdFinEquiv (c, r')) *
          bb84SiftedConditionOp b x k c y =
        ψ.toOp (finProdFinEquiv (a, r)) (finProdFinEquiv (c, r')) *
          (bb84SiftedConditionOp b x k c y * bb84SiftedConditionOp b x k y a) := by
    intro y; ring
  simp_rw [hstep]
  rw [← Finset.mul_sum, ← Matrix.mul_apply, bb84SiftedConditionOp_idem]
  ring

/-- On a round that is not an X-test round (`b && x = false`, i.e. every key round and every
Z-test PE round) the sift is the identity. -/
lemma bb84SiftedSinglePairOp_of_not_xTest (b x : Bool) (h : (b && x) = false) :
    bb84SiftedSinglePairOp b x = (1 : Op signalDim) := by
  unfold bb84SiftedSinglePairOp
  rw [ite_eq_right (by simp [h])]

/-- On a non-X-test round the conditioning operator is the bare computational projector
`|k⟩⟨k|`. -/
lemma bb84SiftedConditionOp_of_not_xTest (b x : Bool) (h : (b && x) = false)
    (k : Fin signalDim) :
    bb84SiftedConditionOp b x k = bb84ComputationalPOVM k := by
  unfold bb84SiftedConditionOp
  rw [bb84SiftedSinglePairOp_of_not_xTest b x h, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one]

/-- **On a non-X-test round the block IS the referee key-round block.**  `b && x = false`
covers every key round (`peSel = false`) and every Z-test PE round (`xSel = false`), on both of
which the sift and the referee key-round sift are the same operator `1`.  This is what lets the
Devetak–Winter / AEP rate layer built on `bb84RefereeSiftedSingleRoundRefBlock ψ false` be reused
unchanged: the protocol changes only the X-test PE factor. -/
lemma bb84SiftedSingleRoundRefBlock_eq_of_not_xTest
    (ψ : DensityOp (signalDim * signalDim)) (b x : Bool) (h : (b && x) = false)
    (k : Fin signalDim) :
    bb84SiftedSingleRoundRefBlock ψ b x k = bb84RefereeSiftedSingleRoundRefBlock ψ false k := by
  apply SubDensityOp.ext
  rw [bb84SiftedSingleRoundRefBlock_toOp, bb84RefereeSiftedSingleRoundRefBlock_toOp,
    bb84SiftedConditionOp_of_not_xTest b x h, bb84RefereeSiftedConditionOp_false]

/-- The single-round conditioning operators sum to the identity over the outcome `k`. -/
lemma bb84SiftedConditionOp_sum (b x : Bool) :
    ∑ k : Fin signalDim, bb84SiftedConditionOp b x k = (1 : Op signalDim) := by
  simp only [bb84SiftedConditionOp]
  rw [← Finset.sum_mul, ← Finset.mul_sum, bb84ComputationalPOVM_complete, Matrix.mul_one,
    bb84SiftedSinglePairOp_unitary b x]

/-- The single-round reference blocks have total weight one (over the outcome `k`). -/
lemma bb84SiftedRoundBlock_trace_sum (ψ : DensityOp (signalDim * signalDim)) (b x : Bool) :
    ∑ k : Fin signalDim, (bb84SiftedSingleRoundRefBlock ψ b x k).trace = 1 := by
  have heach : ∀ k : Fin signalDim, (bb84SiftedSingleRoundRefBlock ψ b x k).trace =
      ((bb84SiftedConditionOp b x k) * partialTraceB ψ.toOp).trace.re := by
    intro k
    rw [SubDensityOp.trace, bb84SiftedSingleRoundRefBlock_toOp,
      trace_partialTraceA_projector_sandwich_eq_trace_projector_partialTraceB
        (bb84SiftedConditionOp b x k) ψ.toOp (bb84SiftedConditionOp_idem b x k)]
  simp_rw [heach]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, bb84SiftedConditionOp_sum,
    Matrix.one_mul, trace_partialTraceB, ψ.trace_one, Complex.one_re]

/-- Entry of the single-round conditioning operator `C = Vᴴ|k⟩⟨k|V`:
`C_{s',s} = conj(V_{k,s'}) · V_{k,s}`. -/
lemma bb84SiftedConditionOp_entry (b x : Bool) (k s' s : Fin signalDim) :
    bb84SiftedConditionOp b x k s' s =
      star (bb84SiftedSinglePairOp b x k s') * bb84SiftedSinglePairOp b x k s := by
  unfold bb84SiftedConditionOp bb84ComputationalPOVM
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · simp [Matrix.conjTranspose_apply]
    · intro p _ hp; simp [hp.symm]
    · intro h; exact absurd (Finset.mem_univ k) h
  · intro j _ hj
    rw [Matrix.mul_apply, Finset.sum_eq_zero (fun p _ => ?_), zero_mul]
    simp [hj.symm]
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ## The per-round factorization of the trivial-attack sifted τ-block -/

/-- Entry form of `Op.castDim`.  Local copy of the private `op_castDim_apply_localSRF`. -/
private lemma op_castDim_apply_localSRF {d e : ℕ} (h : d = e) (A : Op d) (i j : Fin e) :
    (Op.castDim h A) i j = A (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h; rfl

/-- The index identity behind the eveDim-`1` collapse.  Local copy of the private
`unitFactor_collapse_idx`. -/
private lemma unitFactor_collapse_idx {m : ℕ} [NeZero m] (h : m * m = (m * 1) * m)
    (p : Fin ((m * 1) * m)) :
    finProdFinEquiv
        ((finProdFinEquiv.symm (finProdFinEquiv.symm p).1).1, (finProdFinEquiv.symm p).2) =
      Fin.cast h.symm p := by
  set a : Fin (m * 1) := (finProdFinEquiv.symm p).1 with ha
  set s : Fin m := (finProdFinEquiv.symm p).2 with hs
  set a' : Fin m := (finProdFinEquiv.symm a).1 with ha'
  set c : Fin 1 := (finProdFinEquiv.symm a).2 with hc
  have hp : finProdFinEquiv (a, s) = p := by
    rw [ha, hs, Prod.mk.eta, Equiv.apply_symm_apply]
  have hav : finProdFinEquiv (a', c) = a := by
    rw [ha', hc, Prod.mk.eta, Equiv.apply_symm_apply]
  apply Fin.ext
  rw [Fin.val_cast, ← hp, ← hav]
  simp only [finProdFinEquiv_apply_val]
  have hc0 : (c : ℕ) = 0 := by omega
  rw [hc0]
  ring

/-- **Conjugation + eveDim-`1` collapse, double-sum form.**  At the trivial attack the sifted
τ-conditioned Eve/reference block reads, entrywise, the `bb84SiftedRotation`-conjugated reindexed
tensor-power source over the signal register, the eveDim-`1` register having collapsed to a point.
-/
lemma bb84SiftedTauEveRefConditioned_trivial_entry
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ψ : DensityOp (signalDim * signalDim))
    (ω : Fin n → Fin signalDim)
    (i j : Fin (1 * signalDim ^ n)) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    (bb84SiftedTauEveRefConditioned 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
        peSel xSel
        (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)) ω).toOp i j =
      ∑ sa : Fin (signalDim ^ n), ∑ sc : Fin (signalDim ^ n),
        bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) sa *
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp
            (finProdFinEquiv (sa, (finProdFinEquiv.symm i).2))
            (finProdFinEquiv (sc, (finProdFinEquiv.symm j).2)) *
          star (bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) sc) := by
  have : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hss : Subsingleton (Fin 1) :=
    inferInstanceAs (Subsingleton (Fin 1))
  simp only [bb84SiftedTauEveRefConditioned, Matrix.submatrix_apply,
    bb84SiftedTauPreOutputDensity, densityOpUnitaryConj_toOp,
    bb84TauOutputDensity, bb84TauOutputOp]
  rw [bb84_mapTensorId_unitRegisterEmbed_eq_castDim, Op.tensor_conjTranspose, conjTranspose_one,
    bb84TauOutcomeEveRefEmbedding, bb84TauOutcomeEveRefEmbedding]
  rw [tensor_one_mul_mul_conjTranspose_tensor_one_apply]
  simp only [Op_tensor_apply_finProd, Equiv.symm_apply_apply, op_castDim_apply_localSRF]
  have h1 : ∀ p q : Fin 1,
      (1 : Op 1) p q = 1 := by
    intro p q; rw [Subsingleton.elim p q, Matrix.one_apply_eq]
  simp only [h1, mul_one]
  have hcast : ∀ (hc : signalDim ^ n * 1 * signalDim ^ n =
        signalDim ^ n * signalDim ^ n)
      (y : Fin (signalDim ^ n * 1)) (r : Fin (signalDim ^ n)),
      Fin.cast hc (finProdFinEquiv (y, r)) =
        finProdFinEquiv ((finProdFinEquiv.symm y).1, r) := by
    intro hc y r
    have hci := unitFactor_collapse_idx (m := signalDim ^ n) (by rw [Nat.mul_one])
      (finProdFinEquiv (y, r))
    simp only [Equiv.symm_apply_apply] at hci
    exact hci.symm
  have hsum_collapse : ∀ (g : Fin (signalDim ^ n) → ℂ),
      (∑ y : Fin (signalDim ^ n * 1),
          g (finProdFinEquiv.symm y).1) = ∑ sa : Fin (signalDim ^ n), g sa := by
    intro g
    rw [← Equiv.sum_comp finProdFinEquiv (fun y => g (finProdFinEquiv.symm y).1),
      Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
    refine Finset.sum_congr rfl (fun sa _ => ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  simp only [hcast]
  refine
    (Finset.sum_congr rfl fun y _ =>
      hsum_collapse fun sc =>
        bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) (finProdFinEquiv.symm y).1 *
            (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp
              (finProdFinEquiv ((finProdFinEquiv.symm y).1, (finProdFinEquiv.symm i).2))
              (finProdFinEquiv (sc, (finProdFinEquiv.symm j).2)) *
          star (bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) sc)).trans
    (hsum_collapse fun sa =>
      ∑ sc, bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) sa *
            (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp
              (finProdFinEquiv (sa, (finProdFinEquiv.symm i).2))
              (finProdFinEquiv (sc, (finProdFinEquiv.symm j).2)) *
          star (bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) sc))

/-- **Per-round factorization of the trivial-attack sifted double sum.**  The
`bb84SiftedRotation`-conjugated reindexed tensor-power source factorizes over rounds into the
single-round reference blocks (round-major order; the source `tensorPowGen` and the rotation both
index by `finFunctionFinEquiv`, no `Fin.rev`). -/
lemma bb84_siftedTrivial_doubleSum_eq_prod
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ψ : DensityOp (signalDim * signalDim))
    (ω : Fin n → Fin signalDim) (ri rj : Fin (signalDim ^ n)) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    (∑ sa : Fin (signalDim ^ n), ∑ sc : Fin (signalDim ^ n),
        bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) sa *
          (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp
            (finProdFinEquiv (sa, ri)) (finProdFinEquiv (sc, rj)) *
          star (bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) sc)) =
      ∏ b : Fin n, (bb84SiftedSingleRoundRefBlock ψ (peSel b) (xSel b) (ω b)).toOp
        ((finFunctionFinEquiv.symm ri) b) ((finFunctionFinEquiv.symm rj) b) := by
  have : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have : NeZero ((signalDim * signalDim) ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  have hV : ∀ s : Fin (signalDim ^ n),
      bb84SiftedRotation n peSel xSel (bb84OutcomeIndex ω) s =
        ∏ b : Fin n, bb84SiftedSinglePairOp (peSel b) (xSel b) (ω b)
          ((finFunctionFinEquiv.symm s) b) := by
    intro s
    simp only [bb84SiftedRotation, tensorFamily_apply, bb84OutcomeIndex, Equiv.symm_apply_apply]
  have hint : ∀ u v : Fin (signalDim ^ n),
      interleavingEquiv signalDim n (finProdFinEquiv (u, v)) =
        finFunctionFinEquiv (fun b => finProdFinEquiv
          ((finFunctionFinEquiv.symm u) b, (finFunctionFinEquiv.symm v) b)) := by
    intro u v
    simp only [interleavingEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  have hτ : ∀ sa sc : Fin (signalDim ^ n),
      (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp
          (finProdFinEquiv (sa, ri)) (finProdFinEquiv (sc, rj)) =
        ∏ b : Fin n, ψ.toOp
          (finProdFinEquiv ((finFunctionFinEquiv.symm sa) b, (finFunctionFinEquiv.symm ri) b))
          (finProdFinEquiv ((finFunctionFinEquiv.symm sc) b, (finFunctionFinEquiv.symm rj) b)) := by
    intro sa sc
    rw [show (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)).toOp
          (finProdFinEquiv (sa, ri)) (finProdFinEquiv (sc, rj)) =
        (ψ.tensorPowGen n).toOp
          (interleavingEquiv signalDim n (finProdFinEquiv (sa, ri)))
          (interleavingEquiv signalDim n (finProdFinEquiv (sc, rj))) from by
      simp [densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]]
    rw [hint, hint]
    exact tensorPowGen_toOp_eq_prod ψ _ _
  have hfactor : ∀ b : Fin n,
      (∑ s : Fin signalDim, ∑ s' : Fin signalDim,
        bb84SiftedSinglePairOp (peSel b) (xSel b) (ω b) s *
          ψ.toOp (finProdFinEquiv (s, finFunctionFinEquiv.symm ri b))
            (finProdFinEquiv (s', finFunctionFinEquiv.symm rj b)) *
          star (bb84SiftedSinglePairOp (peSel b) (xSel b) (ω b) s')) =
        (bb84SiftedSingleRoundRefBlock ψ (peSel b) (xSel b) (ω b)).toOp
          (finFunctionFinEquiv.symm ri b) (finFunctionFinEquiv.symm rj b) := by
    intro b
    rw [bb84SiftedSingleRoundRefBlock_toOp_entry]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => ?_))
    rw [bb84SiftedConditionOp_entry]; ring
  simp_rw [hV, hτ, star_prod, ← Finset.prod_mul_distrib,
    ← Equiv.sum_comp finFunctionFinEquiv, Equiv.symm_apply_apply]
  simp_rw [← hfactor, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **KEYSTONE — the per-round factorization of the trivial-attack τ-block.**

At the trivial attack the sifted τ-conditioned de-Finetti reference block factorizes over rounds
into the single-round reference blocks.  Because the source `tensorPowGen` /
`bb84SiftedRotation` index round-major (`finFunctionFinEquiv`) while `SubDensityOp.tensorFinProd`
uses the reversed (`Fin.rev`) convention, the tensor-product factor at position `a` is the
round-`Fin.rev a` block.

It is this product structure — a factor per round, each
carrying its own reference block — that the per-Carathéodory labeled-announce step consumes; round
disjointness alone does not suffice. -/
theorem bb84_siftedUnitRegisterEmbed_tauConditioned_eq_tensorFinProd
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (ψ : DensityOp (signalDim * signalDim))
    (ω : Fin n → Fin signalDim) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    bb84SiftedTauEveRefConditioned 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
        peSel xSel
        (densityOp_reindex (interleavingEquiv signalDim n).symm (ψ.tensorPowGen n)) ω =
      SubDensityOp.castDim (by rw [Nat.one_mul])
        (SubDensityOp.tensorFinProd n
          (fun a => bb84SiftedSingleRoundRefBlock ψ (peSel (Fin.rev a)) (xSel (Fin.rev a))
            (ω (Fin.rev a)))) := by
  have : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  apply SubDensityOp.ext
  ext i j
  have hicast : ∀ (h : 1 * signalDim ^ n = signalDim ^ n)
      (p : Fin (1 * signalDim ^ n)),
      Fin.cast h p = (finProdFinEquiv.symm p).2 := by
    intro h p
    apply Fin.ext
    simp only [Fin.val_cast, finProdFinEquiv_symm_apply, Fin.coe_modNat]
    exact (Nat.mod_eq_of_lt (lt_of_lt_of_le p.isLt
      (le_of_eq (by rw [Nat.one_mul])))).symm
  rw [bb84SiftedTauEveRefConditioned_trivial_entry, SubDensityOp.castDim_toOp_cast,
    bb84_siftedTrivial_doubleSum_eq_prod]
  simp only [hicast]
  rw [show (finProdFinEquiv.symm i).2 =
        finFunctionFinEquiv (finFunctionFinEquiv.symm (finProdFinEquiv.symm i).2) from
      (Equiv.apply_symm_apply _ _).symm,
    show (finProdFinEquiv.symm j).2 =
        finFunctionFinEquiv (finFunctionFinEquiv.symm (finProdFinEquiv.symm j).2) from
      (Equiv.apply_symm_apply _ _).symm,
    InfoTheory.SmoothMinEntropy.SubDensityOp.tensorFinProd_toOp_entry_prod_fwd]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  simp [Fin.rev_rev]

/-! ## The accept test on the sorted PE rounds -/

/-- **The fail-closed LOCC two-basis PE test depends only on the PE-round outcomes.**  If two
outcome strings agree on every PE round (`peSel a = true ⟹ ω a = ω' a`), the test returns the
same verdict: both subsample error counts filter on `peSel i = true`, and the two subsample sizes do
not depend on `ω` at all. -/
theorem bb84SiftedLocalPETestPassed_key_indep {n : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (ω ω' : Fin n → Fin signalDim)
    (h : ∀ a, peSel a = true → ω a = ω' a) :
    bb84SiftedLocalPETestPassed peSel xSel δ Q ω =
      bb84SiftedLocalPETestPassed peSel xSel δ Q ω' := by
  have hZ : bb84SiftedZTestErrorCount peSel xSel ω = bb84SiftedZTestErrorCount peSel xSel ω' := by
    unfold bb84SiftedZTestErrorCount
    congr 1
    apply Finset.filter_congr
    intro i _
    by_cases hpe : peSel i = true
    · rw [h i hpe]
    · simp [hpe]
  have hX : bb84SiftedXTestErrorCount peSel xSel ω = bb84SiftedXTestErrorCount peSel xSel ω' := by
    unfold bb84SiftedXTestErrorCount
    congr 1
    apply Finset.filter_congr
    intro i _
    by_cases hpe : peSel i = true
    · rw [h i hpe]
    · simp [hpe]
  simp only [bb84SiftedLocalPETestPassed, hZ, hX]

/-! ## The accept test and PE-round product at a general test-set size `m`

Nahar, Tupkary, Zhao, Lütkenhaus and Tan state the protocol for a **general** test-set size `m`:
arXiv:2403.11851, `main.tex:909` ("They then choose a random subset of $m$ signals, and
announce their measurement outcomes for those rounds in the register $\Cat^m$") and `:913` ("For the
remaining $\nkey=n-m$ signals"), both inside `\subsection{Classical part}` (`:906`) of
`\section{Application to the Three State Protocol}` (`\label{sec:applicationtothreestate}`, `:829`).
The decls above pin `m = ⌈n/2⌉` through the closed term `bb84KeyRoundCountCanonical n = n − ⌈n/2⌉`;
the three decls below are their general-`m` forms, over the split-point-parametrised round partition
`bb84KeyRoundCount`, `bb84PERoundIdx`, `bb84PartEquiv`, `bb84KeyCount`.

Substituting `m := ⌈n/2⌉` into the general-`m` forms recovers
`bb84SiftedPEPass` and `bb84SiftedPERoundProd` definitionally, with no `castDim` transport.

The three general-`m` forms below carry **no** constraint relating `m` to `n`; in particular they do
not carry `2·m ≤ n`.  They are round-partition statements: the split point enters only through
`bb84KeyRoundCount` and the selector's own counting hypothesis, and neither compares `m` with
`n`.  `m = 0` and `m = n` are covered and degenerate rather than excluded.
-/

/-- **The PE-pass verdict read off the sorted PE-round outcomes, at a general test-set size `m`.**

The fail-closed LOCC two-basis test
`bb84SiftedLocalPETestPassed` evaluated on any outcome string extending `p` on the `m` sorted PE
rounds, realised by extending `p` with the all-`0` key string through the general-`m` partition
equivalence `bb84PartEquiv`.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
def bb84SiftedPEPass {n m : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (p : Fin (n - bb84KeyRoundCount n m) → Fin signalDim) : Bool :=
  bb84SiftedLocalPETestPassed peSel xSel δ Q
    ((bb84PartEquiv (m := m) peSel).symm ((fun _ => 0), p))

/-- **The PE test factors through the sorted PE-round outcomes, at a general test-set size `m`**
(fibre form).

For any outcome string `ω`, the
fail-closed LOCC two-basis verdict equals the general-`m` PE-pass verdict on `ω`'s sorted PE-round
restriction.  The `hcount : bb84KeyCount n m peSel` hypothesis is what converts the subtype
indexing of the PE rounds to the sorted `bb84PERoundIdx`.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
lemma bb84SiftedLocalPETestPassed_eq_pePass {n m : ℕ} (peSel xSel : Fin n → Bool)
    (δ Q : ℝ) (hcount : bb84KeyCount n m peSel) (ω : Fin n → Fin signalDim) :
    bb84SiftedLocalPETestPassed peSel xSel δ Q ω =
      bb84SiftedPEPass (m := m) peSel xSel δ Q (bb84PartEquiv (m := m) peSel ω).2 := by
  unfold bb84SiftedPEPass
  apply bb84SiftedLocalPETestPassed_key_indep
  intro a ha
  obtain ⟨j, rfl⟩ := bb84_peRound_eq_peIdx peSel hcount a ha
  rw [bb84PartEquiv_symm_apply_peIdx, bb84PartEquiv_apply_snd]

/-- **The PE-round product factor `ρ_PE` at a general test-set size `m`.**

The general-`m`-PE-pass-filtered finite tensor
product of the single-round reference blocks over the `n − bb84KeyRoundCount n m = m` sorted
PE rounds.  The `j`-th factor is read in the frame of its own round — the `H ⊗ H`-rotated frame when
the sorted PE round `bb84PERoundIdx peSel j` is X-designated, the computational `Z` frame when
it is Z-designated.  Classical register the sorted PE outcomes, quantum the PE reference
`4^{n − n_K}`.  Mentions no key string, so key-independence is syntactic.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
noncomputable def bb84SiftedPERoundProd {n m : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    CQState (Fin (n - bb84KeyRoundCount n m) → Fin signalDim)
      (signalDim ^ (n - bb84KeyRoundCount n m)) where
  stateMap p :=
    if bb84SiftedPEPass (m := m) peSel xSel δ Q p then
      SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
        (fun j => bb84SiftedSingleRoundRefBlock ψ true
          (xSel (bb84PERoundIdx peSel j)) (p j))
    else 0
  weight_le_one := by
    have : NeZero signalDim := ⟨by norm_num [signalDim]⟩
    calc ∑ p : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
            (if bb84SiftedPEPass (m := m) peSel xSel δ Q p then
              SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
                (fun j => bb84SiftedSingleRoundRefBlock ψ true
                  (xSel (bb84PERoundIdx peSel j)) (p j))
            else 0).trace
        ≤ ∑ p : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
            (SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
              (fun j => bb84SiftedSingleRoundRefBlock ψ true
                (xSel (bb84PERoundIdx peSel j)) (p j))).trace := by
          apply Finset.sum_le_sum
          intro p _
          by_cases hp : bb84SiftedPEPass (m := m) peSel xSel δ Q p
          · rw [ite_eq_left hp]
          · rw [ite_eq_right hp]
            have hz : (0 : SubDensityOp
                (signalDim ^ (n - bb84KeyRoundCount n m))).trace = 0 := by
              rw [SubDensityOp.trace]
              change (Matrix.trace
                (0 : Op (signalDim ^ (n - bb84KeyRoundCount n m)))).re = 0
              simp
            rw [hz]
            exact (SubDensityOp.tensorFinProd (n - bb84KeyRoundCount n m)
              (fun j => bb84SiftedSingleRoundRefBlock ψ true
                (xSel (bb84PERoundIdx peSel j)) (p j))).trace_nonneg
      _ = ∑ p : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
            ∏ j : Fin (n - bb84KeyRoundCount n m),
              (bb84SiftedSingleRoundRefBlock ψ true
                (xSel (bb84PERoundIdx peSel j)) (p j)).trace := by
          apply Finset.sum_congr rfl
          intro p _
          exact SubDensityOp.tensorFinProd_trace _ _
      _ = ∏ j : Fin (n - bb84KeyRoundCount n m),
            ∑ k : Fin signalDim,
              (bb84SiftedSingleRoundRefBlock ψ true
                (xSel (bb84PERoundIdx peSel j)) k).trace := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      _ = 1 := by
          simp only [bb84SiftedRoundBlock_trace_sum, Finset.prod_const_one]

end QKD.BB84.Engine

end -- noncomputable section
