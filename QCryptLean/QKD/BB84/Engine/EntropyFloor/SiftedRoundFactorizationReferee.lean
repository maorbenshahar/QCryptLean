import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.Quantum.TensorProducts.ProjectiveConditioning
import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PostMeasurementCQ
import QCryptLean.InfoTheory.DeFinetti.Theorem.Interleaving
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.QKD.BB84.Engine.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.Engine.Budgets.SmoothEntropyBound
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.TensorFinProdPartition

/-!
# Sifted single-round reference blocks and the trivial-attack channel collapse

This module carries the **per-round** data and small helper lemmas used by the per-round
factorization of the de-Finetti reference at the trivial attack.

## Main definitions
- `bb84RefereeSiftedSingleRoundRefBlock` (Def 1): the single-round sifted-measured reference block
of a
  pure paired state `ψ` on `A⊗R₀ = ℂ⁴⊗ℂ⁴`.
- `bb84SiftedKeyRoundCQ` (Def 2): the ψ-reference single-round Alice-`Z` bit-CQ state (key round).

## Main results
- `bb84_mapTensorId_unitRegisterEmbed_eq_castDim` (L0): at the unit register embedding the
  `mapTensorId`-extended pre-channel is the dimension cast that absorbs the one-dimensional Eve
  register.

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

/-! ## The single-round sifted conditioning projector `P_{b,k} = Vᴴ |k⟩⟨k| V` -/

/-- The single-round sifted conditioning operator: rotate the computational projector `|k⟩⟨k|` by
    the
per-round sifted op (`V` on a PE round, `1` on a key round).  Explicit; no `Classical.choose`. -/
def bb84RefereeSiftedConditionOp (b : Bool) (k : Fin signalDim) : Op signalDim :=
  (bb84RefereeSiftedSinglePairOp b)ᴴ * bb84ComputationalPOVM k * bb84RefereeSiftedSinglePairOp b

/-- `bb84RefereeSiftedConditionOp` is Hermitian. -/
lemma bb84RefereeSiftedConditionOp_isHermitian (b : Bool) (k : Fin signalDim) :
    (bb84RefereeSiftedConditionOp b k)ᴴ = bb84RefereeSiftedConditionOp b k := by
  unfold bb84RefereeSiftedConditionOp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (bb84ComputationalPOVM_isHermitian k).eq, Matrix.mul_assoc]

/-- The per-round sifting op satisfies `V Vᴴ = 1` (from `Vᴴ V = 1` on a square matrix). -/
lemma bb84RefereeSiftedSinglePairOp_mul_conjTranspose (b : Bool) :
    bb84RefereeSiftedSinglePairOp b * (bb84RefereeSiftedSinglePairOp b)ᴴ = (1 : Op signalDim) :=
  mul_eq_one_comm.mp (bb84RefereeSiftedSinglePairOp_unitary b)

/-- `bb84RefereeSiftedConditionOp` is idempotent: `Vᴴ |k⟩⟨k| V Vᴴ |k⟩⟨k| V = Vᴴ |k⟩⟨k| V`
(using `V Vᴴ = 1` and `|k⟩⟨k|` idempotent). -/
lemma bb84RefereeSiftedConditionOp_idem (b : Bool) (k : Fin signalDim) :
    bb84RefereeSiftedConditionOp b k * bb84RefereeSiftedConditionOp b k =
        bb84RefereeSiftedConditionOp b k := by
  unfold bb84RefereeSiftedConditionOp
  calc (bb84RefereeSiftedSinglePairOp b)ᴴ * bb84ComputationalPOVM k *
          bb84RefereeSiftedSinglePairOp b *
          ((bb84RefereeSiftedSinglePairOp b)ᴴ * bb84ComputationalPOVM k *
              bb84RefereeSiftedSinglePairOp b)
         = (bb84RefereeSiftedSinglePairOp b)ᴴ * bb84ComputationalPOVM k *
          (bb84RefereeSiftedSinglePairOp b * (bb84RefereeSiftedSinglePairOp b)ᴴ) *
          (bb84ComputationalPOVM k * bb84RefereeSiftedSinglePairOp b) := by
        simp only [Matrix.mul_assoc]
    _ = (bb84RefereeSiftedSinglePairOp b)ᴴ * bb84ComputationalPOVM k *
          (bb84ComputationalPOVM k * bb84RefereeSiftedSinglePairOp b) := by
        rw [bb84RefereeSiftedSinglePairOp_mul_conjTranspose, Matrix.mul_one]
    _ = (bb84RefereeSiftedSinglePairOp b)ᴴ * (bb84ComputationalPOVM k * bb84ComputationalPOVM k) *
          bb84RefereeSiftedSinglePairOp b := by
        simp only [Matrix.mul_assoc]
    _ = (bb84RefereeSiftedSinglePairOp b)ᴴ * bb84ComputationalPOVM k *
          bb84RefereeSiftedSinglePairOp b := by
        rw [bb84ComputationalPOVM_isProjection]

/-! ## Def 1 — the single-round sifted reference block -/

/-- **Single-round sifted-measured reference block of a pure paired state `ψ` on `A⊗R₀ = ℂ⁴⊗ℂ⁴`**
rotate the signal by the per-round sifted op `bb84RefereeSiftedSinglePairOp b` (`V` on a PE round,
`1` on a key round), project the signal onto the computational `|k⟩`, trace out the signal. The
conditioned reference block on `R₀ = ℂ⁴`.  Sifted single-round analogue of the Schrödinger block
read by `bb84ComponentAliceZCQState_origin`. -/
noncomputable def bb84RefereeSiftedSingleRoundRefBlock
    (ψ : DensityOp (signalDim * signalDim)) (b : Bool) (k : Fin signalDim) :
    SubDensityOp signalDim where
  toOp :=
    partialTraceA (Op.tensor (bb84RefereeSiftedConditionOp b k) (1 : Op signalDim) * ψ.toOp
      * Op.tensor (bb84RefereeSiftedConditionOp b k) (1 : Op signalDim))
  isHermitian :=
    partialTraceA_projector_sandwich_isHermitian (bb84RefereeSiftedConditionOp b k) ψ.toOp
      (bb84RefereeSiftedConditionOp_isHermitian b k)
      (posSemidefOp_implies_mathlib ψ.toPosSemidefOp).isHermitian
  pos_semidef :=
    partialTraceA_projector_sandwich_quadraticForm_re_nonneg (bb84RefereeSiftedConditionOp b k)
        ψ.toOp
      (bb84RefereeSiftedConditionOp_isHermitian b k)
      (posSemidefOp_implies_mathlib ψ.toPosSemidefOp)
  trace_le_one := by
    refine le_trans
        (trace_partialTraceA_projector_sandwich_le (bb84RefereeSiftedConditionOp b k) ψ.toOp
      (bb84RefereeSiftedConditionOp_idem b k) (bb84RefereeSiftedConditionOp_isHermitian b k)
      (posSemidefOp_implies_mathlib ψ.toPosSemidefOp)) ?_
    rw [ψ.trace_one]; simp

@[simp] lemma bb84RefereeSiftedSingleRoundRefBlock_toOp
    (ψ : DensityOp (signalDim * signalDim)) (b : Bool) (k : Fin signalDim) :
    (bb84RefereeSiftedSingleRoundRefBlock ψ b k).toOp =
      partialTraceA (Op.tensor (bb84RefereeSiftedConditionOp b k) (1 : Op signalDim) * ψ.toOp
        * Op.tensor (bb84RefereeSiftedConditionOp b k) (1 : Op signalDim)) := rfl

/-- **Entry formula for the single-round sifted reference block.**  At reference indices `r r'`
the conditioned block reads the `bb84RefereeSiftedConditionOp`-weighted single-round paired entries
of `ψ`: `Block_{r,r'} = ∑_{t,t'} C_{t',t} · ψ_{(t,r),(t',r')}` with `C = Vᴴ|k⟩⟨k|V`.  This is
`partialTraceA` of the `(C⊗1)`-sandwich expanded entrywise via
`Quantum.TensorProducts.tensor_one_mul_mul_tensor_one_apply`, collapsed using the idempotence of
`C`. -/
lemma bb84RefereeSiftedSingleRoundRefBlock_toOp_entry
    (ψ : DensityOp (signalDim * signalDim)) (b : Bool) (k r r' : Fin signalDim) :
    (bb84RefereeSiftedSingleRoundRefBlock ψ b k).toOp r r' =
      ∑ t : Fin signalDim, ∑ t' : Fin signalDim,
        bb84RefereeSiftedConditionOp b k t' t *
          ψ.toOp (finProdFinEquiv (t, r)) (finProdFinEquiv (t', r')) := by
  rw [bb84RefereeSiftedSingleRoundRefBlock_toOp]
  simp only [partialTraceA, Matrix.of_apply]
  simp_rw [Quantum.TensorProducts.tensor_one_mul_mul_tensor_one_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hstep : ∀ x : Fin signalDim,
      bb84RefereeSiftedConditionOp b k x a *
          ψ.toOp (finProdFinEquiv (a, r)) (finProdFinEquiv (c, r')) *
          bb84RefereeSiftedConditionOp b k c x =
        ψ.toOp (finProdFinEquiv (a, r)) (finProdFinEquiv (c, r')) *
          (bb84RefereeSiftedConditionOp b k c x * bb84RefereeSiftedConditionOp b k x a) := by
    intro x; ring
  simp_rw [hstep]
  rw [← Finset.mul_sum, ← Matrix.mul_apply, bb84RefereeSiftedConditionOp_idem]
  ring

/-- On a **key** round (`b = false`, so `V = 1`) the sifted conditioning operator is the bare
computational projector `|k⟩⟨k|`. -/
lemma bb84RefereeSiftedConditionOp_false (k : Fin signalDim) :
    bb84RefereeSiftedConditionOp false k = bb84ComputationalPOVM k := by
  unfold bb84RefereeSiftedConditionOp bb84RefereeSiftedSinglePairOp
  simp

/-- **Key-round single-round reference block entry.**  On a key round the diagonal computational
conditioning reads the paired entry `ψ_{(k,r),(k,r')}` (the `|k⟩⟨k|` sandwich collapses the double
sum of `bb84RefereeSiftedSingleRoundRefBlock_toOp_entry`). -/
lemma bb84RefereeSiftedSingleRoundRefBlock_false_toOp_entry
    (ψ : DensityOp (signalDim * signalDim)) (k r r' : Fin signalDim) :
    (bb84RefereeSiftedSingleRoundRefBlock ψ false k).toOp r r' =
      ψ.toOp (finProdFinEquiv (k, r)) (finProdFinEquiv (k, r')) := by
  rw [bb84RefereeSiftedSingleRoundRefBlock_toOp_entry, bb84RefereeSiftedConditionOp_false]
  simp only [bb84ComputationalPOVM, Matrix.single_apply, ite_mul, one_mul, zero_mul, ite_and,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The single-round sifted conditioning operators sum to the identity over the outcome `k`
(`∑_k Vᴴ |k⟩⟨k| V = Vᴴ (∑_k |k⟩⟨k|) V = Vᴴ V = 1`). -/
lemma bb84RefereeSiftedConditionOp_sum (b : Bool) :
    ∑ k : Fin signalDim, bb84RefereeSiftedConditionOp b k = (1 : Op signalDim) := by
  simp only [bb84RefereeSiftedConditionOp]
  rw [← Finset.sum_mul, ← Finset.mul_sum, bb84ComputationalPOVM_complete, Matrix.mul_one,
    bb84RefereeSiftedSinglePairOp_unitary b]

/-- The single-round sifted reference blocks have total weight one (over the outcome `k`). -/
lemma bb84RefereeSiftedRoundBlock_trace_sum (ψ : DensityOp (signalDim * signalDim)) (b : Bool) :
    ∑ k : Fin signalDim, (bb84RefereeSiftedSingleRoundRefBlock ψ b k).trace = 1 := by
  have heach : ∀ k : Fin signalDim, (bb84RefereeSiftedSingleRoundRefBlock ψ b k).trace =
      ((bb84RefereeSiftedConditionOp b k) * partialTraceB ψ.toOp).trace.re := by
    intro k
    rw [SubDensityOp.trace, bb84RefereeSiftedSingleRoundRefBlock_toOp,
      trace_partialTraceA_projector_sandwich_eq_trace_projector_partialTraceB
        (bb84RefereeSiftedConditionOp b k) ψ.toOp (bb84RefereeSiftedConditionOp_idem b k)]
  simp_rw [heach]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, bb84RefereeSiftedConditionOp_sum,
    Matrix.one_mul, trace_partialTraceB, ψ.trace_one, Complex.one_re]

/-! ## Def 2 — the ψ-reference key and PE round CQ factors -/

/-- **ψ-reference single-round key-round block CQ object**: the per-round
sifted conditioning of `ψ` on a **key** round (`b = false`, so `V = 1` and the signal is read in the
computational `Z` basis), packaged as a finite CQ state with classical register the computational
outcome `Fin signalDim` and quantum register the reference `R₀ = ℂ⁴`. -/
noncomputable def bb84SiftedKeyRoundCQRaw (ψ : DensityOp (signalDim * signalDim)) :
    CQState (Fin signalDim) signalDim where
  stateMap := fun k => bb84RefereeSiftedSingleRoundRefBlock ψ false k
  weight_le_one := le_of_eq (bb84RefereeSiftedRoundBlock_trace_sum ψ false)

/-- **ψ-reference single-round Alice-`Z` bit-CQ state** (key round): coarsen the
key-round computational block `bb84SiftedKeyRoundCQRaw` by `bb84AliceBitMap` (`k ↦ k/2`, Alice's
bit). Its `n_K`-fold `CQState.tensorPower` is the ψ-reference counterpart of the canonical
`ρ_σ^{⊗n_K}`, identified with the canonical via the purification unitary `W` at the bridge. -/
noncomputable def bb84SiftedKeyRoundCQ (ψ : DensityOp (signalDim * signalDim)) :
    CQState (Fin 2) signalDim :=
  CQState.coarsen bb84AliceBitMap (bb84SiftedKeyRoundCQRaw ψ)

/-! ## L0 — the trivial-attack channel collapses the one-dimensional Eve register -/

/-- Entry form of `Op.castDim`. -/
private lemma op_castDim_apply_localSRF {d e : ℕ} (h : d = e) (A : Op d) (i j : Fin e) :
    (Op.castDim h A) i j = A (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h; rfl

/-- The index identity behind the eveDim-`1` collapse: a `Fin ((m*1)*m)` index, after extracting
the leading `Fin m` digit through the trivial middle `Fin 1` factor, casts back to `Fin (m*m)`. -/
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

/-- **L0 — at the unit register embedding the `mapTensorId`-extended
pre-channel is the dimension cast.**  The pre-channel is `A ↦ A ⊗ 1₁`, so applying it to the first
tensor factor and inserting the one-dimensional side register is the identity up to the
`m*m = (m*1)*m` dimension cast: the side register collapses to a point.

No attack object appears; this is generic in the pre-channel. -/
theorem bb84_mapTensorId_unitRegisterEmbed_eq_castDim {n : ℕ} [NeZero (4 ^ n)]
    (M : Op (4 ^ n * 4 ^ n)) :
    mapTensorId (bb84UnitRegisterEmbed n) M =
      Op.castDim (by rw [Nat.mul_one]) M := by
  ext p q
  rw [op_castDim_apply_localSRF]
  simp only [mapTensorId, Matrix.of_apply]
  have hΦ : ∀ i j : Fin (4 ^ n),
      bb84UnitRegisterEmbed n (Matrix.single i j 1)
          (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1 =
        Matrix.single i j 1 (finProdFinEquiv.symm (finProdFinEquiv.symm p).1).1
          (finProdFinEquiv.symm (finProdFinEquiv.symm q).1).1 := by
    intro i j
    rw [bb84UnitRegisterEmbed_apply, Op_tensor_apply_finProd, Matrix.one_apply,
      if_pos (Subsingleton.elim _ _), mul_one]
  simp only [Equiv.toFun_as_coe, hΦ, Matrix.single_apply]
  rw [Finset.sum_eq_single (finProdFinEquiv.symm (finProdFinEquiv.symm p).1).1]
  · rw [Finset.sum_eq_single (finProdFinEquiv.symm (finProdFinEquiv.symm q).1).1]
    · rw [if_pos ⟨rfl, rfl⟩, one_mul]
      congr 1 <;> exact unitFactor_collapse_idx (by rw [Nat.mul_one]) _
    · intro j _ hj
      rw [if_neg (fun hcon => hj hcon.2), zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg (fun hcon => hi hcon.1), zero_mul]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-! ## (d) The PE-pass predicate on sorted PE outcomes, and the PE-round product factor `ρ_PE` -/

/-! ## (e) The key-round fiber sum: `coarsen`-of-`tensorPower` model identity -/

end QKD.BB84.Engine

end -- noncomputable section
