import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledFibreOrientation
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.Engine.EntropyFloor.AnnouncePEFloorChain
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.AnnounceCoarsenProduct
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.SpectatorKernelReindex
import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernelFibreRef
import QCryptLean.InfoTheory.SmoothMinEntropy.ChainRule.SmoothEntropyBridgeLemmas

/-!
# Product-reference and register transport for PE-labelled component floors

The component's conditioning reference is its own quantum marginal. After sorting rounds and
coarsening Alice's key, this marginal is `bb84PELabelledProductRefSplit`. Classical relabelling,
quantum reindexing and dimension casts move the state and its marginal together without entropy
loss. The announced PE register is a spectator to the key-round IID AEP.

References: Renner 2005, `cor:Hmincondrepclass`; Nahar et al. 2024, arXiv:2403.11851,
Appendix B, `eq:boundingsmoothedmin`, `lemma:infsmoothedmin`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Coarsening and register transport -/

/-- A classical coarsening whose target register is relabelled by an `Equiv` is the relabel of the
coarsening along the factor: if `e (g x) = h x` pointwise then `coarsen g ρ = relabel e (coarsen h
ρ)`. Both sides sum the same fibre, by injectivity of `e`. -/
lemma CQState.coarsen_eq_relabel_coarsen {Xc Yc Zc : Type*} [Fintype Xc] [Fintype Yc] [Fintype Zc]
    [DecidableEq Yc] [DecidableEq Zc] {d : ℕ} (e : Yc ≃ Zc) (g : Xc → Yc) (h : Xc → Zc)
    (he : ∀ x, e (g x) = h x) (ρ : CQState Xc d) :
    CQState.coarsen g ρ = CQState.relabel e (CQState.coarsen h ρ) := by
  apply CQState.ext_stateMap
  funext y
  apply SubDensityOp.ext
  have hL : ((CQState.coarsen g ρ).stateMap y).toOp =
      ∑ x : Xc, if g x = y then (ρ.stateMap x).toOp else 0 := rfl
  have hR : ((CQState.relabel e (CQState.coarsen h ρ)).stateMap y).toOp =
      ∑ x : Xc, if h x = e y then (ρ.stateMap x).toOp else 0 := rfl
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : g x = y
  · rw [ite_eq_left hx, ite_eq_left (by rw [← he x, hx])]
  · rw [ite_eq_right hx, ite_eq_right (fun hcon => hx (e.injective (by rw [he x]; exact hcon)))]

/-- Coarsening the classical register commutes with a heterogeneous reindex of the quantum
register: the two act on independent factors. -/
lemma CQState.coarsen_reindexQHetero {Xc Yc : Type*} [Fintype Xc] [Fintype Yc] [DecidableEq Yc]
    {a b : ℕ} (e : Fin a ≃ Fin b) (g : Xc → Yc) (ρ : CQState Xc a) :
    CQState.coarsen g (CQState.reindexQHetero e ρ) =
      CQState.reindexQHetero e (CQState.coarsen g ρ) := by
  apply CQState.ext_stateMap
  funext y
  apply SubDensityOp.ext
  have hL : ((CQState.coarsen g (CQState.reindexQHetero e ρ)).stateMap y).toOp =
      ∑ x : Xc, if g x = y then Matrix.reindex e e ((ρ.stateMap x).toOp) else 0 := rfl
  have hR : ((CQState.reindexQHetero e (CQState.coarsen g ρ)).stateMap y).toOp =
      Matrix.reindex e e (∑ x : Xc, if g x = y then (ρ.stateMap x).toOp else 0) := rfl
  rw [hL, hR, ← Matrix.coe_reindexLinearEquiv ℂ ℂ, map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : g x = y
  · rw [ite_eq_left hx, ite_eq_left hx, Matrix.coe_reindexLinearEquiv]
  · rw [ite_eq_right hx, ite_eq_right hx]
    simp [Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply]

/-- **An announce kernel that factors through a second classical map is the announce kernel of the
refined coarsening.**

If the announced block at `x` is `K (h x)` — a function of a second classical read-out `h` — then
coarsening the classical register along `g` and announcing is the same as first refining the
coarsening to the pair `(g, h)`, announcing `K` on the `h`-component, and then projecting the pair
register onto its first factor.

This is what puts an announce-then-coarsen state into the shape
`reindexQHetero_rotateLead_coarsen_fst_tensorLeftKernel_tensor`
reads: there the kernel depends only on the coarsened-away classical factor. -/
lemma CQState.coarsen_tensorLeftKernel_factor {Xc Yc Zc : Type*}
    [Fintype Xc] [Fintype Yc] [Fintype Zc] [DecidableEq Yc] [DecidableEq Zc] {dE dC : ℕ}
    (g : Xc → Yc) (h : Xc → Zc) (K : Zc → SubDensityOp dC) (ρ : CQState Xc dE) :
    CQState.coarsen g (ρ.tensorLeftKernel (fun x => K (h x))) =
      CQState.coarsen Prod.fst
        ((CQState.coarsen (fun x => (g x, h x)) ρ).tensorLeftKernel (fun yz => K yz.2)) := by
  apply CQState.ext_stateMap
  funext y
  apply SubDensityOp.ext
  have hL : ((CQState.coarsen g (ρ.tensorLeftKernel (fun x => K (h x)))).stateMap y).toOp =
      ∑ x : Xc, if g x = y then Op.tensor (K (h x)).toOp ((ρ.stateMap x).toOp) else 0 := rfl
  have hR : ((CQState.coarsen Prod.fst
        ((CQState.coarsen (fun x => (g x, h x)) ρ).tensorLeftKernel (fun yz => K yz.2))).stateMap
          y).toOp =
      ∑ yz : Yc × Zc, if yz.1 = y then
        Op.tensor (K yz.2).toOp (∑ x : Xc, if (g x, h x) = yz then (ρ.stateMap x).toOp else 0)
      else 0 := rfl
  rw [hL, hR, Fintype.sum_prod_type]
  -- Collapse the `Yc` sum on the right to `y`, then exchange the `Zc` and `Xc` sums.
  have hinner : ∀ y' : Yc,
      (∑ z : Zc, if y' = y then
          Op.tensor (K z).toOp (∑ x : Xc, if (g x, h x) = (y', z) then (ρ.stateMap x).toOp else 0)
        else 0) =
      if y' = y then
        (∑ z : Zc, Op.tensor (K z).toOp
          (∑ x : Xc, if (g x, h x) = (y', z) then (ρ.stateMap x).toOp else 0))
      else 0 := by
    intro y'
    split_ifs with hy' <;> simp
  simp_rw [hinner]
  rw [Finset.sum_ite_eq' Finset.univ y
    (fun y' => ∑ z : Zc, Op.tensor (K z).toOp
      (∑ x : Xc, if (g x, h x) = (y', z) then (ρ.stateMap x).toOp else 0))]
  rw [ite_eq_left (Finset.mem_univ y)]
  -- Push the tensor through the inner `Xc` sum, then exchange the sums.
  have hpush : ∀ z : Zc,
      Op.tensor (K z).toOp (∑ x : Xc, if (g x, h x) = (y, z) then (ρ.stateMap x).toOp else 0) =
      ∑ x : Xc, if (g x, h x) = (y, z) then Op.tensor (K z).toOp ((ρ.stateMap x).toOp) else 0 := by
    intro z
    rw [tensor_sum_op]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : (g x, h x) = (y, z)
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx, Op.tensor_zero_right]
  simp_rw [hpush]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : g x = y
  · rw [ite_eq_left hx, Finset.sum_eq_single (h x)]
    · rw [ite_eq_left (show (g x, h x) = (y, h x) by rw [hx])]
    · intro z _ hz
      exact ite_eq_right (fun hcon => hz (congrArg Prod.snd hcon).symm)
    · intro hmem
      exact absurd (Finset.mem_univ (h x)) hmem
  · rw [ite_eq_right hx, Finset.sum_eq_zero]
    intro z _
    exact ite_eq_right (fun hcon => hx (congrArg Prod.fst hcon))

/-! ## Register casts on the low factor of an announced pair -/

end InfoTheory.SmoothMinEntropy

namespace QKD.BB84.Engine

/-- A register cast of the **low** factor commutes with attaching the announce kernel: the
announced block never meets the register being recast. -/
lemma bb84CastCQState_tensorLeftKernel {Xc : Type*} [Fintype Xc] {a b dC : ℕ}
    (h : a = b) (h' : dC * a = dC * b) (ρ : CQState Xc a) (K : Xc → SubDensityOp dC) :
    bb84CastCQState h' (ρ.tensorLeftKernel K) = (bb84CastCQState h ρ).tensorLeftKernel K := by
  subst h; rfl

/-! ## The labelled product reference at a general test size -/

/-- **The PE-labelled product block reference in the sorted key/PE split frame, at a general
test-set size `m`.**

`Σ_p |p⟩⟨p| ⊗ (μ_key ⊗ PEprod_p̂)` with
`μ_key = ((bb84SiftedKeyRoundCQ ψ)^{⊗ n_K}).quantumMarginal` over the `n_K = n − m` sorted key
rounds and `p̂ = finFunctionFinEquiv.symm p` the sorted PE-outcome string of the `m` test rounds.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
def bb84PELabelledProductRefSplit {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (δ Q : ℝ) (ψ : DensityOp (signalDim * signalDim)) :
    SubDensityOp (bb84PEAnnounceLabelDim n m *
      (signalDim ^ bb84KeyRoundCount n m *
        signalDim ^ (n - bb84KeyRoundCount n m))) :=
  blockDiagRef
    (fun p => (((bb84SiftedKeyRoundCQ ψ).tensorPower
        (bb84KeyRoundCount n m)).quantumMarginal).tensor
      ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap
        (finFunctionFinEquiv.symm p)))
    (by
      have hprod : ∀ p : Fin (bb84PEAnnounceLabelDim n m),
          ((((bb84SiftedKeyRoundCQ ψ).tensorPower
              (bb84KeyRoundCount n m)).quantumMarginal).tensor
            ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap
              (finFunctionFinEquiv.symm p))).trace =
            (((bb84SiftedKeyRoundCQ ψ).tensorPower
              (bb84KeyRoundCount n m)).quantumMarginal).trace *
              ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap
                (finFunctionFinEquiv.symm p)).trace :=
        fun p => SubDensityOp.tensor_trace _ _
      have hreindex : ∑ p : Fin (bb84PEAnnounceLabelDim n m),
            ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap
              (finFunctionFinEquiv.symm p)).trace =
          ∑ q : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
            ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).trace :=
        Equiv.sum_comp finFunctionFinEquiv.symm
          (fun q => ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).trace)
      simp_rw [hprod]
      rw [← Finset.mul_sum, hreindex]
      exact (mul_le_of_le_one_left
        (Finset.sum_nonneg fun q _ =>
          ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).trace_nonneg)
        (((bb84SiftedKeyRoundCQ ψ).tensorPower
          (bb84KeyRoundCount n m)).quantumMarginal).trace_le_one).trans
        (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).weight_le_one)

/-- **The PE label kernel on the sorted PE-outcome register, at a general test-set size `m`.**

The announced block `bb84PEBlockIndex` is
`finFunctionFinEquiv` of the sorted PE-outcome string of the `m` test rounds, so on that register
the kernel is this projector.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
def bb84PELabelKernelSorted {n m : ℕ}
    (q : Fin (n - bb84KeyRoundCount n m) → Fin signalDim) :
    SubDensityOp (bb84PEAnnounceLabelDim n m) :=
  stdProj (bb84PEAnnounceLabelDim n m) (finFunctionFinEquiv q)

/-- The announcement-tagged quantum marginal of the general-`m` PE-round product,
`Σ_q PEprod_q ⊗ |q⟩⟨q|` — the single fixed ancilla the labelled announce attaches. -/
lemma bb84_peLabelledAncilla_trace {n m : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    (((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).tensorRightKernel
        bb84PELabelKernelSorted).quantumMarginal).trace =
      ∑ q : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
        ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).trace := by
  rw [quantumMarginal_tensorRightKernel_trace]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [show (bb84PELabelKernelSorted (m := m) q).trace = 1 from stdProj_trace _ _, mul_one]

/-- **The rotation carries the general-`m` product block reference to `μ_key ⊗ τ_lab`.**

General-`m` form of `bb84_reindexHetero_rotateLead_peLabelledProductRefSplit`:
`rotateLeadTensorEquiv` moves the announced label from the high digits past the surviving key
register into the trailing slot, where it merges with the coarsened-away PE factor into the single
fixed ancilla `τ_lab = Σ_q PEprod_q ⊗ |q⟩⟨q|`. -/
theorem bb84_reindexHetero_rotateLead_peLabelledProductRefSplit {n m : ℕ} [NeZero n]
    [NeZero (4 ^ n)] (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    SubDensityOp.reindexHetero
        (rotateLeadTensorEquiv (bb84PEAnnounceLabelDim n m)
          (signalDim ^ bb84KeyRoundCount n m)
          (signalDim ^ (n - bb84KeyRoundCount n m)))
        (bb84PELabelledProductRefSplit (m := m) peSel xSel δ Q ψ) =
      SubDensityOp.tensor
        (((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).quantumMarginal)
        (((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).tensorRightKernel
          bb84PELabelKernelSorted).quantumMarginal) := by
  apply SubDensityOp.ext
  rw [SubDensityOp.reindexHetero_toOp, bb84PELabelledProductRefSplit, blockDiagRef_toOp,
    blockDiagRefOp, Matrix.reindex_sum]
  simp_rw [bb84_subDensityOp_tensor_toOp, reindex_rotateLeadTensorEquiv_tensor]
  rw [← tensor_sum_op]
  congr 1
  rw [show (((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).tensorRightKernel
          bb84PELabelKernelSorted).quantumMarginal).toOp =
        ∑ q : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
          Op.tensor ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).toOp
            (bb84PELabelKernelSorted (m := m) q).toOp from rfl]
  refine Eq.trans ?_ (Equiv.sum_comp
    (finFunctionFinEquiv.symm :
      Fin (signalDim ^ (n - bb84KeyRoundCount n m)) ≃
        (Fin (n - bb84KeyRoundCount n m) → Fin signalDim))
    (fun q => Op.tensor ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).toOp
      (bb84PELabelKernelSorted (m := m) q).toOp))
  refine Finset.sum_congr rfl fun p _ => ?_
  exact (congrArg (fun i : Fin (bb84PEAnnounceLabelDim n m) =>
    Op.tensor ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap
      (finFunctionFinEquiv.symm p)).toOp (stdProj (bb84PEAnnounceLabelDim n m) i).toOp)
    (finFunctionFinEquiv.apply_symm_apply p)).symm

/-- **The trivial-attack key/PE product factorisation on the pair-coarsened per-σ family, at a
general test-set size `m`.**

General-`m` form of `bb84_coarsenKeyPair_transport`: the register transport of
`bb84_sifted_unitRegisterEmbed_coarsenKey_eq` with the classical coarsening pulled outside the
transport (`coarsen_reindexQ`, `coarsen_bb84CastCQState`).  Coarsening the trivial-attack per-σ
family along the general-`m` key/PE round partition `bb84PartEquiv` and transporting to the
sorted split register gives the `n_K = n − m`-fold key bit-CQ tensor power tensored with the
general-`m` PE-round product.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
theorem bb84_coarsenKeyPair_transport {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel) (Q δ : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    bb84CastCQState (bb84SignalPow_keyPE_split n m).symm
        (CQState.reindexQHetero (registerPerm signalDim n (bb84SortRoundPerm peSel).symm)
          (bb84CastCQState (bb84UnitEveDim_mul_signalPow n)
            (CQState.coarsen
              (fun ω : Fin n → Fin signalDim =>
                (fun i => bb84AliceBitMap ((bb84PartEquiv (m := m) peSel ω).1 i),
                  (bb84PartEquiv (m := m) peSel ω).2))
              (bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
                  (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ)))) =
      ((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).tensor
        (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ) := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  rw [CQState.reindexQHetero_eq_reindexQ]
  have hinner : CQState.reindexQ (registerPerm signalDim n (bb84SortRoundPerm peSel).symm)
      (bb84CastCQState (bb84UnitEveDim_mul_signalPow n)
        (CQState.coarsen
          (fun ω : Fin n → Fin signalDim =>
            (fun i => bb84AliceBitMap ((bb84PartEquiv (m := m) peSel ω).1 i),
              (bb84PartEquiv (m := m) peSel ω).2))
          (bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
              peSel xSel Q δ ψ))) =
      bb84CoarsenKey (m := m) peSel xSel Q δ ψ := by
    unfold bb84CoarsenKey
    rw [coarsen_reindexQ, coarsen_bb84CastCQState]
  rw [hinner, bb84_sifted_unitRegisterEmbed_coarsenKey_eq peSel xSel Q δ hcount ψ]
  exact bb84CastCQState_symm_cast (bb84SignalPow_keyPE_split n m).symm _

/-- Summing the labelled blocks over the surviving key register recovers the key marginal
in every announced block, so the sorted quantum marginal equals its product reference. -/
theorem bb84_peLabelledSorted_quantumMarginalOp_eq_productRef {n m : ℕ} [NeZero n]
    [NeZero (4 ^ n)] (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    (CQState.coarsen Prod.fst
        ((((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).tensor
            (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ)).tensorLeftKernel
          (fun zq => bb84PELabelKernelSorted (m := m) zq.2))).quantumMarginalOp =
      (bb84PELabelledProductRefSplit (m := m) peSel xSel δ Q ψ).toOp := by
  rw [CQState.coarsen_quantumMarginalOp]
  have hL : ((((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).tensor
        (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ)).tensorLeftKernel
          (fun zq => bb84PELabelKernelSorted (m := m) zq.2)).quantumMarginalOp =
      ∑ z : Fin (bb84KeyRoundCount n m) → Fin 2,
        ∑ q : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
          Op.tensor (bb84PELabelKernelSorted (m := m) q).toOp
            (Op.tensor (((bb84SiftedKeyRoundCQ ψ).tensorPower
                (bb84KeyRoundCount n m)).stateMap z).toOp
              ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).toOp) := by
    rw [show ((((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).tensor
          (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ)).tensorLeftKernel
            (fun zq => bb84PELabelKernelSorted (m := m) zq.2)).quantumMarginalOp =
        ∑ zq : (Fin (bb84KeyRoundCount n m) → Fin 2) ×
            (Fin (n - bb84KeyRoundCount n m) → Fin signalDim),
          Op.tensor (bb84PELabelKernelSorted (m := m) zq.2).toOp
            (Op.tensor
              (((bb84SiftedKeyRoundCQ ψ).tensorPower
                (bb84KeyRoundCount n m)).stateMap zq.1).toOp
              ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap zq.2).toOp)
      from rfl]
    exact Fintype.sum_prod_type _
  rw [hL, Finset.sum_comm]
  -- The key sum collapses to the key marginal inside every announced block.
  have hkey : ∀ q : Fin (n - bb84KeyRoundCount n m) → Fin signalDim,
      (∑ z : Fin (bb84KeyRoundCount n m) → Fin 2,
        Op.tensor (bb84PELabelKernelSorted (m := m) q).toOp
          (Op.tensor (((bb84SiftedKeyRoundCQ ψ).tensorPower
              (bb84KeyRoundCount n m)).stateMap z).toOp
            ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).toOp)) =
      Op.tensor (bb84PELabelKernelSorted (m := m) q).toOp
        (Op.tensor (((bb84SiftedKeyRoundCQ ψ).tensorPower
            (bb84KeyRoundCount n m)).quantumMarginal).toOp
          ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).toOp) := by
    intro q
    rw [show (((bb84SiftedKeyRoundCQ ψ).tensorPower
          (bb84KeyRoundCount n m)).quantumMarginal).toOp =
        ∑ z : Fin (bb84KeyRoundCount n m) → Fin 2,
          (((bb84SiftedKeyRoundCQ ψ).tensorPower
            (bb84KeyRoundCount n m)).stateMap z).toOp from rfl,
      Op.tensor_finsetSum_left, tensor_sum_op]
  rw [Finset.sum_congr rfl (fun q _ => hkey q), bb84PELabelledProductRefSplit,
    blockDiagRef_toOp, blockDiagRefOp]
  refine Eq.trans (Equiv.sum_comp
    (finFunctionFinEquiv.symm :
      Fin (signalDim ^ (n - bb84KeyRoundCount n m)) ≃
        (Fin (n - bb84KeyRoundCount n m) → Fin signalDim))
    (fun q => Op.tensor (bb84PELabelKernelSorted (m := m) q).toOp
      (Op.tensor (((bb84SiftedKeyRoundCQ ψ).tensorPower
          (bb84KeyRoundCount n m)).quantumMarginal).toOp
        ((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).stateMap q).toOp))).symm ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold bb84PELabelKernelSorted
  rw [Equiv.apply_symm_apply]
  exact congrArg (Op.tensor (stdProj (bb84PEAnnounceLabelDim n m) p).toOp)
    (bb84_subDensityOp_tensor_toOp _ _).symm

/-- **(e) The key-round tensor-power isometric invariance, at a general test-set size `m`.**

General-`m` form of `bb84_keyRoundCQ_tensorPower_smoothMinEntropy_ge_componentAliceZ`: conjugating
by the `n_K`-fold power of the L4 purification unitary
(`bb84SiftedKeyRoundCQ_eq_componentAliceZ_conj`) carries the Devetak–Winter component object
`bb84ComponentAliceZCQState (Tr_B ψ)^{⊗ n_K}` onto the protocol's key-round bit-CQ tensor power,
object and reference together, at no cost (`smoothMinEntropy_tensorPower_conj_le`), with the copy
count taken at a general split point `n_K = n − m`.

`hψPure` is load-bearing: the purification unitary exists only at a pure paired `ψ`.

References: Renner 2005 (`arXiv:quant-ph/0512258v2`) §3.1; Tomamichel 2016 §6.1; Nahar et al. 2024
(arXiv:2403.11851, `main.tex:909`, `:913`). -/
theorem bb84_keyRoundCQ_tensorPower_smoothMinEntropy_ge_componentAliceZ {n m : ℕ}
    (εTensor : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) (hψPure : ψ.IsPure) :
    haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
    haveI hKpow : NeZero (signalDim ^ bb84KeyRoundCount n m) :=
      ⟨pow_ne_zero _ (NeZero.ne _)⟩
    smoothMinEntropy εTensor
        (CQState.tensorPower (bb84ComponentAliceZCQState (DensityOp.partialTraceB ψ))
          (bb84KeyRoundCount n m))
        (SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp
            ((bb84ComponentAliceZCQState (DensityOp.partialTraceB ψ)).quantumMarginalDensityOp
              (bb84ComponentAliceZCQState_norm (DensityOp.partialTraceB ψ))))
          (bb84KeyRoundCount n m)) ≤
      smoothMinEntropy εTensor
        ((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m))
        (((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).quantumMarginal) := by
  have hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  have hKpow : NeZero (signalDim ^ bb84KeyRoundCount n m) :=
    ⟨pow_ne_zero _ (NeZero.ne _)⟩
  obtain ⟨W, hWblock, hWmarg⟩ := bb84SiftedKeyRoundCQ_eq_componentAliceZ_conj ψ hψPure
  rw [tensorPower_quantumMarginal_eq (bb84SiftedKeyRoundCQ ψ) (bb84KeyRoundCount n m)]
  refine smoothMinEntropy_tensorPower_conj_le (bb84KeyRoundCount n m) W.toOp W.unitary_left
    (bb84ComponentAliceZCQState ψ.partialTraceB) (bb84SiftedKeyRoundCQ ψ)
    (DensityOp.toSubDensityOp ((bb84ComponentAliceZCQState ψ.partialTraceB).quantumMarginalDensityOp
      (bb84ComponentAliceZCQState_norm ψ.partialTraceB)))
    (bb84SiftedKeyRoundCQ ψ).quantumMarginal ?_ ?_ εTensor
  · intro z
    rw [hWblock z, show W.toOp * (W.toOpᴴ * ((bb84SiftedKeyRoundCQ ψ).stateMap z).toOp * W.toOp)
          * W.toOpᴴ = (W.toOp * W.toOpᴴ) * ((bb84SiftedKeyRoundCQ ψ).stateMap z).toOp
            * (W.toOp * W.toOpᴴ) from by simp only [← mul_assoc], W.unitary_right, one_mul, mul_one]
  · have hEeq : (DensityOp.toSubDensityOp
          ((bb84ComponentAliceZCQState ψ.partialTraceB).quantumMarginalDensityOp
            (bb84ComponentAliceZCQState_norm ψ.partialTraceB))).toOp =
        W.toOpᴴ * (bb84SiftedKeyRoundCQ ψ).quantumMarginalOp * W.toOp := hWmarg
    rw [show (bb84SiftedKeyRoundCQ ψ).quantumMarginal.toOp =
          (bb84SiftedKeyRoundCQ ψ).quantumMarginalOp from rfl, hEeq,
      show W.toOp * (W.toOpᴴ * (bb84SiftedKeyRoundCQ ψ).quantumMarginalOp * W.toOp) * W.toOpᴴ =
        (W.toOp * W.toOpᴴ) * (bb84SiftedKeyRoundCQ ψ).quantumMarginalOp * (W.toOp * W.toOpᴴ)
        from by simp only [← mul_assoc], W.unitary_right, one_mul, mul_one]

/-- **The labelled announce is penalty-free, at a general test-set size `m`.**

General-`m` form of `bb84_peLabelledAnnounce_smoothMinEntropy_ge_key`:

`Hmin^ε((keyCQ ψ)^{⊗n_K} ‖ μ_key) ≤ Hmin^ε(labelled announce-then-coarsen state ‖ Σ_p |p⟩⟨p| ⊗
(μ_key ⊗ PEprod_p̂))`

at `n_K = bb84KeyRoundCount n m = n − m`.  The announce kernel depends only on the
coarsened-away PE outcome, so `reindexQHetero_rotateLead_coarsen_fst_tensorLeftKernel_tensor`
exhibits the rotated state as `key ⊗ (fixed ancilla)` — the rotation is
`bb84_reindexHetero_rotateLead_peLabelledProductRefSplit` — and
`smoothMinEntropy_le_condTensor_decoupled_ancilla` applies at the same radius and at
`polyDim = 1`.  **Charge zero, at every `m`.**

The comparison includes zero ancillas and needs no lower bound on accepted weight.

This is a per-Carathéodory-point statement: the product factorisation it rests on holds at a
product state, not at a de Finetti mixture.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `main.tex:909`, `:913`, `:919`;
Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5, Lemma 3.1.10. -/
theorem bb84_peLabelledAnnounce_smoothMinEntropy_ge_key {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ εTensor : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
    haveI hKpow : NeZero (signalDim ^ bb84KeyRoundCount n m) :=
      ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hPEpow : NeZero (signalDim ^ (n - bb84KeyRoundCount n m)) :=
      ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hAnn : NeZero (bb84PEAnnounceLabelDim n m) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hsplit : NeZero (bb84PEAnnounceLabelDim n m *
        (signalDim ^ bb84KeyRoundCount n m *
          signalDim ^ (n - bb84KeyRoundCount n m))) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    smoothMinEntropy εTensor ((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m))
        (((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).quantumMarginal) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen Prod.fst
          ((((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).tensor
              (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ)).tensorLeftKernel
            (fun zq => bb84PELabelKernelSorted (m := m) zq.2)))
        (bb84PELabelledProductRefSplit (m := m) peSel xSel δ Q ψ) := by
  have hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  have hKpow : NeZero (signalDim ^ bb84KeyRoundCount n m) :=
    ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hPEpow : NeZero (signalDim ^ (n - bb84KeyRoundCount n m)) :=
    ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hAnn : NeZero (bb84PEAnnounceLabelDim n m) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hsplit : NeZero (bb84PEAnnounceLabelDim n m *
      (signalDim ^ bb84KeyRoundCount n m *
        signalDim ^ (n - bb84KeyRoundCount n m))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  have hτ : NeZero (signalDim ^ (n - bb84KeyRoundCount n m) *
      bb84PEAnnounceLabelDim n m) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hrot : NeZero (signalDim ^ bb84KeyRoundCount n m *
      (signalDim ^ (n - bb84KeyRoundCount n m) * bb84PEAnnounceLabelDim n m)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  -- Rotate object and reference together, then announce the decoupled ancilla.
  rw [← smoothMinEntropy_reindexQHetero
    (rotateLeadTensorEquiv (bb84PEAnnounceLabelDim n m)
      (signalDim ^ bb84KeyRoundCount n m)
      (signalDim ^ (n - bb84KeyRoundCount n m))) εTensor _
    (bb84PELabelledProductRefSplit (m := m) peSel xSel δ Q ψ),
    reindexQHetero_rotateLead_coarsen_fst_tensorLeftKernel_tensor,
    bb84_reindexHetero_rotateLead_peLabelledProductRefSplit peSel xSel δ Q ψ]
  exact smoothMinEntropy_le_condTensor_decoupled_ancilla εTensor
    ((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m))
    (((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).tensorAncilla
      (((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).tensorRightKernel
        bb84PELabelKernelSorted).quantumMarginal))
    (((bb84SiftedKeyRoundCQ ψ).tensorPower (bb84KeyRoundCount n m)).quantumMarginal)
    (((bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ).tensorRightKernel
      bb84PELabelKernelSorted).quantumMarginal)
    (fun _ => rfl)

/-- **The classical half of the labelled transport, at a general test-set size `m`.**

General-`m` form of `bb84_peLabelledCoarsenAliceKey_eq_pairCoarsen`: Alice's key string is the
sorted-bit coarsening relabelled by `bb84SortedKeyBitEquiv`
(`bb84SortedKeyBitEquiv_bb84AliceKeyString`), and the labelled announce kernel is a function of
the sorted PE-outcome string alone, so the announce-then-coarsen state refines to the general-`m`
key/PE pair register.  No register move and no charge, at any `m`.

Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
theorem bb84_peLabelledCoarsenAliceKey_eq_pairCoarsen {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel) (Q δ : ℝ)
    (ψ : DensityOp (signalDim * signalDim)) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    CQState.coarsen (aliceKeyString peSel)
        (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ) =
      CQState.relabel (bb84SortedKeyBitEquiv peSel hcount)
        (CQState.coarsen Prod.fst
          ((CQState.coarsen
              (fun ω : Fin n → Fin signalDim =>
                (fun i => bb84AliceBitMap ((bb84PartEquiv (m := m) peSel ω).1 i),
                  (bb84PartEquiv (m := m) peSel ω).2))
              (bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
                  (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ)).tensorLeftKernel
            (fun zq => bb84PELabelKernelSorted (m := m) zq.2))) := by
  have : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  rw [CQState.coarsen_eq_relabel_coarsen (bb84SortedKeyBitEquiv peSel hcount)
      (aliceKeyString peSel)
      (fun ω : Fin n → Fin signalDim =>
        fun i => bb84AliceBitMap ((bb84PartEquiv (m := m) peSel ω).1 i))
      (fun ω => bb84SortedKeyBitEquiv_bb84AliceKeyString peSel hcount ω) _,
    show bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
        (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ ψ =
      (bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
          peSel xSel Q δ ψ).tensorLeftKernel
        (fun ω => bb84PELabelKernelSorted (m := m) ((bb84PartEquiv (m := m) peSel ω).2)) from rfl]
  exact congrArg (CQState.relabel (bb84SortedKeyBitEquiv peSel hcount))
    (CQState.coarsen_tensorLeftKernel_factor _ _ _ _)

/-- The own-marginal smooth min-entropy of the PE-labelled Alice key equals the sorted
key/PE product expression. Classical relabelling preserves the marginal, while dimension
casts and quantum reindexing carry it with the state. The sorted marginal is exactly
`bb84PELabelledProductRefSplit`, so the transport has no reference-change penalty. -/
theorem bb84_peLabelledCoarsenAliceKey_smoothMinEntropy_quantumMarginal_eq_sortedSplit
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (Q δ εTensor : ℝ) (ψ : DensityOp (signalDim * signalDim)) :
    haveI hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
    haveI hAnn : NeZero (bb84PEAnnounceLabelDim n m) :=
      ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hEve : NeZero (1 * signalDim ^ n) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hfine : NeZero (bb84PEAnnounceLabelDim n m * (1 * signalDim ^ n)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    haveI hKpow : NeZero (signalDim ^ bb84KeyRoundCount n m) :=
      ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hPEpow : NeZero (signalDim ^ (n - bb84KeyRoundCount n m)) :=
      ⟨pow_ne_zero _ (NeZero.ne _)⟩
    haveI hsplit : NeZero (bb84PEAnnounceLabelDim n m *
        (signalDim ^ bb84KeyRoundCount n m *
          signalDim ^ (n - bb84KeyRoundCount n m))) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _)
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
    let ρ := CQState.coarsen (aliceKeyString peSel)
      (bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1
        (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
        peSel xSel Q δ ψ)
    smoothMinEntropy εTensor ρ ρ.quantumMarginal =
      smoothMinEntropy εTensor
        (CQState.coarsen Prod.fst
          ((((bb84SiftedKeyRoundCQ ψ).tensorPower
                (bb84KeyRoundCount n m)).tensor
              (bb84SiftedPERoundProd (m := m) peSel xSel δ Q ψ)).tensorLeftKernel
            (fun zq => bb84PELabelKernelSorted (m := m) zq.2)))
        (bb84PELabelledProductRefSplit (m := m) peSel xSel δ Q ψ) := by
  have hSig : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  have hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  have hAnn : NeZero (bb84PEAnnounceLabelDim n m) :=
    ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hEve : NeZero (1 * signalDim ^ n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hfine : NeZero (bb84PEAnnounceLabelDim n m * (1 * signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hKpow : NeZero (signalDim ^ bb84KeyRoundCount n m) :=
    ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hPEpow : NeZero (signalDim ^ (n - bb84KeyRoundCount n m)) :=
    ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hsplit : NeZero (bb84PEAnnounceLabelDim n m *
      (signalDim ^ bb84KeyRoundCount n m *
        signalDim ^ (n - bb84KeyRoundCount n m))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _)
      (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))⟩
  have hmid : NeZero (bb84PEAnnounceLabelDim n m * signalDim ^ n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hCast : ∀ {Xc : Type} [Fintype Xc] {a b : ℕ} (h : a = b) (ρ : CQState Xc a),
      SubDensityOp.castDim h ρ.quantumMarginal =
        (bb84CastCQState h ρ).quantumMarginal := by
    intro Xc _ a b h ρ
    subst h
    rfl
  dsimp only
  rw [bb84_peLabelledCoarsenAliceKey_eq_pairCoarsen peSel xSel hcount Q δ ψ]
  conv_lhs =>
    arg 3
    tactic => exact CQState.relabel_quantumMarginal (bb84SortedKeyBitEquiv peSel hcount) _
  conv_lhs =>
    tactic => exact smoothMinEntropy_relabel (bb84SortedKeyBitEquiv peSel hcount) _ _ _
  conv_lhs =>
    tactic =>
      exact bb84_smoothMinEntropy_castDim
        (congrArg (fun k => bb84PEAnnounceLabelDim n m * k) (bb84UnitEveDim_mul_signalPow n))
        εTensor _ _
  conv_lhs =>
    arg 3
    tactic => exact hCast _ _
  rw [← coarsen_bb84CastCQState,
    bb84CastCQState_tensorLeftKernel (bb84UnitEveDim_mul_signalPow n)]
  conv_lhs =>
    tactic =>
      exact (smoothMinEntropy_reindexQHetero
        (tensorRightCongrEquiv (bb84PEAnnounceLabelDim n m)
          (registerPerm signalDim n (bb84SortRoundPerm peSel).symm)) εTensor _ _).symm
  rw [← CQState.reindexQHetero_quantumMarginal, ← CQState.coarsen_reindexQHetero,
    CQState.reindexQHetero_tensorRightCongr_tensorLeftKernel]
  conv_lhs =>
    tactic =>
      exact bb84_smoothMinEntropy_castDim
        (congrArg (fun k => bb84PEAnnounceLabelDim n m * k)
          (bb84SignalPow_keyPE_split n m).symm)
        εTensor _ _
  conv_lhs =>
    arg 3
    tactic => exact hCast _ _
  rw [← coarsen_bb84CastCQState,
    bb84CastCQState_tensorLeftKernel (bb84SignalPow_keyPE_split n m).symm,
    bb84_coarsenKeyPair_transport peSel xSel hcount Q δ ψ]
  congr 1
  apply SubDensityOp.ext
  exact bb84_peLabelledSorted_quantumMarginalOp_eq_productRef peSel xSel δ Q ψ

/-! ## The PE-labelled per-σ collective floor at a general test-set size `m` -/

end QKD.BB84.Engine

end -- noncomputable section
