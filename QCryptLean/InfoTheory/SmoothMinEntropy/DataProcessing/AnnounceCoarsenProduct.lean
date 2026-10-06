import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.RegisterSwapBridge
import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernel
import QCryptLean.InfoTheory.QuantumLHL.ClassicalCoarsening
import QCryptLean.Quantum.Matrix.Reindex

/-!
# The announce-then-coarsen product factorization

Take a CQ state that is a **product** of two independent parts,

* `A : CQState XA dA` — the part whose classical register survives, and
* `B : CQState XB dB` — the part whose classical register is coarsened away,

announce a message that depends only on `B`'s classical value (`K : XB → SubDensityOp dAnn`,
tensored into the **high** digits of the conditioning register by `CQState.tensorLeftKernel`), and
then push the classical register forward onto `XA` (`CQState.coarsen Prod.fst`).

The result is again a product: after the register rotation `rotateLeadTensorEquiv`
(`InfoTheory/SmoothMinEntropy/RegisterSwapBridge.lean`) that moves the announcement register past
the surviving system register, every block factorizes as

`A_y ⊗ τ`,  with the **`y`-independent** ancilla `τ := (B.tensorRightKernel K).quantumMarginal`.

`τ` is the announcement-tagged quantum marginal `∑_ω B_ω ⊗ K ω` of the coarsened part — a single
fixed sub-density operator, decoupled from the surviving classical register.  That is exactly the
`hproduct` hypothesis of the penalty-free decoupled-ancilla kernel
`smoothMinEntropy_le_condTensor_decoupled_ancilla`
(`InfoTheory/SmoothMinEntropy/ExtensionPenalty.lean`), so this module is what lets that kernel be
applied to an announce-then-coarsen state.

Scope: the factorization holds **at a product state**.  It is a statement about one point, not
about a mixture: for a state that is only a convex combination of such products the announced
block acquires a dependence on the mixing variable and no fixed `τ` exists.  Nothing here asserts
otherwise.

A second, silently inherited obligation: `hproduct` requires the *accept predicate itself* to
factor as (PE-accept) ∧ (key-accept) — a product of a test that reads only `B`'s (PE) classical
value and a test that is independent of `A`'s (key) classical value — not merely to be
round-disjoint. This holds only per-Carathéodory point of a de Finetti mixture: it is **false at
the mixture itself** and **false for a genuinely coupled accept predicate** that
mixes PE- and key-round data instead of factoring.
Every consumer of `hproduct` must supply an accept test that already factors this way; this lemma
does not derive the factoring.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B Eqs.
(B16)–(B19) (the announced side information entering the conditioning register); Renner 2005
(arXiv:quant-ph/0512258v2) §6.5 and Lemma 3.1.10 (classical side information); Tomamichel 2016
§6.1–6.2 (smooth conditional min-entropy under register extensions).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open scoped ComplexOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Reindexing and tensoring through finite sums -/

/-- The tensor product is additive in its right argument. -/
lemma tensor_sum_op {ι : Type*} {n m : ℕ} (s : Finset ι) (A : Op n) (B : ι → Op m) :
    Op.tensor A (∑ i ∈ s, B i) = ∑ i ∈ s, Op.tensor A (B i) := by
  ext I J
  simp [Op_tensor_apply_finProd, Matrix.sum_apply, Finset.mul_sum]

/-! ## The blockwise form of the announce-then-coarsen product state -/

/-- **Blockwise form.**  Announcing `K` (high digits) on the product `A ⊗ B` and coarsening the
classical register onto `XA` leaves, in the `y`-block, the fiber sum over `B`'s classical
register: `∑_ω K ω ⊗ (A_y ⊗ B_ω)`.  The `A_y` factor is constant along the sum. -/
lemma coarsen_fst_tensorLeftKernel_tensor_stateMap_toOp
    {XA XB : Type*} [Fintype XA] [Fintype XB] [DecidableEq XA] {dA dB dAnn : ℕ}
    (A : CQState XA dA) (B : CQState XB dB) (K : XB → SubDensityOp dAnn) (y : XA) :
    ((CQState.coarsen Prod.fst ((A.tensor B).tensorLeftKernel fun p => K p.2)).stateMap y).toOp =
      ∑ ω : XB, Op.tensor (K ω).toOp
        (Op.tensor (A.stateMap y).toOp (B.stateMap ω).toOp) := by
  have hblk : ∀ p : XA × XB,
      (((A.tensor B).tensorLeftKernel fun q => K q.2).stateMap p).toOp =
        Op.tensor (K p.2).toOp (Op.tensor (A.stateMap p.1).toOp (B.stateMap p.2).toOp) :=
    fun _ => rfl
  rw [CQState.coarsen_stateMap_toOp]
  simp_rw [hblk]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : XA,
      (∑ ω : XB, if a = y then
          Op.tensor (K ω).toOp (Op.tensor (A.stateMap a).toOp (B.stateMap ω).toOp) else 0) =
        if a = y then
          (∑ ω : XB, Op.tensor (K ω).toOp
            (Op.tensor (A.stateMap a).toOp (B.stateMap ω).toOp)) else 0 := by
    intro a
    split_ifs with h <;> simp
  simp_rw [hinner]
  rw [Finset.sum_ite_eq' Finset.univ y
    (fun a => ∑ ω : XB, Op.tensor (K ω).toOp
      (Op.tensor (A.stateMap a).toOp (B.stateMap ω).toOp))]
  simp

/-! ## The product factorization -/

/-- **The announce-then-coarsen state of a product is a product with a fixed ancilla.**

After the register rotation `rotateLeadTensorEquiv dAnn dA dB` — which moves the announcement
register from the high digits to the trailing slot, past the surviving system register — the
announce-then-coarsen state of `A ⊗ B` equals `A` tensored with the single, classically
independent ancilla `(B.tensorRightKernel K).quantumMarginal = ∑_ω B_ω ⊗ K ω`.

The rotation is smooth-min-entropy neutral by `smoothMinEntropy_reindexQHetero_rotateLead`, so the
entropy of the left-hand side is the entropy of the right-hand side once the reference is rotated
with it (`SubDensityOp.reindexHetero_rotateLeadTensorEquiv_tensor`). -/
theorem reindexQHetero_rotateLead_coarsen_fst_tensorLeftKernel_tensor
    {XA XB : Type*} [Fintype XA] [Fintype XB] [DecidableEq XA] {dA dB dAnn : ℕ}
    (A : CQState XA dA) (B : CQState XB dB) (K : XB → SubDensityOp dAnn) :
    CQState.reindexQHetero (rotateLeadTensorEquiv dAnn dA dB)
        (CQState.coarsen Prod.fst ((A.tensor B).tensorLeftKernel fun p => K p.2)) =
      A.tensorAncilla (B.tensorRightKernel K).quantumMarginal := by
  apply CQState.ext
  funext y
  apply SubDensityOp.ext
  change Matrix.reindex (rotateLeadTensorEquiv dAnn dA dB) (rotateLeadTensorEquiv dAnn dA dB)
      ((CQState.coarsen Prod.fst ((A.tensor B).tensorLeftKernel fun p => K p.2)).stateMap y).toOp
    = _
  rw [coarsen_fst_tensorLeftKernel_tensor_stateMap_toOp, Matrix.reindex_sum]
  simp_rw [reindex_rotateLeadTensorEquiv_tensor]
  rw [← tensor_sum_op]
  rfl

/-- **The `hproduct` hypothesis of the decoupled-ancilla kernel, discharged.**

This is literally the shape required by
`smoothMinEntropy_le_condTensor_decoupled_ancilla`'s
`hproduct : ∀ x, (ρEV.stateMap x).toOp = ((ρE.stateMap x).tensor τ).toOp`, instantiated at
`ρE := A`, `ρEV := ` the rotated announce-then-coarsen state, and
`τ := (B.tensorRightKernel K).quantumMarginal`. -/
theorem coarsen_fst_tensorLeftKernel_tensor_hproduct
    {XA XB : Type*} [Fintype XA] [Fintype XB] [DecidableEq XA] {dA dB dAnn : ℕ}
    (A : CQState XA dA) (B : CQState XB dB) (K : XB → SubDensityOp dAnn) (y : XA) :
    ((CQState.reindexQHetero (rotateLeadTensorEquiv dAnn dA dB)
        (CQState.coarsen Prod.fst ((A.tensor B).tensorLeftKernel fun p => K p.2))).stateMap y).toOp
      = ((A.stateMap y).tensor (B.tensorRightKernel K).quantumMarginal).toOp := by
  rw [reindexQHetero_rotateLead_coarsen_fst_tensorLeftKernel_tensor]
  rfl

/-- **The weight of the fixed ancilla.**  It is the announcement-weighted total weight of the
coarsened part; with normalised announce blocks (`(K ω).trace = 1`) it is exactly `B`'s classical
weight.  This is what supplies the `hτ_weight : 0 < τ.trace` side condition of
`smoothMinEntropy_le_condTensor_decoupled_ancilla`. -/
lemma quantumMarginal_tensorRightKernel_trace {XB : Type*} [Fintype XB] {dB dAnn : ℕ}
    (B : CQState XB dB) (K : XB → SubDensityOp dAnn) :
    (B.tensorRightKernel K).quantumMarginal.trace =
      ∑ ω : XB, (B.stateMap ω).trace * (K ω).trace := by
  rw [CQState.quantumMarginal_trace]
  exact Finset.sum_congr rfl fun ω _ => SubDensityOp.tensor_trace _ _

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
