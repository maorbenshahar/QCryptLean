import QCryptLean.InfoTheory.QuantumLHL.CollisionAnnounceCharge
import QCryptLean.InfoTheory.QuantumLHL.CollisionBlockRef

/-!
# The collision-route coarsening bridge from σ-weighted fibre orthogonality

`InfoTheory.QuantumLHL.collisionQuantity_coarsen_eq_of_injOn` transfers the collision quantity
across a classical coarsening when the coarsening map is injective on the support.  That route is
**dead** for the BB84 Alice-key coarsening: the protocol's own coarsening
exhibits a genuinely merging fibre inside the accept-and-agree keep set.

This file supplies the **other** mechanism: a coarsening is free for the collision quantity as soon
as the blocks merged inside each fibre are pairwise **σ-weighted orthogonal**,
`Tr[A_x σ^{−1/2} A_{x'} σ^{−1/2}] = 0`.  No injectivity, and no hypothesis on the state's support.

## What is here

* `weightedFrobeniusPairing` — the σ-weighted Hilbert–Schmidt pairing
  `Tr[A σ^{−1/2} B σ^{−1/2}]`, the bilinear form whose diagonal is `weightedFrobeniusSq`.
* `weightedFrobeniusSq_sum_of_pairwiseWeightedOrthogonal` — Hilbert–Schmidt Pythagoras for a finite
  sum of pairwise σ-orthogonal Hermitian blocks, the `n`-ary form of
  `weightedFrobeniusSq_add_of_weightedOrthogonal`.
* `collisionQuantity_coarsen_eq_of_fibreWeightedOrthogonal` — **the bridge**:
  `Γ(coarsen g ρ) = Γ(ρ)` from fibrewise σ-orthogonality.
* `weightedFrobeniusPairing_tensor` — the pairing factorises over a tensor reference, which is what
  lets a *fibre-constant* announcement kernel be pulled out of every cross term.
* `weightedFrobeniusPairing_blockDiagRefOp_stdProj_tensor` — at a reference block-diagonal across a
  classical label register, the pairing of two single-label blocks **vanishes** when the labels
  differ and reduces to the per-label pairing when they agree.

## Why the order of composition is forced

The blocks of a *coarsened* state are sums of fine blocks, hence not rank ≤ 1 even when the fine
blocks are; so the rank-one register-extension identity `(★)`
`InfoTheory.QuantumLHL.collisionQuantity_regExt_pure_eq` cannot be applied to them.  The
coarsening bridge below must therefore be used **before** `(★)`, at the fine register — never
after.

Equally, the label register must still be present when the bridge is applied: it is
`weightedFrobeniusPairing_blockDiagRefOp_stdProj_tensor` that kills every cross term between fine
blocks carrying *different* labels, and that lemma has no content once the label has been charged
away.  The announce charge
(`collisionQuantity_tensorLeftKernel_blockDiagRef_eq`, an exact `0`) is what makes it legitimate to
keep the label all the way to this point at no cost.

Elementary Hilbert–Schmidt geometry throughout; no external reference is claimed.  In particular
this is **not** Renner 2005 `\label{rem:Htworewr}`
(arXiv:quant-ph/0512258v2, `main.tex:6889`): that remark's identity holds for any cq state
*without* an orthogonality hypothesis, and its "orthogonal" means support orthogonality
`ρ^x ρ^y = 0`, which is a strictly different, σ-independent condition from the one used here.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace InfoTheory.QuantumLHL

/-! ## The σ-weighted Hilbert–Schmidt pairing -/

/-- **The σ-weighted Hilbert–Schmidt pairing** `Tr[A σ^{−1/2} B σ^{−1/2}]`.

For Hermitian `A` this is the Hilbert–Schmidt inner product of the sandwiched operators
`σ^{−1/4} A σ^{−1/4}` and `σ^{−1/4} B σ^{−1/4}`, i.e. the bilinear form polarising
`weightedFrobeniusSq`.  It is a genuinely **σ-dependent** condition: `weightedFrobeniusPairing σ A B
= 0` is weaker than support orthogonality `A * B = 0` in general and neither implies the other. -/
def weightedFrobeniusPairing {d : ℕ} (σ A B : Op d) : ℂ :=
  (A * σ ^ (-1/2 : ℝ) * B * σ ^ (-1/2 : ℝ)).trace

lemma weightedFrobeniusPairing_def {d : ℕ} (σ A B : Op d) :
    weightedFrobeniusPairing σ A B = (A * σ ^ (-1/2 : ℝ) * B * σ ^ (-1/2 : ℝ)).trace := rfl

/-- The pairing is additive in its right argument over a finite sum. -/
lemma weightedFrobeniusPairing_sum_right {d : ℕ} {ι : Type*} (σ A : Op d) (B : ι → Op d)
    (s : Finset ι) :
    weightedFrobeniusPairing σ A (∑ i ∈ s, B i) = ∑ i ∈ s, weightedFrobeniusPairing σ A (B i) := by
  simp only [weightedFrobeniusPairing]
  rw [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum]

@[simp] lemma weightedFrobeniusPairing_zero_left {d : ℕ} (σ B : Op d) :
    weightedFrobeniusPairing σ 0 B = 0 := by
  simp [weightedFrobeniusPairing]

@[simp] lemma weightedFrobeniusPairing_zero_right {d : ℕ} (σ A : Op d) :
    weightedFrobeniusPairing σ A 0 = 0 := by
  simp [weightedFrobeniusPairing]

/-! ## Pythagoras for a finite sum of pairwise σ-orthogonal blocks -/

/-- **Hilbert–Schmidt Pythagoras for a finite sum.**

If the Hermitian blocks `A i`, `i ∈ s`, are pairwise σ-weighted orthogonal, their sum costs exactly
what the summands cost separately.  The binary case is
`weightedFrobeniusSq_add_of_weightedOrthogonal`, whose asymmetric hypothesis (`Aᴴ = A` on the *left*
argument only) is what makes the induction go through with a single Hermitian hypothesis per
block. -/
theorem weightedFrobeniusSq_sum_of_pairwiseWeightedOrthogonal {d : ℕ} [NeZero d] {ι : Type*}
    (σ : Op d) (hσ : σ.PosDef) (A : ι → Op d) (s : Finset ι)
    (hherm : ∀ i ∈ s, (A i)ᴴ = A i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → weightedFrobeniusPairing σ (A i) (A j) = 0) :
    weightedFrobeniusSq σ (∑ i ∈ s, A i) = ∑ i ∈ s, weightedFrobeniusSq σ (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hherm' : ∀ i ∈ t, (A i)ᴴ = A i := fun i hi => hherm i (Finset.mem_insert_of_mem hi)
    have horth' : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → weightedFrobeniusPairing σ (A i) (A j) = 0 :=
      fun i hi j hj hij =>
        horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hcross : weightedFrobeniusPairing σ (A a) (∑ i ∈ t, A i) = 0 := by
      rw [weightedFrobeniusPairing_sum_right]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact horth a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      weightedFrobeniusSq_add_of_weightedOrthogonal σ hσ (A a) (∑ i ∈ t, A i)
        (hherm a (Finset.mem_insert_self a t)) hcross,
      ih hherm' horth']

/-! ## The coarsening bridge -/

/-- **The collision quantity is unchanged by a coarsening whose fibres are σ-weighted orthogonal.**

`Γ_coarse = Γ_fine` for the classical pushforward along `g : X → Y`, whenever any two *distinct*
blocks sitting in a common fibre of `g` pair to zero against the reference.

This is the mechanism that replaces injectivity.  Merging blocks does in general **increase** the
collision quantity — `tr((A+B)²) = tr A² + tr B² + 2·tr(AB)` with `tr(AB) ≥ 0` for positive
semidefinite `A, B` — so the equality genuinely needs `horth`, which is exactly the statement that
the merged blocks are orthogonal in the σ-weighted Hilbert–Schmidt geometry the collision quantity
measures.

`horth` is only asked of pairs in a common fibre: blocks that the coarsening keeps apart never meet
in a sum. -/
theorem collisionQuantity_coarsen_eq_of_fibreWeightedOrthogonal
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {d : ℕ} [NeZero d]
    (g : X → Y) (σ : Op d) (hσ : σ.PosDef) (ρ : CQState X d)
    (horth : ∀ x x', g x = g x' → x ≠ x' →
      weightedFrobeniusPairing σ (ρ.stateMap x).toOp (ρ.stateMap x').toOp = 0) :
    collisionQuantity σ (fun y => ((CQState.coarsen g ρ).stateMap y).toOp)
      = collisionQuantity σ (fun x => (ρ.stateMap x).toOp) := by
  classical
  have hherm : ∀ x : X, ((ρ.stateMap x).toOp)ᴴ = (ρ.stateMap x).toOp := fun x =>
    (ρ.stateMap x).isHermitian
  -- the coarsened block at `y` is the sum of the fine blocks over the fibre of `y`
  have hblock : ∀ y : Y, ((CQState.coarsen g ρ).stateMap y).toOp
      = ∑ x ∈ Finset.univ.filter (fun x => g x = y), (ρ.stateMap x).toOp := by
    intro y
    rw [CQState.coarsen_stateMap_toOp, Finset.sum_filter]
  rw [collisionQuantity, collisionQuantity]
  calc ∑ y : Y, weightedFrobeniusSq σ ((CQState.coarsen g ρ).stateMap y).toOp
      = ∑ y : Y, ∑ x ∈ Finset.univ.filter (fun x => g x = y),
          weightedFrobeniusSq σ (ρ.stateMap x).toOp := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hblock y]
        refine weightedFrobeniusSq_sum_of_pairwiseWeightedOrthogonal σ hσ
          (fun x => (ρ.stateMap x).toOp) _ (fun x _ => hherm x) (fun x hx x' hx' hne => ?_)
        exact horth x x' (by
          rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hx').2]) hne
    _ = ∑ x : X, weightedFrobeniusSq σ (ρ.stateMap x).toOp := by
        rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset X)) (g := g)
          (f := fun x => weightedFrobeniusSq σ (ρ.stateMap x).toOp)]

/-- **The coarsening bridge at a `filterKeep`-restricted state.**

`CQState.filterKeep` is the shape the BB84 accept gates produce, and a dropped block is the zero
operator, which pairs to zero against everything.  So the σ-orthogonality hypothesis only has to be
supplied for the **unfiltered** blocks. -/
theorem collisionQuantity_coarsen_filterKeep_eq_of_fibreWeightedOrthogonal
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {d : ℕ} [NeZero d]
    (g : X → Y) (keep : X → Bool) (σ : Op d) (hσ : σ.PosDef) (ρ : CQState X d)
    (horth : ∀ x x', g x = g x' → x ≠ x' →
      weightedFrobeniusPairing σ (ρ.stateMap x).toOp (ρ.stateMap x').toOp = 0) :
    collisionQuantity σ
        (fun y => ((CQState.coarsen g (CQState.filterKeep keep ρ)).stateMap y).toOp)
      = collisionQuantity σ (fun x => ((CQState.filterKeep keep ρ).stateMap x).toOp) := by
  refine collisionQuantity_coarsen_eq_of_fibreWeightedOrthogonal g σ hσ
    (CQState.filterKeep keep ρ) fun x x' hg hne => ?_
  have hx : ((CQState.filterKeep keep ρ).stateMap x).toOp
      = if keep x then (ρ.stateMap x).toOp else 0 := by
    rw [CQState.filterKeep_stateMap]
    by_cases h : keep x
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; rfl
  have hx' : ((CQState.filterKeep keep ρ).stateMap x').toOp
      = if keep x' then (ρ.stateMap x').toOp else 0 := by
    rw [CQState.filterKeep_stateMap]
    by_cases h : keep x'
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; rfl
  rw [hx, hx']
  by_cases h : keep x
  · by_cases h' : keep x'
    · rw [if_pos h, if_pos h']; exact horth x x' hg hne
    · rw [if_neg h', weightedFrobeniusPairing_zero_right]
  · rw [if_neg h, weightedFrobeniusPairing_zero_left]

/-! ## The pairing factorises over a tensor reference -/

/-- **Tensor factorisation of the σ-weighted pairing.**

`⟨K ⊗ M, K' ⊗ M'⟩_{τ⊗σ} = ⟨K, K'⟩_τ · ⟨M, M'⟩_σ`.  This is the mechanism by which a
**fibre-constant** announcement kernel drops out of every cross term of the coarsening bridge: for
fibre-mates the two announcement factors are the *same* operator, so the left factor is a common
scalar and only the inner pairing has to vanish. -/
theorem weightedFrobeniusPairing_tensor {dC dE : ℕ} (τ : Op dC) (σ : Op dE)
    (hτ : (0 : Op dC) ≤ τ) (hσ : (0 : Op dE) ≤ σ) (K K' : Op dC) (M M' : Op dE) :
    weightedFrobeniusPairing (τ ⊗ σ) (K ⊗ M) (K' ⊗ M')
      = weightedFrobeniusPairing τ K K' * weightedFrobeniusPairing σ M M' := by
  simp only [weightedFrobeniusPairing]
  rw [Op.tensor_rpow τ σ hτ hσ, Op.tensor_mul, Op.tensor_mul, Op.tensor_mul, Op.trace_tensor]

/-! ## The pairing at a reference block-diagonal across a classical label -/

/-- The computational-basis projectors are idempotent.  (Local re-derivation: the copy in
`CollisionBlockRef.lean` is `private`.) -/
private lemma stdKetProj_idem_local {dC : ℕ} (q : Fin dC) :
    (stdKet dC q * (stdKet dC q).dag) * (stdKet dC q * (stdKet dC q).dag)
      = stdKet dC q * (stdKet dC q).dag := by
  ext i j
  simp [Matrix.mul_apply, ket_mul_bra_apply, Ket.dag_vec, stdKet_apply, Finset.sum_ite_eq]

/-- The computational-basis projectors at distinct labels are orthogonal.  (Local re-derivation:
the copy in `CollisionBlockRef.lean` is `private`.) -/
private lemma stdKetProj_orthogonal_local {dC : ℕ} {q q' : Fin dC} (h : q ≠ q') :
    (stdKet dC q * (stdKet dC q).dag) * (stdKet dC q' * (stdKet dC q').dag) = 0 := by
  ext i j
  simp [Matrix.mul_apply, ket_mul_bra_apply, Ket.dag_vec, stdKet_apply, h]

/-- **A reference block-diagonal across the label register kills every label-crossing pairing, and
reduces the label-preserving one to the per-label pairing.**

At `σ = Σ_q |q⟩⟨q| ⊗ ν_q`, two blocks carrying announced labels `p`, `p'` pair as

`⟨|p⟩⟨p| ⊗ M, |p'⟩⟨p'| ⊗ M'⟩_σ = δ_{p,p'} · ⟨M, M'⟩_{ν_p}`.

Both halves are load-bearing for the coarsening bridge at the BB84 object: the Alice-key fibre
contains outcome strings with *different* announced PE blocks, and those cross terms are killed here
structurally — it is precisely this that fails once the label has been charged away, which is why
the
announce charge may not be taken before the coarsening.

No positivity or invertibility of `ν` is needed: the blockwise action of the real power
(`blockDiagRefOp_rpow`) is proved through the spectral resolution and handles singular blocks under
Lean's `0 ^ y = 0` convention. -/
theorem weightedFrobeniusPairing_blockDiagRefOp_stdProj_tensor {dE dC : ℕ}
    (ν : Fin dC → SubDensityOp dE) (p p' : Fin dC) (M M' : Op dE) :
    weightedFrobeniusPairing (blockDiagRefOp ν)
        ((stdKet dC p * (stdKet dC p).dag) ⊗ M) ((stdKet dC p' * (stdKet dC p').dag) ⊗ M')
      = if p = p' then weightedFrobeniusPairing (ν p).toOp M M' else 0 := by
  classical
  have hleft : ∀ (q : Fin dC) (N : Op dE),
      ((stdKet dC q * (stdKet dC q).dag) ⊗ N) * (blockDiagRefOp ν) ^ (-1/2 : ℝ)
        = (stdKet dC q * (stdKet dC q).dag) ⊗ (N * (ν q).toOp ^ (-1/2 : ℝ)) := by
    intro q N
    rw [blockDiagRefOp_rpow, Finset.mul_sum, Finset.sum_eq_single q]
    · rw [Op.tensor_mul, stdKetProj_idem_local]
    · intro r _ hr
      rw [Op.tensor_mul, stdKetProj_orthogonal_local (Ne.symm hr)]
      simp [Op.tensor]
    · intro h; exact absurd (Finset.mem_univ q) h
  have hassoc : ∀ A B X : Op (dC * dE), A * X * B * X = (A * X) * (B * X) := by
    intro A B X; noncomm_ring
  simp only [weightedFrobeniusPairing]
  rw [hassoc, hleft p M, hleft p' M', Op.tensor_mul]
  by_cases hpp : p = p'
  · subst hpp
    rw [if_pos rfl, stdKetProj_idem_local, Quantum.TensorProducts.Op.trace_tensor,
      trace_ketbra_normalized _ (stdKet_braket_self p), one_mul,
      show (M * (ν p).toOp ^ (-1/2 : ℝ)) * (M' * (ν p).toOp ^ (-1/2 : ℝ))
        = M * (ν p).toOp ^ (-1/2 : ℝ) * M' * (ν p).toOp ^ (-1/2 : ℝ) from by noncomm_ring]
  · rw [if_neg hpp, stdKetProj_orthogonal_local hpp]
    simp [Op.tensor]

end InfoTheory.QuantumLHL

end -- noncomputable section
