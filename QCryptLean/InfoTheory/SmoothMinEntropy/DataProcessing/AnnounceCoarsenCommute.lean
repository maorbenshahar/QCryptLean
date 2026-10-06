import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.AnnounceCoarsenProduct

/-!
# The announce kernel slides past a classical coarsening it factors through

An announce kernel that is **constant on the fibres of a classical coarsening** commutes with that
coarsening: announcing first and coarsening second gives the same CQ state as coarsening first and
announcing the induced `Y`-indexed kernel second.

`CQState.tensorLeftKernel` puts the announcement in the **high** digits of the conditioning
register, and `CQState.coarsen` (`InfoTheory/QuantumLHL/ClassicalCoarsening.lean`) only sums blocks
inside a fibre, leaving the quantum register alone.  So the `y`-block of the announce-then-coarsen
state is

`∑_{x : g x = y} K x ⊗ ρ_x`,

and when `K` is constant on the fibre — `K x = L (g x)` — the constant factor `L y` pulls out of the
fibre sum, leaving `L y ⊗ (∑_{x : g x = y} ρ_x)`, which is the `y`-block of the
coarsen-then-announce state.

The hypothesis `hK : ∀ x, K x = L (g x)` says exactly that `K` is constant on the fibres of `g`,
with `L` naming the induced `Y`-indexed kernel; it is choice-free.  At a `y` outside the range of
`g` the value `L y` is unconstrained, and both sides vanish there (an empty fibre sum against
`L y ⊗ 0`).

This is the *slide* rule that lets an announcement be moved past an intermediate coarsening; the
block form of the composite construction it is stated about is
`bb84AnnounceCoarsenCQ_stateMap`.

References: Renner 2005 (arXiv:quant-ph/0512258v2) §6.5 and Lemma 3.1.10 (classical side
information); Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B
main.tex:1341–:1413 (Appendix B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}`
(main.tex:1356–:1362), the Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed
min-entropy bound `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting
step `\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413)
(the announced side information entering the conditioning register).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Tensoring the zero operator on the right of a fixed operator gives zero. -/
lemma tensor_zero_op {n m : ℕ} (A : Op n) : Op.tensor A (0 : Op m) = 0 := by
  ext i j
  simp [Op_tensor_apply_finProd]

/-- **Block form of the slide.**  If the announce kernel `K` factors through the coarsening
(`K x = L (g x)`, i.e. `K` is constant on the fibres of `g`), the constant announcement factor
pulls out of the fibre sum:

`∑_{x : g x = y} K x ⊗ ρ_x = L y ⊗ (∑_{x : g x = y} ρ_x)`.

Block twin of `bb84AnnounceCoarsenCQ_stateMap`. -/
lemma CQState.coarsenBlock_tensorLeftKernel_of_fiberConstant
    {X Y : Type*} [Fintype X] [DecidableEq Y] {dE dC : ℕ}
    (g : X → Y) (ρ : CQState X dE) (K : X → SubDensityOp dC) (L : Y → SubDensityOp dC)
    (hK : ∀ x, K x = L (g x)) (y : Y) :
    (CQState.coarsenBlock g (ρ.tensorLeftKernel K) y).toOp =
      Op.tensor (L y).toOp (CQState.coarsenBlock g ρ y).toOp := by
  rw [CQState.coarsenBlock_toOp, CQState.coarsenBlock_toOp, tensor_sum_op]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : g x = y
  · rw [ite_eq_left hx, ite_eq_left hx, CQState.tensorLeftKernel_stateMap, hK x, hx]
    rfl
  · rw [ite_eq_right hx, ite_eq_right hx, tensor_zero_op]

/-- **The announce kernel slides past a coarsening it factors through.**

For a coarsening `g : X → Y` and an announce kernel `K : X → SubDensityOp dC` constant on the
fibres of `g` — `hK : ∀ x, K x = L (g x)` — announcing then coarsening equals coarsening then
announcing the induced kernel `L`:

`coarsen g (ρ.tensorLeftKernel K) = (coarsen g ρ).tensorLeftKernel L`.

Both sides are CQ states on the classical register `Y` with conditioning register `dC * dE`, the
announcement riding in the high digits. -/
theorem CQState.coarsen_tensorLeftKernel_of_fiberConstant
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {dE dC : ℕ}
    (g : X → Y) (ρ : CQState X dE) (K : X → SubDensityOp dC) (L : Y → SubDensityOp dC)
    (hK : ∀ x, K x = L (g x)) :
    CQState.coarsen g (ρ.tensorLeftKernel K) = (CQState.coarsen g ρ).tensorLeftKernel L := by
  refine CQState.ext_stateMap (funext fun y => SubDensityOp.ext ?_)
  rw [CQState.coarsen_stateMap, CQState.tensorLeftKernel_stateMap,
    CQState.coarsenBlock_tensorLeftKernel_of_fiberConstant g ρ K L hK y]
  rfl

/-- **Announcement-index form of the slide.**  The kernel is built from a classical announcement
map `ann : X → A` through a fixed family `K : A → SubDensityOp dC`; the announcement is constant on
the fibres of the coarsening because it factors as `ann = annY ∘ g`.  This is the shape of the BB84
announce-then-coarsen construction `bb84AnnounceCoarsenCQ`, where
`K = stdProj dAnn`. -/
theorem CQState.coarsen_tensorLeftKernel_ann_of_fiberConstant
    {X Y A : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] {dE dC : ℕ}
    (g : X → Y) (ρ : CQState X dE) (ann : X → A) (annY : Y → A) (K : A → SubDensityOp dC)
    (hann : ∀ x, ann x = annY (g x)) :
    CQState.coarsen g (ρ.tensorLeftKernel fun x => K (ann x)) =
      (CQState.coarsen g ρ).tensorLeftKernel fun y => K (annY y) :=
  CQState.coarsen_tensorLeftKernel_of_fiberConstant g ρ _ _ fun x => by rw [hann x]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
