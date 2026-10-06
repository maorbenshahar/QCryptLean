import QCryptLean.QKD.BB84.Engine.EntropyFloor.IsometricInvarianceReferee
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.FinitePostFilterFloorCoarsen

/-!
# Classical-coarsening commutation lemmas for CQ-state register transport

Generic algebraic facts about how classical coarsening of a `CQState` interacts with the
register-transport operations used throughout the BB84 finite-key chain: a dimension cast, a
quantum-register reindex, and composition of two coarsening maps.  These are register-generic (no
BB84 content) and are consumed by the key/PE-round coarsening machinery of
`PELabelledPerSigmaFloor.lean` (`bb84_coarsenKeyPair_transport`).

## Main results
- `coarsen_bb84CastCQState`: classical coarsening commutes with a CQ register-dimension cast.
- `coarsen_reindexQ`: classical coarsening commutes with a quantum-register reindex.
- `coarsen_coarsen`: coarsening by `f` then `g` equals coarsening by `g ∘ f`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open InfoTheory.QuantumLHL
open InfoTheory.VonNeumannEntropy
open Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker

noncomputable section

namespace QKD.BB84.Engine

/-! ### Register-plumbing: coarsening commutes with the register transports

A register transport composing a dimension cast with a quantum-register reindex,
`bb84CastCQState h_split ∘ reindexQ P ∘ bb84CastCQState h_collapse`, acts only on the quantum
register, while classical coarsening acts only on the classical register — so the two commute; and
coarsening composes.  These are the algebraic facts that turn a transported family into a
coarsening of the transported original. -/

/-- Classical coarsening commutes with the CQ register-dimension cast. -/
lemma coarsen_bb84CastCQState {Xc Yc : Type*} [Fintype Xc] [Fintype Yc] [DecidableEq Yc]
    {a b : ℕ} (h : a = b) (g : Xc → Yc) (ρ : CQState Xc a) :
    CQState.coarsen g (bb84CastCQState h ρ) = bb84CastCQState h (CQState.coarsen g ρ) := by
  subst h; rfl

/-- Classical coarsening commutes with the quantum-register reindex. -/
lemma coarsen_reindexQ {Xc Yc : Type*} [Fintype Xc] [Fintype Yc] [DecidableEq Yc]
    {d : ℕ} (e : Fin d ≃ Fin d) (g : Xc → Yc) (ρ : CQState Xc d) :
    CQState.coarsen g (CQState.reindexQ e ρ) = CQState.reindexQ e (CQState.coarsen g ρ) := by
  apply CQState.ext_stateMap
  funext y
  apply SubDensityOp.ext
  have hL : ((CQState.coarsen g (CQState.reindexQ e ρ)).stateMap y).toOp =
      ∑ x : Xc, if g x = y then Matrix.reindex e e ((ρ.stateMap x).toOp) else 0 := rfl
  have hR : ((CQState.reindexQ e (CQState.coarsen g ρ)).stateMap y).toOp =
      Matrix.reindex e e (∑ x : Xc, if g x = y then (ρ.stateMap x).toOp else 0) := rfl
  rw [hL, hR]
  conv_rhs => rw [← Matrix.coe_reindexLinearEquiv ℂ ℂ, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.coe_reindexLinearEquiv]
  by_cases hx : g x = y <;> simp [hx, Matrix.reindex_apply, Matrix.submatrix_zero]

/-- Classical coarsening composes: coarsening by `f` then `g` is coarsening by `g ∘ f`. -/
lemma coarsen_coarsen {Xc Yc Zc : Type*} [Fintype Xc] [Fintype Yc] [Fintype Zc]
    [DecidableEq Yc] [DecidableEq Zc] {d : ℕ} (f : Xc → Yc) (g : Yc → Zc) (ρ : CQState Xc d) :
    CQState.coarsen g (CQState.coarsen f ρ) = CQState.coarsen (g ∘ f) ρ := by
  apply CQState.ext_stateMap
  funext z
  apply SubDensityOp.ext
  have hL : ((CQState.coarsen g (CQState.coarsen f ρ)).stateMap z).toOp =
      ∑ y : Yc, if g y = z then (∑ x : Xc, if f x = y then (ρ.stateMap x).toOp else 0) else 0 := rfl
  have hR : ((CQState.coarsen (g ∘ f) ρ).stateMap z).toOp =
      ∑ x : Xc, if g (f x) = z then (ρ.stateMap x).toOp else 0 := rfl
  rw [hL, hR]
  rw [show (∑ y : Yc, if g y = z then (∑ x : Xc, if f x = y then (ρ.stateMap x).toOp else 0) else 0)
      =
        ∑ y : Yc, ∑ x : Xc, if g y = z then (if f x = y then (ρ.stateMap x).toOp else 0) else 0 from
            by
      apply Finset.sum_congr rfl; intro y _; by_cases hy : g y = z <;> simp [hy]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy; rw [if_neg (Ne.symm hy)]; simp
  · intro h; exact absurd (Finset.mem_univ (f x)) h

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

end QKD.BB84.Engine

end -- noncomputable section
