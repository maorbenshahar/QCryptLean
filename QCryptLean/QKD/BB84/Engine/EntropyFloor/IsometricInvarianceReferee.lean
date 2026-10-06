import QCryptLean.QKD.BB84.Engine.EntropyFloor.EnVDecompositionReferee
import QCryptLean.Quantum.Channels.CPTP.CKRBound.MapIdTensorConjugation
import QCryptLean.Quantum.Metrics.SwapBridge
import QCryptLean.QKD.BB84.Engine.PerRound.DevetakWinter
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.PureCoreUncertainty
import QCryptLean.Quantum.TensorProducts.TensorPow

/-! The generic tensor-power isometric-invariance block: tensor-power conjugation,
    smooth-min-entropy invariance, the key-scoped DW register bridge and collective/per-σ/per-point
    smooth floors, the accepting set, and the non-accepting trace-norm bound. -/

-- The paired-Haar per-σ family wiring (below) states Bochner integrability of `Op`-valued block
-- maps; as in `FinitePostFilterFloor.lean`/`Reference/Mixed.lean`, this uses the Frobenius norm on
-- matrices.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

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

/-! ### Generic tensor-power isometric invariance.

A single-copy conjugation by `W`, applied to every block and the reference, is conjugation by the
operator tensor power `Op.tensorPow W m`; for an isometry `W` it embeds isometrically into the
`m`-fold smooth min-entropy. -/

/-- **Tensor-product of conjugated blocks.**  If `g j = W (f j) Wᴴ` blockwise, the finite tensor
product `tensorFinProd m g` is the `Op.tensorPow W m`-conjugate of `tensorFinProd m f`. -/
lemma tensorFinProd_toOp_conj {d : ℕ} [NeZero d] (W : Op d) (m : ℕ)
    (f g : Fin m → SubDensityOp d)
    (h : ∀ j, (g j).toOp = W * (f j).toOp * Wᴴ) :
    (SubDensityOp.tensorFinProd m g).toOp =
      Op.tensorPow W m * (SubDensityOp.tensorFinProd m f).toOp * (Op.tensorPow W m)ᴴ := by
  induction m with
  | zero =>
      change (SubDensityOp.tensorFinProd 0 g).toOp =
          (1 : Op (d ^ 0)) * (SubDensityOp.tensorFinProd 0 f).toOp * (1 : Op (d ^ 0))ᴴ
      rw [conjTranspose_one, one_mul, mul_one]
      congr 1
  | succ k ih =>
      haveI : NeZero (d ^ k) := NeZero.pow
      have hc : d * d ^ k = d ^ (k + 1) := by ring
      have ihk := ih (f ∘ Fin.succ) (g ∘ Fin.succ) (fun j => h j.succ)
      change (SubDensityOp.castDim hc ((g 0).tensor
            (SubDensityOp.tensorFinProd k (g ∘ Fin.succ)))).toOp =
          Op.castDim hc (Op.tensor W (Op.tensorPow W k)) *
            (SubDensityOp.castDim hc ((f 0).tensor
              (SubDensityOp.tensorFinProd k (f ∘ Fin.succ)))).toOp *
            (Op.castDim hc (Op.tensor W (Op.tensorPow W k)))ᴴ
      rw [InfoTheory.SmoothMinEntropy.SubDensityOp.castDim_toOp,
          InfoTheory.SmoothMinEntropy.SubDensityOp.castDim_toOp, bb84_subDensityOp_tensor_toOp,
        bb84_subDensityOp_tensor_toOp, Op.castDim_conjTranspose, Op.castDim_mul, Op.castDim_mul]
      congr 1
      rw [show (g 0).toOp = W * (f 0).toOp * Wᴴ from h 0, ihk, Op.tensor_conjTranspose,
        Op.tensor_mul, Op.tensor_mul]

/-- **(e) generic tensor-power isometric invariance.**  If one unitary `W` conjugates each
    single-copy
block (`hblock`) and the reference (`hmarg`), the `m`-fold tensor-power smooth min-entropy of the
canonical pair is `≤` that of the embedded pair. -/
lemma smoothMinEntropy_tensorPower_conj_le {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {d : ℕ} [NeZero d] (m : ℕ) [NeZero (d ^ m)]
    (W : Op d) (hW : Wᴴ * W = 1)
    (ρ ρ' : CQState α d) (E σR : SubDensityOp d)
    (hblock : ∀ z : α, (ρ'.stateMap z).toOp = W * (ρ.stateMap z).toOp * Wᴴ)
    (hmarg : σR.toOp = W * E.toOp * Wᴴ)
    (ε : ℝ) :
    smoothMinEntropy ε (CQState.tensorPower ρ m) (SubDensityOp.tensorPower E m) ≤
      smoothMinEntropy ε (CQState.tensorPower ρ' m) (SubDensityOp.tensorPower σR m) := by
  refine smoothMinEntropy_left_isometry_embed_arbitraryRef_le (Op.tensorPow W m)
    (Op.conjTranspose_tensorPow_mul_self hW m) ε (CQState.tensorPower ρ m)
    (SubDensityOp.tensorPower E m)
    (CQState.tensorPower ρ' m) ?_ (SubDensityOp.tensorPower σR m) ?_
  · intro xs
    rw [CQState.tensorPower_stateMap_toOp, CQState.tensorPower_stateMap_toOp]
    exact tensorFinProd_toOp_conj W m (fun j => ρ.stateMap (xs j)) (fun j => ρ'.stateMap (xs j))
      (fun j => hblock (xs j))
  · change (SubDensityOp.tensorFinProd m (fun _ => σR)).toOp =
        Op.tensorPow W m * (SubDensityOp.tensorFinProd m (fun _ => E)).toOp * (Op.tensorPow W m)ᴴ
    exact tensorFinProd_toOp_conj W m (fun _ => E) (fun _ => σR) (fun _ => hmarg)

/-- **Round reference marginal.**  Summing the single-round sifted reference blocks over the outcome
`k` recovers the partial trace over Alice of `ψ`, independent of the round type `b`. -/
lemma bb84_referee_siftedRoundRefBlock_sum_eq_partialTraceA
    (ψ : DensityOp (signalDim * signalDim)) (b : Bool) :
    ∑ k : Fin signalDim, (bb84RefereeSiftedSingleRoundRefBlock ψ b k).toOp =
      Quantum.TensorProducts.partialTraceA ψ.toOp := by
  ext r r'
  rw [Matrix.sum_apply,
    show Quantum.TensorProducts.partialTraceA ψ.toOp r r' =
        ∑ t : Fin signalDim, ψ.toOp (finProdFinEquiv (t, r)) (finProdFinEquiv (t, r'))
      from by simp [Quantum.TensorProducts.partialTraceA]]
  simp_rw [bb84RefereeSiftedSingleRoundRefBlock_toOp_entry]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Matrix.sum_apply, bb84RefereeSiftedConditionOp_sum, Matrix.one_apply,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

/-- **Sum-over-outcomes tensor swap, general classical index.**  The `X`-string sum of the per-round
tensor product is the tensor product of the per-round marginals (`Href a = ∑_k Gfam a k`): the
finite tensor product is a (reversed) tensor family (`SubDensityOp.tensorFinProd_toOp`), which is
multilinear in its factors (`tensorFamily_sum`). -/
lemma sum_tensorFinProd_toOp_classical {Xc : Type*} [Fintype Xc] {d m : ℕ} [NeZero d]
    [NeZero (d ^ m)]
    (Gfam : Fin m → Xc → SubDensityOp d) (Href : Fin m → SubDensityOp d)
    (hH : ∀ a, (Href a).toOp = ∑ k : Xc, (Gfam a k).toOp) :
    ∑ ω : Fin m → Xc, (SubDensityOp.tensorFinProd m (fun a => Gfam a (ω a))).toOp =
      (SubDensityOp.tensorFinProd m Href).toOp := by
  simp only [SubDensityOp.tensorFinProd_toOp, hH]
  rw [tensorFamily_sum (ι := fun _ => Xc) fun k x => (Gfam (Fin.rev k) x).toOp]
  exact Fintype.sum_equiv (Equiv.arrowCongr Fin.revPerm (Equiv.refl Xc)) _ _ fun ω => rfl

/-- **Marginal of a CQ tensor power.**  The quantum marginal of `CQState.tensorPower ρ m` is the
`m`-fold tensor power of `ρ`'s own quantum marginal (sum over the `m`-string outcomes factors). -/
lemma tensorPower_quantumMarginal_eq {Xc : Type*} [Fintype Xc]
    {d : ℕ} [NeZero d] (ρ : CQState Xc d) (m : ℕ) [NeZero (d ^ m)] :
    (CQState.tensorPower ρ m).quantumMarginal = SubDensityOp.tensorPower ρ.quantumMarginal m := by
  apply SubDensityOp.ext
  change (CQState.tensorPower ρ m).quantumMarginalOp =
    (SubDensityOp.tensorPower ρ.quantumMarginal m).toOp
  rw [CQState.quantumMarginalOp]
  simp_rw [InfoTheory.SmoothMinEntropy.CQState.tensorPower_stateMap_toOp ρ m]
  rw [SubDensityOp.tensorPower]
  exact sum_tensorFinProd_toOp_classical (fun _ => ρ.stateMap) (fun _ => ρ.quantumMarginal)
    (fun _ => rfl)

/-- Tensor powers of two sub-density operators with equal underlying operators are equal
operatorwise. -/
lemma tensorPower_toOp_congr {d : ℕ} [NeZero d] {A B : SubDensityOp d} (h : A.toOp = B.toOp)
    (k : ℕ) :
    (SubDensityOp.tensorPower A k).toOp = (SubDensityOp.tensorPower B k).toOp := by
  rw [SubDensityOp.tensorPower, SubDensityOp.tensorPower, SubDensityOp.tensorFinProd_const_toOp,
    SubDensityOp.tensorFinProd_const_toOp, h]

end QKD.BB84.Engine

end -- noncomputable section
