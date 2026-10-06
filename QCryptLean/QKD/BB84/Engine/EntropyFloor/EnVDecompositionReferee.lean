import QCryptLean.QKD.BB84.Engine.EntropyFloor.PhaseErrorUncertainty
import QCryptLean.Math.Concentration.BernoulliKLLowQ
import QCryptLean.Math.Concentration.BinomialKLChernoff
import QCryptLean.Math.Concentration.SelectedBinomialPassSum
import QCryptLean.QKD.BB84.Engine.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.Engine.EntropyFloor.SiftedRoundFactorizationReferee
import QCryptLean.QKD.BB84.Engine.Budgets.SmoothEntropyBound
import QCryptLean.QKD.BB84.Engine.Budgets
import QCryptLean.InfoTheory.DistanceBounds.AcceptSplit
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyOperatorBlock
import QCryptLean.InfoTheory.QuantumLHL.SeedKeySmoothing
import QCryptLean.InfoTheory.SmoothMinEntropy.ChainRule.ChainRule
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.SymmetricPurifier
import QCryptLean.Quantum.Metrics.FidelityScaling
import QCryptLean.Quantum.Channels.CPTP.IdTensorRect
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture.FinitePostFilterFloor
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Mixed
import QCryptLean.InfoTheory.DeFinetti.Theorem.TensorPowerPushforward
import QCryptLean.Quantum.Metrics.SameAncillaPurification
import QCryptLean.Quantum.Metrics.PurificationFreedom
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.TensorFinProdPartition
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSmooth
import QCryptLean.InfoTheory.BellDiagonal.AliceZMonotone
import QCryptLean.InfoTheory.BellDiagonal.AliceZIsospectral
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.CoarsenLift
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorOwnMarginal
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.LeftIsometrySupportedExtension
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.PairedLowner
import QCryptLean.InfoTheory.DistanceBounds.CPDilation
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.FilterKeepContraction
import QCryptLean.Quantum.Channels.CPTP.PositiveTransport

/-!
# BB84 sifted `Eⁿ⊗V` register decomposition and round reindexing

The dimension-casting, tensor-with-maximally-mixed-reference, and round-permutation /
key-coarsening infrastructure used to decompose the sifted BB84 `Eⁿ⊗V` register into
its trivial-attack tensor factorization and to sort/coarsen it against the PE
selection `peSel`. Also carries the paired-Haar per-σ family used by the smoothing
floor and the corresponding floor-level constant `bb84PairedHaarFloorLevel`.

The paired-Haar level has the free-deviation twin `bb84PairedHaarFloorLevelDev`: the window `δ`
keeps its protocol role (the accept-test window), while the level charges the soundness edge
`Q + δ + dev`; `bb84PairedHaarFloorLevelDev_eq` recovers `bb84PairedHaarFloorLevel` at `dev = δ`
(the `2δ` form), per Nahar et al. 2024 (arXiv:2403.11851) Lemma 9 Eq. 44 with §V.C.
-/

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

/-! The EnV decomposition objects, the pure-paired-Haar per-σ family `f`, the L3 coarsen-key split,
    and the carried floor level (Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 Thm 3, Eqs. B13–B19). -/

/-! ## Nahar et al. B13-B19 sifted privacy amplification, composed directly on the de Finetti
    reference `ρEV`

No smooth-min-entropy is ever formed on an attacked state, no fixed correlated Eve⊗reference ridge
is constructed, and no `iidReference → attacked` CP-`Λ` accept-block transfer is used: the entropy
floor is read off the de Finetti reference's own Eve marginal `ρE = partialTraceB ρEV` (Nahar et al.
B16 / Eq. 11), lifted to the full reference register through the free-reference register-extension
penalty (Nahar et al. B17) and the symmetric-subspace purifier identification (Nahar et al. B19). -/

/-! ## Own-marginal references and supported purifier extensions

The de Finetti floor uses the full `Eⁿ` quantum marginal. Extending the reference to the
supported purifier register costs `2 log₂ g`; register reassociation transports this floor to
`eveDim·(4ⁿ·V.dV)`. Leftover hashing regularizes the reference at levels below the floor.
-/

/-- Cast a CQ state across a register-dimension equality (the per-block register reassociation). -/
noncomputable def bb84CastCQState {Xc : Type*} [Fintype Xc] {a b : ℕ} (h : a = b)
    (ρ : CQState Xc a) : CQState Xc b := h ▸ ρ

/-- The cast roundtrips: casting back by `h.symm` recovers the original CQ state. -/
lemma bb84CastCQState_symm_cast {Xc : Type*} [Fintype Xc] {a b : ℕ} (h : a = b)
    (ρ : CQState Xc b) : bb84CastCQState h (bb84CastCQState h.symm ρ) = ρ := by
  subst h; rfl

/-- Block form of the CQ-state register cast: each classical block is the sub-density-operator cast
of the original block. -/
@[simp] lemma bb84CastCQState_stateMap {Xc : Type*} [Fintype Xc] {a b : ℕ} (h : a = b)
    (ρ : CQState Xc a) (x : Xc) :
    (bb84CastCQState h ρ).stateMap x = SubDensityOp.castDim h (ρ.stateMap x) := by
  subst h; rfl

/-- **Register-reassociation transport of the smooth min-entropy.**  The smooth min-entropy is
invariant under casting both the CQ state and its reference across a register-dimension equality
`h : a = b` (Nahar et al. B19 "identifying `Eⁿ V` with `R`": the host emits the bound on
`(eveDim·4ⁿ)·dV`, which is the canonical EnV purification register `eveDim·(4ⁿ·dV)` reassociated,
where `dV` is the purifier's register dimension). -/
theorem bb84_smoothMinEntropy_castDim {Xc : Type*} [Fintype Xc] [DecidableEq Xc] [Nonempty Xc]
    {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (ε : ℝ)
    (ρ : CQState Xc a) (σ : SubDensityOp a) :
    smoothMinEntropy ε ρ σ =
      smoothMinEntropy ε (bb84CastCQState h ρ) (SubDensityOp.castDim h σ) := by
  subst h; rfl

/-! ### `bb84SortRoundPerm`, the quantum register sort that gathers the key rounds into the
leading block -/

/-- `0`'s underlying operator is the zero matrix. -/
@[simp] lemma bb84_subDensityOp_zero_toOp {m : ℕ} : (0 : SubDensityOp m).toOp = 0 := rfl

/-- The underlying operator of a `SubDensityOp` tensor is the Kronecker tensor of the operators. -/
lemma bb84_subDensityOp_tensor_toOp {dA dB : ℕ} (ρ : SubDensityOp dA) (σ : SubDensityOp dB) :
    (ρ.tensor σ).toOp = ρ.toOp ⊗ σ.toOp := rfl

/-- Entry form of a `SubDensityOp` tensor: the product of the two factor entries at the
`finProdFinEquiv`-split index. -/
lemma bb84_subDensityOp_tensor_toOp_apply {dA dB : ℕ} (ρ : SubDensityOp dA) (σ : SubDensityOp dB)
    (idx idx' : Fin (dA * dB)) :
    (ρ.tensor σ).toOp idx idx' =
      ρ.toOp (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx').1 *
        σ.toOp (finProdFinEquiv.symm idx).2 (finProdFinEquiv.symm idx').2 := by
  rw [bb84_subDensityOp_tensor_toOp, Quantum.TensorProducts.Op_tensor_apply_finProd]

/-- The register reindex of the zero sub-density operator is zero. -/
@[simp] lemma bb84_subDensityOp_reindex_zero {m : ℕ} (e : Fin m ≃ Fin m) :
    SubDensityOp.reindex e (0 : SubDensityOp m) = 0 := by
  apply SubDensityOp.ext
  ext p q
  change (Matrix.reindex e e (0 : SubDensityOp m).toOp) p q = (0 : SubDensityOp m).toOp p q
  simp [bb84_subDensityOp_zero_toOp]

/-- **The key-first round sort, rev-corrected.**  `tensorFinProd` factors are stored in reversed
(`Fin.rev`) order while the L2 family reads round `a.rev`; conjugating the key-first sort
`bb84PeSelSort peSel` by `Fin.rev` aligns the two so the `tensorFinProd_sortSplit` of the L2 factor
reads exactly the sorted key/PE blocks. -/
def bb84SortRoundPerm {n : ℕ} (peSel : Fin n → Bool) : Equiv.Perm (Fin n) :=
  (bb84PeSelSort peSel).trans Fin.revPerm

/-- The component entropy floor `(n_K / log 2) * (log 2 - h(Q + 2δ)) - P(n_K, ε)`.
Here `n_K = n - m` and `P` is the bit-register IID AEP penalty. Components are compared with
their own quantum marginals, so this floor pays no reference-change logarithm. The separate
purifier adjunction costs `2 log₂ C(n+15,15)`.

References: Renner 2005, `cor:Hmincondrepclass`; Nahar et al. 2024, arXiv:2403.11851,
Appendix B, `eq:boundingsmoothedmin` and `eq:splittingoffV`. -/
noncomputable def bb84PairedHaarFloorLevel (n m : ℕ) (Q δ εTensor : ℝ) : ℝ :=
  (bb84KeyRoundCount n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ)) -
    finiteSizePenalty (bb84KeyRoundCount n m) εTensor

/-- The component entropy floor `(n_K / log 2) * (log 2 - h(Q + δ + dev)) - P(n_K, ε)`.
Here `n_K = n - m` and `P` is the bit-register IID AEP penalty. Components are compared with
their own quantum marginals, so this floor pays no reference-change logarithm. The separate
purifier adjunction costs `2 log₂ C(n+15,15)`.

References: Renner 2005, `cor:Hmincondrepclass`; Nahar et al. 2024, arXiv:2403.11851,
Appendix B, `eq:boundingsmoothedmin` and `eq:splittingoffV`. -/
noncomputable def bb84PairedHaarFloorLevelDev (n m : ℕ) (Q δ dev εTensor : ℝ) : ℝ :=
  (bb84KeyRoundCount n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + δ + dev)) -
    finiteSizePenalty (bb84KeyRoundCount n m) εTensor

/-- A positive component entropy floor requires at least one key round. -/
lemma lt_of_bb84PairedHaarFloorLevelDev_pos {n m : ℕ} {Q δ dev ε : ℝ}
    (h : 0 < bb84PairedHaarFloorLevelDev n m Q δ dev ε) : m < n := by
  by_contra hmn
  have hzero : bb84KeyRoundCount n m = 0 := Nat.sub_eq_zero_of_le (by omega)
  simp [bb84PairedHaarFloorLevelDev, hzero, finiteSizePenalty] at h

/-- The carried floor level is the Dev level at `dev = δ` (up to `δ + δ = 2 * δ`). -/
lemma bb84PairedHaarFloorLevelDev_eq (n m : ℕ) (Q δ εTensor : ℝ) :
    bb84PairedHaarFloorLevelDev n m Q δ δ εTensor = bb84PairedHaarFloorLevel n m Q δ εTensor := by
  unfold bb84PairedHaarFloorLevelDev bb84PairedHaarFloorLevel
  rw [add_assoc, two_mul]

/-! ### The conditioning-side PE-announce key CQ constructor

The faithful register move announces the PE-round product block into the **conditioning** (quantum)
register while keeping the key-round bits on the secret (classical) register.  The announced block
is the PE-round product's own quantum marginal `τ = (bb84RefereeSiftedPERoundProd
…).quantumMarginal` — an `x`-independent (key-outcome-independent) sub-normalized operator — so the
`smoothMinEntropy_le_condTensor_decoupled_ancilla` applies without penalty
at each Carathéodory point, before the mixture over the de Finetti measure (where `ω_PE` becomes
`σ`-correlated and announcing can lower the entropy).

The product reference may be singular. The floor is preserved against the own marginal,
then extended over the supported purifier register with the `2 log₂ g` charge. For leftover
hashing, every level strictly below the resulting floor is certified against a positive
definite reference by `exists_posDef_smoothMinEntropy_ge_of_lt`; taking the limit gives
the reference-optimised LHL bound. No positive-definiteness assumption is imposed on the
original product marginal. -/

end QKD.BB84.Engine

end -- noncomputable section
