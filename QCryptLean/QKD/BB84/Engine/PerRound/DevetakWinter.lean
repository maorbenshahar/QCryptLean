import QCryptLean.QKD.BB84.Engine.EntropyFloor.EnVDecompositionReferee
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSmoothRankBound

/-!
# The Devetak–Winter collective key-rate route

The per-σ collective smooth-min-entropy floor, discharged through the Devetak–Winter single-round
von-Neumann key rate `H(Z_A|E) ≥ 1 − h(q_phase)/log 2`, lifted by the Renner smooth AEP against
the component's own quantum marginal. Alice's classical register is a bit, so its finite-size
penalty coefficient is `2 log₂ 5`. The proof uses the witness single-round CQ state, purification
unitary freedom, and Bell twirling with error-rate preservation.

## Main definitions

- `QKD.BB84.Engine.bb84ComponentAliceZCQState`: the single-round Alice-`Z` bit-CQ state of an AB
  component `σ`, the IID building block of the Devetak–Winter rate `H(Z_A|E)_σ`.
-/

-- The paired-Haar per-σ family wiring (below) states Bochner integrability of `Op`-valued block
-- maps; as in `FinitePostFilterFloor.lean`/`Reference/Mixed.lean`, this uses the Frobenius norm on
-- matrices.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Quantum.Metrics.KitaevWatrousPurification
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open InfoTheory.QuantumLHL
open InfoTheory.VonNeumannEntropy
open Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- **The witness state `ρ_σ`.** The single-round Alice-`Z` bit-CQ state of the AB component
`σ`: the round state is the explicit canonical Schmidt purification `sameAncillaPurificationDensity
σ` (pure, `partialTraceB = σ`, so Eve's register is a `signalDim`- dimensional purifying ancilla —
no `Classical.choose`), Alice measures her qubit in `Z` (the `bb84AliceBitMap` coarsening of the
four-outcome single-round CQ state), and the quantum register `E` purifies `σ_AB`.  This is the IID
building block of the Devetak–Winter rate (`H(Z_A|E)_σ`). -/
noncomputable def bb84ComponentAliceZCQState (σ : DensityOp signalDim) :
    CQState (Fin 2) signalDim :=
  bb84AliceZCQState signalDim
    (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ)

/-- The component Alice-`Z` bit-CQ state is normalized (total weight `1`): the `bb84AliceBitMap`
coarsening preserves the weight of the normalized single-round CQ state. -/
lemma bb84ComponentAliceZCQState_norm (σ : DensityOp signalDim) :
    ∑ z : Fin 2, ((bb84ComponentAliceZCQState σ).stateMap z).trace = 1 := by
  let ρN : NormalizedCQState (Fin signalDim) signalDim :=
    bb84SingleRoundCQState signalDim
      (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ)
  calc ∑ z : Fin 2, ((bb84ComponentAliceZCQState σ).stateMap z).trace
         = ∑ x : Fin signalDim,
          ((ρN : CQState (Fin signalDim) signalDim).stateMap x).trace := by
        simpa [bb84ComponentAliceZCQState, bb84AliceZCQState, ρN] using
          (CQState.sum_coarsen_stateMap_trace_eq bb84AliceBitMap
            (ρN : CQState (Fin signalDim) signalDim))
    _ = 1 := ρN.weight_eq_one

/-! ### Single-round Devetak–Winter rate: the purifier-free identity and Bell-twirl monotonicity,
so the floor's proof can route the generic-`σ` rate through the Bell twirl. -/

/-- The Alice-`Z` block projector `aliceZProj` (computational `i/2 = z` selector) agrees with the
BB84 coarse Alice-`Z` POVM projector `bb84AliceZProjector` (fiber sum of `bb84AliceBitMap`). -/
lemma aliceZProj_eq_bb84AliceZProjector (z : Fin 2) :
    QKD.BB84.Engine.aliceZProj z = bb84AliceZProjector z := by
  rw [bb84AliceZProjector_eq_diagonal]
  unfold QKD.BB84.Engine.aliceZProj
  congr 1
  funext k
  simp only [bb84AliceBitMap, Fin.ext_iff]

/-- The component Alice-`Z` bit-CQ blocks are Eve's reduced states after the Alice-`Z` measurement
    of
the canonical purifier `Ψ = sameAncillaPurificationDensity σ` (whose Alice–Bob marginal is `σ`). -/
lemma bb84ComponentAliceZCQState_origin (σ : DensityOp signalDim) (z : Fin 2) :
    ((bb84ComponentAliceZCQState σ).stateMap z).toOp =
      partialTraceA (Op.tensor (QKD.BB84.Engine.aliceZProj z) (1 : Op 4)
        * (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ).toOp
        * Op.tensor (QKD.BB84.Engine.aliceZProj z) (1 : Op 4)) := by
  rw [aliceZProj_eq_bb84AliceZProjector z]
  exact bb84AliceZCQState_origin signalDim
    (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ) z

/-! ### The `W`-unitary purification swap between the ψ-reference key blocks and the canonical
component Alice-`Z` blocks. -/

/-- **Key-block as an Alice-`Z` projector sandwich.**  The `bb84AliceBitMap`-coarsened key-round CQ
block of `ψ` is `partialTraceA` of the Alice-`Z` projector sandwich of `ψ`: the diagonal Alice-`Z`
projector's cross terms vanish under the signal trace, so the coarsened bit-fiber sum of per-`k`
computational sandwiches collapses to a single projector sandwich. -/
private lemma bb84SiftedKeyRoundCQ_stateMap_toOp_eq_aliceZProj_sandwich
    (ψ : DensityOp (signalDim * signalDim)) (z : Fin 2) :
    ((bb84SiftedKeyRoundCQ ψ).stateMap z).toOp =
      partialTraceA (Op.tensor (QKD.BB84.Engine.aliceZProj z) (1 : Op signalDim) * ψ.toOp
        * Op.tensor (QKD.BB84.Engine.aliceZProj z) (1 : Op signalDim)) := by
  rw [show QKD.BB84.Engine.aliceZProj z =
        Matrix.diagonal (fun i : Fin signalDim => if i.val / 2 = z.val then (1 : ℂ) else 0)
        from rfl, partialTraceA_sandwich_tensor_diagonal_one]
  ext r r'
  rw [bb84SiftedKeyRoundCQ, CQState.coarsen_stateMap_toOp, Matrix.sum_apply, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hval : (bb84AliceBitMap k = z) ↔ (k.val / 2 = z.val) := by
    constructor
    · intro h; have := congrArg Fin.val h; simpa [bb84AliceBitMap] using this
    · intro h; apply Fin.ext; simpa [bb84AliceBitMap] using h
  by_cases hk : bb84AliceBitMap k = z
  · rw [ite_eq_left hk, ite_eq_left (hval.mp hk), one_mul, mul_one]
    exact bb84RefereeSiftedSingleRoundRefBlock_false_toOp_entry ψ k r r'
  · rw [ite_eq_right hk, ite_eq_right (fun h => hk (hval.mpr h)), Matrix.zero_apply, zero_mul,
    zero_mul]

/-- **`(1 ⊗ W)`-conjugation pushes through the Alice-`Z` projector sandwich.**  Since `P ⊗ 1`
commutes with `1 ⊗ W`, the partial trace of the projector-sandwiched `(1 ⊗ W)`-conjugate equals the
`W`-conjugate of the partial trace of the projector sandwich. -/
private lemma bb84_partialTraceA_aliceZProj_conj
    (W P : Op signalDim) (M : Op (signalDim * signalDim)) :
    partialTraceA (Op.tensor P 1 * (Op.tensor 1 W * M * (Op.tensor 1 W)ᴴ) * Op.tensor P 1) =
      W * partialTraceA (Op.tensor P 1 * M * Op.tensor P 1) * Wᴴ := by
  have h1 : Op.tensor P (1 : Op signalDim) * Op.tensor (1 : Op signalDim) W
      = Op.tensor (1 : Op signalDim) W * Op.tensor P (1 : Op signalDim) :=
    Op.tensor_one_mul_one_tensor_comm P W
  have hconjT : (Op.tensor (1 : Op signalDim) W)ᴴ = Op.tensor (1 : Op signalDim) Wᴴ := by
    rw [Op.tensor_conjTranspose, conjTranspose_one]
  have h2 : (Op.tensor (1 : Op signalDim) W)ᴴ * Op.tensor P (1 : Op signalDim)
      = Op.tensor P (1 : Op signalDim) * (Op.tensor (1 : Op signalDim) W)ᴴ := by
    rw [hconjT]; exact (Op.tensor_one_mul_one_tensor_comm P Wᴴ).symm
  have hM : Op.tensor P 1 * (Op.tensor 1 W * M * (Op.tensor 1 W)ᴴ) * Op.tensor P 1
      = Op.tensor 1 W * (Op.tensor P 1 * M * Op.tensor P 1) * (Op.tensor 1 W)ᴴ := by
    simp only [← mul_assoc]
    rw [h1, mul_assoc (Op.tensor 1 W * Op.tensor P 1 * M) ((Op.tensor 1 W)ᴴ) (Op.tensor P 1), h2]
    simp only [← mul_assoc]
  rw [hM, hconjT, partialTraceA_one_tensor_sandwich]

/-- **The two `W`-identities.**  For a **pure** paired state `ψ`, the ψ-reference
key-round bit-CQ blocks `bb84SiftedKeyRoundCQ ψ` and the canonical component Alice-`Z` blocks
`bb84ComponentAliceZCQState σ` (`σ = Tr_B ψ`) coincide up to a single unitary `W` on the 4-dim
reference (the purification-freedom unitary of Watrous Lemma 2.41): per block
`keyblock z = W · ρ_σ[z] · Wᴴ`, and on the reference marginal `σ_R = W · E_key · Wᴴ`.

**The purity hypothesis is load-bearing**: `purification_unitary_freedom_canonical`
relates two *purifications* of `σ`, so `ψ` must be a pure state purifying `σ`; for mixed `ψ` no such
`W` exists. -/
theorem bb84SiftedKeyRoundCQ_eq_componentAliceZ_conj
    (ψ : DensityOp (signalDim * signalDim)) (hψ : ψ.IsPure) :
    ∃ W : UnitaryOp signalDim,
      (∀ z : Fin 2, ((bb84ComponentAliceZCQState (DensityOp.partialTraceB ψ)).stateMap z).toOp =
        (W.toOp)ᴴ * ((bb84SiftedKeyRoundCQ ψ).stateMap z).toOp * W.toOp) ∧
      (bb84ComponentAliceZCQState (DensityOp.partialTraceB ψ)).quantumMarginalOp =
        (W.toOp)ᴴ * (bb84SiftedKeyRoundCQ ψ).quantumMarginalOp * W.toOp := by
  set σ := DensityOp.partialTraceB ψ with hσ
  -- ψ is the rank-1 projector of its purifying ket.
  have hket : ψ.toOp = (ψ.pureKetOf hψ) * (ψ.pureKetOf hψ).dag := ψ.pureKetOf_spec hψ
  have hpu : partialTraceB ((ψ.pureKetOf hψ) * (ψ.pureKetOf hψ).dag) = σ.toOp := by
    rw [← hket]; rfl
  obtain ⟨W, hW⟩ := Quantum.Metrics.purification_unitary_freedom_canonical σ (ψ.pureKetOf hψ) hpu
  have hUU : (W.toOp)ᴴ * W.toOp = 1 := W.unitary_left
  -- Density form of the purification-freedom identity: `ψ = (1⊗W) Ψ (1⊗W)ᴴ`.
  have hΨ : (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ).toOp
      = Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet σ
        * (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet σ).dag :=
    sameAncillaPurification_eq_ketbra_sameAncillaPurificationKet σ
  have hPsi : ψ.toOp = Op.tensor 1 W.toOp
      * (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ).toOp
      * (Op.tensor 1 W.toOp)ᴴ := by
    rw [hket, hW, ← op_mul_ketbra_mul_conjTranspose, ← hΨ]
  -- The per-block identity `ρ_σ[z] = Wᴴ · keyblock z · W` (all factors on the 4-dim register).
  have hblock : ∀ z : Fin 2, ((bb84ComponentAliceZCQState σ).stateMap z).toOp =
      (W.toOp)ᴴ * ((bb84SiftedKeyRoundCQ ψ).stateMap z).toOp * W.toOp := by
    intro z
    rw [bb84ComponentAliceZCQState_origin,
      bb84SiftedKeyRoundCQ_stateMap_toOp_eq_aliceZProj_sandwich, hPsi,
      bb84_partialTraceA_aliceZProj_conj]
    rw [show (W.toOp)ᴴ * (W.toOp * partialTraceA (Op.tensor (QKD.BB84.Engine.aliceZProj z) 1
          * (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ).toOp
          * Op.tensor (QKD.BB84.Engine.aliceZProj z) 1) * (W.toOp)ᴴ) * W.toOp
        = ((W.toOp)ᴴ * W.toOp) * partialTraceA (Op.tensor (QKD.BB84.Engine.aliceZProj z) 1
          * (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ).toOp
          * Op.tensor (QKD.BB84.Engine.aliceZProj z) 1) * ((W.toOp)ᴴ * W.toOp)
        from by simp only [← mul_assoc], hUU, one_mul, mul_one]
  refine ⟨W, hblock, ?_⟩
  -- Sum the per-block identity over `z` to get the reference-marginal identity.
  rw [CQState.quantumMarginalOp, CQState.quantumMarginalOp, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun z _ => hblock z)

/-- **Witness `H(Z_A|E)_σ`.** The single-round Alice-`Z` Devetak–Winter key rate of the `AB`
    component
`σ`: `(S(joint_σ) − S(E_σ))/log 2`. -/
noncomputable def bb84ComponentAliceZRate (σ : DensityOp signalDim) : ℝ :=
  (vonNeumannEntropy
        ((bb84ComponentAliceZCQState σ).toJointDensityOp (bb84ComponentAliceZCQState_norm σ))
      - vonNeumannEntropy
        ((bb84ComponentAliceZCQState σ).quantumMarginalDensityOp
          (bb84ComponentAliceZCQState_norm σ)))
    / Real.log 2

/-- **(A.3) purifier-free rate identity.** `S(joint_σ) − S(E_σ) = S(Δ_A σ) − S(σ)` (Devetak–Winter
2005; Coles–Colbeck–Yu–Zwolak 2012). -/
theorem bb84ComponentAliceZRate_eq_dephasingRate (σ : DensityOp signalDim) :
    vonNeumannEntropy
        ((bb84ComponentAliceZCQState σ).toJointDensityOp (bb84ComponentAliceZCQState_norm σ))
      - vonNeumannEntropy
        ((bb84ComponentAliceZCQState σ).quantumMarginalDensityOp
          (bb84ComponentAliceZCQState_norm σ))
    = vonNeumannEntropy (QKD.BB84.Engine.aliceZDephase σ) - vonNeumannEntropy σ := by
  rw [QKD.BB84.Engine.aliceZ_measuredJoint_entropy_eq_dephase σ (bb84ComponentAliceZCQState σ)
        (bb84ComponentAliceZCQState_norm σ)
        (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ)
        (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity_isPure σ)
        (Quantum.Metrics.KitaevWatrousPurification.partialTraceB_sameAncillaPurificationDensity σ)
        (bb84ComponentAliceZCQState_origin σ),
      QKD.BB84.Engine.aliceZ_quantumMarginal_entropy_eq_self σ (bb84ComponentAliceZCQState σ)
        (bb84ComponentAliceZCQState_norm σ)
        (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity σ)
        (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity_isPure σ)
        (Quantum.Metrics.KitaevWatrousPurification.partialTraceB_sameAncillaPurificationDensity σ)
        (bb84ComponentAliceZCQState_origin σ)]

/-- **(A.4) Bell-twirl monotonicity.** The Bell twirl `T = bellDephasingDensity` does not increase
    the
BB84 single-round Devetak–Winter rate: `H(Z_A|E)_{T σ} ≤ H(Z_A|E)_σ`. -/
theorem bb84ComponentAliceZRate_bellTwirl_monotone (σ : DensityOp signalDim) :
    bb84ComponentAliceZRate (QKD.BB84.Engine.bellDephasingDensity σ) ≤
      bb84ComponentAliceZRate σ := by
  unfold bb84ComponentAliceZRate
  rw [bb84ComponentAliceZRate_eq_dephasingRate (QKD.BB84.Engine.bellDephasingDensity σ),
      bb84ComponentAliceZRate_eq_dephasingRate σ]
  have hlog : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  exact div_le_div_of_nonneg_right (QKD.BB84.Engine.aliceZDephasingRate_bellTwirl_monotone σ) hlog

/-! ### Bell-twirl `(a,c,c,a)`-pairing and error-rate preservation -/

/-- Each Bell-Born weight equals the Bell-state fidelity (`Tr(|β_k⟩⟨β_k| σ) = ⟨β_k|σ|β_k⟩`). -/
lemma bb84BellBorn_eq_fidelitySq (σ : DensityOp signalDim) (k : Fin signalDim) :
    bb84BellBorn σ k =
      Quantum.Metrics.DensityOp.fidelitySq σ
        (DensityOp.fromPure (bb84BellState k) (bb84BellState_normalized k)) := by
  rw [bb84BellBorn, bb84BellPOVM, trace_ketbra_mul, Quantum.Metrics.fidelitySq_fromPure]

/-- The IID AEP lift `ofReal (nH - P) ≤ smoothMinEntropy` for Alice's bit against
its own product quantum marginal, at every positive radius.
The classical rank cap of two gives the penalty `2 log₂ 5 · n · noiseFactor n ε`.
Reference: Renner 2005, `cor:Hmincondrepclass`. -/
theorem bb84_perSigma_smoothHmin_ge_nfold_DW (σ : DensityOp signalDim) (n_copies : ℕ)
    [NeZero n_copies] [NeZero (signalDim ^ n_copies)] (ε : ℝ)
    (hε : 0 < ε) :
    ENNReal.ofReal ((n_copies : ℝ) *
        ((vonNeumannEntropy
              ((bb84ComponentAliceZCQState σ).toJointDensityOp (bb84ComponentAliceZCQState_norm σ))
            - vonNeumannEntropy
              ((bb84ComponentAliceZCQState σ).quantumMarginalDensityOp
                (bb84ComponentAliceZCQState_norm σ))) / Real.log 2) -
        finiteSizePenalty n_copies ε) ≤
      smoothMinEntropy ε (CQState.tensorPower (bb84ComponentAliceZCQState σ) n_copies)
        (SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp
            ((bb84ComponentAliceZCQState σ).quantumMarginalDensityOp
              (bb84ComponentAliceZCQState_norm σ))) n_copies) := by
  have h := iid_smoothHmin_lower_bound_bit_normalized_rankBound
    (bb84ComponentAliceZCQState σ) (bb84ComponentAliceZCQState_norm σ)
    n_copies ε hε 2 (by
      unfold CQState.classicalRank
      exact (Finset.card_filter_le _ _).trans (by simp))
  simpa only [Nat.cast_ofNat, show (2 : ℝ) + 3 = 5 by norm_num,
    mul_sub, finiteSizePenalty] using h

/-! ### The sharp *phase-only* single-round Devetak–Winter floor -/

/-- **(C1-phase, unconditional) The phase-only single-round Devetak–Winter floor at the component's
own phase rate.**  For **every** component `σ`, with **no hypotheses whatsoever**,

`(log 2 − h(θ)) / log 2 ≤ H(Z_A|E)_σ`,  where `θ = phaseFlipErrorRate_single σ`,

i.e. `1 − h(e_phase)` in bits.  This is the primitive form of the floor;
`bb84ComponentAliceZRate_ge_phaseOnly_of_good` is the corollary that substitutes the statistical
estimate `Q + 2δ` for `θ`.

Mechanism (why no hypothesis is needed).  `bb84ComponentAliceZRate_eq_dephasingRate` puts the rate
in purifier-free form `S(Δ_A ρ) − S(ρ)`, and the Bell twirl `T` only decreases it
(`bb84ComponentAliceZRate_bellTwirl_monotone`), so it suffices to bound the rate at `T σ`.  There
both entropies are *exactly* computable in the Bell weights `f = (f₀₀, f₀₁, f₁₀, f₁₁)` read as a
`2×2` table with **rows = phase index**, **columns = bit index**:

* `S(Δ_A (T σ)) = log 2 + h(e_bit)` — an **equality**
  (`QKD.BB84.Engine.aliceZDephase_bellDephasing_entropy`);
* `S(T σ) = H(f) ≤ h(e_bit) + h(e_phase)` (`QKD.BB84.Engine.bellDephasing_entropy` plus
  `shannonEntropy_2x2_subadditivity`, i.e. `I(bit;phase) ≥ 0`).

Subtracting, the bit term `h(e_bit)` **cancels exactly** — it appears with the same coefficient on
both sides — leaving `S(Δ_A (T σ)) − S(T σ) ≥ log 2 − h(e_phase)` with nothing left to constrain.

**The bound is tight.**  It saturates as `θ → 1`: at `θ = 1` the component is the pure maximally
entangled state `|β₀₁⟩` (all Bell weight on a single phase-flipped Bell vector), Eve is completely
decoupled, and the bound returns a full bit (`h(1) = 0`, so `(log 2 − h(1))/log 2 = 1`).  So the
fact that `1 − h(θ)` **rises again above `θ = 1/2`** is physically correct and not a defect of the
statement: a *deterministic* phase flip is as good for Alice and Bob as no phase flip at all,
because it is a known unitary they can undo.

⚠ What must **not** be extended past `θ = 1/2` is the *estimate substitution* `h(θ) ≤ h(Q + 2δ)`,
which needs `θ ≤ Q + 2δ ≤ 1/2` because `h` is only monotone on `[0, 1/2]`.  That — not the validity
of the formula above — is the real job of the `hbound` hypothesis in
`bb84ComponentAliceZRate_ge_phaseOnly_of_good`: it certifies monotonicity of the **upper estimate**,
never of the floor itself.

⚠ The identity `S(Δ_A ρ) = log 2 + h(e_bit)` is **false for a general `ρ`** (it can fail by `≈0.68`
nats); it holds only on the Bell-diagonal `T σ`, which is why the twirl step is essential and not
merely a convenience.

Reference: Devetak–Winter 2005 (Proc. R. Soc. A 461); Coles–Colbeck–Yu–Zwolak 2012 (PRL 108,
210405); Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem bb84ComponentAliceZRate_ge_phaseOnly (σ : DensityOp signalDim) :
    (Real.log 2 - binaryEntropy (phaseFlipErrorRate_single σ)) / Real.log 2
      ≤ bb84ComponentAliceZRate σ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- The four Bell fidelities of `σ` are its Bell-Born weights.
  have e0 : Quantum.Metrics.DensityOp.fidelitySq σ
      (DensityOp.fromPure Quantum.Basis.BellStates.bellState00
        Quantum.Basis.BellStates.bellState00_normalized) = bb84BellBorn σ 0 :=
    (bb84BellBorn_eq_fidelitySq σ 0).symm
  have e1 : Quantum.Metrics.DensityOp.fidelitySq σ
      (DensityOp.fromPure Quantum.Basis.BellStates.bellState01
        Quantum.Basis.BellStates.bellState01_normalized) = bb84BellBorn σ 1 :=
    (bb84BellBorn_eq_fidelitySq σ 1).symm
  have e2 : Quantum.Metrics.DensityOp.fidelitySq σ
      (DensityOp.fromPure Quantum.Basis.BellStates.bellState10
        Quantum.Basis.BellStates.bellState10_normalized) = bb84BellBorn σ 2 :=
    (bb84BellBorn_eq_fidelitySq σ 2).symm
  have e3 : Quantum.Metrics.DensityOp.fidelitySq σ
      (DensityOp.fromPure Quantum.Basis.BellStates.bellState11
        Quantum.Basis.BellStates.bellState11_normalized) = bb84BellBorn σ 3 :=
    (bb84BellBorn_eq_fidelitySq σ 3).symm
  -- `S(Δ_A (T σ)) = log 2 + h(e_bit)`.
  have hΔ := QKD.BB84.Engine.aliceZDephase_bellDephasing_entropy σ
  rw [e1, e3] at hΔ
  -- `S(T σ) = H(f)`.
  have hT := QKD.BB84.Engine.bellDephasing_entropy σ
  rw [e0, e1, e2, e3] at hT
  -- `H(f) ≤ h(e_bit) + h(e_phase)` (mutual information of the `(phase, bit)` table is `≥ 0`).
  have hsub := shannonEntropy_2x2_subadditivity (bb84BellBorn σ 0) (bb84BellBorn σ 1)
    (bb84BellBorn σ 2) (bb84BellBorn σ 3) (bb84BellBorn_nonneg σ 0) (bb84BellBorn_nonneg σ 1)
    (bb84BellBorn_nonneg σ 2) (bb84BellBorn_nonneg σ 3)
    (by have h := bb84BellBorn_sum σ; rwa [Fin.sum_univ_four] at h)
  rw [bb84BellBorn_phase_rate σ] at hsub
  -- The `h(e_bit)` terms cancel: no monotonicity of `h` is invoked anywhere.
  have hstep : (Real.log 2 - binaryEntropy (phaseFlipErrorRate_single σ)) / Real.log 2 ≤
      bb84ComponentAliceZRate (QKD.BB84.Engine.bellDephasingDensity σ) := by
    unfold bb84ComponentAliceZRate
    rw [bb84ComponentAliceZRate_eq_dephasingRate, hΔ, hT]
    exact (div_le_div_iff_of_pos_right hlog2).mpr (by linarith)
  exact hstep.trans (bb84ComponentAliceZRate_bellTwirl_monotone σ)

/-- **(C1-phase) The sharp phase-only single-round Devetak–Winter floor at the free phase-error
deviation.**  For a component `σ` whose **phase**-flip rate is at most `Q + δ + dev ≤ ½` — where
`δ` is the accept-test window and `dev` the free deviation between the window edge and the
phase-error rate the entropy floor is charged at (Nahar et al. 2024, Lemma 9 Eq. 44, §V.C) — the
single-round Alice-`Z` key rate obeys

`(log 2 − h(Q+δ+dev)) / log 2 ≤ H(Z_A|E)_σ`.

The Dev-variant twin of `bb84ComponentAliceZRate_ge_phaseOnly_of_good`; the `2δ` form is
the special case `dev = δ` (modulo the `δ + δ = 2 * δ` rewrite): the proof reads only the two
hypotheses, through the estimate substitution `h(e_phase) ≤ h(Q+δ+dev)` (monotonicity of `h` on
`[0, ½]`), so nothing below the hypothesis-free `bb84ComponentAliceZRate_ge_phaseOnly` moves.

Reference: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, §V.C;
Devetak–Winter 2005 (Proc. R. Soc. A 461); Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem bb84ComponentAliceZRate_ge_phaseOnly_of_goodDev (σ : DensityOp signalDim) (Q δ dev : ℝ)
    (hbound : Q + δ + dev ≤ 1 / 2)
    (hphase : phaseFlipErrorRate_single σ ≤ Q + δ + dev) :
    (Real.log 2 - binaryEntropy (Q + δ + dev)) / Real.log 2 ≤ bb84ComponentAliceZRate σ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- The ONLY use of `hbound`/`hphase`: `h(e_phase) ≤ h(Q+δ+dev)` on `[0, ½]`.
  have hmp : binaryEntropy (phaseFlipErrorRate_single σ) ≤ binaryEntropy (Q + δ + dev) :=
    binaryEntropy_le_of_le_of_le_half (phaseFlipErrorRate_single_bounds σ).1 hphase hbound
  exact le_trans ((div_le_div_iff_of_pos_right hlog2).mpr (by linarith))
    (bb84ComponentAliceZRate_ge_phaseOnly σ)

/-- **(C1-phase) The sharp phase-only single-round Devetak–Winter floor.**  For a component `σ`
whose **phase**-flip rate is at most `Q + 2δ ≤ ½`, the single-round Alice-`Z` key rate obeys

`(log 2 − h(Q+2δ)) / log 2 ≤ H(Z_A|E)_σ`,

i.e. `1 − h(e_phase)` in bits.  This is strictly sharper than a Shor–Preskill-style floor that
charges `h(e_bit)` a second time (see the mechanism below), and the bit-flip rate is not needed
as a hypothesis for this floor at all — it remains load-bearing downstream, for error-correction
decoding and completeness, but not here.

Mechanism.  `bb84ComponentAliceZRate_eq_dephasingRate` puts the rate in purifier-free form
`S(Δ_A ρ) − S(ρ)`, and the Bell twirl `T` only decreases it
(`bb84ComponentAliceZRate_bellTwirl_monotone`), so it suffices to bound the rate at `T σ`.
There the two entropies are *exactly* computable in the Bell weights
`f = (f₀₀, f₀₁, f₁₀, f₁₁)` viewed as a `2×2` table with **rows = phase index**, **columns = bit
index**:

* `S(Δ_A (T σ)) = log 2 + h(f₀₁ + f₁₁) = log 2 + h(e_bit)`
  (`QKD.BB84.Engine.aliceZDephase_bellDephasing_entropy`: the pinching averages the *phase* index
  and leaves the bit index intact);
* `S(T σ) = H(f)` (`QKD.BB84.Engine.bellDephasing_entropy`) and `H(f) ≤ h(e_bit) + h(e_phase)`
  (`shannonEntropy_2x2_subadditivity`, i.e. `I(bit;phase) ≥ 0`).

Subtracting, the bit term **cancels**: `S(Δ_A (T σ)) − S(T σ) ≥ log 2 − h(e_phase)`.  The
Shor–Preskill floor charges `h(e_bit)` a second time because it bounds `S(σ_AB)` by
`h(e_bit) + h(e_phase)` while discarding the matching `+h(e_bit)` inside `S(Δ_A σ)`.

⚠ The identity `S(Δ_A ρ) = log 2 + h(e_bit)` is **false for a general `ρ`** (it can fail by `≈0.68`
nats); it holds only on the Bell-diagonal `T σ`, which is why the twirl step is essential and not
merely a convenience.

The two hypotheses are consumed by **exactly one** step, the estimate substitution
`h(e_phase) ≤ h(Q+2δ)` (monotonicity of `h` on `[0, ½]`).  The floor itself is hypothesis-free —
see `bb84ComponentAliceZRate_ge_phaseOnly`; the proof is the case `dev = δ` of the Dev twin
`bb84ComponentAliceZRate_ge_phaseOnly_of_goodDev`, modulo the `δ + δ = 2 * δ` associativity
rewrite.

Reference: Devetak–Winter 2005 (Proc. R. Soc. A 461); Coles–Colbeck–Yu–Zwolak 2012 (PRL 108,
210405); Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem bb84ComponentAliceZRate_ge_phaseOnly_of_good (σ : DensityOp signalDim) (Q δ : ℝ)
    (hbound : Q + 2 * δ ≤ 1 / 2)
    (hphase : phaseFlipErrorRate_single σ ≤ Q + 2 * δ) :
    (Real.log 2 - binaryEntropy (Q + 2 * δ)) / Real.log 2 ≤ bb84ComponentAliceZRate σ := by
  -- Case `dev = δ` of the Dev twin; `linarith` bridges `Q + 2 * δ` ↔ `Q + δ + δ`.
  have h := bb84ComponentAliceZRate_ge_phaseOnly_of_goodDev σ Q δ δ (by linarith) (by linarith)
  rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring] at h

/-! ### Compiled sanity witness at `Q + 2δ = 1/10` -/

end QKD.BB84.Engine

end -- noncomputable section
