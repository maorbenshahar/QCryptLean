import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.BB84.Model.BellPostMeasurement
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.Quantum.Operators.PrincipalSubmatrix
import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination

/-!
# The genuine-LOCC two-basis sift: H⊗H on X-test rounds, fail-closed local PE

The genuine-LOCC sifting layer of BB84: a **local product** `H ⊗ H` on X-designated test rounds
(EB-honest, licensed by the source-replacement identity that an `X`-basis measurement on Alice's
half of an EPR pair is equivalent to preparing and sending an `X`-basis state), contrasted with the
Bell-rotation sift `bb84RefereeSiftedSinglePairOp`, which is not LOCC-implementable (it requires
four-Bell-state discrimination). The parameter-estimation test built on the local sift is the LOCC
two-basis test on announced local outcomes, **fail-closed** on empty subsamples (an empty Z- or
X-subsample rejects, rather than silently passing).

## Main definitions

* `bb84RefereeSiftedSinglePairOp` — the per-round Bell-rotation sift `V` on PE rounds, identity on
  key rounds; not LOCC-implementable.
* `bb84SiftedSinglePairOp`, `bb84SiftedRotation` — the per-round / `n`-round LOCC sift: `H ⊗ H` on
  `peSel ∧ xSel` rounds, identity elsewhere.
* `bb84SiftedLocalPETestPassed` — the fail-closed LOCC two-basis test (Z- and X-subsample
  disagreement fractions each within `δ` of `Q`, both subsamples required non-empty).
* `bb84SiftedLocalPEAndEVPassed` — the full accept predicate: the PE test above **and** the
  error-verification tag matches (`evVerified`).
* `bb84SiftedRotatedPreOutput`, `bb84SiftedEveConditioned`, `bb84SiftedPostMeasurementCQState` —
  the sifted pre-channel output and its outcome-conditioned CQ state.
* `bb84PostMeasurementCQSiftedLocalPEPassFilter`,
  `bb84SiftedLocalPEAcceptedPostMeasurementCQState` — the fail-closed local-PE pass filter and the
  physical accept CQ state at `bb84SiftedLocalPETestPassed`.

## Main results

* `bb84SiftedRotation_unitary`, `bb84SiftedRotation_tensor_one_unitary` — the sift is unitary.
* `bb84SiftedPostMeasurementCQState_weight_eq_one` — the post-measurement CQ blocks have total
  weight one.
* `hadamardPair_conj_bellTwirl` — `(H⊗H) G_k (H⊗H) = G_{σ k}` with `σ = ![0,3,2,1]`: the X-test sift
  relabels the bilateral Bell twirl group by `I ↦ I, X ↦ Z, Y ↦ Y, Z ↦ X`, with no sign.

Bell-twirl invariance of the accept gate defined here
(`bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant`, `evVerified_shift_invariant`,
`key_strings_shift`, `bb84SiftedLocalPETestPassed_bellTwirl_invariant`) is analysis built on the
Engine's twirl-permutation machinery (`bellKeyOutcomePerm`, `RoundKernel.lean`) and lives in
`QKD.BB84.Engine.Postselection.SiftedAcceptTwirlInvariant`, not here.

## References

Renner 2005 §5, §6.5; Nahar et al. 2024 (`arXiv:2403.11851`) §B; Shor–Preskill 2000 (the Z↔X basis
duality).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open Quantum.Basis.BellStates InfoTheory.DeFinetti MeasureTheory
open QKD.BB84.Engine
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-!
## The Bell-rotation sift: `V` on PE rounds, identity on key rounds

The sifting rotation `bb84RefereeSiftedSinglePairOp` is `V` on PE rounds, `1` on key rounds.
Reading the `V`-rotated PE rounds in the computational basis is reading them in the **Bell** basis
(Renner 2005 `arXiv:quant-ph/0512258v2`, §6.5); the key rounds are read in the genuine
computational `Z` basis. It requires four-Bell-state discrimination and so is not
LOCC-implementable; the genuine-LOCC replacement below (`bb84SiftedSinglePairOp`/
`bb84SiftedRotation`, `H ⊗ H`) uses only local single-qubit gates. -/

/-- The per-round sifting operator: the single-pair Bell rotation `V` on a PE round, the
identity on a key round.  Both are unitary, so the per-round operator is unitary. -/
def bb84RefereeSiftedSinglePairOp (peSel : Bool) : Op signalDim :=
  if peSel then bb84BellSinglePairRotation else (1 : Op signalDim)

/-- The per-round sifting operator is unitary: `Vᴴ V = 1` on PE rounds (Bell orthonormality),
`1ᴴ 1 = 1` on key rounds. -/
theorem bb84RefereeSiftedSinglePairOp_unitary (peSel : Bool) :
    (bb84RefereeSiftedSinglePairOp peSel)ᴴ * bb84RefereeSiftedSinglePairOp peSel =
        (1 : Op signalDim) := by
  cases peSel with
  | true =>
    change (bb84BellSinglePairRotation)ᴴ * bb84BellSinglePairRotation = (1 : Op signalDim)
    -- The Bell single-pair rotation is unitary (re-derived from Bell completeness).
    ext p q
    rw [Matrix.mul_apply, ← bb84BellPOVM_complete, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [bb84BellSinglePairRotation, bb84BellPOVM, Matrix.conjTranspose_apply,
      Matrix.of_apply, ket_mul_bra_apply, Ket.dag_vec, starRingEnd_apply, star_star]
  | false =>
    change (1 : Op signalDim)ᴴ * (1 : Op signalDim) = (1 : Op signalDim)
    rw [Matrix.conjTranspose_one, Matrix.one_mul]

/-! ## The H⊗H sift on X-test rounds -/

/-- The per-round LOCC sift operator: the local product `H ⊗ H` (`bb84HadamardPair`) on a round that
is both PE-designated and X-designated, the identity otherwise. Both are unitary and, crucially,
both are **local products of single-qubit gates** — LOCC-implementable (unlike the referee Bell
rotation `V`). -/
def bb84SiftedSinglePairOp (peSel xSel : Bool) : Op signalDim :=
  if peSel && xSel then bb84HadamardPair else (1 : Op signalDim)

/-- The per-round LOCC sift operator is unitary: `(H⊗H)ᴴ (H⊗H) = 1` on X-test rounds (Hermitian
involution), `1ᴴ 1 = 1` elsewhere. -/
theorem bb84SiftedSinglePairOp_unitary (peSel xSel : Bool) :
    (bb84SiftedSinglePairOp peSel xSel)ᴴ * bb84SiftedSinglePairOp peSel xSel =
      (1 : Op signalDim) := by
  unfold bb84SiftedSinglePairOp
  by_cases h : (peSel && xSel) = true
  · rw [if_pos h, bb84HadamardPair_hermitian, bb84HadamardPair_unitary]
  · rw [if_neg h, Matrix.conjTranspose_one, Matrix.one_mul]

/-- The `n`-round LOCC sift unitary: the tensor product over rounds of
`bb84SiftedSinglePairOp (peSel a) (xSel a)`, entry `(i, j) = ∏ a, (H⊗H or 1)_{i_a, j_a}` under
the mixed-radix tensor index. On X-test rounds it is the LOCAL `H ⊗ H`; on Z-test and key rounds
it is the identity. A product of local unitaries, LOCC-implementable. Explicit; no
`Classical.choose`. -/
def bb84SiftedRotation (n : ℕ) (peSel xSel : Fin n → Bool) : Op (signalDim ^ n) :=
  tensorFamily fun a => bb84SiftedSinglePairOp (peSel a) (xSel a)

/-- **`bb84SiftedRotation` is unitary**: every round factor is unitary
(`bb84SiftedSinglePairOp_unitary`), and a tensor product of isometries is an isometry
(`conjTranspose_tensorFamily_mul_self`). -/
theorem bb84SiftedRotation_unitary (n : ℕ) (peSel xSel : Fin n → Bool) :
    (bb84SiftedRotation n peSel xSel)ᴴ * bb84SiftedRotation n peSel xSel = 1 :=
  conjTranspose_tensorFamily_mul_self fun a => bb84SiftedSinglePairOp_unitary (peSel a) (xSel a)

/-- `bb84SiftedRotation peSel xSel ⊗ 1_E` is unitary, from `bb84SiftedRotation_unitary`. -/
theorem bb84SiftedRotation_tensor_one_unitary (n : ℕ) (peSel xSel : Fin n → Bool) (e : ℕ) :
    (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op e))ᴴ *
        Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op e) = 1 := by
  rw [Op.tensor_conjTranspose, Op.tensor_mul, bb84SiftedRotation_unitary,
    Matrix.conjTranspose_one, Matrix.one_mul, Op.tensor_one]

/-! ## The fail-closed LOCC two-basis parameter-estimation test -/

/-- Disagreement count on the Z-test subsample: PE rounds that are NOT X-designated with a
bit-mismatch outcome (`ω i ∈ {1, 2}`). -/
def bb84SiftedZTestErrorCount {n : ℕ} (peSel xSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) : ℕ :=
  (Finset.univ.filter (fun i =>
    peSel i = true ∧ xSel i = false ∧ (ω i = 1 ∨ ω i = 2))).card

/-- Disagreement count on the X-test subsample: PE rounds that ARE X-designated with a
(rotated-frame) bit-mismatch outcome (`ω i ∈ {1, 2}`). -/
def bb84SiftedXTestErrorCount {n : ℕ} (peSel xSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) : ℕ :=
  (Finset.univ.filter (fun i =>
    peSel i = true ∧ xSel i = true ∧ (ω i = 1 ∨ ω i = 2))).card

/-- **The fail-closed LOCC two-basis PE test.** Both subsamples must be non-empty and both
disagreement fractions must lie within `δ` of `Q`. Computed entirely from announced local
outcomes — no joint (trans-laboratory) measurement anywhere, so it is genuinely LOCC.
**Fail-closed:** an empty Z-subsample OR an empty X-subsample rejects
(`decide (0 < mZ) && decide (0 < mX) && …`), so a degenerate selector cannot silently disable a
basis's test. -/
def bb84SiftedLocalPETestPassed {n : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (ω : Fin n → Fin signalDim) : Bool :=
  let mZ : ℕ := bb84SiftedZTestSampleSize peSel xSel
  let mX : ℕ := bb84SiftedXTestSampleSize peSel xSel
  (decide (0 < mZ) &&
    decide (|(bb84SiftedZTestErrorCount peSel xSel ω : ℝ) / mZ - Q| ≤ δ)) &&
  (decide (0 < mX) &&
    decide (|(bb84SiftedXTestErrorCount peSel xSel ω : ℝ) / mX - Q| ≤ δ))

/-- **The full accept predicate: parameter estimation AND error verification.**

The protocol accepts a round-outcome string `ω` under the error-verification seed `t` iff the
fail-closed LOCC two-basis PE test passes *and* Alice's announced `ℓEV`-bit tag matches the tag of
Bob's syndrome-decoded string (`evVerified`). This is the predicate the real and ideal pass
Kraus operators are gated on.

The PE-only test `bb84SiftedLocalPETestPassed` is deliberately left as its own declaration: it is
the predicate the accept-weight functional `bb84SiftedEveVisible_tauLocalPEAcceptedWeight`, the
accept-weight dichotomy, and `bb84_completeness_of_mem_band` read. Since accepting here implies
accepting there, the EV conjunct only shrinks the accept set relative to the PE-only test.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C "Classical part"
(main.tex:906–919): error correction followed by error verification comparing hash values of
length `log(1/ε_EV)` (main.tex:917). -/
def bb84SiftedLocalPEAndEVPassed {n : ℕ} (ℓEV : ℕ) (peSel xSel : Fin n → Bool)
    {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (t : KeyHashSeed n ℓEV peSel) (ω : Fin n → Fin signalDim) : Bool :=
  bb84SiftedLocalPETestPassed peSel xSel δ Q ω && evVerified ℓEV peSel ec t ω

/-- Accepting the full gate implies accepting the PE-only test: the EV conjunct can only shrink
the accept set. Consumed wherever a bound stated at the PE-only accept event must cover the
channels' actual (PE ∧ EV) accept event. -/
theorem bb84SiftedLocalPEAndEVPassed_imp_PETestPassed {n : ℕ} (ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (t : KeyHashSeed n ℓEV peSel) (ω : Fin n → Fin signalDim)
    (h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true) :
    bb84SiftedLocalPETestPassed peSel xSel δ Q ω = true :=
  (Bool.and_eq_true _ _ |>.mp h).1

/-! ## The `H ⊗ H` relabel of the bilateral Bell twirl group

On an X-designated PE round the LOCC sift conjugates the round by `H ⊗ H`, so a bilateral Pauli
`G_k` of the twirl group `bb84BellSinglePairTwirlGroup = ![I⊗I, X⊗X, Y⊗Y, Z⊗Z]` is seen in the
rotated frame as `G_{σ k}`.  The relabel `σ` is the involution `I ↦ I, X ↦ Z, Y ↦ Y, Z ↦ X`, and it
is **sign-free**: the single-qubit `H Y H = −Y` sign is real, but it appears twice in `Y ⊗ Y` and
squares away.

The relabel is why a twirl argument may be run round-wise across the two PE bases at once: the twirl
group is closed under it (`hadamardPair_conj_bellTwirl`), and every element's key-round action is
already covered by `bb84SiftedLocalPETestPassed_bellTwirl_invariant`.  Under `σ` the off-diagonal
(bit-flipping) set `{X⊗X, Y⊗Y}` is carried to `{Y⊗Y, Z⊗Z}`, so on X-designated PE rounds the
flipping elements are `{Y, Z}`, not `{X, Y}`.
-/

/-- **The `H ⊗ H` relabel `σ` of the bilateral Bell twirl group**: `I ↦ I, X ↦ Z, Y ↦ Y, Z ↦ X`,
i.e. `![0, 3, 2, 1]`.  An involution, with no sign. -/
def bellHadSwap : Fin 4 → Fin 4 := ![0, 3, 2, 1]

/-- **`(H⊗H) G_k (H⊗H) = G_{σ k}`** with `σ = bellHadSwap = ![0,3,2,1]`: the X-test sift carries the
bilateral Bell twirl group to itself, relabelling `I⊗I ↦ I⊗I`, `X⊗X ↦ Z⊗Z`, `Y⊗Y ↦ Y⊗Y`,
`Z⊗Z ↦ X⊗X`, with **coefficient `+1` in every case** — the `H Y H = −Y` sign appears on both tensor
factors of `Y ⊗ Y` and cancels. -/
theorem hadamardPair_conj_bellTwirl (k : Fin 4) :
    bb84HadamardPair * Quantum.Symmetry.bb84BellSinglePairTwirlGroup k * bb84HadamardPair
      = Quantum.Symmetry.bb84BellSinglePairTwirlGroup (bellHadSwap k) := by
  have hneg : Op.tensor (-Quantum.Gates.pauliY) (-Quantum.Gates.pauliY)
      = Op.tensor Quantum.Gates.pauliY Quantum.Gates.pauliY := by
    ext i j
    simp [Op.tensor, Matrix.neg_apply]
  have hH : bb84HadamardPair = Op.tensor Quantum.Gates.hadamard Quantum.Gates.hadamard := rfl
  fin_cases k
  · change bb84HadamardPair * Quantum.Symmetry.bb84BellSinglePairTwirlGroup 0 * bb84HadamardPair
        = Quantum.Symmetry.bb84BellSinglePairTwirlGroup 0
    rw [show Quantum.Symmetry.bb84BellSinglePairTwirlGroup 0 = (1 : Op 4) from rfl,
      Matrix.mul_one, bb84HadamardPair_unitary]
  · change bb84HadamardPair * Quantum.Symmetry.bb84BellSinglePairTwirlGroup 1 * bb84HadamardPair
        = Quantum.Symmetry.bb84BellSinglePairTwirlGroup 3
    rw [show Quantum.Symmetry.bb84BellSinglePairTwirlGroup 1
        = Op.tensor Quantum.Gates.pauliX Quantum.Gates.pauliX from rfl,
      show Quantum.Symmetry.bb84BellSinglePairTwirlGroup 3
        = Op.tensor Quantum.Gates.pauliZ Quantum.Gates.pauliZ from rfl,
      hH, Op.tensor_mul, Op.tensor_mul, Quantum.Gates.hadamard_conj_pauliX]
  · change bb84HadamardPair * Quantum.Symmetry.bb84BellSinglePairTwirlGroup 2 * bb84HadamardPair
        = Quantum.Symmetry.bb84BellSinglePairTwirlGroup 2
    rw [show Quantum.Symmetry.bb84BellSinglePairTwirlGroup 2
        = Op.tensor Quantum.Gates.pauliY Quantum.Gates.pauliY from rfl,
      hH, Op.tensor_mul, Op.tensor_mul, Quantum.Gates.hadamard_conj_pauliY, hneg]
  · change bb84HadamardPair * Quantum.Symmetry.bb84BellSinglePairTwirlGroup 3 * bb84HadamardPair
        = Quantum.Symmetry.bb84BellSinglePairTwirlGroup 1
    rw [show Quantum.Symmetry.bb84BellSinglePairTwirlGroup 3
        = Op.tensor Quantum.Gates.pauliZ Quantum.Gates.pauliZ from rfl,
      show Quantum.Symmetry.bb84BellSinglePairTwirlGroup 1
        = Op.tensor Quantum.Gates.pauliX Quantum.Gates.pauliX from rfl,
      hH, Op.tensor_mul, Op.tensor_mul, Quantum.Gates.hadamard_conj_pauliZ]

/-! ## The post-measurement CQ stack: sifted blocks, local-PE filter, accept state

The channel's accept event is read from the sifted state: the difference of the real and ideal
channels is supported on `bb84SiftedLocalPETestPassed` evaluated after the local `H ⊗ H` sift, so
the accept-weight functional that bounds it must read that test on a
`bb84SiftedRotation`-conjugated state. -/

/-- **The pre-channel output rotated by the LOCC sift.**
`(bb84SiftedRotation peSel xSel ⊗ 1_E) · pre(ρ) · (…)†`, a genuine density operator because `pre`
is CPTP (`cptpDensityOp`) and the conjugating operator is unitary
(`bb84SiftedRotation_tensor_one_unitary`).  Reading its computational-basis outcome blocks reads
the X-test rounds in the `H ⊗ H`-rotated frame (the X-basis local outcomes) and every other round
in the computational `Z` basis.

Indexed by a bare retained-Eve dimension `eveDim` and an opaque CPTP pre-channel `pre` rather than
by an attack object: the attack instance is `eveDim := atk.eveDim`,
`pre := attackChannelLinear atk`, `hpre := attackChannelLinear_isCPTP atk`. -/
def bb84SiftedRotatedPreOutput {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (4 ^ n)) :
    DensityOp (4 ^ n * eveDim) :=
  densityOpUnitaryConj
    (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
    (bb84SiftedRotation_tensor_one_unitary n peSel xSel eveDim)
    (cptpDensityOp pre hpre ρ)

/-- **Eve's sifted-outcome-conditioned sub-density.**  The `(ωIdx, ωIdx)`-diagonal
`eveDim × eveDim` block of the sifted attack output. -/
def bb84SiftedEveConditioned {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (4 ^ n))
    (ω : Fin n → Fin signalDim) : SubDensityOp eveDim :=
  let σ := bb84SiftedRotatedPreOutput eveDim pre hpre peSel xSel ρ
  let ωIdx := bb84OutcomeIndex ω
  let embed : Fin eveDim → Fin (4 ^ n * eveDim) :=
    bb84OutcomeEveEmbedding (eveDim := eveDim) ωIdx
  { toOp := σ.toOp.submatrix embed embed
    isHermitian := densityOp_submatrix_isHermitian σ embed
    pos_semidef := densityOp_submatrix_pos_semidef σ embed
    trace_le_one := densityOp_submatrix_trace_le_one σ embed
      (bb84OutcomeEveEmbedding_injective (eveDim := eveDim) ωIdx) }

/-- The total weight of the post-measurement CQ state is one. -/
theorem bb84SiftedPostMeasurementCQState_weight_eq_one {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (4 ^ n)) :
    ∑ ω : Fin n → Fin signalDim,
      (bb84SiftedEveConditioned eveDim pre hpre peSel xSel ρ ω).trace = 1 := by
  simpa only [bb84SiftedEveConditioned, SubDensityOp.trace, trace_re_submatrix_eq_sum_diag_re]
    using bb84OutcomeEveEmbedding_diag_sum_eq_one (n := n)
      (eveDim := eveDim) (bb84SiftedRotatedPreOutput eveDim pre hpre peSel xSel ρ)

/-- The post-measurement CQ state: classical register the outcome string, quantum register
Eve's ancilla, blocks `bb84SiftedEveConditioned`.  The attack instance of the bare stack above:
`eveDim := atk.eveDim`, `pre := attackChannelLinear atk`, `hpre := attackChannelLinear_isCPTP atk`.
-/
def bb84SiftedPostMeasurementCQState {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (ρ : DensityOp (4 ^ n)) :
    CQState (Fin n → Fin signalDim) eveDim :=
  { stateMap := bb84SiftedEveConditioned eveDim pre hpre peSel xSel ρ
    weight_le_one :=
      (bb84SiftedPostMeasurementCQState_weight_eq_one eveDim pre hpre peSel xSel ρ).le }

/-- The total weight of the fail-closed local-PE pass filter is at most one. -/
private theorem bb84_SiftedLocalPEPassFilter_weight_le_one
    {n dE : ℕ} [NeZero dE]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ρ : CQState (Fin n → Fin signalDim) dE) :
    ∑ ω : Fin n → Fin signalDim,
      (if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then ρ.stateMap ω
        else (0 : SubDensityOp dE)).trace ≤ 1 := by
  apply le_trans _ ρ.weight_le_one
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with h
  · exact le_refl _
  · have hzero : SubDensityOp.trace (0 : SubDensityOp dE) = 0 := by
      unfold SubDensityOp.trace
      simp only [Matrix.trace, show (0 : SubDensityOp dE).toPosSemidefOp.toOp = 0 from rfl,
                 Matrix.diag_zero, Pi.zero_apply, Complex.zero_re, Finset.sum_const_zero]
    linarith [hzero, (ρ.stateMap ω).trace_nonneg]

/-- **The fail-closed local-PE pass filter on a CQ state.**  Keeps the block at every outcome `ω`
passing the LOCC two-basis test `bb84SiftedLocalPETestPassed` and zeros the failing blocks. -/
def bb84PostMeasurementCQSiftedLocalPEPassFilter
    {n dE : ℕ} [NeZero dE]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ρ : CQState (Fin n → Fin signalDim) dE) :
    CQState (Fin n → Fin signalDim) dE where
  stateMap := fun ω => if bb84SiftedLocalPETestPassed peSel xSel δ Q ω then ρ.stateMap ω else 0
  weight_le_one := bb84_SiftedLocalPEPassFilter_weight_le_one peSel xSel Q δ ρ

/-- **The physical accept CQ state.**  The fail-closed local-PE pass filter applied to the
post-measurement CQ state of the de Finetti `n`-round source `integralTensorPower n μ`: the physical
accept of the genuine-LOCC two-basis protocol — `H ⊗ H` on the X-test rounds, computational read-out
everywhere, both PE subsamples tested separately.

Indexed by a bare retained-Eve dimension `eveDim` and a CPTP pre-channel `pre`: the attack instance
is `eveDim := atk.eveDim`, `pre := attackChannelLinear atk`,
`hpre := attackChannelLinear_isCPTP atk`. -/
def bb84SiftedLocalPEAcceptedPostMeasurementCQState {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    (μ : InfoTheory.DeFinetti.DensityMeasure signalDim) (Q δ : ℝ) :
    CQState (Fin n → Fin signalDim) eveDim :=
  bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
    (bb84SiftedPostMeasurementCQState eveDim pre hpre peSel xSel
      (InfoTheory.DeFinetti.integralTensorPower n μ))

end QKD.BB84.Model

end
