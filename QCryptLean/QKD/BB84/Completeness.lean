import QCryptLean.Math.Concentration.BinarySymmetricTail
import QCryptLean.Math.Combinatorics.CoordinateCounts
import QCryptLean.QKD.BB84.Model.ABRegister
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Engine.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.Engine.Budgets
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Engine.EntropyFloor.SiftedRoundFactorizationReferee
import QCryptLean.Math.Concentration.SelectedBinomialPassSum
import QCryptLean.Math.Concentration.BinomialPassSumCompleteness
import QCryptLean.Math.Concentration.BinomialPassSumBand
import QCryptLean.Math.Concentration.BinomialKLChernoff

/-!
# BB84 completeness (honest channel at QBER `Q`, no attack)

The completeness endpoint of the BB84 statement surface: without it, every security theorem is
vacuously satisfiable by the always-abort protocol. On `n` EPR pairs with Bob's half sent through
the **honest channel at QBER `Q`** with **no attack**, the full accept gate — the LOCC two-basis
parameter-estimation test AND the error-verification tag match — passes and the error-correction
decode succeeds with probability at least `1 − ε_c`.

**The honest run is noisy.** The source is `bb84HonestSource n Q`: the i.i.d. Pauli channel
`ρ ↦ (1 − 2Q)·ρ + Q·(X_B ρ X_B) + Q·(Z_B ρ Z_B)` on Bob's half of each EPR pair, whose bit error
rate and phase error rate are both exactly `Q`. The completeness statement is a genuine
two-subsample Hoeffding statement, valid for every `Q ∈ [0, 1/2]` and every `δ > 0`.

## Main definitions
- `bb84HonestPauliChannel`, `bb84HonestSourceSingle`: the honest QBER-`Q` channel on Bob's half and
  its action on one EPR pair.
- `bb84HonestSource`: the `n`-fold i.i.d. honest source.
- `bb84HonestOutcomeWeight`: the computational-basis Born weight of a round-outcome string `ω`
  under the honest source (apply the `H ⊗ H` sift on X-test rounds, then measure both halves in
  the computational basis).
- `bb84HonestKeyErrWeight`: the honest-run conditional probability that Bob's key string is `b`
  given Alice's is `a`, read off `bb84HonestOutcomeWeight`. This is the reference error model that
  the reconciliation guarantee `ECScheme.DecodesWhp` is charged against.
- `bb84CompletenessBudget`: the completeness error
  `ε_c = 2·exp(−2·m_Z·δ²) + 2·exp(−2·m_X·δ²) + εEC` — the two two-sided Hoeffding tails of the
  split-subsample test at the actual subsample sizes, plus the reconciliation-failure mass.
- `bb84CompletenessBudgetKL`: the completeness error at the relative-entropy (Chernoff) rate,
  `ε_c^KL = Σ_{±} exp(−m_Z·klBer (Q±δ) q) + Σ_{±} exp(−m_X·klBer (Q±δ) q) + εEC` — the four
  one-sided KL tails of the split-subsample test; no margin `η` is needed.

## Main statements
- `bb84_honest_closedForm`: the honest outcome weight is the i.i.d. product
  `∏_r (if ω r ∈ {0,3} then (1−Q)/2 else Q/2)` — each round independently disagrees with
  probability exactly `Q`, in BOTH bases (the honest state is `H ⊗ H`-invariant because its bit and
  phase error rates coincide).
- `bb84_completeness_of_mem_band`: on the honest source at a QBER `q` within margin `η` of the
  accept centre `Q` (`|q − Q| ≤ δ − η`), the total honest Born mass of the joint event "the full
  accept gate passes AND Bob's syndrome-decode reproduces Alice's key string" is at least
  `1 − ε_c(m_Z, m_X, η, εEC)`. Valid for every `Q ∈ [0, 1/2]` and every `δ, η > 0`.
- `bb84_completeness_of_mem_band_klBer`: the same completeness statement with the PE tails priced
  at the Bernoulli relative-entropy rate `klBer` (Chernoff bound; Cover–Thomas, *Elements of
  Information Theory*, §11.1): for `Q − δ < q < Q + δ` no margin is needed, and the budget is
  `ε_c^KL(m_Z, m_X, Q, δ, q, εEC)`, far sharper than the Hoeffding budget at small error rates.
- `two_le_bb84CompletenessBudget_of_empty`: an empty PE subsample forces the budget to at least `2`.

References: Bennett–Brassard 1984; Renner 2005 (arXiv:quant-ph/0512258v2) §6.5; Nahar, Tupkary,
Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V (robustness); CKR 2009 (arXiv:0809.3019)
main.tex:268–:401 (\emph{Main Result}: Theorem `\label{thm:main}` :291–:301, Lemma
`\label{lem:extractpart}` :319–:328). -/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84

open QKD.BB84.Engine
open QKD.BB84.Model

/-! ## The honest channel at QBER `Q`

Alice's qubit is the high index of the `4`-dimensional round register and Bob's the low one, so the
channel Alice → Bob acts on the second tensor factor. -/

/-- Pauli `X` on Bob's half of a signal pair, `1 ⊗ X`: the bit-flip error of the honest channel. -/
def bb84BobPauliX : Op signalDim := Op.tensor (1 : Op 2) Quantum.Gates.pauliX

/-- Pauli `Z` on Bob's half of a signal pair, `1 ⊗ Z`: the phase-flip error of the honest
channel. -/
def bb84BobPauliZ : Op signalDim := Op.tensor (1 : Op 2) Quantum.Gates.pauliZ

/-- Explicit `4×4` matrix form of `1 ⊗ X`: the permutation exchanging Bob's bit. -/
lemma bb84BobPauliX_eq_matrix :
    bb84BobPauliX = Matrix.of (fun i j : Fin signalDim =>
      if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
      then (1 : ℂ) else 0) := by
  -- `1 ⊗ X` from the explicit `2×2` factors, then read off the permutation pattern entrywise
  rw [bb84BobPauliX, Matrix.one_fin_two, Quantum.Gates.pauliX_eq_matrix,
    Op.tensor_fin_two_eq_matrix]
  ext i j
  -- evaluate each explicit entry: the array lookups, the index tests and the `0`/`1` products
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Fin.reduceFinMk, Matrix.cons_val, mul_one, mul_zero, Fin.reduceEq,
      and_self, and_false, false_and, or_false, or_true, ↓reduceIte]

/-- Explicit `4×4` matrix form of `1 ⊗ Z`: diagonal with sign `−1` exactly where Bob's bit is
`1`. -/
lemma bb84BobPauliZ_eq_matrix :
    bb84BobPauliZ = Matrix.of (fun i j : Fin signalDim =>
      if i = j then (if i = 0 ∨ i = 2 then (1 : ℂ) else -1) else 0) := by
  -- `1 ⊗ Z` from the explicit `2×2` factors, then read off the sign pattern entrywise
  rw [bb84BobPauliZ, Matrix.one_fin_two, Quantum.Gates.pauliZ_eq_matrix,
    Op.tensor_fin_two_eq_matrix]
  ext i j
  -- evaluate each explicit entry: the array lookups, the index tests and the `±1`/`0` products
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Fin.reduceFinMk, Matrix.cons_val, mul_one, mul_zero, mul_neg,
      neg_zero, Fin.reduceEq, or_false, or_true, ↓reduceIte]

/-- **The honest channel at QBER `Q`.** The per-round Pauli channel on Bob's half of the pair,
`ρ ↦ (1 − 2Q)·ρ + Q·(X_B ρ X_B) + Q·(Z_B ρ Z_B)`: with probability `Q` the transmitted qubit
suffers a bit flip, with probability `Q` a phase flip, and otherwise, with probability `1 − 2Q`, it
arrives intact.  The two errors are mutually exclusive: the channel has no `Y` component, so no
qubit suffers both.  It is therefore neither a depolarizing channel nor independent bit- and
phase-flip channels, whose composition at rate `Q` would put weight `Q²` on `Y`.  Its bit and phase
error rates are both `Q`, and those two rates are what the matched-basis measurements read.  The
weights leave the probability simplex, and the map stops being a channel, outside `0 ≤ Q ≤ 1/2`. -/
def bb84HonestPauliChannel (Q : ℝ) (ρ : Op signalDim) : Op signalDim :=
  ((1 - 2 * Q : ℝ) : ℂ) • ρ + ((Q : ℝ) : ℂ) • (bb84BobPauliX * ρ * bb84BobPauliX) +
    ((Q : ℝ) : ℂ) • (bb84BobPauliZ * ρ * bb84BobPauliZ)

/-- **The honest single-pair source at QBER `Q`**: one EPR pair `|Φ⁺⟩⟨Φ⁺|` with Bob's half sent
through `bb84HonestPauliChannel Q`. Bell-diagonal:
`(1 − 2Q)|Φ⁺⟩⟨Φ⁺| + Q|Ψ⁺⟩⟨Ψ⁺| + Q|Φ⁻⟩⟨Φ⁻|`. -/
def bb84HonestSourceSingle (Q : ℝ) : Op signalDim :=
  bb84HonestPauliChannel Q bb84EPRSingle.toOp

open Quantum.Basis.BellStates in
/-- **The honest single-pair source is Bell-diagonal**:
`ρ_Q = (1 − 2Q)|Φ⁺⟩⟨Φ⁺| + Q|Ψ⁺⟩⟨Ψ⁺| + Q|Φ⁻⟩⟨Φ⁻|`. The bit flip `1 ⊗ X` maps `|Φ⁺⟩ ↦ |Ψ⁺⟩`, the
phase flip `1 ⊗ Z` maps `|Φ⁺⟩ ↦ |Φ⁻⟩`, and both are Hermitian, so each error term of the channel
is the projector onto the image Bell state. -/
private lemma bb84HonestSourceSingle_eq_bellDiagonal (Q : ℝ) :
    bb84HonestSourceSingle Q =
      ((1 - 2 * Q : ℝ) : ℂ) • (bellState00 * bellState00.dag) +
        ((Q : ℝ) : ℂ) • (bellState01 * bellState01.dag) +
        ((Q : ℝ) : ℂ) • (bellState10 * bellState10.dag) := by
  have hX : bb84BobPauliX * bellState00 = bellState01 := by
    rw [bb84BobPauliX, bellState00, bellState01, op_mul_smul_ket, Op_mul_add_ket,
      Op.tensor_mulKet, Op.tensor_mulKet, one_op_mul_ket, one_op_mul_ket, Quantum.Gates.X_ket0,
      Quantum.Gates.X_ket1]
  have hZ : bb84BobPauliZ * bellState00 = bellState10 := by
    rw [bb84BobPauliZ, bellState00, bellState10, op_mul_smul_ket, Op_mul_add_ket,
      Op.tensor_mulKet, Op.tensor_mulKet, one_op_mul_ket, one_op_mul_ket, Quantum.Gates.Z_ket0,
      Quantum.Gates.Z_ket1, Ket.tensor_smul_right, Ket.sub_eq_add_neg_smul]
  -- conjugating the EPR projector by a Hermitian `A` gives the projector onto `A |Φ⁺⟩`
  have hflip : ∀ A : Op signalDim, A† = A →
      A * bb84EPRSingle.toOp * A = (A * bellState00) * (A * bellState00).dag := by
    intro A hA
    rw [← op_mul_ketbra_mul_conjTranspose, hA]
    rfl
  unfold bb84HonestSourceSingle bb84HonestPauliChannel
  rw [hflip _ (by rw [bb84BobPauliX, Op.tensor_conjTranspose, Matrix.conjTranspose_one,
      Quantum.Gates.pauliX_hermitian]),
    hflip _ (by rw [bb84BobPauliZ, Op.tensor_conjTranspose, Matrix.conjTranspose_one,
      Quantum.Gates.pauliZ_hermitian]), hX, hZ]
  rfl

open Quantum.Basis.BellStates in
/-- **Explicit matrix form of the honest single-pair source.** Bell-diagonal with weights
`(1 − 2Q, Q, Q, 0)` on `(|Φ⁺⟩, |Ψ⁺⟩, |Φ⁻⟩, |Ψ⁻⟩)`, which in the computational basis reads:
diagonal `(1−Q)/2` on the agreement indices `{0, 3}` and `Q/2` on the mismatch indices `{1, 2}`,
coherence `(1−3Q)/2` between `|00⟩` and `|11⟩`, coherence `Q/2` between `|01⟩` and `|10⟩`. -/
lemma bb84HonestSourceSingle_eq_matrix (Q : ℝ) :
    bb84HonestSourceSingle Q =
      Matrix.of (fun i j : Fin signalDim =>
        if i = j then (if i = 0 ∨ i = 3 then ((1 - Q : ℝ) : ℂ) / 2 else ((Q : ℝ) : ℂ) / 2)
        else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then ((1 - 3 * Q : ℝ) : ℂ) / 2
        else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then ((Q : ℝ) : ℂ) / 2
        else 0) := by
  -- each Bell projector entry is `(√2)⁻¹ v i · (√2)⁻¹ v j = ½ v i v j` for a real `±1/0` vector
  have hfactor : ∀ c a b : ℂ, c * a * (c * b) = (c * c) * (a * b) := by
    intros; ring
  rw [bb84HonestSourceSingle_eq_bellDiagonal]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, ket_mul_bra_apply, Ket.dag_vec, bellState00_vec,
    bellState01_vec, bellState10_vec, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀,
    Complex.conj_ofReal]
  rw [hfactor, hfactor, hfactor, inv_sqrt_two_mul_self]
  -- evaluate each explicit entry (array lookups, index tests, signs), then the scalar arithmetic
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Fin.reduceFinMk, Matrix.cons_val, map_one, map_zero, map_neg,
      mul_one, mul_zero, mul_neg, neg_neg, add_zero, Fin.reduceEq, and_self, and_false,
      false_and, or_false, or_true, ↓reduceIte] <;>
    push_cast <;> ring

open Quantum.Basis.BellStates Quantum.Gates in
/-- **The honest source is `H ⊗ H`-invariant.** Bit and phase error rates are both `Q`, so the
X-basis sift `H ⊗ H` — which exchanges `|Ψ⁺⟩ ↔ |Φ⁻⟩` and fixes `|Φ⁺⟩` — leaves the state alone.
This is why the honest run reads the SAME error statistics on the Z-test and X-test subsamples. -/
lemma hadamardPair_honestSourceSingle_conj (Q : ℝ) :
    bb84HadamardPair * bb84HonestSourceSingle Q * bb84HadamardPair
      = bb84HonestSourceSingle Q := by
  -- `ρ_Q` is Bell-diagonal, and `H ⊗ H` fixes `|Φ⁺⟩` and exchanges `|Ψ⁺⟩ ↔ |Φ⁻⟩` (equal weights)
  have hconj : ∀ ψ : Ket signalDim, bb84HadamardPair * (ψ * ψ.dag) * bb84HadamardPair =
      ((hadamard ⊗ hadamard) * ψ) * ((hadamard ⊗ hadamard) * ψ).dag := by
    intro ψ
    nth_rewrite 2 [← bb84HadamardPair_hermitian]
    exact op_mul_ketbra_mul_conjTranspose _ ψ
  rw [bb84HonestSourceSingle_eq_bellDiagonal]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hconj,
    hadamard_tensor_hadamard_mul_bellState00, hadamard_tensor_hadamard_mul_bellState01,
    hadamard_tensor_hadamard_mul_bellState10]
  exact add_right_comm _ _ _

/-- The honest single-pair source has trace one. -/
lemma bb84_honestSourceSingle_trace_one (Q : ℝ) :
    (bb84HonestSourceSingle Q).trace = 1 := by
  rw [bb84HonestSourceSingle_eq_matrix]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_four, Matrix.of_apply, Fin.ext_iff,
    Fin.isValue]
  norm_num
  ring

/-- The honest single-pair source is positive semidefinite for `0 ≤ q ≤ 1/2`. -/
theorem bb84HonestSourceSingle_posSemidef (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    (bb84HonestSourceSingle q).PosSemidef := by
  have h12 : (0 : ℝ) ≤ 1 - 2 * q := by linarith
  rw [bb84HonestSourceSingle_eq_bellDiagonal]
  refine Matrix.PosSemidef.add (Matrix.PosSemidef.add ?_ ?_) ?_
  · exact Matrix.PosSemidef.smul (ketbra_posSemidef Quantum.Basis.BellStates.bellState00)
      (RCLike.ofReal_nonneg.mpr h12)
  · exact Matrix.PosSemidef.smul (ketbra_posSemidef Quantum.Basis.BellStates.bellState01)
      (RCLike.ofReal_nonneg.mpr hq0)
  · exact Matrix.PosSemidef.smul (ketbra_posSemidef Quantum.Basis.BellStates.bellState10)
      (RCLike.ofReal_nonneg.mpr hq0)

/-- **The `n`-fold honest source at QBER `Q`**: `n` independent EPR pairs, each with Bob's half sent
through the honest channel — the tensor product of `n` copies of the single-pair operator `ρ_Q`,
with entries `∏_r ρ_Q (i_r, j_r)` on the mixed-radix tensor index. -/
def bb84HonestSource (n : ℕ) (Q : ℝ) : Op (signalDim ^ n) :=
  tensorFamily fun _ : Fin n => bb84HonestSourceSingle Q

/-! ## The honest error rates

The two statistics the PE test reads are exactly `Q`. -/

/-! ## The honest outcome weight -/

/-- The **honest computational-basis Born weight** of the round-outcome string `ω` under the
attack-free run at QBER `Q`: the honest source `bb84HonestSource n Q` conjugated by the `H ⊗ H`
sift `bb84SiftedRotation` (identity off the X-test rounds), read on its computational-basis
diagonal. This is the honest outcome probability `⟨ω| (V ρ_Q^{⊗n} V†) |ω⟩` — an explicit real
diagonal entry, no `Classical.choose`. -/
def bb84HonestOutcomeWeight (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) : ℝ :=
  (((bb84SiftedRotation n peSel xSel) * bb84HonestSource n Q *
      (bb84SiftedRotation n peSel xSel)ᴴ)
    (finFunctionFinEquiv ω) (finFunctionFinEquiv ω)).re

/-- The conditional honest law of Bob's key given Alice's key, obtained by dividing the
joint outcome mass by Alice's marginal. The marginal is positive for every Alice word, and
`bb84HonestKeyErrWeight_eq_bscWeight` identifies this law with the binary-symmetric product law.
A decoding guarantee for this law is a completeness assumption on the supplied scheme. -/
def bb84HonestKeyErrWeight (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool)
    (a b : KeyBitString n peSel) : ℝ :=
  (∑ ω : Fin n → Fin signalDim,
      if aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b
      then bb84HonestOutcomeWeight n Q peSel xSel ω else 0) /
  (∑ ω : Fin n → Fin signalDim,
      if aliceKeyString peSel ω = a
      then bb84HonestOutcomeWeight n Q peSel xSel ω else 0)

/-- The **completeness error** `ε_c = 2·exp(−2·m_Z·δ²) + 2·exp(−2·m_X·δ²) + εEC`: the two-sided
Hoeffding tails of the two PE subsamples, at the actual subsample sizes `m_Z`, `m_X`, plus the
reconciliation-failure budget `εEC`. The honest channel sits at the centre of the accept ball, so
each subsample contributes the two-sided tail `2·exp(−2·m·δ²)`; a smaller subsample gives a larger
tail, so a biased PE split that shrinks one subsample costs completeness. -/
def bb84CompletenessBudget (mZ mX : ℕ) (δ εEC : ℝ) : ℝ :=
  2 * Real.exp (-2 * (mZ : ℝ) * δ ^ 2) + 2 * Real.exp (-2 * (mX : ℝ) * δ ^ 2) + εEC

/-- **The KL-rate completeness budget** `ε_c^KL = exp(−m_Z·klBer (Q+δ) q) + exp(−m_Z·klBer (Q−δ) q)
+ exp(−m_X·klBer (Q+δ) q) + exp(−m_X·klBer (Q−δ) q) + εEC`: the four one-sided relative-entropy
tails of the split-subsample PE test at the actual subsample sizes — no margin `η` is needed,
because the honest QBER only has to lie strictly inside the accept window — plus the
reconciliation-failure mass `εEC`. By the Chernoff bound the binomial tail decays at the Bernoulli
relative-entropy rate `klBer` (Cover–Thomas, *Elements of Information Theory*, §11.1), which at
small error rates is far sharper than the Hoeffding rate `2·δ²` priced by
`bb84CompletenessBudget`. -/
def bb84CompletenessBudgetKL (mZ mX : ℕ) (Q δ q εEC : ℝ) : ℝ :=
  (Real.exp (-(mZ : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) q) +
      Real.exp (-(mZ : ℝ) * Math.Concentration.BernoulliKL.klBer (Q - δ) q)) +
    (Real.exp (-(mX : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) q) +
      Real.exp (-(mX : ℝ) * Math.Concentration.BernoulliKL.klBer (Q - δ) q)) + εEC

/-! ## Honest-run outcome weight: closed form at QBER `Q`

The honest single-pair state `ρ_Q` is `H ⊗ H`-invariant (its bit and phase error rates are both
`Q`), so every round of the honest run — X-tested or not — reads an agreement outcome `{0, 3}` with
weight `(1−Q)/2` and a mismatch outcome `{1, 2}` with weight `Q/2`. The honest outcome weight
therefore factors round-wise into `∏_r ((1−Q)/2 if ω r ∈ {0, 3} else Q/2)`: an i.i.d. sequence of
rounds, each disagreeing with probability exactly `Q`. -/

/-- **Single-round honest diagonal weight.** For either sift setting (`H ⊗ H` on an X-test round or
the identity otherwise), the computational-basis diagonal of the conjugated single-pair honest state
`rot · ρ_Q · rotᴴ` is `(1−Q)/2` on the agreement outcomes `{0, 3}` and `Q/2` on the mismatch
outcomes `{1, 2}`. On the X-test branch this uses that `H ⊗ H` fixes `ρ_Q`. -/
private lemma bb84_honest_singleRound_diag (Q : ℝ) (pe x : Bool) (k : Fin signalDim) :
    (bb84SiftedSinglePairOp pe x * bb84HonestSourceSingle Q *
        (bb84SiftedSinglePairOp pe x)ᴴ) k k
      = (if k = 0 ∨ k = 3 then ((1 - Q : ℝ) : ℂ) / 2 else ((Q : ℝ) : ℂ) / 2) := by
  have hdiag : bb84HonestSourceSingle Q k k
      = (if k = 0 ∨ k = 3 then ((1 - Q : ℝ) : ℂ) / 2 else ((Q : ℝ) : ℂ) / 2) := by
    rw [bb84HonestSourceSingle_eq_matrix, Matrix.of_apply]
    fin_cases k <;> simp [Fin.ext_iff]
  unfold bb84SiftedSinglePairOp
  by_cases h : (pe && x) = true
  · rw [if_pos h, bb84HadamardPair_hermitian,
      show bb84HadamardPair * bb84HonestSourceSingle Q * bb84HadamardPair
          = bb84HonestSourceSingle Q from hadamardPair_honestSourceSingle_conj Q]
    exact hdiag
  · rw [if_neg h, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    exact hdiag

/-- **Round factorization of the honest diagonal weight.** The computational-basis diagonal entry
of the honest conjugated `n`-fold source `V ρ_Q^{⊗n} Vᴴ` at the round-outcome string `ω` factors
round-wise into the single-round diagonal entries `rot_r · ρ_Q · rot_rᴴ`: all three operators are
tensor products over rounds, so their product is the tensor product of the single-round
products. -/
private lemma bb84_honest_diag_prod (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) :
    ((bb84SiftedRotation n peSel xSel * bb84HonestSource n Q *
        (bb84SiftedRotation n peSel xSel)ᴴ)
        (finFunctionFinEquiv ω) (finFunctionFinEquiv ω))
      = ∏ r : Fin n, ((bb84SiftedSinglePairOp (peSel r) (xSel r) * bb84HonestSourceSingle Q *
          (bb84SiftedSinglePairOp (peSel r) (xSel r))ᴴ) (ω r) (ω r)) := by
  rw [bb84SiftedRotation, bb84HonestSource, conjTranspose_tensorFamily, tensorFamily_mul,
    tensorFamily_mul, tensorFamily_apply_finFunctionFinEquiv]

/-- **Closed form of the honest outcome weight.** On the honest channel at QBER `Q` the honest
computational-basis Born weight factors round-wise into
`∏_r ((1−Q)/2 if ω r ∈ {0, 3} else Q/2)`: each round independently reads an agreement outcome
`{0, 3}` with weight `(1−Q)/2` and a mismatch outcome `{1, 2}` with weight `Q/2`, INDEPENDENT of
the sift — the honest state is `H ⊗ H`-invariant, so the X-test rounds see the same rate. The two
PE subsamples are therefore two independent `Binomial(m, Q)` samples. -/
theorem bb84_honest_closedForm (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) :
    bb84HonestOutcomeWeight n Q peSel xSel ω
      = ∏ r : Fin n, (if ω r = 0 ∨ ω r = 3 then (1 - Q) / 2 else Q / 2) := by
  unfold bb84HonestOutcomeWeight
  rw [bb84_honest_diag_prod]
  simp only [bb84_honest_singleRound_diag]
  have hcast : (∏ r : Fin n, (if ω r = 0 ∨ ω r = 3 then ((1 - Q : ℝ) : ℂ) / 2
        else ((Q : ℝ) : ℂ) / 2))
      = (((∏ r : Fin n, (if ω r = 0 ∨ ω r = 3 then (1 - Q) / 2 else Q / 2) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun r _ => ?_
    split_ifs <;> push_cast <;> ring
  rw [hcast, Complex.ofReal_re]

/-- The honest outcome weight is nonnegative (a product of nonnegative single-round weights). -/
private lemma bb84_honest_nonneg (n : ℕ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (peSel xSel : Fin n → Bool) (ω : Fin n → Fin signalDim) :
    0 ≤ bb84HonestOutcomeWeight n Q peSel xSel ω := by
  rw [bb84_honest_closedForm]
  refine Finset.prod_nonneg fun _ _ => ?_
  split_ifs <;> linarith

/-- A double-to-product identity: summing a per-round product over all round-outcome strings equals
the product over rounds of the single-round sum. -/
private lemma bb84_honest_sum_prod {d m : ℕ} (f : Fin d → ℝ) :
    (∑ ω : Fin m → Fin d, ∏ r : Fin m, f (ω r)) = ∏ _r : Fin m, ∑ k : Fin d, f k := by
  symm
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The single-round honest weight vector `k ↦ ((1−Q)/2 if k ∈ {0,3} else Q/2)` sums to `1`. -/
private lemma bb84_honest_singleRound_sum_one (Q : ℝ) :
    (∑ k : Fin signalDim, if k = 0 ∨ k = 3 then (1 - Q) / 2 else Q / 2) = 1 := by
  simp only [Fin.sum_univ_four]
  norm_num [Fin.ext_iff]
  ring

/-- Alice's single-round bit is uniform in the honest outcome law. -/
private lemma bb84_honest_singleRound_aliceBit_sum (q : ℝ) (a : Fin 2) :
    (∑ k : Fin signalDim, if aliceBit k = a then
      (if k = 0 ∨ k = 3 then (1 - q) / 2 else q / 2) else 0) = 1 / 2 := by
  fin_cases a <;> simp only [signalDim, Fin.sum_univ_four] <;>
    norm_num [aliceBit, Fin.ext_iff] <;> ring

/-- The joint single-round bit mass is half the binary-symmetric transition weight. -/
private lemma bb84_honest_singleRound_bitPair_sum (q : ℝ) (a b : Fin 2) :
    (∑ k : Fin signalDim, if aliceBit k = a ∧ bobBit k = b then
      (if k = 0 ∨ k = 3 then (1 - q) / 2 else q / 2) else 0) =
      (if a = b then 1 - q else q) / 2 := by
  fin_cases a <;> fin_cases b <;> simp only [signalDim, Fin.sum_univ_four] <;>
    norm_num [aliceBit, bobBit, Fin.ext_iff]

/-- Every Alice key has the same strictly positive honest marginal mass. -/
private lemma bb84_honest_aliceKey_sum (n : ℕ) (q : ℝ) (peSel xSel : Fin n → Bool)
    (a : KeyBitString n peSel) :
    (∑ ω, if aliceKeyString peSel ω = a then
      bb84HonestOutcomeWeight n q peSel xSel ω else 0) =
        (1 / 2 : ℝ) ^ Fintype.card {i : Fin n // peSel i = false} := by
  classical
  simp only [bb84_honest_closedForm, funext_iff, aliceKeyString]
  rw [Fintype.sum_ite_forall_subtype_prod (fun i => peSel i = false)
    (fun _ k => if k = 0 ∨ k = 3 then (1 - q) / 2 else q / 2)
    (fun _ => bb84_honest_singleRound_sum_one q) (fun i k => aliceBit k = a i)]
  simp only [bb84_honest_singleRound_aliceBit_sum, Finset.prod_const, Finset.card_univ]

/-- The honest joint key mass factors as the uniform Alice mass times the BSC transition law. -/
private lemma bb84_honest_keyPair_sum (n : ℕ) (q : ℝ) (peSel xSel : Fin n → Bool)
    (a b : KeyBitString n peSel) :
    (∑ ω, if aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b then
      bb84HonestOutcomeWeight n q peSel xSel ω else 0) =
        Math.Concentration.BinarySymmetricTail.bscWeight q a b /
          (2 : ℝ) ^ Fintype.card {i : Fin n // peSel i = false} := by
  classical
  simp only [bb84_honest_closedForm, funext_iff, aliceKeyString, bobKeyString,
    ← forall_and]
  rw [Fintype.sum_ite_forall_subtype_prod (fun i => peSel i = false)
    (fun _ k => if k = 0 ∨ k = 3 then (1 - q) / 2 else q / 2)
    (fun _ => bb84_honest_singleRound_sum_one q) (fun i k => aliceBit k = a i ∧ bobBit k = b i)]
  simp only [bb84_honest_singleRound_bitPair_sum, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Math.Concentration.BinarySymmetricTail.bscWeight]

/-- Conditioned on Alice's word, Bob's honest key has the binary-symmetric product law. -/
theorem bb84HonestKeyErrWeight_eq_bscWeight (n : ℕ) (q : ℝ) (peSel xSel : Fin n → Bool) :
    bb84HonestKeyErrWeight n q peSel xSel =
      Math.Concentration.BinarySymmetricTail.bscWeight q := by
  funext a b
  rw [bb84HonestKeyErrWeight, bb84_honest_keyPair_sum,
    bb84_honest_aliceKey_sum, _root_.one_div_pow,
    div_div_div_cancel_right₀ (by positivity), div_one]

/-- **Normalization of the honest outcome weight.** The honest Born weights sum to `1`: each round's
single-round weights sum to `(1−Q)/2 + Q/2 + Q/2 + (1−Q)/2 = 1`, and the product over rounds
is `1`. -/
private lemma bb84_honest_sum_one (n : ℕ) (Q : ℝ) (peSel xSel : Fin n → Bool) :
    ∑ ω : Fin n → Fin signalDim, bb84HonestOutcomeWeight n Q peSel xSel ω = 1 := by
  simp only [bb84_honest_closedForm]
  rw [bb84_honest_sum_prod (fun k : Fin signalDim =>
    if k = 0 ∨ k = 3 then (1 - Q) / 2 else Q / 2)]
  exact Finset.prod_eq_one fun _ _ => bb84_honest_singleRound_sum_one Q

/-! ## The PE test on the honest channel: two independent binomial subsamples -/

/-- **The selected-subsample band mass is the binomial pass mass.** For any round selector `sel`,
the honest mass at QBER `q` of the round-outcome strings whose disagreement fraction on the
`sel`-subsample lies within `δ` of `Q` equals `binomialPassSum m Q δ q` at the subsample size
`m = #{i | sel i}`: the honest rounds are i.i.d. with mismatch probability `q`, and the unselected
rounds sum out freely.

This is the honest-run instance of the sifted PE reduction
`Math.Concentration.SelectedBinomialPassSum.selectedFlagOutcomePassSum_eq_binomialPassSum`; unlike
the attacked case, the selected and unselected Born vectors coincide (the honest state is
`H ⊗ H`-invariant), so the constant-family form suffices. -/
private lemma bb84_honest_selectedBand_pass (n : ℕ) (q Q δ : ℝ) (peSel xSel sel : Fin n → Bool) :
    (∑ ω : Fin n → Fin signalDim,
        if |((Finset.univ.filter (fun i => sel i = true ∧ (ω i = 1 ∨ ω i = 2))).card : ℝ) /
              ((Finset.univ.filter (fun i => sel i = true)).card : ℝ) - Q| ≤ δ
          then bb84HonestOutcomeWeight n q peSel xSel ω else 0)
      = Math.Concentration.BinomialPassSum.binomialPassSum
          (Finset.univ.filter (fun i => sel i = true)).card Q δ q := by
  classical
  set g : Fin signalDim → ℝ := fun k => if k = 0 ∨ k = 3 then (1 - q) / 2 else q / 2 with hg_def
  have hg : (∑ j, g j) = 1 := bb84_honest_singleRound_sum_one q
  have hcard : Fintype.card {i // sel i = true}
      = (Finset.univ.filter (fun i => sel i = true)).card := Fintype.card_subtype _
  have hflag : (∑ j ∈ Finset.univ.filter (fun j : Fin signalDim => j = 1 ∨ j = 2), g j) = q := by
    rw [Finset.sum_filter]
    simp only [hg_def, Fin.sum_univ_four]
    norm_num [Fin.ext_iff]
  have key :=
      Math.Concentration.SelectedBinomialPassSum.selectedFlagOutcomePassSum_eq_binomialPassSum
      (n := n) (d := signalDim) sel (fun k => k = 1 ∨ k = 2) g g hg hg Q δ
  rw [hflag, hcard] at key
  rw [← key]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hprod : (∏ i : Fin n, (if sel i then g (ω i) else g (ω i)))
      = bb84HonestOutcomeWeight n q peSel xSel ω := by
    simp only [ite_self, hg_def]
    exact (bb84_honest_closedForm n q peSel xSel ω).symm
  rw [hprod]

/-- The Z-test disagreement count is the flag count on the selector `peSel && !xSel`. -/
private lemma bb84_zTest_count_eq (n : ℕ) (peSel xSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) :
    (Finset.univ.filter (fun i => (peSel i && !xSel i) = true ∧ (ω i = 1 ∨ ω i = 2))).card
      = bb84SiftedZTestErrorCount peSel xSel ω := by
  rw [bb84SiftedZTestErrorCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, Bool.not_eq_true',
    and_assoc]

/-- The Z-test subsample size is the size of the selector `peSel && !xSel`. -/
private lemma bb84_zTest_size_eq (n : ℕ) (peSel xSel : Fin n → Bool) :
    (Finset.univ.filter (fun i => (peSel i && !xSel i) = true)).card
      = bb84SiftedZTestSampleSize peSel xSel := by
  rw [bb84SiftedZTestSampleSize]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, Bool.not_eq_true']

/-- The X-test disagreement count is the flag count on the selector `peSel && xSel`. -/
private lemma bb84_xTest_count_eq (n : ℕ) (peSel xSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) :
    (Finset.univ.filter (fun i => (peSel i && xSel i) = true ∧ (ω i = 1 ∨ ω i = 2))).card
      = bb84SiftedXTestErrorCount peSel xSel ω := by
  rw [bb84SiftedXTestErrorCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, and_assoc]

/-- The X-test subsample size is the size of the selector `peSel && xSel`. -/
private lemma bb84_xTest_size_eq (n : ℕ) (peSel xSel : Fin n → Bool) :
    (Finset.univ.filter (fun i => (peSel i && xSel i) = true)).card
      = bb84SiftedXTestSampleSize peSel xSel := by
  rw [bb84SiftedXTestSampleSize]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true]

/-- **The honest mass failing one PE band is exactly `1 − binomialPassSum m Q δ q`.** The honest
band mass equals the binomial pass mass (`bb84_honest_selectedBand_pass`), and the band mass and
its complement add up to the total honest mass `1`, so the failure mass is the exact binomial band
failure — at every subsample size, including the empty one (both sides read the same `0/0 = 0`
junk convention). This is the exact-mass input for both the Hoeffding-priced and the KL-rate
completeness budgets. -/
private lemma bb84_honest_bandFail_exact (n : ℕ) (q Q δ : ℝ) (peSel xSel sel : Fin n → Bool) :
    (∑ ω : Fin n → Fin signalDim,
        if |((Finset.univ.filter (fun i => sel i = true ∧ (ω i = 1 ∨ ω i = 2))).card : ℝ) /
              ((Finset.univ.filter (fun i => sel i = true)).card : ℝ) - Q| ≤ δ
          then 0 else bb84HonestOutcomeWeight n q peSel xSel ω)
      = 1 - Math.Concentration.BinomialPassSum.binomialPassSum
          (Finset.univ.filter (fun i => sel i = true)).card Q δ q := by
  classical
  -- The band mass and its complement add up to the total honest mass `1`.
  have hsplit : (∑ ω : Fin n → Fin signalDim,
        if |((Finset.univ.filter (fun i => sel i = true ∧ (ω i = 1 ∨ ω i = 2))).card : ℝ) /
              ((Finset.univ.filter (fun i => sel i = true)).card : ℝ) - Q| ≤ δ
          then bb84HonestOutcomeWeight n q peSel xSel ω else 0)
      + (∑ ω : Fin n → Fin signalDim,
        if |((Finset.univ.filter (fun i => sel i = true ∧ (ω i = 1 ∨ ω i = 2))).card : ℝ) /
              ((Finset.univ.filter (fun i => sel i = true)).card : ℝ) - Q| ≤ δ
          then 0 else bb84HonestOutcomeWeight n q peSel xSel ω) = 1 := by
    rw [← Finset.sum_add_distrib, ← bb84_honest_sum_one n q peSel xSel]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  have hpass := bb84_honest_selectedBand_pass n q Q δ peSel xSel sel
  linarith [hsplit, hpass]

/-- **Honest decode-failure bound.** The total honest Born mass of round-outcome strings whose
syndrome-decode fails is at most `εEC`. Regrouping by `(Alice key, Bob key)` and using
`num = errWeight · marg` (with `marg = Alice-marginal`, `∑ marg = 1`), the reconciliation guarantee
`ec.DecodesWhp (bb84HonestKeyErrWeight …) εEC` charges each Alice-conditional failure mass
to `εEC`. -/
private lemma bb84_honest_decode_bound (n leakEC : ℕ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (peSel xSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (εEC : ℝ)
    (hDecode : ec.DecodesWhp (bb84HonestKeyErrWeight n Q peSel xSel) εEC) :
    (∑ ω : Fin n → Fin signalDim,
        if ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else bb84HonestOutcomeWeight n Q peSel xSel ω) ≤ εEC := by
  classical
  set num : KeyBitString n peSel → KeyBitString n peSel → ℝ :=
    fun a b => ∑ ω : Fin n → Fin signalDim,
      if aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b
      then bb84HonestOutcomeWeight n Q peSel xSel ω else 0 with hnum
  set den : KeyBitString n peSel → ℝ :=
    fun a => ∑ ω : Fin n → Fin signalDim,
      if aliceKeyString peSel ω = a
      then bb84HonestOutcomeWeight n Q peSel xSel ω else 0 with hden
  have hden_nonneg : ∀ a, 0 ≤ den a := by
    intro a; simp only [hden]; refine Finset.sum_nonneg fun ω _ => ?_
    split_ifs
    · exact bb84_honest_nonneg n Q hQ0 hQ1 peSel xSel ω
    · exact le_refl 0
  have hnum_nonneg : ∀ a b, 0 ≤ num a b := by
    intro a b; simp only [hnum]; refine Finset.sum_nonneg fun ω _ => ?_
    split_ifs
    · exact bb84_honest_nonneg n Q hQ0 hQ1 peSel xSel ω
    · exact le_refl 0
  have hnum_le : ∀ a b, num a b ≤ den a := by
    intro a b; simp only [hnum, hden]; refine Finset.sum_le_sum fun ω _ => ?_
    by_cases h : aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b
    · rw [if_pos h, if_pos h.1]
    · rw [if_neg h]; split_ifs
      · exact bb84_honest_nonneg n Q hQ0 hQ1 peSel xSel ω
      · exact le_refl 0
  have herrW : ∀ a b, num a b = bb84HonestKeyErrWeight n Q peSel xSel a b * den a := by
    intro a b
    by_cases hm : den a = 0
    · have hj : num a b = 0 := le_antisymm (hm ▸ hnum_le a b) (hnum_nonneg a b)
      rw [hj, hm, mul_zero]
    · have heq : bb84HonestKeyErrWeight n Q peSel xSel a b = num a b / den a := by
        simp only [hnum, hden, bb84HonestKeyErrWeight]
      rw [heq, div_mul_cancel₀ _ hm]
  have hden_sum : (∑ a, den a) = 1 := by
    simp only [hden]
    rw [Finset.sum_comm]
    have hcollapse : ∀ ω, (∑ a, if aliceKeyString peSel ω = a
        then bb84HonestOutcomeWeight n Q peSel xSel ω else 0)
        = bb84HonestOutcomeWeight n Q peSel xSel ω := fun ω => by simp [Finset.sum_ite_eq]
    rw [Finset.sum_congr rfl (fun ω _ => hcollapse ω)]
    exact bb84_honest_sum_one n Q peSel xSel
  have hregroup : (∑ ω : Fin n → Fin signalDim,
        if ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else bb84HonestOutcomeWeight n Q peSel xSel ω)
      = ∑ a, ∑ b, if ec.decode b (ec.syndrome a) = a then 0 else num a b := by
    have hpt : ∀ ω, (if ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else bb84HonestOutcomeWeight n Q peSel xSel ω)
        = ∑ a, ∑ b, if ec.decode b (ec.syndrome a) = a then 0
            else if aliceKeyString peSel ω = a ∧ bobKeyString peSel ω = b
              then bb84HonestOutcomeWeight n Q peSel xSel ω else 0 := by
      intro ω
      rw [Finset.sum_eq_single (aliceKeyString peSel ω)]
      · rw [Finset.sum_eq_single (bobKeyString peSel ω)]
        · simp
        · intro b _ hb
          have hb' : bobKeyString peSel ω ≠ b := fun h => hb h.symm
          simp [hb']
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        have ha' : aliceKeyString peSel ω ≠ a := fun h => ha h.symm
        simp [ha']
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun ω _ => hpt ω)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hnum]
    split_ifs with hC
    · simp
    · rfl
  rw [hregroup]
  have hpera : ∀ a, (∑ b, if ec.decode b (ec.syndrome a) = a then 0 else num a b)
      ≤ den a * εEC := by
    intro a
    have hstep : (∑ b, if ec.decode b (ec.syndrome a) = a then 0 else num a b)
        = den a * ∑ b, (if ec.decode b (ec.syndrome a) = a then 0
            else bb84HonestKeyErrWeight n Q peSel xSel a b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [herrW a b]
      split_ifs <;> ring
    rw [hstep]
    exact mul_le_mul_of_nonneg_left (hDecode a) (hden_nonneg a)
  calc (∑ a, ∑ b, if ec.decode b (ec.syndrome a) = a then 0 else num a b)
         ≤ ∑ a, den a * εEC := Finset.sum_le_sum fun a _ => hpera a
    _ = (∑ a, den a) * εEC := by rw [← Finset.sum_mul]
    _ = 1 * εEC := by rw [hden_sum]
    _ = εEC := one_mul εEC

/-- **A reconciliation guarantee against the honest error model has a nonnegative budget.**  The
honest conditional key-error weights are nonnegative for `0 ≤ Q ≤ 1`, so the decode-failure mass
of any Alice key string, which `hDecode` bounds by `εEC`, is nonnegative. -/
theorem nonneg_of_decodesWhp_bb84HonestKeyErrWeight {n leakEC : ℕ} {peSel xSel : Fin n → Bool}
    {ec : ECScheme n peSel leakEC} {Q εEC : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hDecode : ec.DecodesWhp (bb84HonestKeyErrWeight n Q peSel xSel) εEC) : 0 ≤ εEC := by
  classical
  refine le_trans (Finset.sum_nonneg fun b _ => ?_) (hDecode fun _ => 0)
  split_ifs
  · exact le_rfl
  · exact div_nonneg
      (Finset.sum_nonneg fun ω _ => by
        split_ifs
        · exact bb84_honest_nonneg n Q hQ0 hQ1 peSel xSel ω
        · exact le_rfl)
      (Finset.sum_nonneg fun ω _ => by
        split_ifs
        · exact bb84_honest_nonneg n Q hQ0 hQ1 peSel xSel ω
        · exact le_rfl)

/-- **An empty subsample makes the completeness budget at least two.**  It contributes the term
`2·exp(0) = 2`; the other terms are nonnegative once `εEC` is. -/
theorem two_le_bb84CompletenessBudget_of_empty (mZ mX : ℕ) (δ εEC : ℝ) (hεEC : 0 ≤ εEC)
    (h : mZ = 0 ∨ mX = 0) : 2 ≤ bb84CompletenessBudget mZ mX δ εEC := by
  unfold bb84CompletenessBudget
  rcases h with rfl | rfl
  · have := Real.exp_pos (-2 * (mX : ℝ) * δ ^ 2)
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero]
    linarith
  · have := Real.exp_pos (-2 * (mZ : ℝ) * δ ^ 2)
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero]
    linarith

/-- **An empty subsample makes the KL-rate completeness budget at least two.**  It contributes the
two terms `exp(0) + exp(0) = 2`; the other terms are nonnegative once `εEC` is. -/
theorem two_le_bb84CompletenessBudgetKL_of_empty (mZ mX : ℕ) (Q δ q εEC : ℝ) (hεEC : 0 ≤ εEC)
    (h : mZ = 0 ∨ mX = 0) : 2 ≤ bb84CompletenessBudgetKL mZ mX Q δ q εEC := by
  unfold bb84CompletenessBudgetKL
  rcases h with rfl | rfl
  · have h1 := Real.exp_pos (-(mX : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) q)
    have h2 := Real.exp_pos (-(mX : ℝ) * Math.Concentration.BernoulliKL.klBer (Q - δ) q)
    simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero] at h1 h2 ⊢
    linarith
  · have h1 := Real.exp_pos (-(mZ : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) q)
    have h2 := Real.exp_pos (-(mZ : ℝ) * Math.Concentration.BernoulliKL.klBer (Q - δ) q)
    simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero] at h1 h2 ⊢
    linarith

/-- **BB84 completeness core: exact PE-band failure tails.**

On the honest source at QBER `q` with no attack, the total honest Born mass of round-outcome strings
for which the full accept gate — the fail-closed two-basis PE test with window `|· − Q| ≤ δ` AND
the error-verification tag match at the announced seed `t` — accepts and Bob's syndrome-decode
reproduces Alice's key string is at least `1 − (eZ + eX + εEC)`, where `eZ` and `eX` are any upper
bounds on the exact binomial band-failure masses `1 − binomialPassSum m Q δ q` of the Z- and
X-test subsamples (`bb84_honest_bandFail_exact`). The reconciliation hypothesis is charged against
the honest error model at the actual QBER `q`. Both the Hoeffding-priced
(`bb84_completeness_of_mem_band`) and the KL-rate Chernoff-priced
(`bb84_completeness_of_mem_band_klBer`) completeness statements are instances, differing only in
how `eZ`, `eX` are priced. -/
private lemma bb84_completeness_of_bandFail_le (n ℓEV leakEC : ℕ)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (t : KeyHashSeed n ℓEV peSel)
    (q Q δ εEC eZ eX : ℝ)
    (hZnonempty : 0 < bb84SiftedZTestSampleSize peSel xSel)
    (hXnonempty : 0 < bb84SiftedXTestSampleSize peSel xSel)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hZ : 1 - Math.Concentration.BinomialPassSum.binomialPassSum
        (bb84SiftedZTestSampleSize peSel xSel) Q δ q ≤ eZ)
    (hX : 1 - Math.Concentration.BinomialPassSum.binomialPassSum
        (bb84SiftedXTestSampleSize peSel xSel) Q δ q ≤ eX)
    (hDecode : ec.DecodesWhp (bb84HonestKeyErrWeight n q peSel xSel) εEC) :
    1 - (eZ + eX + εEC) ≤
      ∑ ω : Fin n → Fin signalDim,
        (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) =
               aliceKeyString peSel ω
         then bb84HonestOutcomeWeight n q peSel xSel ω else 0) := by
  classical
  set w : (Fin n → Fin signalDim) → ℝ := bb84HonestOutcomeWeight n q peSel xSel with hw
  have hw_nonneg : ∀ ω, 0 ≤ w ω := fun ω => bb84_honest_nonneg n q hq0 hq1 peSel xSel ω
  -- Split the accept∧decode mass off the total: `∑ [P] w = (∑ w) − ∑ [¬P] w`.
  have hsplit : (∑ ω : Fin n → Fin signalDim,
        if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then w ω else 0)
      = (∑ ω : Fin n → Fin signalDim, w ω)
        - ∑ ω : Fin n → Fin signalDim,
            (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
                 ec.decode (bobKeyString peSel ω)
                     (ec.syndrome (aliceKeyString peSel ω)) =
                   aliceKeyString peSel ω
              then 0 else w ω) := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  rw [hsplit, bb84_honest_sum_one]
  -- The gate-or-decode failure mass is at most the PE-failure mass plus the decode-failure mass:
  -- wherever the decode succeeds the two error-verification tags are the same value, so the only
  -- way the full gate can reject is the PE test.
  have hfail_le : (∑ ω : Fin n → Fin signalDim,
        if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else w ω)
      ≤ (∑ ω : Fin n → Fin signalDim,
          if bb84SiftedLocalPETestPassed peSel xSel δ Q ω = true then 0 else w ω)
        + ∑ ω : Fin n → Fin signalDim,
          if ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
            then 0 else w ω := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    have hPEi : (0 : ℝ) ≤
        if bb84SiftedLocalPETestPassed peSel xSel δ Q ω = true then 0 else w ω := by
      split_ifs
      · exact le_refl 0
      · exact hw_nonneg ω
    have hDi : (0 : ℝ) ≤
        if ec.decode (bobKeyString peSel ω)
            (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
          then 0 else w ω := by
      split_ifs
      · exact le_refl 0
      · exact hw_nonneg ω
    by_cases hd : ec.decode (bobKeyString peSel ω)
        (ec.syndrome (aliceKeyString peSel ω)) = aliceKeyString peSel ω
    · -- The decode succeeds, so the EV tags coincide and only the PE test can reject.
      have hEV : evVerified ℓEV peSel ec t ω = true := by
        simp [evVerified, hd]
      rw [if_pos hd, add_zero]
      by_cases hp : bb84SiftedLocalPETestPassed peSel xSel δ Q ω = true
      · have ha : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true := by
          simp [bb84SiftedLocalPEAndEVPassed, hp, hEV]
        rw [if_pos ⟨ha, hd⟩, if_pos hp]
      · rw [if_neg hp]
        split_ifs
        · exact hw_nonneg ω
        · exact le_refl _
    · rw [if_neg (fun h : _ ∧ _ => hd h.2), if_neg hd]
      linarith
  -- The PE-failure mass is at most the sum of the two exact band-failure masses, hence at most
  -- `eZ + eX` by the tail hypotheses.
  have hpe : (∑ ω : Fin n → Fin signalDim,
        if bb84SiftedLocalPETestPassed peSel xSel δ Q ω = true then 0 else w ω)
      ≤ eZ + eX := by
    have hZsize := bb84_zTest_size_eq n peSel xSel
    have hXsize := bb84_xTest_size_eq n peSel xSel
    have hZexact := bb84_honest_bandFail_exact n q Q δ peSel xSel
      (fun i => peSel i && !xSel i)
    have hXexact := bb84_honest_bandFail_exact n q Q δ peSel xSel
      (fun i => peSel i && xSel i)
    simp only [bb84_zTest_count_eq, hZsize, bb84_xTest_count_eq, hXsize] at hZexact hXexact
    calc (∑ ω : Fin n → Fin signalDim,
          if bb84SiftedLocalPETestPassed peSel xSel δ Q ω = true then 0 else w ω)
        ≤ (∑ ω : Fin n → Fin signalDim,
            if |(bb84SiftedZTestErrorCount peSel xSel ω : ℝ) /
                  (bb84SiftedZTestSampleSize peSel xSel : ℝ) - Q| ≤ δ then 0 else w ω)
          + ∑ ω : Fin n → Fin signalDim,
            if |(bb84SiftedXTestErrorCount peSel xSel ω : ℝ) /
                  (bb84SiftedXTestSampleSize peSel xSel : ℝ) - Q| ≤ δ then 0 else w ω := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun ω _ => ?_
          by_cases hp : bb84SiftedLocalPETestPassed peSel xSel δ Q ω = true
          · have hband := hp
            rw [bb84SiftedLocalPETestPassed] at hband
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hband
            rw [if_pos hp, if_pos hband.1.2, if_pos hband.2.2]
            norm_num
          · rw [if_neg hp]
            have hZi : (0 : ℝ) ≤ if |(bb84SiftedZTestErrorCount peSel xSel ω : ℝ) /
                  (bb84SiftedZTestSampleSize peSel xSel : ℝ) - Q| ≤ δ then 0 else w ω := by
              split_ifs
              · exact le_refl 0
              · exact hw_nonneg ω
            have hXi : (0 : ℝ) ≤ if |(bb84SiftedXTestErrorCount peSel xSel ω : ℝ) /
                  (bb84SiftedXTestSampleSize peSel xSel : ℝ) - Q| ≤ δ then 0 else w ω := by
              split_ifs
              · exact le_refl 0
              · exact hw_nonneg ω
            -- Failing the conjunctive test means failing at least one band.
            have hone : ¬ (|(bb84SiftedZTestErrorCount peSel xSel ω : ℝ) /
                  (bb84SiftedZTestSampleSize peSel xSel : ℝ) - Q| ≤ δ ∧
              |(bb84SiftedXTestErrorCount peSel xSel ω : ℝ) /
                (bb84SiftedXTestSampleSize peSel xSel : ℝ) - Q| ≤ δ) := by
              intro ⟨h1, h2⟩
              exact hp (by
                rw [bb84SiftedLocalPETestPassed]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨⟨hZnonempty, h1⟩, ⟨hXnonempty, h2⟩⟩)
            rcases not_and_or.mp hone with h | h
            · rw [if_neg h]; linarith
            · rw [if_neg h]; linarith
      _ = (1 - Math.Concentration.BinomialPassSum.binomialPassSum
              (bb84SiftedZTestSampleSize peSel xSel) Q δ q)
          + (1 - Math.Concentration.BinomialPassSum.binomialPassSum
              (bb84SiftedXTestSampleSize peSel xSel) Q δ q) := by
          rw [hZexact, hXexact]
      _ ≤ eZ + eX := add_le_add hZ hX
  have hdec := bb84_honest_decode_bound n leakEC q hq0 hq1 peSel xSel ec εEC hDecode
  linarith [hfail_le, hpe, hdec]

/-- **BB84 completeness at a shifted honest QBER, priced at the relative-entropy (Chernoff) rate.**

On the honest source at QBER `q` with no attack, the total honest Born mass of round-outcome strings
for which the full accept gate — the fail-closed two-basis PE test with window `|· − Q| ≤ δ` AND
the error-verification tag match at the announced seed `t` — accepts and Bob's syndrome-decode
reproduces Alice's key string is at least `1 − ε_c^KL(m_Z, m_X, Q, δ, q, εEC)`, whenever the honest
QBER lies strictly inside the accept window, `Q − δ < q < Q + δ`. No margin is needed: each
subsample's PE-failure mass is the exact binomial band failure (`bb84_honest_bandFail_exact`),
dominated by the two one-sided KL-rate Chernoff exponents
(`one_sub_binomialPassSum_le_exp_klBer`; Chernoff bound, Cover–Thomas, *Elements of Information
Theory*, §11.1). The reconciliation hypothesis is charged against the honest error model at the
actual QBER `q`. -/
theorem bb84_completeness_of_mem_band_klBer (n ℓEV leakEC : ℕ)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (t : KeyHashSeed n ℓEV peSel)
    (q Q δ εEC : ℝ)
    (hZnonempty : 0 < bb84SiftedZTestSampleSize peSel xSel)
    (hXnonempty : 0 < bb84SiftedXTestSampleSize peSel xSel)
    (hq0 : 0 < q) (hq1 : q < 1) (hlo : Q - δ < q) (hhi : q < Q + δ)
    (hDecode : ec.DecodesWhp (bb84HonestKeyErrWeight n q peSel xSel) εEC) :
    1 - bb84CompletenessBudgetKL (bb84SiftedZTestSampleSize peSel xSel)
          (bb84SiftedXTestSampleSize peSel xSel) Q δ q εEC ≤
      ∑ ω : Fin n → Fin signalDim,
        (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) =
               aliceKeyString peSel ω
         then bb84HonestOutcomeWeight n q peSel xSel ω else 0) := by
  refine bb84_completeness_of_bandFail_le n ℓEV leakEC peSel xSel ec t q Q δ εEC
    (Real.exp (-(bb84SiftedZTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q + δ) q) +
      Real.exp (-(bb84SiftedZTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q - δ) q))
    (Real.exp (-(bb84SiftedXTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q + δ) q) +
      Real.exp (-(bb84SiftedXTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q - δ) q))
    hZnonempty hXnonempty hq0.le hq1.le ?_ ?_ hDecode
  · exact Math.Concentration.BinomialKLChernoff.one_sub_binomialPassSum_le_exp_klBer _ _ _ _
      hq0 hq1 hlo hhi
  · exact Math.Concentration.BinomialKLChernoff.one_sub_binomialPassSum_le_exp_klBer _ _ _ _
      hq0 hq1 hlo hhi

/-- **BB84 completeness at a shifted honest QBER** (Hoeffding-priced statement, unchanged).

On the honest source at QBER `q` with no attack, the total honest Born mass of round-outcome strings
for which the full accept gate — the fail-closed two-basis PE test with window `|· − Q| ≤ δ` AND
the error-verification tag match at the announced seed `t` — accepts and Bob's syndrome-decode
reproduces Alice's key string is at least `1 − ε_c(m_Z, m_X, η, εEC)`, whenever `q` lies in the
window shrunk by a margin `η > 0`, i.e. `|q − Q| ≤ δ − η`. The centred case `q = Q`, `η = δ` is the
completeness guarantee at the accept centre itself.

Corollary of the exact-band core `bb84_completeness_of_bandFail_le` with the two subsample tails
priced at the two-sided Hoeffding rate `2·exp(−2·m·η²)` (which is what needs the margin `η`); the
KL-rate Chernoff corollary `bb84_completeness_of_mem_band_klBer` prices the same core without a
margin. -/
theorem bb84_completeness_of_mem_band (n ℓEV leakEC : ℕ)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (t : KeyHashSeed n ℓEV peSel)
    (q Q δ η εEC : ℝ)
    (hZnonempty : 0 < bb84SiftedZTestSampleSize peSel xSel)
    (hXnonempty : 0 < bb84SiftedXTestSampleSize peSel xSel)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη : 0 < η) (hband : |q - Q| ≤ δ - η)
    (hDecode : ec.DecodesWhp (bb84HonestKeyErrWeight n q peSel xSel) εEC) :
    1 - bb84CompletenessBudget (bb84SiftedZTestSampleSize peSel xSel)
          (bb84SiftedXTestSampleSize peSel xSel) η εEC ≤
      ∑ ω : Fin n → Fin signalDim,
        (if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω = true ∧
             ec.decode (bobKeyString peSel ω)
                 (ec.syndrome (aliceKeyString peSel ω)) =
               aliceKeyString peSel ω
         then bb84HonestOutcomeWeight n q peSel xSel ω else 0) := by
  refine bb84_completeness_of_bandFail_le n ℓEV leakEC peSel xSel ec t q Q δ εEC
    (2 * Real.exp (-2 * (bb84SiftedZTestSampleSize peSel xSel : ℝ) * η ^ 2))
    (2 * Real.exp (-2 * (bb84SiftedXTestSampleSize peSel xSel : ℝ) * η ^ 2))
    hZnonempty hXnonempty hq0 hq1 ?_ ?_ hDecode
  · exact Math.Concentration.BinomialPassSum.one_sub_binomialPassSum_le_two_hoeffding_of_mem_band
      _ (ne_of_gt hZnonempty) Q δ η q hq0 hq1 hη hband
  · exact Math.Concentration.BinomialPassSum.one_sub_binomialPassSum_le_two_hoeffding_of_mem_band
      _ (ne_of_gt hXnonempty) Q δ η q hq0 hq1 hη hband

end QKD.BB84

end -- noncomputable section
