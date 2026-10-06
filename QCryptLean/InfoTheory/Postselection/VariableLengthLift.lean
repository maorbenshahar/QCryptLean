import QCryptLean.InfoTheory.Postselection.VariableLength
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistanceBarrier

/-!
# Variable-length reference secrecy from event-wise entropy bounds

`HasVariableLengthIIDSecurityProof` records acceptance and secrecy weights for the length events.
`variableLength_postselection_security` combines an event-wise entropy floor, a leftover-hashing
bound, and a reference-distance decomposition to bound `SatisfiesVariableLengthReferenceBound`.
The Cauchy–Schwarz aggregation produces the term `√(8 * εsec)`.

The event-wise entropy, hashing, and decomposition statements are explicit hypotheses of this
reduction. It does not construct them from the protocol channels or prove a variable-length
coherent lift. The fixed-length lift is `permInvariant_postselection_security_of_referenceBound`.

References: Nahar et al., arXiv:2403.11851, `thm:maintheoremvar` (main.tex:573–590),
`eq:temptau` (1470–1472), `eq:conversePA` (1490–1492), `eq:afterconversepa` (1495–1502),
and `eq:varproofend` (1508–1516).
-/

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-- Cauchy–Schwarz for a sub-distribution: `∑ₜ pₜ √wₜ ≤ √(∑ₜ pₜ wₜ)` when `p ≥ 0`, `∑ p ≤ 1`
and `w ≥ 0`. -/
private theorem sum_mul_sqrt_le_sqrt_sum_mul {T : Type*} [Fintype T]
    (p w : T → ℝ) (hp_nonneg : ∀ t, 0 ≤ p t) (hp_sum_le : ∑ t, p t ≤ 1)
    (hw_nonneg : ∀ t, 0 ≤ w t) :
    ∑ t, p t * Real.sqrt (w t) ≤ Real.sqrt (∑ t, p t * w t) := by
  have hkey := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun t => Real.sqrt (p t)) (fun t => Real.sqrt (p t * w t))
  have hlhs : ∀ t, Real.sqrt (p t) * Real.sqrt (p t * w t) = p t * Real.sqrt (w t) := by
    intro t
    rw [← Real.sqrt_mul (hp_nonneg t), show p t * (p t * w t) = p t ^ 2 * w t by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hp_nonneg t)]
  have hsq1 : ∑ t, (Real.sqrt (p t)) ^ 2 = ∑ t, p t := by
    apply Finset.sum_congr rfl; intro t _; exact Real.sq_sqrt (hp_nonneg t)
  have hsq2 : ∑ t, (Real.sqrt (p t * w t)) ^ 2 = ∑ t, p t * w t := by
    apply Finset.sum_congr rfl; intro t _
    exact Real.sq_sqrt (mul_nonneg (hp_nonneg t) (hw_nonneg t))
  rw [hsq1, hsq2] at hkey
  calc ∑ t, p t * Real.sqrt (w t)
      = ∑ t, Real.sqrt (p t) * Real.sqrt (p t * w t) := by
        apply Finset.sum_congr rfl; intro t _; exact (hlhs t).symm
    _ ≤ Real.sqrt (∑ t, p t) * Real.sqrt (∑ t, p t * w t) := hkey
    _ ≤ 1 * Real.sqrt (∑ t, p t * w t) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        calc Real.sqrt (∑ t, p t) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hp_sum_le
          _ = 1 := Real.sqrt_one
    _ = Real.sqrt (∑ t, p t * w t) := one_mul _

/-! ## The `M`-event concavity aggregation (Nahar et al. main.tex:1470–:1516 (Appendix B's proof of
Theorem 4/variable-length: the `\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the
converse-PA step `\label{eq:conversePA}` :1490–:1492, the register-splitting step
`\label{eq:afterconversepa}` :1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516), the new
algebraic body) -/

/-- **Nahar et al. main.tex:1470–:1516 (Appendix B's proof of Theorem 4/variable-length: the
`\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the converse-PA step
`\label{eq:conversePA}` :1490–:1492, the register-splitting step `\label{eq:afterconversepa}`
:1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516) aggregation** (lines 2410–2448): the
`M`-event assembly that produces the
    `√(8 ε_sec)` secrecy term.

    From the per-event collapsed leftover-hashing bound
    `d_i ≤ ε̃ + 4√(2λ'_i − λ'_i²)` with `λ'_i = λ_i / Pr(Ω_i)`, and the accept-averaged secrecy
    budget `Σ_i λ_i ≤ ε_sec` (Nahar et al. main.tex:1470–:1516 (Appendix B's proof of Theorem
    4/variable-length: the `\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the
    converse-PA step `\label{eq:conversePA}` :1490–:1492, the register-splitting step
    `\label{eq:afterconversepa}` :1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516)), the
    accept-weighted half-sum is bounded:

      `½ Σ_i Pr(Ω_i)·d_i ≤ √(8 ε_sec) + ε̃/2`.

    The two moves are Nahar et al.'s own: drop the `−λ'_i²` (`Real.sqrt_le_sqrt`), and apply
    concavity of the
    square root (the proved stock lemma `sum_mul_sqrt_le_sqrt_sum_mul`) with
    `Pr(Ω_i)·λ'_i = λ_i`, giving `Σ_i Pr(Ω_i)√λ'_i ≤ √(Σ_i λ_i) ≤ √ε_sec`. The factor
    `√8 = 2√2` is the leftover-hashing `4`, halved by the `½ Pr(Ω_i)` weight to `2`, times the `√2`
    of `√(2λ'_i)`. The `ε̃/2` is `½ ε̃ Σ_i Pr(Ω_i) ≤ ε̃/2` since `Σ_i Pr(Ω_i) ≤ 1`. -/
theorem variableLengthPostselection_aggregate {M : ℕ}
    (pAcc lam dPrime : Fin M → ℝ) (εsec εe : ℝ)
    (hpAcc_pos : ∀ i, 0 < pAcc i)
    (hlam_nonneg : ∀ i, 0 ≤ lam i)
    (hpAcc_sum_le : ∑ i, pAcc i ≤ 1)
    (hlam_sum_le : ∑ i, lam i ≤ εsec)
    (hεe_nonneg : 0 ≤ εe)
    (hEvent : ∀ i,
      dPrime i ≤ εe + 4 * Real.sqrt (2 * (lam i / pAcc i) - (lam i / pAcc i) ^ 2)) :
    (1 / 2 : ℝ) * ∑ i, pAcc i * dPrime i ≤ Real.sqrt (8 * εsec) + εe / 2 := by
  -- λ'_i = λ_i / Pr(Ω_i) ≥ 0.
  have hlamP_nonneg : ∀ i, 0 ≤ lam i / pAcc i := fun i =>
    div_nonneg (hlam_nonneg i) (hpAcc_pos i).le
  -- Concavity aggregation with `Pr(Ω_i)·λ'_i = λ_i`.
  have hconc : ∑ i, pAcc i * Real.sqrt (lam i / pAcc i) ≤ Real.sqrt (∑ i, lam i) := by
    have h := sum_mul_sqrt_le_sqrt_sum_mul pAcc (fun i => lam i / pAcc i)
      (fun i => (hpAcc_pos i).le) hpAcc_sum_le hlamP_nonneg
    have hsum_eq : ∑ i, pAcc i * (lam i / pAcc i) = ∑ i, lam i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      exact div_mul_cancel₀ (lam i) (ne_of_gt (hpAcc_pos i))
    rwa [hsum_eq] at h
  have hA_le : ∑ i, pAcc i * Real.sqrt (lam i / pAcc i) ≤ Real.sqrt εsec :=
    hconc.trans (Real.sqrt_le_sqrt hlam_sum_le)
  -- Per-event `√`-excision: `√(2λ'_i − λ'_i²) ≤ √2·√λ'_i`.
  have hexc : ∀ i, Real.sqrt (2 * (lam i / pAcc i) - (lam i / pAcc i) ^ 2)
      ≤ Real.sqrt 2 * Real.sqrt (lam i / pAcc i) := by
    intro i
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (lam i / pAcc i)])
  -- Termwise bound of the weighted sum.
  have hterm : ∑ i, pAcc i * dPrime i
      ≤ εe * (∑ i, pAcc i) + 4 * Real.sqrt 2 * (∑ i, pAcc i * Real.sqrt (lam i / pAcc i)) := by
    have hstep : ∑ i, pAcc i * dPrime i
        ≤ ∑ i, (pAcc i * εe
            + 4 * Real.sqrt 2 * (pAcc i * Real.sqrt (lam i / pAcc i))) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hpi := (hpAcc_pos i).le
      have h1 : dPrime i ≤ εe + 4 * (Real.sqrt 2 * Real.sqrt (lam i / pAcc i)) := by
        nlinarith [hEvent i, hexc i]
      calc pAcc i * dPrime i
          ≤ pAcc i * (εe + 4 * (Real.sqrt 2 * Real.sqrt (lam i / pAcc i))) :=
            mul_le_mul_of_nonneg_left h1 hpi
        _ = pAcc i * εe + 4 * Real.sqrt 2 * (pAcc i * Real.sqrt (lam i / pAcc i)) := by ring
    refine hstep.trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  -- `2√2·√ε_sec = √(8 ε_sec)`.
  have h8 : 2 * Real.sqrt 2 * Real.sqrt εsec = Real.sqrt (8 * εsec) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8) εsec]
    have h82 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity) 2,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h82]
  -- `ε̃·Σ Pr(Ω_i) ≤ ε̃`.
  have hεeSum : εe * (∑ i, pAcc i) ≤ εe := by
    calc εe * (∑ i, pAcc i) ≤ εe * 1 := mul_le_mul_of_nonneg_left hpAcc_sum_le hεe_nonneg
      _ = εe := mul_one εe
  -- Assemble.
  have hprod : 0 ≤ Real.sqrt 2 * (Real.sqrt εsec - ∑ i, pAcc i * Real.sqrt (lam i / pAcc i)) :=
    mul_nonneg (Real.sqrt_nonneg 2) (sub_nonneg.mpr hA_le)
  nlinarith [mul_le_mul_of_nonneg_left hterm (by norm_num : (0 : ℝ) ≤ 1 / 2), hεeSum, h8, hprod]

variable {dA dB n M : ℕ} [NeZero dA] [NeZero dB] [NeZero n] [NeZero M]

/-! ## The `M`-event IID security proof (Nahar et al. `\label{eq:epsSecVar}` (main.tex:562–:566) for
IID states) -/

/-- **Nahar et al. "the `ε_sec`-secrecy condition (`\label{eq:epsSecVar}` (main.tex:562–:566)) holds
for all IID states"** (Theorem 4
    hypothesis, lines 700 / 2254): the `M`-event data extracted from that condition.

    Over the `M` **accept** events `Ω₁,…,Ω_M` (the abort branch is dropped: its real/ideal outputs
    are identical, so it contributes `0` to the main.tex:583–:585 (unlabeled; the conclusion of
    `\label{thm:maintheoremvar}` :573–:590) trace norm — Nahar et al. line 2339), it supplies
    the per-event accept probabilities `pAcc = Pr(Ωᵢ)`, the per-event secrecy weights `lam = λᵢ`
    (Nahar et al. main.tex:1470–:1516 (Appendix B's proof of Theorem 4/variable-length: the
    `\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the converse-PA step
    `\label{eq:conversePA}` :1490–:1492, the register-splitting step `\label{eq:afterconversepa}`
    :1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516)), the register-extended pre-PA
    raw-key CQ states/references, and the two
    `\label{eq:epsSecVar}` (main.tex:562–:566)-derived facts:
    - `sum_lam_le` : Nahar et al. main.tex:1470–:1516 (Appendix B's proof of Theorem
    4/variable-length: the `\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the
    converse-PA step `\label{eq:conversePA}` :1490–:1492, the register-splitting step
    `\label{eq:afterconversepa}` :1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516) `Σᵢ
    λᵢ ≤ ε_sec`, the orthogonal-support collapse of `\label{eq:epsSecVar}` (main.tex:562–:566);
    - `lam_lt_pAcc` : Nahar et al. main.tex:1470–:1516 (Appendix B's proof of Theorem
    4/variable-length: the `\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the
    converse-PA step `\label{eq:conversePA}` :1490–:1492, the register-splitting step
    `\label{eq:afterconversepa}` :1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516) WLOG
    `Pr(Ωᵢ) > λᵢ`.

    This is honest data — every field is an
    explicit functional, no `Classical.choose`. It is keyed to **`\label{eq:epsSecVar}`
    (main.tex:562–:566)** (direct IID
    `ε_sec`-secrecy), not to Theorem 3's `\label{eq:condS}` (main.tex:457–:459) and
    `\label{eq:condLHL}` (main.tex:462–:467): Theorem 4 never forms the accept-test /
    leftover-hashing split. Every field of this structure (`pAcc`, `lam`, `lam_nonneg`,
    `lam_lt_pAcc`, `pAcc_sum_le`, `sum_lam_le`, `condDim`/`condDim_neZero`, `rawKeyCQ`, `ref`) is
    read by `variableLength_postselection_security` below, unlike `HasIIDSecurityProof`
    (`Lift.lean`), whose `eq10`/`Sσhat`/`pAcc`/`condTraceDist` fields that theorem's counterpart
    does not consume. The mechanical identification of the `rawKeyCQ`/`ref` functionals with `P`'s
    induced
    quantities is the App-B protocol semantics required by this reduction; it enters
    `variableLength_postselection_security` through the named `hEventFloor` / hEventLeftover /
    hReferenceDecompose interfaces, not through hidden strengthening here. The parameter is
    `ε_sec` alone: `ε̃` appears only in the length reduction and the leftover-hashing interface, so
    it is a theorem parameter, not structure data. -/
structure HasVariableLengthIIDSecurityProof
    (P : VariableLengthPMQKDProtocol dA dB n M) (εsec : ℝ) where
  /-- Dimension of the register-extended per-event conditioning register `Eⁿ V Cⁿ C_E`. -/
  condDim : ℕ
  /-- The conditioning register is nonzero. -/
  condDim_neZero : NeZero condDim
  /-- Per accept event `Ωᵢ`, the accept probability `Pr(Ωᵢ)`. -/
  pAcc : Fin M → ℝ
  /-- Per accept event, the secrecy weight `λᵢ = ½ Pr(Ωᵢ) ‖τ^{(lᵢ)}_{|Ωᵢ} − τ^{(lᵢ),ideal}_{|Ωᵢ}‖₁`
      (Nahar et al. main.tex:1470–:1516 (Appendix B's proof of Theorem 4/variable-length: the
      `\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the converse-PA step
      `\label{eq:conversePA}` :1490–:1492, the register-splitting step `\label{eq:afterconversepa}`
      :1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516)). -/
  lam : Fin M → ℝ
  /-- Each secrecy weight is nonnegative (it is a scaled trace norm). -/
  lam_nonneg : ∀ i, 0 ≤ lam i
  /-- **Nahar et al. main.tex:1470–:1516 (Appendix B's proof of Theorem 4/variable-length: the
  `\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the converse-PA step
  `\label{eq:conversePA}` :1490–:1492, the register-splitting step `\label{eq:afterconversepa}`
  :1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516) WLOG** `Pr(Ωᵢ) > λᵢ` (Nahar et al.:
  if equality holds the main.tex:1470–:1516 (Appendix B's proof of Theorem 4/variable-length: the
  `\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the converse-PA step
  `\label{eq:conversePA}` :1490–:1492, the register-splitting step `\label{eq:afterconversepa}`
  :1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516) bound follows
      trivially). In particular `Pr(Ωᵢ) > 0`, so the per-event smoothing `λ'ᵢ = λᵢ / Pr(Ωᵢ)` is
      well-defined. -/
  lam_lt_pAcc : ∀ i, lam i < pAcc i
  /-- The accept probabilities of the disjoint accept events `Ω₁,…,Ω_M` sum to at most `1`. -/
  pAcc_sum_le : ∑ i, pAcc i ≤ 1
  /-- **Nahar et al. main.tex:1470–:1516 (Appendix B's proof of Theorem 4/variable-length: the
  `\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the converse-PA step
  `\label{eq:conversePA}` :1490–:1492, the register-splitting step `\label{eq:afterconversepa}`
  :1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516)** `Σᵢ λᵢ ≤ ε_sec`: the
  orthogonal-support collapse of the IID `ε_sec`-secrecy
      condition (`\label{eq:epsSecVar}` (main.tex:562–:566)). Since each event `Ωᵢ` yields a
      distinct key length, the conditional
      output states `τ^{(lᵢ)}_{K_A C̃_e Eⁿ|Ωᵢ}` have orthogonal supports and the abort-conditioned
      output is real/ideal-identical, so the `\label{eq:epsSecVar}` (main.tex:562–:566) trace norm
      is exactly `Σᵢ λᵢ`
      (Nahar et al. lines 2337–2354). -/
  sum_lam_le : ∑ i, lam i ≤ εsec
  /-- Per accept event, the register-extended pre-PA raw-key CQ state `(Zⁿ, Eⁿ V Cⁿ C_E)_{τ|Ωᵢ}`
      (Nahar et al. lines 2364–2386). -/
  rawKeyCQ : Fin M → CQState (Fin P.rawKeyDim) condDim
  /-- Per accept event, the reference operator for the conditional smooth min-entropy. -/
  ref : Fin M → SubDensityOp condDim

namespace HasVariableLengthIIDSecurityProof

/-- **Nahar et al. main.tex:1470–:1516 (Appendix B's proof of Theorem 4/variable-length: the
`\tau_{A^nB^nE^n}` mixture `\label{eq:temptau}` :1470–:1472, the converse-PA step
`\label{eq:conversePA}` :1490–:1492, the register-splitting step `\label{eq:afterconversepa}`
:1495–:1502, closing at `\label{eq:varproofend}` :1508–:1516) per-event smoothing weight** `λ'ᵢ = λᵢ
/ Pr(Ωᵢ)`. Well-defined and in `[0, 1)`
    by `lam_nonneg` and `lam_lt_pAcc`. Reducible so it unfolds transparently in the assembly. -/
@[reducible] def lamPrime {P : VariableLengthPMQKDProtocol dA dB n M} {εsec : ℝ}
    (h : HasVariableLengthIIDSecurityProof P εsec) (i : Fin M) : ℝ :=
  h.lam i / h.pAcc i

end HasVariableLengthIIDSecurityProof

/-! ## Theorem 4 (Postselection Theorem for Variable-length, Nahar et al. main.tex:583–:585
(unlabeled; the conclusion of `\label{thm:maintheoremvar}` :573–:590)) -/

/-- Extended event entropy floors and top-aware hashing errors give the variable-length
reference bound. Signed length penalties are completed before applying `ENNReal.ofReal`. -/
theorem variableLength_postselection_security
    (P : VariableLengthPMQKDProtocol dA dB n M)
    (μ : DensityMeasure (dA * dB))
    (εsec εe : ℝ) (hεe_pos : 0 < εe) (lt' : Fin M → ℕ)
    (hproof : HasVariableLengthIIDSecurityProof P εsec)
    (hl' : ∀ i, (lt' i : ℝ) ≤ (P.lengths i : ℝ)
      - 2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n)
      - 2 * Real.logb 2 (1 / εe))
    (dPrime : Fin M → ℝ)
    (hReferenceDecompose :
      2 * referenceSecrecy_var P lt' μ ≤ ∑ i, hproof.pAcc i * dPrime i)
    (hEventFloor : ∀ i,
      haveI := P.rawKeyDim_neZero
      haveI := hproof.condDim_neZero
      ENNReal.ofReal ((P.lengths i : ℝ) -
          2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n)) ≤
        smoothMinEntropy (Real.sqrt (2 * hproof.lamPrime i - hproof.lamPrime i ^ 2))
          (hproof.rawKeyCQ i) (hproof.ref i))
    (hEventLeftover : ∀ i,
      haveI := P.rawKeyDim_neZero
      haveI := hproof.condDim_neZero
      dPrime i ≤ 2 * hashingError (lt' i)
          (smoothMinEntropy (Real.sqrt (2 * hproof.lamPrime i - hproof.lamPrime i ^ 2))
            (hproof.rawKeyCQ i) (hproof.ref i)) +
        4 * Real.sqrt (2 * hproof.lamPrime i - hproof.lamPrime i ^ 2)) :
    SatisfiesVariableLengthReferenceBound P lt' μ εsec εe := by
  have := P.rawKeyDim_neZero
  have := hproof.condDim_neZero
  have hCollapse : ∀ i,
      dPrime i ≤ εe + 4 * Real.sqrt (2 * hproof.lamPrime i - hproof.lamPrime i ^ 2) := by
    intro i
    let k := (P.lengths i : ℝ) -
      2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n)
    have herr := (hashingError_antitone (lt' i) (hEventFloor i)).trans
      (hashingError_ofReal_le (lt' i) k)
    have hli : (lt' i : ℝ) ≤ k - 2 * Real.logb 2 (1 / εe) := hl' i
    have hlogInv : Real.logb 2 (1 / εe) = -Real.logb 2 εe := by
      rw [one_div, Real.logb_inv]
    rw [hlogInv] at hli
    have hExp : -(1 / 2 : ℝ) * (k - (lt' i : ℝ)) ≤ Real.logb 2 εe := by
      linarith only [hli]
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hExp
    rw [Real.rpow_logb (by norm_num) (by norm_num) hεe_pos] at hpow
    change Real.rpow 2 (-(1 / 2 : ℝ) * (k - (lt' i : ℝ))) ≤ εe at hpow
    linarith only [hEventLeftover i, herr, hpow]
  have hagg := variableLengthPostselection_aggregate hproof.pAcc hproof.lam dPrime εsec εe
    (fun i => lt_of_le_of_lt (hproof.lam_nonneg i) (hproof.lam_lt_pAcc i))
    hproof.lam_nonneg hproof.pAcc_sum_le hproof.sum_lam_le hεe_pos.le hCollapse
  change referenceSecrecy_var P lt' μ ≤ variableLengthCoherentSecrecy εsec εe
  unfold variableLengthCoherentSecrecy
  linarith only [hReferenceDecompose, hagg]

end InfoTheory.Postselection

end
