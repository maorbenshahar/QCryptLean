import QCryptLean.Math.Analysis.LogBounds
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP.Transport

/-!
# Symmetric-Subspace AEP — dephasing, aggregation, and the main per-round bound

Split-out (part 3 of 3) of the symmetric-subspace AEP development. Pure
relocation — no statement, signature, definition value, or proof changed. See the
re-export hub `SymmetricAEP.lean` for the full module
docstring and textbook reference.

This part carries: the dephasing trace-preservation lemmas
(`SubDensityOp.trace_eq_one_of_reindex_densityOp`, `superposition_dephased_trace_eq`),
the superposition counting/dephasing smooth-min-entropy bounds
(`superposition_card_log_le_counting`, and the mixture-counting and per-component
dephasing lower bounds), the
conditional-entropy alphabet bounds, the aggregation `√`-comparison lemmas, the
and correction-term aggregation (`aep_correction_distvN_aggregation`).
The per-round smooth min-entropy lower bound itself lives elsewhere
(`smoothMinEntropy_tensorPower_ge_classical_aep_floor`), not here.
-/

open Real Math.ClassicalEntropy InfoTheory.VonNeumannEntropy
open Quantum.Operators Quantum.Symmetry
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy.SymmetricAEP

/-- A sub-density operator whose `.toOp` is a symmetric reindex (same equiv on rows
    and columns) of the `.toOp` of a genuine `DensityOp` has real trace `1`. The
    reindex collapses by `Matrix.trace_reindex_self`, leaving the channel-output
    `DensityOp.trace_one`. This is the shared step for `ρ_n` and each `componentCQ s`
    in `superposition_dephased_trace_eq`. -/
lemma SubDensityOp.trace_eq_one_of_reindex_densityOp
    {N M : ℕ} (τ : SubDensityOp N) {e : Fin M ≃ Fin N} {D : DensityOp M}
    (h : τ.toOp = Matrix.reindex e e D.toOp) : τ.trace = 1 := by
  unfold SubDensityOp.trace
  rw [h, Matrix.trace_reindex_self, D.trace_one, Complex.one_re]

/-- **Trace-preservation bridge for the dephasing step (Renner main.tex:4019,
    `lem:smoothHinfcondlowbound`, `tr(ρ̃_dephased) = tr(ρ_n)`).**

    The total trace of the **dephased mixture**
    `ρ̃_{X^n B^n S} = Σ_s |γ_s|² (componentCQ s) ⊗ |s⟩⟨s|`
    (`dephasedMixtureCQ symWit.S imgWit.componentCQ (superpositionWeight symWit) …`)
    equals the total trace of the n-round output `ρ_n = 𝒩^{⊗n}(|Ψ⟩⟨Ψ|)`.

    This is the single place Renner uses the orthogonality of the superposition
    vectors `|Ψ^s⟩` (symWit.horthonormal, symWit.hcoeffs_norm): the dephasing of
    the coherent superposition `|Ψ⟩ = Σ_s γ_s |Ψ^s⟩` drops the cross terms
    `γ_s conj(γ_t) |Ψ^s⟩⟨Ψ^t|` (`s ≠ t`) whose images carry **zero trace** under the
    trace-preserving channel `𝒩^{⊗n}` (orthogonality kills the diagonal of the
    off-diagonal blocks), so the surviving weighted diagonal blocks
    `Σ_s |γ_s|² 𝒩^{⊗n}(|Ψ^s⟩⟨Ψ^s|)` have the same total trace as `ρ_n`. This is the
    trace-equality input consumed by Renner's Lemma A;
    the `−log₂|S|` penalty comes
    from the flag register `S`, not from any per-outcome block orthogonality. -/
theorem superposition_dephased_trace_eq
    {d dX dB n r : ℕ} [NeZero d] [NeZero dX] [NeZero dB] [NeZero (dX * dB)]
    [NeZero (d ^ n)] [NeZero (dX ^ n)] [NeZero (dB ^ n)]
    [NeZero (dX ^ r)] [NeZero (dB ^ r)] [NeZero (dX ^ n * dB ^ n)]
    {θ : NormKet d} {Ψ : NormKet (d ^ n)}
    (symWit : RestrictedSymSpaceWitness d n r θ Ψ)
    {σ_XB : DensityOp (dX * dB)}
    {ρ_n : CQState (Fin (dX ^ n)) (dB ^ n)}
    {σ_ref : SubDensityOp (dB ^ n)}
    {ε : ℝ}
    (imgWit : CQChannelImageWitness θ Ψ symWit σ_XB ρ_n σ_ref ε)
    (hweight_nonneg : ∀ s ∈ symWit.S, 0 ≤ superpositionWeight symWit s)
    (hweight_le_one : ∀ s ∈ symWit.S, superpositionWeight symWit s ≤ 1)
    (hweight_sum : ∑ s ∈ symWit.S, superpositionWeight symWit s ≤ 1) :
    ∑ p : Fin (dX ^ n) × {s // s ∈ symWit.S},
        ((InfoTheory.SmoothMinEntropy.dephasedMixtureCQ symWit.S
          imgWit.componentCQ (superpositionWeight symWit)
          hweight_nonneg hweight_le_one hweight_sum).stateMap p).trace =
      ∑ x : Fin (dX ^ n), (ρ_n.stateMap x).trace := by
  -- RHS = 1: channel trace preservation.
  have hRHS : ∑ x : Fin (dX ^ n), (ρ_n.stateMap x).trace = 1 := by
    rw [← CQState.toJointDensity_trace_eq_sum]
    exact SubDensityOp.trace_eq_one_of_reindex_densityOp _ imgWit.hρ_image
  -- LHS = ∑_{s∈S} weight s = 1.
  have hLHS : ∑ p : Fin (dX ^ n) × {s // s ∈ symWit.S},
      ((InfoTheory.SmoothMinEntropy.dephasedMixtureCQ symWit.S
        imgWit.componentCQ (superpositionWeight symWit)
        hweight_nonneg hweight_le_one hweight_sum).stateMap p).trace = 1 := by
    calc ∑ p : Fin (dX ^ n) × {s // s ∈ symWit.S},
            ((InfoTheory.SmoothMinEntropy.dephasedMixtureCQ symWit.S
              imgWit.componentCQ (superpositionWeight symWit)
              hweight_nonneg hweight_le_one hweight_sum).stateMap p).trace
        = ∑ p : Fin (dX ^ n) × {s // s ∈ symWit.S},
            superpositionWeight symWit p.2.1 *
              ((imgWit.componentCQ p.2.1).stateMap p.1).trace := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [InfoTheory.SmoothMinEntropy.dephasedMixtureCQ_stateMap,
            SubDensityOp.smul_trace]
      _ = ∑ s : {s // s ∈ symWit.S}, superpositionWeight symWit s.1 *
            ∑ x : Fin (dX ^ n), ((imgWit.componentCQ s.1).stateMap x).trace := by
          rw [Fintype.sum_prod_type_right]
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ s : {s // s ∈ symWit.S}, superpositionWeight symWit s.1 * 1 := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          congr 1
          rw [← CQState.toJointDensity_trace_eq_sum]
          exact SubDensityOp.trace_eq_one_of_reindex_densityOp _
            (imgWit.hcomponent_image s.1 s.2)
      _ = ∑ s ∈ symWit.S, superpositionWeight symWit s := by
          simp only [mul_one]
          exact Finset.sum_attach symWit.S (superpositionWeight symWit)
      _ = 1 := by
          rw [← symWit.hcoeffs_norm]
          rfl
  rw [hLHS, hRHS]

/-- **Hartley-entropy counting bound (Renner main.tex:6210, `|S| ≤ 2^{n h(r/n)}`).**

    The **base-2** Hartley entropy `log₂|S| = Real.log|S| / Real.log 2` of the
    dephasing register `S` is bounded by the counting penalty `n·binaryEntropyBits(r/n)`:

      `log₂|S| ≤ n · binaryEntropyBits(r/n)`.

    Both sides are base-2: the left-hand side matches the base-2 `smoothMinEntropy`
    (`= −log₂ λ`, MinEntropy.lean), and `binaryEntropyBits` is Renner's base-2 `h(·)`
    (`h(1/2)=1`). The `−log₂|S|` dephasing penalty of Renner's Lemma A
    is dominated by the AEP
    counting penalty `n·binaryEntropyBits(r/n)` carried throughout the downstream chain,
    ending at `aep_correction_distvN_aggregation`.  It follows directly from the cardinality
    bound symWit.hS_card (`(|S| : ℝ) ≤ 2^{n·binaryEntropyBits(r/n)}`): taking `log₂`
    of both sides (monotone, `Real.log 2 > 0`) gives
    `log₂|S| ≤ log₂(2^{n·binaryEntropyBits(r/n)}) = n·binaryEntropyBits(r/n)` exactly,
    with no ceiling slack. -/
theorem superposition_card_log_le_counting
    {d n r : ℕ} [NeZero d] [NeZero (d ^ n)]
    {θ : NormKet d} {Ψ : NormKet (d ^ n)}
    (symWit : RestrictedSymSpaceWitness d n r θ Ψ) :
    Real.log (symWit.S.card) / Real.log 2 ≤
      (n : ℝ) * binaryEntropyBits (r / (n : ℝ)) := by
  have hSne : symWit.S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have := symWit.hcoeffs_norm
    rw [hempty, Finset.sum_empty] at this
    exact zero_ne_one this
  have hScard_pos : (0 : ℝ) < (symWit.S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hSne
  have hlogScard : Real.log (symWit.S.card : ℝ) ≤
      (n : ℝ) * binaryEntropyBits (r / (n : ℝ)) * Real.log 2 := by
    have hle := Real.log_le_log hScard_pos symWit.hS_card
    rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hle
  rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact hlogScard

/-- **Conditional-entropy / `Hmax` bound (Renner main.tex:6130, 6285).**

    The per-round conditional von Neumann entropy is bounded by the classical
    alphabet log: `H(σ_XB) − H(σ_B) ≤ log dX`. Renner uses this to replace the
    dropped r-round tail's `Hmax(ρ_X)` contribution by `log|X|` (the classical
    output `ℋ_X` has dimension `dX`).

    Here `σ_XB : DensityOp (dX * dB)` is a **bare** density operator on the
    `dX·dB`-dimensional tensor system — not packaged as a CQState — so the honest
    route is plain subadditivity rather than the CQState `classicalRank` machinery:
    `cqConditionalVNEntropy σ_XB = H(σ_XB) − H(σ_B)` is the conditional entropy
    `H(A|B)`, and subadditivity `H(AB) ≤ H(A) + H(B)` gives
    `H(AB) − H(B) ≤ H(A) ≤ log (dim A) = log dX`, the dimension bound on the
    von Neumann entropy of the `A = X`-marginal (which has dimension `dX`). -/
theorem cqConditionalVNEntropy_le_log_alphabet
    {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) :
    cqConditionalVNEntropy σ_XB ≤ Real.log dX := by
  unfold cqConditionalVNEntropy
  exact InfoTheory.VonNeumannEntropy.conditionalVNEntropy_le_log_dim σ_XB

/-- **Conditional-entropy / `Hmax` bound in bits (Renner main.tex:6130, 6285).**

    The bit-valued sibling of `cqConditionalVNEntropy_le_log_alphabet`:
    `cqConditionalVNEntropyBits σ_XB ≤ log₂ dX`. This is the form consumed by the
    reshaped (bit-valued) AEP chain, where the dropped r-round tail contributes
    `r · log₂ dX` to `aep_correction_distvN_aggregation`. It follows from the
    nat-valued bound by dividing through by `Real.log 2 > 0`, using
    `Real.logb 2 dX = Real.log dX / Real.log 2`. -/
theorem cqConditionalVNEntropyBits_le_logb_alphabet
    {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) :
    cqConditionalVNEntropyBits σ_XB ≤ Real.logb 2 dX := by
  unfold cqConditionalVNEntropyBits
  rw [Real.logb, div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact cqConditionalVNEntropy_le_log_alphabet σ_XB

/-- **Entropy chord floor** `2p ≤ binaryEntropyBits p` on `[0, 1/2]`.

    The base-2 binary entropy `h(p)` is concave with `h(0)=0`, `h(1/2)=1`; hence it
    lies above its chord `2p` on `[0, 1/2]`. Used in the AEP aggregation to bound the
    dropped r-round tail `r·log dX = n·(r/n)·log dX ≤ n·(h/2)·log dX`. -/
lemma two_mul_le_binaryEntropyBits {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    2 * p ≤ binaryEntropyBits p := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbits : binaryEntropyBits p = Real.binEntropy p / Real.log 2 := by
    rw [binaryEntropyBits, binaryEntropy_eq_binEntropy]
  rw [hbits, le_div_iff₀ hlog2]
  have hconc := Real.strictConcave_binEntropy.concaveOn
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h1 : (2⁻¹ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have key := hconc.2 h0 h1 (show (0:ℝ) ≤ 1 - 2 * p by linarith)
    (show (0:ℝ) ≤ 2 * p by linarith) (show (1 - 2 * p) + 2 * p = 1 by ring)
  simp only [smul_eq_mul, Real.binEntropy_zero, Real.binEntropy_two_inv, mul_zero,
    zero_add] at key
  have hpe : 2 * p * 2⁻¹ = p := by ring
  rw [hpe] at key
  linarith [key]

/-- **Shared `√`-comparison for the AEP aggregation — base-2.** From the base-2
    square relations `s² ≤ N(l6b+1) + N²h + 2Nℓ` and `N·u² = N·h + 2(l4b+ℓ)`
    with `l4b ≥ 2`, `l6b ≤ 2.6`, one obtains `s ≤ N·u` and `h ≤ u`. This is the
    common core of `aggregation_sqrt_bound_C1` and `aggregation_sqrt_bound_C2`. -/
lemma aggregation_sqrt_comparison
    (N h s u ℓb l4b l6b : ℝ)
    (hN : 3 ≤ N) (hh1 : h ≤ 1)
    (hs0 : 0 ≤ s) (hu0 : 0 ≤ u) (hℓ : 0 ≤ ℓb)
    (hs2 : s ^ 2 ≤ N * (l6b + 1) + N ^ 2 * h + 2 * N * ℓb)
    (hnu2 : N * u ^ 2 = N * h + 2 * (l4b + ℓb))
    (hl4 : (2 : ℝ) ≤ l4b) (hl6 : l6b ≤ 2.6) :
    s ≤ N * u ∧ h ≤ u := by
  have hNpos : (0 : ℝ) < N := by linarith only [hN]
  -- `N²·u² = N·(N·u²) = N²·h + 2N·l4b + 2N·ℓb` (multiply `hnu2` by `N`).
  have hN2u2 : N ^ 2 * u ^ 2 = N ^ 2 * h + 2 * N * l4b + 2 * N * ℓb := by
    linear_combination N * hnu2
  -- `N²u² − s² ≥ 2N·l4b − N(l6b+1) = N·(2·l4b − l6b − 1) ≥ 0`, so `s² ≤ (N·u)²`,
  -- hence `s ≤ N·u`.
  have hgap : 0 ≤ N * (2 * l4b - l6b - 1) :=
    mul_nonneg hNpos.le (by linarith only [hl4, hl6])
  have hs2N2u2 : s ^ 2 ≤ (N * u) ^ 2 := by
    rw [mul_pow]; linarith only [hs2, hN2u2, hgap]
  have hsNu : s ≤ N * u :=
    (pow_le_pow_iff_left₀ hs0 (mul_nonneg hNpos.le hu0) two_ne_zero).mp hs2N2u2
  -- `h ≤ u²` (divide `N·u² = N·h + 2(l4b+ℓ) ≥ N·h` by `N`), then `h ≤ u`:
  -- for `u ≤ 1` since `u² ≤ u`, and for `1 ≤ u` since `h ≤ 1`.
  have hu2geh : h ≤ u ^ 2 :=
    le_of_mul_le_mul_left (by rw [hnu2]; linarith only [hl4, hℓ]) hNpos
  have hhu : h ≤ u := by
    rcases le_total u 1 with hu1 | hu1
    · exact hu2geh.trans (pow_le_of_le_one hu0 hu1 two_ne_zero)
    · exact hh1.trans hu1
  exact ⟨hsNu, hhu⟩

/-- **Pooled `√`-inequality, constant part (C1) — base-2.** With `N = n`,
    `h = binaryEntropyBits(r/n)` (bits), `s = (n−r)·√((L₂+1)/(n−r))`, `u = √T`, this is
    the `A⁰` part (constant in `A = log₂ dX`) of the **base-2** aggregation. The square
    relations are now base-2: the smoothing content of `s²` and `N·u²` is measured in
    bits (`l4b = log₂ 4 = 2`, `l6b = log₂ 6`, `ℓb = log₂(1/ε)`), and there is no
    `Real.log 2` factor on the `N²·h` term (`h` is already in bits). The conclusion
    `4·s + N·h ≤ 5·N·u` carries the assembled constant `5` on the right: the `s`-block
    contributes `4` (the `+4` per-block prefactor `δ' = (2·log₂ dX + 4)·noiseFactor`)
    and the `N·h` term is absorbed by the remaining `N·u` via `h ≤ u`. -/
lemma aggregation_sqrt_bound_C1
    (N h s u ℓb l4b l6b : ℝ)
    (hN : 3 ≤ N) (_hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs0 : 0 ≤ s) (hu0 : 0 ≤ u) (hℓ : 0 ≤ ℓb)
    (hs2 : s ^ 2 ≤ N * (l6b + 1) + N ^ 2 * h + 2 * N * ℓb)
    (hnu2 : N * u ^ 2 = N * h + 2 * (l4b + ℓb))
    (hl4 : (2 : ℝ) ≤ l4b) (hl6 : l6b ≤ 2.6) :
    4 * s + N * h ≤ 5 * N * u := by
  obtain ⟨hsNu, hhu⟩ :=
    aggregation_sqrt_comparison N h s u ℓb l4b l6b hN hh1 hs0 hu0 hℓ hs2 hnu2 hl4 hl6
  -- `N·h ≤ N·u` since `h ≤ u`; combine with `s ≤ N·u`.
  have hNhu : N * h ≤ N * u := mul_le_mul_of_nonneg_left hhu (by linarith only [hN])
  linarith only [hsNu, hNhu]

/-- **Pooled `√`-inequality, slope part (C2) — base-2.** The `A¹` coefficient
    inequality `2s + r ≤ (5/2)·N·u`, using the entropy floor `2r ≤ N·h`, with the same
    **base-2** square relations as `aggregation_sqrt_bound_C1`. -/
lemma aggregation_sqrt_bound_C2
    (N h s u r ℓb l4b l6b : ℝ)
    (hN : 3 ≤ N) (_hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs0 : 0 ≤ s) (hu0 : 0 ≤ u) (hℓ : 0 ≤ ℓb) (_hr0 : 0 ≤ r) (hr2 : 2 * r ≤ N * h)
    (hs2 : s ^ 2 ≤ N * (l6b + 1) + N ^ 2 * h + 2 * N * ℓb)
    (hnu2 : N * u ^ 2 = N * h + 2 * (l4b + ℓb))
    (hl4 : (2 : ℝ) ≤ l4b) (hl6 : l6b ≤ 2.6) :
    2 * s + r ≤ 5 / 2 * N * u := by
  obtain ⟨hsNu, hhu⟩ :=
    aggregation_sqrt_comparison N h s u ℓb l4b l6b hN hh1 hs0 hu0 hℓ hs2 hnu2 hl4 hl6
  -- `h ≤ u`, so `2r ≤ N·h ≤ N·u`, i.e. `r ≤ N·u/2`.
  have hrNu : 2 * r ≤ N * u :=
    hr2.trans (mul_le_mul_of_nonneg_left hhu (by linarith only [hN]))
  linarith only [hsNu, hrNu]

/-- **Step 6 — correction-term aggregation (Renner main.tex:6289–6324).**

    Pure-arithmetic bound assembling the symmetric-AEP total correction `n·δ` from
    its three contributions, as in Renner's eqs `Hinffb`–end (main.tex:6291–6324),
    multiplied through by `n`:
    - the product-block correction `(n−r)·δ'` (eq `Hinfreps`, main.tex:6280–6287),
      with `δ' = aep_correction_perComponent dX (n−r) ε'` the library-faithful
      per-block correction `(2·log dX + 4)·√((log(1/ε')+1)/(n−r))`;
    - the counting penalty `n·h(r/n)` (eq `Hinfmins`, main.tex:6212–6218);
    - the dropped r-round tail `r·Hmax(ρ_X) ≤ r·log dX` (eq `Hinfreps`, main.tex:6285).

      `(n−r)·δ' + n·h(r/n) + r·log dX ≤ n · aep_correction_distvN dX n r ε`,

    where `(S_card : ℝ) ≤ 2^{n·h(r/n)}`.

    The `√(n−r)` redistribution is **intrinsic** to `(n−r)·δ'`: since
    `δ' = (2·log₂ dX+4)·√((log₂(1/ε')+1)/(n−r))`, the product is
    `(n−r)·δ' = (2·log₂ dX+4)·√((n−r)·(log₂(1/ε')+1))`, scaling as `√(n−r)·√(log₂(1/ε'))`.
    With `log₂(1/ε') ≤ log₂(2/ε) + log₂ 6 + n·h(r/n)` (eq `epspbound`, main.tex:6220),
    the `n·h(r/n)` lands **inside** the square root and merges with `h(r/n)`
    (eqs main.tex:6299–6315), using `2r/n ≤ h(r/n)`, `h(r/n) ≤ √(h(r/n))`, and
    `c ≤ √c` for `c ≤ 1` (main.tex:6306–6323).

    **Units.** Every term is **base-2** (bits), matching the reshaped chain: the tail
    `r·log₂ dX` (from `cqConditionalVNEntropyBits σ_XB ≤ log₂ dX`), the per-block
    correction `δ' = aep_correction_perComponent` (base-2, `+4` prefactor), and the
    total correction `aep_correction_distvN` (base-2). The assembly reduces, after the
    `s²`/`N·u²` base-2 square relations, to the two pooled `√`-inequalities
    `aggregation_sqrt_bound_C1` (constant in `log₂ dX`, s-coefficient `4`) and
    `aggregation_sqrt_bound_C2` (slope), with base-2 numeric constants
    `log₂ 4 = 2`, `log₂ 6 ≤ 2.6` (the looser `2.6 ≥ log₂ 6 ≈ 2.585` is the
    provable bound `6^5 ≤ 2^13`, with ample margin for the `2·l4b ≥ l6b + 1`
    closing inequality `4 ≥ 2.6 + 1`).

    The assembled additive constant on the right is `+5`: the per-block correction
    `δ'` contributes `+4` (library-faithful prefactor), and the `c ≤ √c`, `h ≤ √h`
    absorptions contribute the remaining `+1`, matching the s-coefficient `5` of
    `aggregation_sqrt_bound_C1`'s conclusion `4·s + N·h ≤ 5·N·u`.

    The hypothesis `3 ≤ n` is the honest floor for the truth of this inequality:
    at `n = 2` the prefactor jump `(2·Hmax+4) → (5/2·Hmax+5)` and the
    `c ≤ √c`, `2r/n ≤ h(r/n)` absorptions Renner uses are not yet dominant, so the
    bound fails there; it holds for every `n ≥ 3`. This floor is far below the
    BB84 finite-size regime and costs nothing downstream. -/
theorem aep_correction_distvN_aggregation
    (dX n r : ℕ) (S_card : ℕ) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1) (hn_ge_three : 3 ≤ n) (hr_le : r ≤ n / 2)
    (hdX : 1 ≤ dX)
    (hS_card : (S_card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits (r / (n : ℝ)))) :
    ((n - r : ℕ) : ℝ) *
        aep_correction_perComponent dX (n - r) (ε ^ 2 / (6 * S_card)) +
      (n : ℝ) * binaryEntropyBits (r / (n : ℝ)) +
      (r : ℝ) * Real.logb 2 dX ≤
    (n : ℝ) * aep_correction_distvN dX n r ε := by
  -- Abbreviations (all base-2 / bits).
  set A : ℝ := Real.logb 2 dX with hA
  set h : ℝ := binaryEntropyBits (r / (n : ℝ)) with hh
  set ℓ : ℝ := Real.logb 2 ε⁻¹ with hℓdef
  set N : ℝ := (n : ℝ) with hN
  -- Basic numeric / nonnegativity facts.
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn_ge_three
  have hN3 : (3 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hn_ge_three
  have hr_le_n : r ≤ n := le_trans hr_le (Nat.div_le_self n 2)
  have hnr_real : ((n - r : ℕ) : ℝ) = N - (r : ℝ) := by rw [hN, Nat.cast_sub hr_le_n]
  have hA0 : 0 ≤ A := by
    rw [hA]; exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hdX)
  -- `2r ≤ n` (from `r ≤ n/2` in ℕ), hence `r/n ≤ 1/2`, so the entropy chord floor
  -- `2·(r/n) ≤ h` gives `2r ≤ N·h`.
  have h2r_le_n : 2 * (r : ℝ) ≤ N := by
    rw [hN]
    have : 2 * r ≤ n := le_trans (Nat.mul_le_mul_left 2 hr_le) (Nat.mul_div_le n 2)
    exact_mod_cast this
  have hrn_le_half : (r : ℝ) / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hNpos (by norm_num : (0:ℝ) < 2)]; linarith only [h2r_le_n]
  have hrn_nonneg : 0 ≤ (r : ℝ) / N := div_nonneg (Nat.cast_nonneg r) hNpos.le
  have hchord : 2 * ((r : ℝ) / N) ≤ h := by
    rw [hh]; exact two_mul_le_binaryEntropyBits hrn_nonneg hrn_le_half
  have hh0 : 0 ≤ h := le_trans (mul_nonneg zero_le_two hrn_nonneg) hchord
  have hh1 : h ≤ 1 := by
    rw [hh, binaryEntropyBits, binaryEntropy_eq_binEntropy]
    rw [div_le_one hlog2_pos]
    have := Real.binEntropy_le_log_two (p := (r : ℝ) / N)
    linarith only [this]
  have hr2 : 2 * (r : ℝ) ≤ N * h := by
    have hstep : N * (2 * ((r : ℝ) / N)) ≤ N * h := mul_le_mul_of_nonneg_left hchord hNpos.le
    rwa [mul_left_comm, mul_div_cancel₀ _ hNpos.ne'] at hstep
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓdef]
    apply Real.logb_nonneg (by norm_num)
    rw [le_inv_comm₀ (by norm_num) hε_pos]; simpa using hε_lt_one.le
  -- `l4b = log₂ 4 = 2`, `l6b = log₂ 6 ≤ 2.6` (since `6 < 2^2.6 ≈ 6.063`).
  have hl4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_self_pow (by norm_num) (by norm_num)]
    norm_num
  have hl6 : Real.logb 2 6 ≤ 2.6 := by
    rw [Real.logb, div_le_iff₀ hlog2_pos]
    -- `log 6 ≤ 2.6 · log 2 = log (2^(13/5))`, i.e. `6 ≤ 2^(13/5)` (5th powers: `6^5 ≤ 2^13`).
    have h65 : (6 : ℝ) ^ (5 : ℕ) ≤ (2 : ℝ) ^ (13 : ℕ) := by norm_num
    have hlog65 : Real.log ((6 : ℝ) ^ (5 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (13 : ℕ)) :=
      Real.log_le_log (by positivity) h65
    rw [Real.log_pow, Real.log_pow] at hlog65
    push_cast at hlog65
    linarith only [hlog65]
  have hl6_0 : 0 ≤ Real.logb 2 6 := Real.logb_nonneg (by norm_num) (by norm_num)
  -- The smoothing log `L = log₂(ε'⁻¹)` with `ε' = ε²/(6·S_card)`.
  set L : ℝ := Real.logb 2 (ε ^ 2 / (6 * (S_card : ℝ)))⁻¹ with hLdef
  -- `log₂(S_card) ≤ N·h` (from `hS_card`, taking `log₂`; also covers `S_card = 0`).
  have hlogScard : Real.logb 2 (S_card : ℝ) ≤ N * h := by
    rcases Nat.eq_zero_or_pos S_card with hS0 | hSpos
    · rw [hS0]
      simp only [Nat.cast_zero, Real.logb_zero]
      exact mul_nonneg hNpos.le hh0
    · have hSpos' : (0 : ℝ) < (S_card : ℝ) := by exact_mod_cast hSpos
      have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hSpos' hS_card
      rwa [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at this
  -- `L ≤ log₂6 + N·h + 2ℓ` and `0 ≤ L`.
  have hLbound : L ≤ Real.logb 2 6 + N * h + 2 * ℓ := by
    rcases Nat.eq_zero_or_pos S_card with hS0 | hSpos
    · -- `S_card = 0`: `ε' = 0`, `ε'⁻¹ = 0`, `L = 0`.
      have : L = 0 := by rw [hLdef, hS0]; simp
      rw [this]; positivity
    · have hSpos' : (0 : ℝ) < (S_card : ℝ) := by exact_mod_cast hSpos
      have hden : (0 : ℝ) < 6 * (S_card : ℝ) := by positivity
      have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
      have hinv : (ε ^ 2 / (6 * (S_card : ℝ)))⁻¹ = 6 * (S_card : ℝ) / ε ^ 2 := by
        rw [inv_div]
      rw [hLdef, hinv]
      rw [Real.logb_div hden.ne' hε2.ne']
      rw [Real.logb_mul (by norm_num) hSpos'.ne']
      have hε2log : Real.logb 2 (ε ^ 2) = 2 * Real.logb 2 ε := by
        rw [show (ε ^ 2 : ℝ) = ε ^ (2 : ℕ) by ring, Real.logb_pow]; push_cast; ring
      have hℓeq : ℓ = - Real.logb 2 ε := by
        rw [hℓdef, Real.logb_inv]
      rw [hε2log]
      have hℓexpand : 2 * ℓ = - (2 * Real.logb 2 ε) := by rw [hℓeq]; ring
      linarith only [hlogScard, hℓexpand]
  have hL0 : 0 ≤ L := by
    rcases Nat.eq_zero_or_pos S_card with hS0 | hSpos
    · rw [hLdef, hS0]; simp
    · have hSpos' : (1 : ℝ) ≤ (S_card : ℝ) := by exact_mod_cast hSpos
      have hinv : (ε ^ 2 / (6 * (S_card : ℝ)))⁻¹ = 6 * (S_card : ℝ) / ε ^ 2 := by rw [inv_div]
      rw [hLdef, hinv]
      apply Real.logb_nonneg (by norm_num)
      -- `ε² ≤ 1 ≤ 6·S_card`
      rw [le_div_iff₀ (pow_pos hε_pos 2), one_mul]
      linarith only [pow_le_one₀ (n := 2) hε_pos.le hε_lt_one.le, hSpos']
  -- `M = n − r ≥ 1` (since `r ≤ n/2 < n` for `n ≥ 3`).
  set M : ℝ := ((n - r : ℕ) : ℝ) with hMdef
  have hMpos : (1 : ℝ) ≤ M := by
    rw [hMdef]
    have : 1 ≤ n - r := by omega
    exact_mod_cast this
  have hMeq : M = N - (r : ℝ) := hnr_real
  have hMle : M ≤ N := by rw [hMeq]; linarith only [Nat.cast_nonneg (α := ℝ) r]
  -- `u := √(h + (2/N)·log₂(4/ε))`, so `aep_correction_distvN = (5/2·A + 5)·u` and
  -- `N·u² = N·h + 2(log₂4 + ℓ)` (`hnu2` of C1/C2 with `l4b = log₂4 = 2`).
  have hlog4ε : Real.logb 2 (4 / ε) = Real.logb 2 4 + ℓ := by
    rw [show (4 / ε : ℝ) = 4 * ε⁻¹ by rw [div_eq_mul_inv],
      Real.logb_mul (by norm_num) (by positivity), hℓdef]
  set u : ℝ := Real.sqrt (h + 2 / N * Real.logb 2 (4 / ε)) with hudef
  have hu_arg_nonneg : 0 ≤ h + 2 / N * Real.logb 2 (4 / ε) := by
    rw [hlog4ε, hl4]; positivity
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hnu2 : N * u ^ 2 = N * h + 2 * (Real.logb 2 4 + ℓ) := by
    rw [hudef, Real.sq_sqrt hu_arg_nonneg, hlog4ε, mul_add, ← mul_assoc,
      mul_div_cancel₀ _ hNpos.ne']
  have hdistvN : aep_correction_distvN dX n r ε = (5 / 2 * A + 5) * u := by
    rw [aep_correction_distvN, hA, ← hh, ← hudef]
  -- `s := √(M·(L+1))`, so `M·δ' = (2A+4)·s` and `s² = M·(L+1) ≤ N(l6b+1)+N²h+2Nℓ`.
  set s : ℝ := Real.sqrt (M * (L + 1)) with hsdef
  have hL1pos : 0 ≤ L + 1 := by linarith only [hL0]
  have hM0 : 0 ≤ M := zero_le_one.trans hMpos
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = M * (L + 1) := by
    rw [hsdef, Real.sq_sqrt (mul_nonneg hM0 hL1pos)]
  -- `M·δ' = (2A+4)·s`: `M·√((L+1)/M) = √(M(L+1))` since `M > 0`.
  have hδ'eq : M * aep_correction_perComponent dX (n - r) (ε ^ 2 / (6 * (S_card : ℝ))) =
      (2 * A + 4) * s := by
    rw [aep_correction_perComponent, InfoTheory.SmoothMinEntropy.noiseFactor, hA,
      ← hLdef, hsdef, hMdef]
    rw [show M * (L + 1) = M ^ 2 * ((L + 1) / M) by
      rw [sq, mul_assoc, mul_div_cancel₀ _ (zero_lt_one.trans_le hMpos).ne']]
    rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0]
    ring
  -- The pooled `√`-bound on `s²` feeding C1/C2.
  have hs2_bound : s ^ 2 ≤ N * (Real.logb 2 6 + 1) + N ^ 2 * h + 2 * N * ℓ := by
    rw [hs2]
    have h1 : M * (L + 1) ≤ N * (L + 1) := mul_le_mul_of_nonneg_right hMle hL1pos
    have h2 : N * (L + 1) ≤ N * (Real.logb 2 6 + N * h + 2 * ℓ + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hLbound le_rfl) hNpos.le
    have h3 : N * (Real.logb 2 6 + N * h + 2 * ℓ + 1) =
        N * (Real.logb 2 6 + 1) + N ^ 2 * h + 2 * N * ℓ := by ring
    exact (h1.trans h2).trans_eq h3
  -- Apply C1 and C2 (with `l4b = log₂4 = 2`, `l6b = log₂6 ≤ 2.6`).
  have hl4_2 : (2 : ℝ) ≤ Real.logb 2 4 := by rw [hl4]
  have hC1 : 4 * s + N * h ≤ 5 * N * u :=
    aggregation_sqrt_bound_C1 N h s u ℓ (Real.logb 2 4) (Real.logb 2 6)
      hN3 hh0 hh1 hs0 hu0 hℓ0 hs2_bound hnu2 hl4_2 hl6
  have hC2 : 2 * s + (r : ℝ) ≤ 5 / 2 * N * u :=
    aggregation_sqrt_bound_C2 N h s u (r : ℝ) ℓ (Real.logb 2 4) (Real.logb 2 6)
      hN3 hh0 hh1 hs0 hu0 hℓ0 (Nat.cast_nonneg r) hr2 hs2_bound hnu2 hl4_2 hl6
  -- Assemble: `M·δ' + N·h + r·A = 4s + N·h + A·(2s + r) ≤ 5Nu + A·(5/2·Nu) = N·distvN`.
  rw [hδ'eq, hdistvN]
  have hAC2 : A * (2 * s + (r : ℝ)) ≤ A * (5 / 2 * N * u) :=
    mul_le_mul_of_nonneg_left hC2 hA0
  have hLHS : (2 * A + 4) * s + N * h + (r : ℝ) * A =
      (4 * s + N * h) + A * (2 * s + (r : ℝ)) := by ring
  have hRHS : N * ((5 / 2 * A + 5) * u) = 5 * N * u + A * (5 / 2 * N * u) := by ring
  rw [hLHS, hRHS]
  exact add_le_add hC1 hAC2

end InfoTheory.SmoothMinEntropy.SymmetricAEP

end -- noncomputable section
