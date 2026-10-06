import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP

/-!
# Statistics of symmetric states — Renner `thm:symstat` (frequency concentration)

**Textbook reference**: Renner, R. (2005). *Security of Quantum Key Distribution*.
PhD thesis, ETH Zürich. arXiv:quant-ph/0512258.
- `sec:symstat`, lines 6330–6537.
- `lem:sumprob` (line 6348), `thm:symstat` (line 6391), `lem:PEsec` (line 7527).

This file states the **frequency-concentration** branch of the symmetric-subspace
machinery, which is a *different theorem* from the smooth-min-entropy AEP
`thm:Renyisym` already formalized in
`InfoTheory/SmoothMinEntropy/SymmetricAEP.lean`. The two share only the
combinatorial decomposition `lem:symspacebin` (here, the existing
`RestrictedSymSpaceWitness`):

| theorem | conclusion | BB84 consumer |
|---|---|---|
| `thm:Renyisym` | operator `H_min^ε(ρ_{XⁿBⁿ}|Bⁿ) ≥ n·H(σ_{XB}|σ_B) − δ` | rate floor (†) |
| `thm:symstat` | classical `Pr_Ψ[‖freq(z) − P_Z‖₁ > radius] ≤ ε` | PE soundness (‡) |

(†) the i.i.d.-tensor reference rate floor `ref.tensorSmoothHmin` (the LHS of the symRef floor
`hentropy`), via the r=0 corollary `smoothMinEntropy_tensorPower_ge_classical_aep_floor`
(register `dB^n`).
(‡) PE soundness via Renner's `lem:PEsec`.

A floor on Eve's register is not a direct instance of `thm:Renyisym`:
the IID endpoint `smoothMinEntropy_tensorPower_ge_classical_aep_floor`
gives smooth min-entropy on `dB^n` against a `B^n` reference. Transport to register `eveDim`
against `maxMixed_E` is a separate cross-register statement.

## What is stated here (and what is deliberately NOT)

The genuinely shared, alphabet-agnostic *engine* of `thm:symstat` is Renner's
`lem:sumprob` specialized to the superposition decomposition of `lem:symspacebin`:
for `|Ψ⟩ = Σ_{s∈S} γ_s |Ψ^s⟩` (the `RestrictedSymSpaceWitness` data) and **any**
positive-semidefinite `A : Op (d^n)`,

  `⟨Ψ| A |Ψ⟩ ≤ |S| · Σ_{s∈S} |γ_s|² · ⟨Ψ^s| A |Ψ^s⟩` ,

the `|S| = 2^{n·h(r/n)}`-multiplicative penalty engine
(`symStat_sumprob_quadraticForm_le`, `symStat_bornMass_le_card_smul_componentMass`).
This is the exact mechanism of the proof at main.tex:6489–6511 (where `A = Σ_{z ∈
W_δ} M_z` is the PE-reject operator and the per-component masses `⟨Ψ^s| A |Ψ^s⟩`
are bounded by the IID typical-sequence tail `cor:typsec`). It is what the BB84
PE-soundness bridge needs, and it requires **no** new measurement / general-alphabet
empirical-type / `‖·‖₁` infrastructure.

The full statement of `thm:symstat` — `Pr_Ψ[‖freq(z) − P_Z‖₁ > radius] ≤ ε` for a
general POVM `M = {M_z}_{z∈Z}`, the Born distribution `P_Z(z) = Tr(M_z |θ⟩⟨θ|)`,
the empirical type `freq(z) : Z → ℝ`, and the `ℓ¹` distance — is **not** stated
here. Stating it faithfully would require a general-alphabet measurement layer
(POVM-as-data, the product Born distribution over `Zⁿ`, the empirical type, and the
`ℓ¹` metric on distributions over `Z`) that does not exist in the repository and
whose only client is the *binary* BB84 bit/phase POVM. That binary specialization
is already serviced by the classical Serfling/`empiricalFreqOf` engine
(`Math/Probability/SamplingConcentration.lean`, `Math/Concentration/Serfling.lean`);
the missing link is the **quantum→classical Born bridge**, whose discharge *is* `lem:PEsec` and
rests
precisely on the `|S|`-penalty engine stated here. See the connection note below.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy.SymmetricStatistics

open InfoTheory.SmoothMinEntropy.SymmetricAEP

/-- **Triangle + Chebyshev**: in any seminormed additive group, the squared norm
of a finite sum is at most `|S|` times the sum of squared norms. This is the
abstract `(Σ aₛ)² ≤ |S| Σ aₛ²` Cauchy–Schwarz step combined with the triangle
inequality `‖Σ uₛ‖ ≤ Σ ‖uₛ‖`. -/
private lemma norm_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type*} {E : Type*} [SeminormedAddCommGroup E]
    (S : Finset ι) (u : ι → E) :
    ‖∑ s ∈ S, u s‖ ^ 2 ≤ (S.card : ℝ) * ∑ s ∈ S, ‖u s‖ ^ 2 := by
  calc ‖∑ s ∈ S, u s‖ ^ 2
      ≤ (∑ s ∈ S, ‖u s‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S u) 2
    _ ≤ (S.card : ℝ) * ∑ s ∈ S, ‖u s‖ ^ 2 := by
        have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun s => ‖u s‖)
        simpa using h

/-- **Core PSD Cauchy–Schwarz inequality**: for a positive-semidefinite `A`, finite
`S`, scalars `c` and vectors `v`, the Born quadratic form of the superposition
`∑ cₛ • vₛ` is bounded by `|S|` times the `|cₛ|²`-weighted sum of per-component
quadratic forms. The proof factors `A = Bᴴ B` so that `⟨y|A|y⟩ = ‖B·y‖²` becomes an
honest `ℓ²`-norm, then applies triangle + Chebyshev (`norm_sum_sq_le_card_mul_sum_norm_sq`). -/
private lemma quadraticForm_sum_le {N : ℕ} {A : Op N} (hA : A.PosSemidef)
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (v : ι → (Fin N → ℂ)) :
    (quadraticForm A (∑ s ∈ S, c s • v s)).re ≤
      (S.card : ℝ) * ∑ s ∈ S, Complex.normSq (c s) * (quadraticForm A (v s)).re := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  change A = Bᴴ * B at hB
  set L := (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm with hL
  -- Bridge: `(quadraticForm A y).re = ‖L (B · y)‖²` for every `y`.
  have bridge : ∀ y : Fin N → ℂ, (quadraticForm A y).re = ‖L (B.mulVec y)‖ ^ 2 := by
    intro y
    have hqf : quadraticForm A y = star (B.mulVec y) ⬝ᵥ (B.mulVec y) := by
      unfold quadraticForm
      rw [hB, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      congr 1
      rw [Matrix.star_mulVec]
    rw [hqf, EuclideanSpace.norm_sq_eq]
    have hexp : star (B.mulVec y) ⬝ᵥ (B.mulVec y)
        = ((∑ i, ‖(B.mulVec y) i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      simp only [dotProduct, Pi.star_apply, ← starRingEnd_apply, Complex.conj_mul',
        Complex.ofReal_pow]
    rw [hexp, Complex.ofReal_re]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [bridge]
  -- Push `L (B · (∑ cₛ vₛ))` through linearity to `∑ cₛ • L (B · vₛ)`.
  have hpush : L (B.mulVec (∑ s ∈ S, c s • v s))
      = ∑ s ∈ S, c s • L (B.mulVec (v s)) := by
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, map_sum, map_smul]
  rw [hpush]
  calc ‖∑ s ∈ S, c s • L (B.mulVec (v s))‖ ^ 2
      ≤ (S.card : ℝ) * ∑ s ∈ S, ‖c s • L (B.mulVec (v s))‖ ^ 2 :=
        norm_sum_sq_le_card_mul_sum_norm_sq S _
    _ = (S.card : ℝ) *
          ∑ s ∈ S, Complex.normSq (c s) * (quadraticForm A (v s)).re := by
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        rw [norm_smul, mul_pow, bridge (v s)]
        congr 1
        rw [Complex.normSq_eq_norm_sq]

/-- **Renner `lem:sumprob` for the symmetric superposition** (main.tex:6348, applied
at main.tex:6492–6505).

For the superposition decomposition `|Ψ⟩ = Σ_{s∈S} γ_s |Ψ^s⟩` carried by a
`RestrictedSymSpaceWitness` and **any** positive-semidefinite operator
`A : Op (d^n)`, the Born quadratic form `⟨Ψ| A |Ψ⟩` is bounded by `|S|` times the
`|γ_s|²`-weighted sum of the per-component quadratic forms:

  `(⟨Ψ| A |Ψ⟩).re ≤ |S| · Σ_{s∈S} |γ_s|² · (⟨Ψ^s| A |Ψ^s⟩).re` .

The `|S|`-multiplicative factor is the symmetric-counting penalty
`|S| ≤ 2^{n·h(r/n)}` (the `RestrictedSymSpaceWitness.hS_card` bound). The proof is
Renner's: spectrally decompose `A = Σ_y p_y |y⟩⟨y|` (PSD), apply Cauchy–Schwarz
`|⟨y|Ψ⟩|² ≤ |S| Σ_s |γ_s|² |⟨y|Ψ^s⟩|²` to each eigenvector via the decomposition
`hdecomp`, and sum against the nonnegative `p_y`.

This is the engine that converts the per-component product-measurement
concentration (`cor:typsec`, the IID typical-sequence tail on the `|θ⟩^{⊗(n−r)}`
factor) into the symmetric-state concentration of `thm:symstat`. It is stated for an
arbitrary PSD `A` because `thm:symstat`/`lem:PEsec` instantiate it with
`A = Σ_{z ∈ W} M_z`, the assembled product-POVM operator of the bad/reject
outcome set `W ⊆ Zⁿ` (PSD as a finite sum of PSD product-POVM elements). -/
theorem symStat_sumprob_quadraticForm_le
    {d n r : ℕ} [NeZero d] [NeZero (d ^ n)]
    {θ : NormKet d} {Ψ : NormKet (d ^ n)}
    (symWit : RestrictedSymSpaceWitness d n r θ Ψ)
    (A : Op (d ^ n)) (hA : A.PosSemidef) :
    (quadraticForm A Ψ.toKet.vec).re ≤
      (symWit.S.card : ℝ) *
        ∑ s ∈ symWit.S,
          Complex.normSq (symWit.coefficients s) *
            (quadraticForm A (symWit.basis_vecs s).toKet.vec).re := by
  rw [symWit.hdecomp]
  exact quadraticForm_sum_le hA symWit.S symWit.coefficients
    (fun s => (symWit.basis_vecs s).toKet.vec)

/-- **Symmetric-state Born-mass bound** (main.tex:6493–6505).

The `lem:sumprob` engine in the form directly consumed by `thm:symstat`/`lem:PEsec`:
for a "reject" PSD operator `A` (in the application, the sum of product-POVM
elements over an outcome set `W ⊆ Zⁿ`), if every per-component Born mass
`⟨Ψ^s| A |Ψ^s⟩` is bounded by a common per-component tail `t` (in the application,
the IID typical-sequence tail `2^{−nδ/2}` of `cor:typsec`), then the symmetric-state
Born mass `⟨Ψ| A |Ψ⟩` is bounded by `|S| · t`.

Combined with `hS_card`, this gives the `2^{n·h(r/n)} · 2^{−nδ/2}` bound of
main.tex:6507–6509 — the source of the BB84 postselection slack
`(n+1)·polyDim/2ⁿ`. The per-component tail `t` is supplied by the caller (it is the
classical concentration, not part of this quantum engine). -/
theorem symStat_bornMass_le_card_smul_componentMass
    {d n r : ℕ} [NeZero d] [NeZero (d ^ n)]
    {θ : NormKet d} {Ψ : NormKet (d ^ n)}
    (symWit : RestrictedSymSpaceWitness d n r θ Ψ)
    (A : Op (d ^ n)) (hA : A.PosSemidef)
    (t : ℝ)
    (hcomponent : ∀ s ∈ symWit.S,
      (quadraticForm A (symWit.basis_vecs s).toKet.vec).re ≤ t) :
    (quadraticForm A Ψ.toKet.vec).re ≤ (symWit.S.card : ℝ) * t := by
  -- Engine: `⟨Ψ|A|Ψ⟩ ≤ |S| · Σ_s |γ_s|² · ⟨Ψ^s|A|Ψ^s⟩`.
  refine le_trans (symStat_sumprob_quadraticForm_le symWit A hA) ?_
  -- Bound the weighted component sum by `t`, using `Σ_s |γ_s|² = 1`.
  have hbound :
      ∑ s ∈ symWit.S,
          Complex.normSq (symWit.coefficients s) *
            (quadraticForm A (symWit.basis_vecs s).toKet.vec).re ≤
        ∑ s ∈ symWit.S, Complex.normSq (symWit.coefficients s) * t := by
    refine Finset.sum_le_sum (fun s hs => ?_)
    exact mul_le_mul_of_nonneg_left (hcomponent s hs) (Complex.normSq_nonneg _)
  calc
    (symWit.S.card : ℝ) *
        ∑ s ∈ symWit.S,
          Complex.normSq (symWit.coefficients s) *
            (quadraticForm A (symWit.basis_vecs s).toKet.vec).re
        ≤ (symWit.S.card : ℝ) *
            ∑ s ∈ symWit.S, Complex.normSq (symWit.coefficients s) * t :=
          mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = (symWit.S.card : ℝ) * t := by
          rw [← Finset.sum_mul, symWit.hcoeffs_norm, one_mul]

/-! ## Connection to parameter-estimation soundness (`lem:PEsec`)

The quantum-to-classical Born identification is a separate hypothesis in an application of
this engine. For example, a bound of the form

`Pr[PE accepts] ≤ P.real{empirical pass event} + (n+1)·polyDim/2ⁿ`,

with `polyDim = C(n + d²−1, d²−1)` and `d = signalDim`, combines with a classical
Serfling bound to give `exp(−2·k·η²) + (n+1)·polyDim/2ⁿ` (or `exp(−2nη²)` when the
sample parameter is `n`). Renner's `lem:PEsec` follows from `thm:symstat` (`main.tex:7546`).

The symmetric-state estimate applies as follows:

1. Express the reject probability as `(quadraticForm A_reject Ψ.vec).re`, where `Ψ` is a
   symmetric purification with a `RestrictedSymSpaceWitness` in `SymR(ℂ^d, n, θ, n−r)`,
   and `A_reject = Σ_{w ∈ W} M_w` is the PSD sum of product-POVM operators over a reject
   set `W ⊆ Wⁿ`.
2. Apply `symStat_bornMass_le_card_smul_componentMass`. With the IID typical-sequence tail
   `t = 2^{−nδ/2}` from `cor:typsec` on the `|θ⟩^{⊗(n−r)}` factor, this gives
   `Born mass ≤ |S| · 2^{−nδ/2} ≤ 2^{n·h(r/n)} · 2^{−nδ/2}` by `hS_card`.
   At the CKR defect `r`, this is the slack `(n+1)·polyDim/2ⁿ`.

Two application-specific facts are required: the concrete purification must satisfy
`lem:symspacebin`, and the attacked-state trace against the pass projection must equal the
appropriate per-component Born mass, with its product POVM and IID tail estimate.
This module does not supply either identification for a BB84 protocol.

The without-replacement sampler with `k = n` is degenerate: `testSample : Fin n ↪ Fin n`
is a bijection, so empirical and population frequencies agree deterministically; it cannot
supply a nontrivial bound from the slack alone. A source-marginal-average classifier is not
the per-component reference, and single-binomial or per-outcome-block-orthogonality bounds
fail for correlated covariant attacks. The concentration in `thm:symstat` is conditioned
product-measurement concentration: the slack is the symmetric `|S|` counting penalty and
the tail is IID concentration on `|θ⟩^{⊗(n−r)}`, not a subsample of all `n` rounds.
-/

end InfoTheory.SmoothMinEntropy.SymmetricStatistics

end -- noncomputable section
