import QCryptLean.InfoTheory.Postselection.Lift

/-!
# QKD postselection — variable-length protocols: Definition 8 and Theorem 4 objects (T3)

Faithful transcription of the variable-length postselection setup of
Nahar–Tupkary–Zhao–Lütkenhaus–Tan 2024 (arXiv:2403.11851), Section III C
(lines 657–725):

- **Object** `VariableLengthPMQKDProtocol` — the variable-length protocol map
  `E_var-QKD^{(l₁,…,l_M)} ∈ C(AⁿBⁿ, K_A C̃_e)` (lines 666–676) producing a key of length `lᵢ` on
  event `Ωᵢ` (`M` possible lengths). The hash-length *tuple* `(l₁',…,l_M') : Fin M → ℕ` indexes the
  variant family.
- **Definition 8** `IsVariableLengthFixedMarginalSecret` (`\label{eq:epsSecVar}`
(main.tex:562–:566), lines 679–691) — `ε_sec`-secrecy
  with fixed marginal `σ̂A`, `½ ‖((E_var − E_var^{ideal}) ⊗ id_{Eⁿ}) ρ‖₁ ≤ ε_sec` for all `ρ` with
  `Tr_{BⁿEⁿ} ρ = (σ̂A)^{⊗n}`. This is exactly the Definition 4 inequality for the variable-length
  difference map, so it reuses `IsFixedMarginalSecret` — the `½` is baked in.
- **Theorem 4 objects** — `referenceSecrecy_var` (main.tex:583–:585 (unlabeled; the conclusion of
`\label{thm:maintheoremvar}` :573–:590) left-hand side),
  `variableLengthCoherentSecrecy` (main.tex:583–:585 (unlabeled; the conclusion of
  `\label{thm:maintheoremvar}` :573–:590) right-hand side `√(8ε_sec) + ε̃/2`), and
  the shortened-length-tuple predicate (`lᵢ' = lᵢ − 2 log g_{n,x} − 2 log(1/ε̃)`, line 712).

## Scope
The Theorem 4 *implication* "`\label{eq:epsSecVar}` (main.tex:562–:566)-for-IID ⟹ main.tex:583–:585
(unlabeled; the conclusion of `\label{thm:maintheoremvar}` :573–:590)" (Nahar et al. App. B,
main.tex:1470–:1516
(Appendix B's proof of Theorem 4/variable-length): per-event smooth
min-entropy floors, register extension, leftover hashing, and the concavity step that produces the
`√(8ε_sec)`) is the variable-length analogue of `postselection_referenceBound_of_iidSecurityProof`
with an added `M`-event sum
structure. It requires a protocol pre-PA raw-key measurement interface and a per-event
accept structure, which are not supplied here. The exact
main.tex:583–:585 (unlabeled; the conclusion of `\label{thm:maintheoremvar}` :573–:590)
statement objects (LHS `referenceSecrecy_var`, RHS `variableLengthCoherentSecrecy`, the length
tuple) are provided here; the implication is not proved in this module.
-/

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-- Positivity of `dA ^ n * dB ^ n`. -/
private theorem neZero_inputDim' (dA dB n : ℕ) [NeZero dA] [NeZero dB] :
    NeZero (dA ^ n * dB ^ n) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (pow_pos (NeZero.pos dA) n) (pow_pos (NeZero.pos dB) n))⟩

/-! ## The variable-length PMQKD protocol object (Nahar et al. lines 666–676) -/

/-- **Variable-length PMQKD protocol object** (Nahar et al. 2024, Section III C, lines 666–676).

    A protocol map `E_var-QKD^{(l₁,…,l_M)} ∈ C(AⁿBⁿ, K_A C̃_e)` on abstract single-round dimensions
    `dA`, `dB`, with `M` possible output key lengths. `KA` stores bit strings up to a maximum
    length;
    on event `Ωᵢ` a key of length `lᵢ` is produced (`⊥` on abort). The hash-length *tuple*
    `lt : Fin M → ℕ` indexes the variant family `E_var-QKD^{(l₁',…,l_M')}` (Theorem 4 hashes to the
    shortened tuple). This mirrors `PMQKDProtocol` with the scalar length replaced by an `M`-tuple.
-/
structure VariableLengthPMQKDProtocol (dA dB n M : ℕ) [NeZero dA] [NeZero dB] [NeZero n]
    [NeZero M] where
  /-- Dimension of Alice's key register `K_A`. -/
  keyDim : ℕ
  /-- `K_A` is nonzero. -/
  keyDim_neZero : NeZero keyDim
  /-- Total announcement dimension `C̃_e`. -/
  annDim : ℕ
  /-- `C̃_e` is nonzero. -/
  annDim_neZero : NeZero annDim
  /-- Dimension of the raw-key register `Zⁿ`. -/
  rawKeyDim : ℕ
  /-- `Zⁿ` is nonzero. -/
  rawKeyDim_neZero : NeZero rawKeyDim
  /-- The `M` base output key lengths `l₁,…,l_M`, produced on events `Ω₁,…,Ω_M`. -/
  lengths : Fin M → ℕ
  /-- Variant family indexed by the hash-length tuple `(l₁',…,l_M')`. -/
  variantReal : (Fin M → ℕ) → (Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op (keyDim * annDim))
  /-- Ideal variant family (`E_var-QKD^{(l₁',…,l_M'),ideal}`). -/
  variantIdeal : (Fin M → ℕ) → (Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op (keyDim * annDim))
  /-- Every real variant is a channel (CPTP). -/
  variantReal_isCPTP : ∀ lt,
    haveI := neZero_inputDim' dA dB n
    haveI := keyDim_neZero
    haveI := annDim_neZero
    haveI : NeZero (keyDim * annDim) := ⟨Nat.pos_iff_ne_zero.mp
      (Nat.mul_pos keyDim_neZero.pos annDim_neZero.pos)⟩
    IsCPTP (⇑(variantReal lt))
  /-- Every ideal variant is a channel (CPTP). -/
  variantIdeal_isCPTP : ∀ lt,
    haveI := neZero_inputDim' dA dB n
    haveI := keyDim_neZero
    haveI := annDim_neZero
    haveI : NeZero (keyDim * annDim) := ⟨Nat.pos_iff_ne_zero.mp
      (Nat.mul_pos keyDim_neZero.pos annDim_neZero.pos)⟩
    IsCPTP (⇑(variantIdeal lt))

namespace VariableLengthPMQKDProtocol

variable {dA dB n M : ℕ} [NeZero dA] [NeZero dB] [NeZero n] [NeZero M]

/-- The variable-length difference map `Δ^{(l₁',…,l_M')} = E_var^{(lt)} − E_var^{(lt),ideal)}`. -/
def differenceMap (P : VariableLengthPMQKDProtocol dA dB n M) (lt : Fin M → ℕ) :
    Op (dA ^ n * dB ^ n) →ₗ[ℂ] Op (P.keyDim * P.annDim) :=
  P.variantReal lt - P.variantIdeal lt

end VariableLengthPMQKDProtocol

/-! ## Definition 8 — variable-length fixed-marginal secrecy (Nahar et al. `\label{eq:epsSecVar}`
(main.tex:562–:566)) -/

/-- **Nahar et al. Definition 8** (`\label{eq:epsSecVar}` (main.tex:562–:566), lines 679–691). The
variable-length protocol `P` at hash-length
    tuple `lt` is `ε_sec`-secret with fixed marginal `σ̂A` iff

      `½ ‖((E_var^{(lt)} − E_var^{(lt),ideal}) ⊗ id_{Eⁿ}) ρ_{AⁿBⁿEⁿ}‖₁ ≤ ε_sec`

    for all `ρ` with `Tr_{BⁿEⁿ} ρ = (σ̂A)^{⊗n}`. This is exactly the Definition 4 inequality for the
    variable-length difference map, so it is `IsFixedMarginalSecret` applied to `differenceMap lt`;
    the `½` is baked in. -/
def IsVariableLengthFixedMarginalSecret {dA dB n M : ℕ}
    [NeZero dA] [NeZero dB] [NeZero n] [NeZero M]
    (P : VariableLengthPMQKDProtocol dA dB n M) (lt : Fin M → ℕ)
    (σA : DensityOp dA) (εsec : ℝ) : Prop :=
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  haveI : NeZero (P.keyDim * P.annDim) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
  IsFixedMarginalSecret (P.differenceMap lt) σA εsec

/-! ## Theorem 4 statement objects (Nahar et al. main.tex:583–:585 (unlabeled; the conclusion of
`\label{thm:maintheoremvar}` :573–:590)) -/

/-- **Nahar et al. Theorem 4 secrecy parameter** (main.tex:583–:585 (unlabeled; the conclusion of
`\label{thm:maintheoremvar}` :573–:590) right-hand side, lines 722 / 2276, whose App-B
    derivation ends at line 2446 in `ε̃/2 + √8·√ε_sec`): `√(8 ε_sec) + ε̃/2`. -/
def variableLengthCoherentSecrecy (εsec εe : ℝ) : ℝ :=
  Real.sqrt (8 * εsec) + εe / 2

/-- **Nahar et al. Theorem 4 shortened hash-length tuple** (line 712): `lᵢ' = lᵢ − 2 log g_{n,x} −
    2 log(1/ε̃)` with `x = d_A² d_B²`, stated as the exact real relation on tuple entry `i`.

    (`Nat`-valued hash lengths satisfying this real relation exist only when the right-hand side is
    a
    nonnegative integer; the relation transcribes Nahar et al.'s exact length choice.) -/
def IsShortenedLengthTuple {dA dB n M : ℕ} [NeZero dA] [NeZero dB] [NeZero n] [NeZero M]
    (P : VariableLengthPMQKDProtocol dA dB n M) (lt' : Fin M → ℕ) (εe : ℝ) : Prop :=
  ∀ i : Fin M, (lt' i : ℝ) = (P.lengths i : ℝ)
    - 2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n)
    - 2 * Real.logb 2 (1 / εe)

/-- **Nahar et al. Theorem 4 / main.tex:583–:585 (unlabeled; the conclusion of
`\label{thm:maintheoremvar}` :573–:590) left-hand side** `½ ‖((E_var^{(lt')} − E_var^{(lt'),ideal})
⊗ id_R)
    (τ_R)‖₁`: the de Finetti reference secrecy of the variable-length variant at hash-length tuple
    `lt'` on the mixture purification `τ_R`. The `½` is baked in; the purification is cast from the
    register `(d_A d_B)^n` to the difference map's input register `AⁿBⁿ = d_A^n d_B^n` exactly as in
    `referenceSecrecy` (via `referenceDimEq`). -/
def referenceSecrecy_var {dA dB n M : ℕ} [NeZero dA] [NeZero dB] [NeZero n] [NeZero M]
    (P : VariableLengthPMQKDProtocol dA dB n M) (lt' : Fin M → ℕ)
    (μ : DensityMeasure (dA * dB)) : ℝ :=
  haveI : NeZero (dA ^ n * dB ^ n) := neZero_inputDim' dA dB n
  haveI := P.keyDim_neZero
  haveI := P.annDim_neZero
  haveI : NeZero (P.keyDim * P.annDim) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)⟩
  haveI : NeZero (P.keyDim * P.annDim * (dA ^ n * dB ^ n)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.mul_pos P.keyDim_neZero.pos P.annDim_neZero.pos)
      (Nat.mul_pos (pow_pos (NeZero.pos dA) n) (pow_pos (NeZero.pos dB) n)))⟩
  (1 / 2 : ℝ) * traceNorm
    (mapTensorId (k := dA ^ n * dB ^ n) (P.differenceMap lt')
      (DensityOp.castDim (referenceDimEq dA dB n)
        (deFinettiMixturePurification dA dB n μ)).toOp)

/-- **Nahar et al. Theorem 4 conclusion** (main.tex:583–:585 (unlabeled; the conclusion of
`\label{thm:maintheoremvar}` :573–:590)) as a predicate: the variable-length variant's de Finetti
    reference secrecy at tuple `lt'` is at most `√(8 ε_sec) + ε̃/2`. -/
def SatisfiesVariableLengthReferenceBound {dA dB n M : ℕ}
    [NeZero dA] [NeZero dB] [NeZero n] [NeZero M]
    (P : VariableLengthPMQKDProtocol dA dB n M) (lt' : Fin M → ℕ)
    (μ : DensityMeasure (dA * dB)) (εsec εe : ℝ) : Prop :=
  referenceSecrecy_var P lt' μ ≤ variableLengthCoherentSecrecy εsec εe

end InfoTheory.Postselection

end
