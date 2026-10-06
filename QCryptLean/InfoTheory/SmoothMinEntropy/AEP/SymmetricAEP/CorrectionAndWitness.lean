import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.Fidelity
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSmooth
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.SmoothSuperadditivity
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.ClassicalExtension
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SuperpositionDephasing.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SuperpositionDephasing.ClassicalReduction
import QCryptLean.InfoTheory.VonNeumannEntropy.Defs
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Quantum.Symmetry.SymmetricSubspace
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.TensorProducts.QuadraticForm
import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.Channels.CPTP.TensorPow
import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.InfoTheory.SmoothMinEntropy.ChainRule.ConditionalVNEntropyBound

/-!
# Symmetric AEP corrections and component witnesses

Real finite-size corrections bound IID component rates in bits. Spectral and transport witnesses
then give an extended smooth entropy floor for each symmetric-state component.
-/

open Real Math.ClassicalEntropy InfoTheory.VonNeumannEntropy
open Quantum.Operators Quantum.Symmetry
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy.SymmetricAEP

/-!
## AEP correction term

The correction term `δ` from Renner Theorem 4.3.1 (`thm:Renyisym`, line 6130).

Renner Theorem 4.3.1 states the bound with assembled additive constant `+4`; the
repo's library-faithful per-block correction `δ'` carries `+4` (vs Renner's `+3`),
which forces the assembled constant to `+5` for the aggregation chain to close:
```
δ := (5/2 · Hmax(ρ_X) + 5) · √(2 · log(4/ε) / n + h(r/n))
```
where `Hmax(ρ_X) ≤ log|X|` for classical ρ_X.

For the BB84 main security theorem (Table `tab:sec`, line 8176), the
formula is instantiated with `Hmax(ρ_X) = log|X|` and the smoothing
parameter shifted to `log(18/ε)`:
```
distvN := (5/2 · log|X| + 5) · √(h(r/n) + 2/n · log(18/ε))
```

Both forms are defined below.
-/

/-- AEP correction term from Renner Theorem 4.3.1 (`thm:Renyisym`, line 6130).

    For a CQ channel with classical output alphabet size alphabetSize, block
    count `n`, symmetric-subspace defect `r`, and smoothing radius `ε > 0`:
      `aep_correction_distvN alphabetSize n r ε`
    `:= (5/2 · log(alphabetSize) + 5) · √(2 · log(4/ε) / n + h(r/n))`

    The assembled additive constant is `+5`: the per-block correction `δ'`
    contributes `+4` (its library-faithful prefactor), and Renner's `c ≤ √c`,
    `h ≤ √h` absorptions contribute the remaining `+1`. (Renner's published `+4`
    arises from a `+3` per-block correction; the repo's `δ'` is `+4`, so the
    assembled constant is `+5`.)

    This is the correction `δ` in the Renner AEP:
      `(1/n) · Hmin^ε ≥ H(σ_{XB}) - H(σ_B) - δ`.

    Theorem 4.3.1 states `Hmax(ρ_X) ≤ log|X|` for classical ρ_X; here we
    substitute `log(alphabetSize)` for `Hmax(ρ_X)` directly, giving the
    maximal correction (worst-case classical alphabet).

    All terms are **base-2** (bits), matching the bit-valued `smoothMinEntropy`
    (with base-2 entropy floors) and the bit-normalized i.i.d. AEP route
    `InfoTheory.SmoothMinEntropy.smoothMinEntropy_tensorPower_ge_classical_aep_floor`.
    Renner's `Hmax(ρ_X) ≤ log₂|X|`
    and his `h(·)` (`binaryEntropyBits`, base-2, `h(1/2)=1`) are base-2; the
    smoothing term `log₂(4/ε)/n` uses `Real.logb 2`. -/
noncomputable def aep_correction_distvN (alphabetSize : ℕ) (n r : ℕ) (ε : ℝ) : ℝ :=
  (5 / 2 * Real.logb 2 alphabetSize + 5) *
    Real.sqrt (binaryEntropyBits (r / n) + 2 / n * Real.logb 2 (4 / ε))

/-- BB84 main-theorem instantiation of the AEP correction (Table `tab:sec`,
    Renner thesis line 8176):
      `(5/2 · log|X| + 5) · √(h(r/n) + 2/n · log(18/ε))`

    This form appears directly in the BB84 security proof where the global
    smoothing parameter `ε` absorbs the factor `9/2` relative to the basic
    Theorem 4.3.1 form (`log₂(4/ε)` vs `log₂(18/ε)`). All terms are **base-2**
    (bits), as in `aep_correction_distvN`: `Hmax(ρ_X) ≤ log₂|X|`, `h(·)` is the
    base-2 binary entropy `binaryEntropyBits`, and the smoothing term uses
    `Real.logb 2`. -/
noncomputable def aep_correction_distvN_tab (alphabetSize : ℕ) (n r : ℕ) (ε : ℝ) : ℝ :=
  (5 / 2 * Real.logb 2 alphabetSize + 5) *
    Real.sqrt (binaryEntropyBits (r / n) + 2 / n * Real.logb 2 (18 / ε))

/-- Per-component AEP correction `δ'` from Renner Theorem 4.3.1 (`thm:Renyisym`,
    main.tex:6288–6289):
      `aep_correction_perComponent alphabetSize m ε`
    `:= (2 · log₂(alphabetSize) + 4) · √((log₂(1/ε) + 1) / m)`.

    This is the i.i.d.-block correction `δ'` controlling the `m = n−r` product copies
    `σ_{XB}^{⊗m}` in Renner's eq `Hinfreps` (main.tex:6280–6289): the per-component
    smooth min-entropy obeys
    `Hmin^{ε}(σ_{XB}^{⊗m} | σ_B^{⊗m}) ≥ m·((H(σ_XB) − H(σ_B))/log 2 − δ')`.

    It is exactly the library penalty `δ_iidAEP_class` (Renner
    `cor:Hmincondrepclass`) under the substitution `Hmax(ρ_X) ≤ log₂(alphabetSize)`:
    its second factor is the library `noiseFactor m ε = √((log₂(1/ε)+1)/m)`, and the
    `+4` prefactor constant matches `δ_iidAEP_class = (2·Hmax + 4)·noiseFactor`
    (clean elementary bound). **All terms are base-2 (bits)**:
    the bit-normalized i.i.d. AEP
    `InfoTheory.SmoothMinEntropy.smoothMinEntropy_tensorPower_ge_classical_aep_floor`
    delivers a bit-valued leading term against
    the bit-valued `smoothMinEntropy`, so the per-component correction must be base-2
    as well. A nats/+3 form is strictly smaller than the library penalty
    and does not satisfy the per-component bound.

    Its shape `(2·Hmax + 4)·√((log₂(1/ε)+1)/m)` is **distinct** from
    `aep_correction_distvN` (which has prefactor `5/2·Hmax + 4` and the AEP shape
    `√(h(r/n) + 2·log₂(4/ε)/n)`); the latter is the *assembled* total correction `δ`,
    not the per-block correction `δ'`.

    The product correction `m·δ' = (2·Hmax+4)·√(m·(log₂(1/ε)+1))` carries an intrinsic
    `√m = √(n−r)` scaling: this is the `√(n−r)`-scaling redistributed in Renner's
    assembly (main.tex:6299–6315) so that the `n·h(r/n)` from
    `log₂(1/ε') ≤ log₂(2/ε) + log₂ 6 + n·h(r/n)` (eq `epspbound`, main.tex:6220) merges
    into the total correction's square root. -/
noncomputable def aep_correction_perComponent (alphabetSize : ℕ) (m : ℕ) (ε : ℝ) : ℝ :=
  (2 * Real.logb 2 alphabetSize + 4) *
    InfoTheory.SmoothMinEntropy.noiseFactor m ε

/-- The classical max-entropy `H_max(ρ_X) = log₂(classicalRank ρ)` of a normalized
    CQ state is bounded above by `log₂` of the size of its classical register: the
    support of the classical distribution has at most `|X|` elements. -/
lemma cqState_classicalHmax_le_logb_card
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    ρ.classicalHmax (ρ.classicalRank_filter_pos hρ_norm) ≤ Real.logb 2 (Fintype.card X) := by
  rw [InfoTheory.SmoothMinEntropy.CQState.classicalHmax]
  have hpos : (0 : ℝ) < (ρ.classicalRank : ℝ) := by
    have := InfoTheory.SmoothMinEntropy.CQState.classicalRank_filter_pos ρ hρ_norm
    have h1 : 1 ≤ ρ.classicalRank := this
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  have hle : (ρ.classicalRank : ℝ) ≤ (Fintype.card X : ℝ) := by
    have : ρ.classicalRank ≤ Fintype.card X := by
      rw [InfoTheory.SmoothMinEntropy.CQState.classicalRank]
      exact le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ)
    exact_mod_cast this
  gcongr
  norm_num

/-- The library penalty `δ_iidAEP_class` of the single-round CQ state
    `σ_XB_cq` (which uses `H_max(ρ_X) = log₂(classicalRank)`) is bounded above by the
    AEP per-component correction `aep_correction_perComponent dX` (which uses the
    cruder `log₂ dX`). Both share the same `noiseFactor m ε` right factor, so the
    bound reduces to `classicalHmax ≤ log₂ dX`. -/
lemma δ_iidAEP_class_le_aep_correction_perComponent
    {dX dB : ℕ} [NeZero dB] [Nonempty (Fin dX)]
    (σ_XB_cq : CQState (Fin dX) dB)
    (hρ_norm : ∑ x : Fin dX, (σ_XB_cq.stateMap x).trace = 1)
    (m : ℕ) (ε : ℝ) :
    InfoTheory.SmoothMinEntropy.δ_iidAEP_class σ_XB_cq m ε ≤
      aep_correction_perComponent dX m ε := by
  rw [InfoTheory.SmoothMinEntropy.δ_iidAEP_class, aep_correction_perComponent]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hHmax := cqState_classicalHmax_le_logb_card σ_XB_cq hρ_norm
  unfold CQState.classicalHmax at hHmax
  rw [Fintype.card_fin] at hHmax
  linarith

/-!
## Properties of the AEP correction

Basic bounds needed by downstream theorems, following from monotonicity of
`Real.sqrt` and nonnegativity of binary entropy.
-/

/-- The AEP correction `aep_correction_distvN` is nonneg whenever
    `alphabetSize ≥ 1`, for every `n`, `r` and `ε`.

    Proof: the prefactor `5/2 · log(d) + 5 ≥ 0` for `d ≥ 1`, and the second factor is a
    square root, hence nonnegative whatever its argument. -/
theorem aep_correction_distvN_nonneg
    (alphabetSize : ℕ) (n r : ℕ)
    (ε : ℝ)
    (hAlpha : 1 ≤ alphabetSize) :
    0 ≤ aep_correction_distvN alphabetSize n r ε := by
  unfold aep_correction_distvN
  apply mul_nonneg
  · have hlog : 0 ≤ Real.logb 2 alphabetSize :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hAlpha)
    linarith
  · exact Real.sqrt_nonneg _

/-- The AEP correction `aep_correction_distvN_tab` is nonneg whenever
    `alphabetSize ≥ 1`, for every `n`, `r` and `ε`.

    Same proof structure as `aep_correction_distvN_nonneg`, with `18`
    replacing `4`. -/
theorem aep_correction_distvN_tab_nonneg
    (alphabetSize : ℕ) (n r : ℕ)
    (ε : ℝ)
    (hAlpha : 1 ≤ alphabetSize) :
    0 ≤ aep_correction_distvN_tab alphabetSize n r ε := by
  unfold aep_correction_distvN_tab
  apply mul_nonneg
  · have hlog : 0 ≤ Real.logb 2 alphabetSize :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hAlpha)
    linarith
  · exact Real.sqrt_nonneg _

/-- The correction `aep_correction_distvN` is bounded above in terms of
    the block count `n`: as `n → ∞` with `r/n → 0`, it converges to 0.

    Formally, at `r = 0`: for every fixed `alphabetSize` and `ε`,
    `aep_correction_distvN alphabetSize n 0 ε → 0` (no sign conditions are needed; the
    prefactor and `log₂(4/ε)` are constants in `n`).

    This is the content needed for the asymptotic key-rate positivity
    argument. -/
theorem aep_correction_distvN_tendsto_zero
    (alphabetSize : ℕ) (ε : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => aep_correction_distvN alphabetSize n 0 ε)
      Filter.atTop
      (nhds 0) := by
  unfold aep_correction_distvN
  -- Inner argument: `2/n * logb 2 (4/ε) → 0`
  have hinner : Filter.Tendsto
      (fun n : ℕ => (2:ℝ) / (n:ℕ) * Real.logb 2 (4 / ε)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1:ℝ) / (n:ℕ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h1 := h0.const_mul (2 * Real.logb 2 (4 / ε))
    simp only [mul_zero] at h1
    refine h1.congr (fun n => ?_)
    ring
  -- Compose with the continuous square root, then with the constant prefactor.
  have hsqrt : Filter.Tendsto
      (fun n : ℕ => Real.sqrt (2 / (n:ℕ) * Real.logb 2 (4 / ε))) Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hinner
    simp only [Real.sqrt_zero] at this
    exact this
  have hfinal := hsqrt.const_mul (5 / 2 * Real.logb 2 alphabetSize + 5)
  simp only [mul_zero] at hfinal
  refine hfinal.congr (fun n => ?_)
  simp [binaryEntropyBits_zero]

/-- Comparison: `aep_correction_distvN ≤ aep_correction_distvN_tab`.

    The two forms differ only in the `log(4/ε)` vs `log(18/ε)` factor inside
    the square root. Since `18 > 4`, `distvN_tab ≥ distvN`; this lemma records
    the monotonicity for accounting in the BB84 security proof. -/
theorem aep_correction_distvN_tab_ge_distvN
    (alphabetSize : ℕ) (n r : ℕ) (ε : ℝ)
    (hε_pos : 0 < ε) :
    aep_correction_distvN alphabetSize n r ε ≤
      aep_correction_distvN_tab alphabetSize n r ε := by
  unfold aep_correction_distvN aep_correction_distvN_tab
  apply mul_le_mul_of_nonneg_left
  · apply Real.sqrt_le_sqrt
    have hn : (0 : ℝ) ≤ 2 / n := by positivity
    have hlog : Real.logb 2 (4 / ε) ≤ Real.logb 2 (18 / ε) := by
      gcongr <;> [norm_num; norm_num]
    nlinarith [mul_le_mul_of_nonneg_left hlog hn]
  · have hlog : 0 ≤ Real.logb 2 alphabetSize := by
      rcases Nat.eq_zero_or_pos alphabetSize with h | h
      · simp [h]
      · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)
    linarith

/-!
## Symmetric subspace AEP — core theorem

The main AEP inequality (Renner Theorem 4.3.1, `thm:Renyisym`).

### Encoding the hypothesis "ρ_n lies in the symmetric subspace along |θ⟩^{⊗(n−r)}"

Renner's `SymR(ℋ, n, θ, n−r)` is the symmetric subspace of `ℋ^{⊗n}` spanned
by vectors of the form `Sym(|θ⟩^{⊗(n−r)} ⊗ |ψ⟩)` for arbitrary `|ψ⟩ ∈ ℋ^{⊗r}`.

The project's `SymmetricSubspace.lean` defines the full symmetric subspace
projector `symmetricProjector d n : Op (d^n)`. The restricted symmetric
subspace `SymR(ℋ, n, θ, n−r)` is contained in the full symmetric subspace
(since the symmetric subspace projector acts as the identity on it), and the
key property used in the proof of `thm:Renyisym` is:

  (a) `|Ψ⟩` decomposes as `Σ_s γ_s |Ψ^s⟩` with each `|Ψ^s⟩` of the form
      `|θ⟩^{⊗(n−r)} ⊗ |ψ̂^s⟩` (up to reordering), and `|S| ≤ 2^{n·h(r/n)}`.

The witness structure below takes this decomposition as a hypothesis, spelled out
as a `Finset`-indexed family of normalized vectors satisfying these structural
properties. The full project-level definition of `SymR` is left to a future
infrastructure file.
-/

/-- Hypothesis package for the symmetric AEP: witnesses that a normalized
    pure state `|Ψ⟩ ∈ (ℂ^d)^{⊗n}` lies in the restricted symmetric
    subspace `SymR(ℂ^d, n, θ, n−r)`.

    Following Renner Theorem 4.3.1 proof (lines 6135–6145), the key
    combinatorial fact used is the decomposition into a family `{|Ψ^s⟩}_{s ∈ S}` of
    at most `2^{n·h(r/n)}` orthonormal vectors, each of the form
    `|θ⟩^{⊗(n−r)} ⊗ |ψ̂^s⟩` (up to permutation), with `|Ψ⟩ = Σ_s γ_s |Ψ^s⟩`.

    This structure is encoded here as explicit Lean data:
    - `S` — the finite index set for the decomposition.
    - `hS_card` — the cardinality bound `|S| ≤ 2^{n·h(r/n)}` in bits (`h = binaryEntropyBits`).
    - `basis_vecs` — the orthonormal basis vectors `{|Ψ^s⟩}_{s ∈ S}`.
    - `coefficients` — the coefficients `{γ_s}`.
    - `hcoeffs_norm` — normalization `Σ_s |γ_s|^2 = 1`.
    - `hdecomp` — the decomposition `|Ψ⟩ = Σ_s γ_s |Ψ^s⟩`.
    - `horthonormal` — orthonormality of the basis.
    - `hprod_form` — each `|Ψ^s⟩` has the tensor-product-along-θ form.

    The `hprod_form` hypothesis is the structural key: it says that after
    some permutation `perm_s` of the `n` tensor factors, each `|Ψ^s⟩` splits as
    `|θ⟩^{⊗(n−r)} ⊗ |ψ̂^s⟩`. In the Lean encoding, this is the existence of a
    per-component permutation `perm_s : Equiv.Perm (Fin n)` and a `tail_s : Ket (d^r)`
    such that `|Ψ^s⟩ = U_{perm_s} (|θ⟩^{⊗(n−r)} ⊗ |ψ̂^s⟩)` (after the dimension
    reindexing), i.e. each `|Ψ^s⟩` is a vector from Renner's `Vrep` set
    (`main.tex:5195`, eq:Vrepdef): a *permuted* product placing `θ` in **any** `n−r`
    of the `n` slots. This matches the membership generators of `InRestrictedSymSpace`
    exactly.

    The per-component permutation is load-bearing: the no-permutation restriction
    (`perm_s = id`, `θ` pinned to the first `n−r` slots) is strictly stronger than
    `Vrep` and collapses the orthonormal family into the single `d^r`-dimensional
    product line `θ^{⊗(n−r)} ⊗ (ℂ^d)^{⊗r}`. Under that encoding the family could carry
    at most `d^r` orthonormal vectors (not the genuine `C(n, n−r)` count of
    `lem:symspacebin`), and a generic member of `SymR` — e.g. `θ⊗a + b⊗θ` with `b ⊥ θ`
    at `n = 2`, `r = 1`, whose `b⊗θ` term lies outside `θ ⊗ ℂ^d` — admits **no** such
    witness at all. Requiring the permutation restores Renner's genuine binomial-superposition
    family.

    This structure is NOT a `Classical.choose` construction; all fields are
    explicit witnesses supplied by the caller. -/
structure RestrictedSymSpaceWitness (d n r : ℕ) [NeZero d] [NeZero (d ^ n)]
    (θ : NormKet d) (Ψ : NormKet (d ^ n)) where
  /-- Finite index set for the orthonormal decomposition. -/
  S : Finset ℕ
  /-- Cardinality bound: `|S| ≤ 2^{n · h(r/n)}` with `h = binaryEntropyBits`
      (base-2 binary entropy), stated as a real-valued inequality on the
      cardinality. This is the clean Hartley/binomial bound from Lemma
      `lem:symspacebin` (Renner thesis, main.tex:6137), `|S| ≤ 2^{n h(r/n)}`,
      with no ceiling slack. It is instantiable at the genuine binomial count
      `S.card = C(n, r)` since `C(n, r) ≤ 2^{n · binaryEntropyBits(r/n)}` holds
      for all `0 ≤ r ≤ n` (the standard base-2 Hartley bound). -/
  hS_card : (S.card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits (r / (n : ℝ)))
  /-- Orthonormal basis vectors for the restricted symmetric subspace. -/
  basis_vecs : ℕ → NormKet (d ^ n)
  /-- Coefficients of the decomposition. -/
  coefficients : ℕ → ℂ
  /-- Normalization: the squared moduli of the coefficients sum to 1. -/
  hcoeffs_norm : ∑ s ∈ S, Complex.normSq (coefficients s) = 1
  /-- Decomposition: |Ψ⟩ = ∑_{s ∈ S} γ_s · |Ψ^s⟩. -/
  hdecomp : Ψ.toKet.vec = ∑ s ∈ S, (coefficients s) • (basis_vecs s).toKet.vec
  /-- Orthonormality: ⟨Ψ^s | Ψ^t⟩ = δ_{st}. -/
  horthonormal : ∀ s ∈ S, ∀ t ∈ S,
    Ket.realInner (basis_vecs s).toKet (basis_vecs t).toKet =
    if s = t then 1 else 0
  /-- Tensor-product-along-θ form: each |Ψ^s⟩, after a per-component permutation
      `perm_s` of the `n` tensor factors, decomposes as |θ⟩^{⊗(n−r)} ⊗ |ψ̂^s⟩ for some
      normalized tail |ψ̂^s⟩ ∈ (ℂ^d)^{⊗r}; i.e. `|Ψ^s⟩ = U_{perm_s} (θ^{⊗(n−r)} ⊗ tail_s)`
      is a vector from Renner's `Vrep` set (`main.tex:5195`, eq:Vrepdef): `θ` placed in
      **any** `n−r` of the `n` slots.

      We assert this via existence of the permutation `perm_s`, the tail vector, and a
      dimension-compatibility proof. `tensorPowVec θ.toKet.vec : Fin (d^(n-r)) → ℂ` gives
      the (n−r)-fold tensor power of the reference vector; `Ket.tensor` then concatenates
      with the tail; `permutationRepresentation d n perm_s` permutes the `n` factors. The
      Lean encoding uses `Ket.cast` for the dimension equation `d^(n-r) * d^r = d^n`, which
      holds by `Nat.pow_add` (when `n-r + r = n`, guaranteed by `hr_le`). -/
  hprod_form : ∀ s ∈ S,
    ∃ (perm_s : Equiv.Perm (Fin n)) (tail_s : NormKet (d ^ r))
      (h_dim : d ^ (n - r) * d ^ r = d ^ n),
      let θ_pow : Ket (d ^ (n - r)) := ⟨Quantum.TensorProducts.tensorPowVec θ.toKet.vec⟩
      (basis_vecs s).toKet.vec =
        (Math.RepresentationTheory.permutationRepresentation d n perm_s).mulVec
          (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor θ_pow tail_s.toKet)).vec

/-- **Membership in the restricted symmetric subspace `SymR(ℂ^d, n, θ, n−r)`.**

The Renner antecedent of `lem:symspacebin` (arXiv:quant-ph/0512258,
`main.tex:5298-5304`): a normalized pure state `|Ψ⟩ ∈ (ℂ^d)^{⊗n}` lies in the
restricted symmetric subspace `SymR(ℂ^d, n, θ, n−r)` iff it is a (finite) linear
combination of **permuted** product generators
`U_{π_t} (|θ⟩^{⊗(n−r)} ⊗ |tail_t⟩)`, with `|tail_t⟩ ∈ (ℂ^d)^{⊗r}` and
`π_t : Equiv.Perm (Fin n)` a per-component permutation of the `n` tensor factors
(`U_π = permutationRepresentation d n π`). The permutation `π_t` places the
distinguished letter `θ` in **any** `n−r` of the `n` slots — exactly the thesis
"`θ` in any `n−r` of the `n` tensor slots, up to a permutation"
(`main.tex:5298-5304`), so the orthonormal family `lem:symspacebin` produces is indexed
by the `(n−r)`-subsets and has the genuine combinatorial size `C(n, n−r)`.

The no-permutation restriction (every generator with `θ` pinned to the *first*
`n−r` factors) is strictly stronger than the thesis and **collapses `SymR` to a single
product line**: every member shares the identical left factor `θ^{⊗(n−r)}`, so the
factored sum was itself a single product vector. Under that encoding `lem:symspacebin`
admitted a trivial **singleton** witness (`|S| = 1`, no `C(n, n−r)` content, no
`|S|`-penalty), which is not the lemma's content. Requiring a per-component permutation
restores the genuine binomial-superposition antecedent.

This is strictly **weaker** than `RestrictedSymSpaceWitness`: it asserts span
membership only (no orthonormality, no cardinality bound, no normalization of
coefficients). It is the genuine load-bearing antecedent that `lem:symspacebin`
turns into the full witness, and that the worst case `r = 0` of an *unconditioned*
witness claim violates: at `r = 0` membership forces `|Ψ⟩ = γ·U_π|θ⟩^{⊗n}` for some `π`,
which a fixed normalized purification does not satisfy for arbitrary `θ`. Hence the
witness existence must take this membership as a hypothesis.

`InRestrictedSymSpace` is an explicit `Prop` (a `∃` over honest witness data: an index
`Finset`, generating coefficients, per-component permutations, and tail vectors); it is
**not** a `Classical.choose` object. -/
def InRestrictedSymSpace (d n r : ℕ) [NeZero d] [NeZero (d ^ n)]
    (θ : NormKet d) (Ψ : NormKet (d ^ n)) : Prop :=
  ∃ (T : Finset ℕ) (coeffs : ℕ → ℂ) (perms : ℕ → Equiv.Perm (Fin n))
    (tails : ℕ → NormKet (d ^ r))
    (h_dim : d ^ (n - r) * d ^ r = d ^ n),
    Ψ.toKet.vec =
      ∑ t ∈ T, coeffs t •
        (Math.RepresentationTheory.permutationRepresentation d n (perms t)).mulVec
          (Ket.cast h_dim
            (Quantum.TensorProducts.Ket.tensor
              (⟨Quantum.TensorProducts.tensorPowVec θ.toKet.vec⟩ : Ket (d ^ (n - r)))
              (tails t).toKet)).vec

/-- A `RestrictedSymSpaceWitness` certifies membership in the restricted symmetric
subspace `SymR(ℂ^d, n, θ, n−r)`: the witness's orthonormal decomposition
`|Ψ⟩ = Σ_s γ_s |Ψ^s⟩` with each `|Ψ^s⟩ = U_{perm_s}(|θ⟩^{⊗(n−r)} ⊗ tail_s)` of permuted
product form (`hprod_form`) is, in particular, a span representation of the membership
predicate `InRestrictedSymSpace`: it reuses the witness's own per-component permutations
`perm_s` and tails `tail_s` as the membership generators. (The converse — `lem:symspacebin`,
turning membership into the orthonormal witness with the genuine `C(n, n−r)` count — is the
combinatorial content, not this lemma.) -/
theorem RestrictedSymSpaceWitness.inRestrictedSymSpace
    {d n r : ℕ} [NeZero d] [NeZero (d ^ n)]
    {θ : NormKet d} {Ψ : NormKet (d ^ n)}
    (symWit : RestrictedSymSpaceWitness d n r θ Ψ) :
    InRestrictedSymSpace d n r θ Ψ := by
  classical
  have hSne : symWit.S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := symWit.hcoeffs_norm
    rw [h, Finset.sum_empty] at this
    exact one_ne_zero this.symm
  obtain ⟨s0, hs0⟩ := hSne
  obtain ⟨perm0, tail0, hdim0, _⟩ := symWit.hprod_form s0 hs0
  choose perms tails hdims heqs using
    fun s (hs : s ∈ symWit.S) => symWit.hprod_form s hs
  refine ⟨symWit.S, symWit.coefficients,
    fun s => if hs : s ∈ symWit.S then perms s hs else perm0,
    fun s => if hs : s ∈ symWit.S then tails s hs else tail0, hdim0, ?_⟩
  rw [symWit.hdecomp]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  congr 1
  rw [heqs s hs]
  simp only [dif_pos hs]

/-!
## Main AEP theorem

The symmetric-subspace AEP lower bound on smooth conditional min-entropy,
Renner Theorem 4.3.1 (`thm:Renyisym`).
-/

/-- Single-copy conditional von Neumann entropy: H(σ_{XB}) - H(σ_B).

    For a CQ state `σ_{XB}` with classical register X, this equals the
    conditional von Neumann entropy H(X|B)_σ = H(σ_{XB}) - H(σ_B).

    This is the "per-round" entropy quantity appearing in the AEP bound.
    We express it via the project's `vonNeumannEntropy` on the joint density
    and on the B-marginal density.

    Requires `NeZero dB` (the B-system has positive dimension) and that
    `dX * dB > 0` (so DensityOp of the joint system is sensible). -/
noncomputable def cqConditionalVNEntropy {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) : ℝ :=
  vonNeumannEntropy σ_XB -
    vonNeumannEntropy (DensityOp.partialTraceA σ_XB)

/-- The per-round conditional von Neumann entropy `H(σ_XB) − H(σ_B)` **in bits**:
    `cqConditionalVNEntropy σ_XB / Real.log 2`.

    `cqConditionalVNEntropy` (and `vonNeumannEntropy`) are nat-valued, but the
    project's `smoothMinEntropy` is bit-valued (with base-2 entropy floors). This bit conversion is
    the leading term delivered by the bit-normalized i.i.d. AEP route
    `InfoTheory.SmoothMinEntropy.smoothMinEntropy_tensorPower_ge_classical_aep_floor`,
    whose conclusion's leading term is `n_copies · (H(ρ_XB) − H(ρ_B))/Real.log 2`.
    It is the bit-valued leading term of the symmetric AEP bound. -/
noncomputable def cqConditionalVNEntropyBits {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) : ℝ :=
  cqConditionalVNEntropy σ_XB / Real.log 2

/-!
## CQ channel image witness

Renner Theorem 4.3.1 fixes a single trace-preserving CPM `𝒩 : ℋ → ℋ_X ⊗ ℋ_B`
that is classical on `ℋ_X`, and defines

  `σ_{XB} := 𝒩(|θ⟩⟨θ|)`,   `ρ_{X^n B^n} := 𝒩^{⊗n}(|Ψ⟩⟨Ψ|)`.

If `ρ_n` and `σ_XB` are unrelated, the bound is false: a deterministic `ρ_n` against a
maximally-mixed `σ_XB` is a counterexample. `CQChannelImageWitness` carries the channel as
explicit data (a single `KrausRepresentation chan = 𝒩`) together with both defining image
equations, so `σ_XB` and `ρ_n` are pinned to `θ`, `Ψ` through the same `𝒩`.

The n-round image equation `ρ_n = 𝒩^{⊗n}(|Ψ⟩⟨Ψ|)` uses the explicit n-fold
tensor power `chan.tensorPow n` of the single channel `chan` (constructed with its
completeness relation in the Quantum.Channels.CPTP.TensorPow module), reindexed from output
dimension `(dX·dB)^n` to `dX^n·dB^n` via the natural-number identity `mul_pow`.
There is no free `chanPow`: the n-round channel is forced to be the tensor power
of the single-round channel that also produces `σ_XB`. All fields are explicit
witnesses (no `Classical.choose`).
-/

/-- The single-round CQ output density operator `𝒩(|θ⟩⟨θ|)` produced by an
    explicit Kraus channel `chan : ℋ_d → ℋ_X ⊗ ℋ_B`. This is `σ_{XB}` in
    Renner Theorem 4.3.1. -/
noncomputable def cqChannelImageSingle {d dX dB : ℕ} [NeZero d] [NeZero (dX * dB)]
    (chan : Quantum.Channels.KrausRepresentation d (dX * dB)) (θ : NormKet d) :
    DensityOp (dX * dB) :=
  chan.apply (DensityOp.fromPure θ.toKet θ.normalized)

/-- **X/B regrouping permutation of the n-round output index.**

    The tensor-power channel `chan.tensorPow n : ℋ_{d^n} → ℋ_{(dX·dB)^n}` writes its
    output index in the **interleaved per-round** layout: through
    `finFunctionFinEquiv : Fin ((dX·dB)^n) ≃ (Fin n → Fin (dX·dB))` each round `k`
    carries one digit in `Fin (dX·dB)`, which `finProdFinEquiv : Fin dX × Fin dB ≃
    Fin (dX·dB)` splits into a pair `(x_k, b_k)`. The CQ joint density
    `CQState.toJointDensity` instead reads a **grouped, quantum-first** layout
    `Fin (dB^n · dX^n)`: all the B-digits `(b_0,…,b_{n−1})` form the high block and
    all the X-digits `(x_0,…,x_{n−1})` the low block (Renner main.tex:6184–6190, the
    `X^n B^n` regrouping underlying `ρ̃_{X^n B^n}`).

    `xbRegroupEquiv dX dB n` is exactly the permutation taking the interleaved tuple
    `(x_0,b_0,…,x_{n−1},b_{n−1})` to the grouped pair `((b_0,…,b_{n−1}),(x_0,…,x_{n−1}))`,
    composed of:
    1. `finFunctionFinEquiv.symm` — unpack `Fin ((dX·dB)^n)` to `Fin n → Fin (dX·dB)`;
    2. `Equiv.piCongrRight (fun _ => finProdFinEquiv.symm)` — split each round digit
       into `(x_k, b_k) ∈ Fin dX × Fin dB`;
    3. `Equiv.arrowProdEquivProdArrow` — regroup to `(Fin n → Fin dX) × (Fin n → Fin dB)`;
    4. `Equiv.prodComm` — put the B-block first (quantum-first, matching
       `CQState.toJointDensity`);
    5. `Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv` — pack each block to
       `Fin (dB^n)`, `Fin (dX^n)`;
    6. `finProdFinEquiv` — pack the pair to `Fin (dB^n · dX^n)`.

    A bare `finCongr`/`castOutput` along `(dX·dB)^n = dX^n·dB^n` is **not** this map: it
    is a linear-index cast that does not commute the interleaved digits into blocks, so
    the witness field `hρ_image` must read through this named permutation, not a cast. -/
noncomputable def xbRegroupEquiv (dX dB n : ℕ) :
    Fin ((dX * dB) ^ n) ≃ Fin (dB ^ n * dX ^ n) :=
  (finFunctionFinEquiv (m := dX * dB) (n := n)).symm.trans <|
    (Equiv.piCongrRight (fun _ : Fin n =>
        (finProdFinEquiv (m := dX) (n := dB)).symm)).trans <|
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin dX) (fun _ => Fin dB)).trans <|
    Equiv.prodComm (Fin n → Fin dX) (Fin n → Fin dB) |>.trans <|
    (Equiv.prodCongr
        (finFunctionFinEquiv (m := dB) (n := n))
        (finFunctionFinEquiv (m := dX) (n := n))).trans
      (finProdFinEquiv (m := dB ^ n) (n := dX ^ n))

/-- Witness pinning the single-round reference `σ_XB` and the n-round output CQ
    state `ρ_n` to `θ`, `Ψ` through a **single** explicit CQ channel `chan = 𝒩`,
    as in Renner Theorem 4.3.1 (`thm:Renyisym`, main.tex:6099, 6122–6123, where a
    single CPM `𝒩` gives both `σ_{XB} = 𝒩(|θ⟩⟨θ|)` and `ρ = 𝒩^{⊗n}(|Ψ⟩⟨Ψ|)`).

    The relation between `σ_XB` and `ρ_n` is necessary: a deterministic `ρ_n` against
    an unrelated maximally-mixed `σ_XB` violates the bound. The n-round channel is **not** a
    free field: it is forced to be the explicit tensor power `chan.tensorPow n`
    (with completeness proved in the Quantum.Channels.CPTP.TensorPow module), so both image
    equations are driven by the same single-round channel. The fields are explicit
    channel data and the two defining image equations, supplied by the caller (the
    future BB84 consumer with its post-measurement CQ channel).

    Fields:
    - `chan` — the single-round CQ channel `𝒩`, classical on `ℋ_X` (a Kraus
      representation `ℋ_d → ℋ_X ⊗ ℋ_B`, i.e. output dimension `dX * dB`).
    - `hσ_image` — the single-round image equation `σ_XB = 𝒩(|θ⟩⟨θ|)`. This ties
      `σ_XB` to `θ` and `𝒩`.
    - `hρ_image` — the n-round image equation `ρ_n's joint density = 𝒩^{⊗n}(|Ψ⟩⟨Ψ|)`,
      where `𝒩^{⊗n} = chan.tensorPow n` is the explicit tensor power of `chan` (cast
      from output dimension `(dX·dB)^n` to `dX^n·dB^n` via `mul_pow`). Written at
      the joint-density-operator level via `CQState.toJointDensity`. This ties
      `ρ_n` to `Ψ` and the tensor power of the *same* `𝒩` that produces `σ_XB`. -/
structure CQChannelImageWitness
    {d dX dB n r : ℕ} [NeZero d] [NeZero dX] [NeZero dB] [NeZero (dX * dB)]
    [NeZero (d ^ n)] [NeZero (dX ^ n)] [NeZero (dB ^ n)] [NeZero (dX ^ r)] [NeZero (dB ^ r)]
    [NeZero (dX ^ n * dB ^ n)]
    (θ : NormKet d) (Ψ : NormKet (d ^ n))
    (symWit : RestrictedSymSpaceWitness d n r θ Ψ)
    (σ_XB : DensityOp (dX * dB))
    (ρ_n : CQState (Fin (dX ^ n)) (dB ^ n))
    (σ_ref : SubDensityOp (dB ^ n))
    (ε : ℝ) where
  /-- The single-round CQ channel `𝒩 : ℋ_d → ℋ_X ⊗ ℋ_B`. -/
  chan : Quantum.Channels.KrausRepresentation d (dX * dB)
  /-- Single-round image equation: `σ_XB = 𝒩(|θ⟩⟨θ|)`. -/
  hσ_image : σ_XB = cqChannelImageSingle chan θ
  /-- n-round image equation: the joint density operator of `ρ_n` equals the
      image `𝒩^{⊗n}(|Ψ⟩⟨Ψ|)`, where `𝒩^{⊗n} = chan.tensorPow n` is the explicit
      tensor power of the single channel `chan` (so the n-round channel is pinned,
      not free).

      The tensor-power output index `Fin ((dX·dB)^n)` is in the **interleaved**
      per-round `(x_k, b_k)` layout; the regrouping into the **grouped**
      `(B-block, X-block)` layout `Fin (dB^n · dX^n)` read by
      `CQState.toJointDensity` is performed by the named permutation `xbRegroupEquiv`
      (see its docstring), reindexing `Fin ((dX·dB)^n) → Fin (dB^n · dX^n) =
      Fin (dB^n · card (Fin (dX^n)))`. A bare linear-index cast cannot effect this
      interleaved→grouped regrouping; reading through `xbRegroupEquiv` is what makes
      the witness constructible by the intended BB84 consumer. -/
  hρ_image :
    ρ_n.toJointDensity.toOp =
      Matrix.reindex
        ((xbRegroupEquiv dX dB n).trans
          (finCongr (by rw [Fintype.card_fin] :
            dB ^ n * dX ^ n = dB ^ n * Fintype.card (Fin (dX ^ n)))))
        ((xbRegroupEquiv dX dB n).trans
          (finCongr (by rw [Fintype.card_fin] :
            dB ^ n * dX ^ n = dB ^ n * Fintype.card (Fin (dX ^ n)))))
        ((chan.tensorPow n).apply
          (DensityOp.fromPure Ψ.toKet Ψ.normalized)).toOp
  /-- Per-component CQ states `ρ̃^s_{X^n B^n}` (Renner main.tex:6184, `ρ̃^s`).
      One CQ state per symmetric-decomposition index `s`, in the same space as
      `ρ_n`. Supplied as explicit data by the consumer (who knows the channel is
      classical on `ℋ_X` and so can write each component as a genuine CQ state);
      pinned to the channel image by `hcomponent_image`. -/
  componentCQ : ℕ → CQState (Fin (dX ^ n)) (dB ^ n)
  /-- Per-component image equation: for each `s ∈ symWit.S`, the joint density of
      `componentCQ s` equals `𝒩^{⊗n}(|Ψ^s⟩⟨Ψ^s|)`, where `|Ψ^s⟩ = symWit.basis_vecs s`
      and `𝒩^{⊗n} = chan.tensorPow n` is the **same** pinned tensor power as in
      `hρ_image`, reindexed interleaved→grouped through `xbRegroupEquiv`. This ties
      each component to the symmetric basis vector and the single channel `chan`. -/
  hcomponent_image : ∀ s ∈ symWit.S,
    (componentCQ s).toJointDensity.toOp =
      Matrix.reindex
        ((xbRegroupEquiv dX dB n).trans
          (finCongr (by rw [Fintype.card_fin] :
            dB ^ n * dX ^ n = dB ^ n * Fintype.card (Fin (dX ^ n)))))
        ((xbRegroupEquiv dX dB n).trans
          (finCongr (by rw [Fintype.card_fin] :
            dB ^ n * dX ^ n = dB ^ n * Fintype.card (Fin (dX ^ n)))))
        ((chan.tensorPow n).apply
          (DensityOp.fromPure (symWit.basis_vecs s).toKet (symWit.basis_vecs s).normalized)).toOp

/-!
## Decomposition lemmas — Part B

The symmetric AEP is proved along Renner's six-step sketch (main.tex:6134–6324).
The new mathematical content is split into the named lemmas below;
the reused infrastructure is cited where it already exists in the library:

- step (1) symmetric decomposition `|Ψ⟩ = Σ_s γ_s |Ψ^s⟩` —
  `RestrictedSymSpaceWitness.hdecomp` (data, reused);
- step (2) **per-component** product structure: for each `s ∈ S`, a lower bound on
  `Hmin^{ε'}(ρ̃^s | σ_B^{⊗n})`
  (stated on the per-component object `componentImage imgWit s`);
- step (3) product-state CQ-AEP (Renner `cor:Hmincondrepclass`, reused);
- step (4) superadditivity + classical nonneg — `smoothMinEntropyReal_tensor_superadditivity`,
  `conditionalMinEntropyReal_classical_extension` (reused);
- step (5) **mixture → component** combination, paying the counting penalty
  `n·h(r/n)` from `|S| ≤ 2^{n·h(r/n)}`
  (consumes the family of per-component bounds via `min over s ∈ S`);
- step (6) correction-term aggregation — `aep_correction_distvN_aggregation`.
-/

/-- **The s-component CQ image `ρ̃^s_{X^n B^n}` (Renner main.tex:6184).**

    Accessor for the per-component CQ state carried by the channel-image witness:
    the CQ state of `𝒩^{⊗n}(|Ψ^s⟩⟨Ψ^s|)` for the `s`-th symmetric basis vector
    `|Ψ^s⟩ = symWit.basis_vecs s`. It lives in the same space as `ρ_n`, and is
    pinned to `chan.tensorPow n` (the same single channel that produces `ρ_n` and
    `σ_XB`) through the witness field `hcomponent_image`. -/
noncomputable def componentImage
    {d dX dB n r : ℕ} [NeZero d] [NeZero dX] [NeZero dB] [NeZero (dX * dB)]
    [NeZero (d ^ n)] [NeZero (dX ^ n)] [NeZero (dB ^ n)]
    [NeZero (dX ^ r)] [NeZero (dB ^ r)] [NeZero (dX ^ n * dB ^ n)]
    {θ : NormKet d} {Ψ : NormKet (d ^ n)}
    {symWit : RestrictedSymSpaceWitness d n r θ Ψ}
    {σ_XB : DensityOp (dX * dB)}
    {ρ_n : CQState (Fin (dX ^ n)) (dB ^ n)}
    {σ_ref : SubDensityOp (dB ^ n)}
    {ε : ℝ}
    (imgWit : CQChannelImageWitness θ Ψ symWit σ_XB ρ_n σ_ref ε)
    (s : ℕ) : CQState (Fin (dX ^ n)) (dB ^ n) :=
  imgWit.componentCQ s

/-- The per-component B-reference `ρ̃^s_{B^n}` (Renner main.tex:6206, 6216).

    In Renner's derivation the per-component min-entropy
    `Hmin^{ε'}(ρ̃^s_{X^n B^n} | ρ̃^s_{B^n})` is taken against the **component's own**
    B-marginal `ρ̃^s_{B^n} := Tr_{X^n}(ρ̃^s_{X^n B^n})`, not against a shared
    reference. This accessor names that per-component reference explicitly as the
    B-marginal (a partial-trace-out of the classical register)
    of the component image `componentImage imgWit s`.

    Renner does **not** pass to a shared reference via a per-component marginal
    equality `ρ̃^s_{B^n} = σ_B^{⊗n}`: that equality is false in general, since the
    full B-marginal of the s-component is `σ_B^{⊗(n−r)} ⊗ ρ̂^s_{B^r}` with an
    s-dependent tail. Instead the per-component bound is established directly at the
    mixture-level shared reference `σ_ref`,
    where the s-dependent r-round tail is dropped via superadditivity
    (`lem:Hminindaddsmooth`) plus classical nonnegativity (`lem:classnn`) — Renner
    eq `Hinfsplit`, main.tex:6243–6273 — never via a marginal equality. -/
noncomputable def componentReference
    {d dX dB n r : ℕ} [NeZero d] [NeZero dX] [NeZero dB] [NeZero (dX * dB)]
    [NeZero (d ^ n)] [NeZero (dX ^ n)] [NeZero (dB ^ n)]
    [NeZero (dX ^ r)] [NeZero (dB ^ r)] [NeZero (dX ^ n * dB ^ n)]
    {θ : NormKet d} {Ψ : NormKet (d ^ n)}
    {symWit : RestrictedSymSpaceWitness d n r θ Ψ}
    {σ_XB : DensityOp (dX * dB)}
    {ρ_n : CQState (Fin (dX ^ n)) (dB ^ n)}
    {σ_ref : SubDensityOp (dB ^ n)}
    {ε : ℝ}
    (imgWit : CQChannelImageWitness θ Ψ symWit σ_XB ρ_n σ_ref ε)
    (s : ℕ) : SubDensityOp (dB ^ n) :=
  (componentImage imgWit s).quantumMarginal

/-- The symmetric-component i.i.d. block floor bounds extended entropy at every positive radius. -/
lemma symmetric_aep_component_iid_lower_bound
    {dX dB : ℕ} [NeZero dX] [NeZero dB]
    (σ_XB : DensityOp (dX * dB)) (σ_XB_cq : CQState (Fin dX) dB)
    (hρ_norm : ∑ x : Fin dX, (σ_XB_cq.stateMap x).trace = 1)
    (hσ_XB_entropy : cqConditionalVNEntropy σ_XB =
      vonNeumannEntropy (σ_XB_cq.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (σ_XB_cq.quantumMarginalDensityOp hρ_norm))
    (m : ℕ) [NeZero m]
    (ε : ℝ) (hε_pos : 0 < ε) :
    ENNReal.ofReal ((m : ℝ) * cqConditionalVNEntropyBits σ_XB
      - (m : ℝ) * aep_correction_perComponent dX m ε) ≤
      smoothMinEntropy ε (CQState.tensorPower σ_XB_cq m)
        (SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp (σ_XB_cq.quantumMarginalDensityOp hρ_norm)) m) := by
  have hiid := smoothMinEntropy_tensorPower_ge_classical_aep_floor
    σ_XB_cq hρ_norm m ε hε_pos
  have hδ := δ_iidAEP_class_le_aep_correction_perComponent σ_XB_cq hρ_norm m ε
  refine (ENNReal.ofReal_le_ofReal ?_).trans hiid
  rw [cqConditionalVNEntropyBits, hσ_XB_entropy, mul_sub]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg m)) _

/-- **`H_min(X|B) ≥ 0` for a CQ state against its own quantum marginal.**

    The scalar `λ = 1` is feasible for `(ρ, ρ_B)`: every classical block
    `ρ.stateMap x` is dominated in the Löwner order by the quantum marginal
    `ρ_B = ∑_y ρ.stateMap y` (`stateMap_opLe_quantumMarginalOp`). Hence
    `minFeasibleLambda ≤ 1`, so `conditionalMinEntropyReal = −log λ*/log 2 ≥ 0`. -/
lemma conditionalMinEntropyReal_quantumMarginal_nonneg
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) :
    0 ≤ conditionalMinEntropyReal ρ ρ.quantumMarginal := by
  have hfeas : isFeasible ρ ρ.quantumMarginal 1 :=
    InfoTheory.SmoothMinEntropy.isFeasible_of_quantumMarginalOp_dominated
      ρ ρ.quantumMarginal zero_le_one
      (by rw [Complex.ofReal_one, one_smul]; intro v; exact le_refl _)
  have hlam_le : minFeasibleLambda ρ ρ.quantumMarginal ≤ 1 :=
    minFeasibleLambda_le_of_isFeasible _ _ hfeas
  have hlam_nn : 0 ≤ minFeasibleLambda ρ ρ.quantumMarginal :=
    minFeasibleLambda_nonneg _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold conditionalMinEntropyReal
  have hlog_le : Real.log (minFeasibleLambda ρ ρ.quantumMarginal) ≤ 0 := by
    rcases eq_or_lt_of_le hlam_nn with h0 | hpos
    · rw [← h0, Real.log_zero]
    · exact Real.log_nonpos hpos.le hlam_le
  exact div_nonneg (by linarith) hlog2.le

/-- `SubDensityOp.trivialOne` (the `ℂ^1` identity sub-density) is positive definite:
    its underlying operator is the `1 × 1` identity matrix. -/
lemma SubDensityOp.trivialOne_posDef : SubDensityOp.trivialOne.toOp.PosDef := by
  have hone : SubDensityOp.trivialOne.toOp = (1 : Op 1) := by
    ext i j
    fin_cases i; fin_cases j
    simp [SubDensityOp.trivialOne, DensityOp.toSubDensityOp, DensityOp.trivial]
  rw [hone]
  exact Matrix.PosDef.one

/-- **Positive-definiteness of the tensor power of a positive-definite reference.**
    The `(n−r)`-fold tensor power `σ_B^{⊗(n−r)}` of a positive-definite single-round
    B-marginal `σ_B` is positive definite (specialization of
    `InfoTheory.SmoothMinEntropy.SubDensityOp.tensorFinProd_posDef` to the constant family). -/
lemma SubDensityOp.tensorPower_posDef {d : ℕ} [NeZero d]
    (σ : SubDensityOp d) (hσ : σ.toOp.PosDef) (m : ℕ) :
    (InfoTheory.SmoothMinEntropy.SubDensityOp.tensorPower σ m).toOp.PosDef :=
  SubDensityOp.tensorFinProd_posDef m (fun _ => σ) (fun _ => hσ)

/-- **Tensor-factor swap `ℂ^X ⊗ ℂ^B → ℂ^B ⊗ ℂ^X` at the index level.**

    `σ_XB : DensityOp (dX * dB)` carries the standard `X ⊗ B` tensor layout, while the
    CQ presentation `σ_XB_cq.toJointDensityOp : DensityOp (dB * Fintype.card (Fin dX))`
    uses the project's quantum-first `B ⊗ X` layout (`CQState.toJointDensity`). This
    equivalence is the corresponding subsystem swap on the flat index: unpack
    `Fin (dB · dX)` to `(b, x)`, swap to `(x, b)`, and repack to `Fin (dX · dB)`,
    absorbing `Fintype.card (Fin dX) = dX` by `finCongr`. It is the index-level data of
    the `dX·dB ↔ dB·dX` operator reindex relating `σ_XB` to its CQ presentation. -/
noncomputable def cqJointSwapEquiv (dX dB : ℕ) :
    Fin (dB * Fintype.card (Fin dX)) ≃ Fin (dX * dB) :=
  (finCongr (by rw [Fintype.card_fin] : dB * Fintype.card (Fin dX) = dB * dX)).trans <|
    (finProdFinEquiv (m := dB) (n := dX)).symm.trans <|
    (Equiv.prodComm (Fin dB) (Fin dX)).trans
      (finProdFinEquiv (m := dX) (n := dB))

/-- **CQ image pin (operator level): `σ_XB` is the `X ⊗ B`-layout of the CQ state
    `σ_XB_cq`, and `σ_B` its B-marginal.**

    The single-round reference `σ_XB : DensityOp (dX·dB)` and its CQ presentation
    `σ_XB_cq : CQState (Fin dX) dB` are the same physical state in two layouts. This
    predicate pins them at the operator level (the entropy-level pin `hσ_XB_entropy`
    is strictly weaker — it does not determine the operators, so it cannot drive the
    tensor-power factorization of Step A):

    - `joint`: `σ_XB.toOp = reindex(swap)(σ_XB_cq.toJointDensityOp).toOp`, the
      `X ⊗ B` operator equal to the swap-reindexed `B ⊗ X` CQ joint density (via
      `cqJointSwapEquiv`);
    - `marginal`: `σ_B.toOp = (σ_XB_cq.quantumMarginalDensityOp).toOp`, the B-marginals
      agree on the nose (both live on `ℂ^B`, no swap needed).

    Supplied by the BB84 consumer, which builds `σ_XB_cq` as the CQ image of its
    classical-on-X measurement channel and so knows both layouts coincide. -/
def CQImagePin {dX dB : ℕ} [NeZero dX] [NeZero dB] [NeZero (dX * dB)]
    (σ_XB : DensityOp (dX * dB)) (σ_XB_cq : CQState (Fin dX) dB)
    (hρ_norm : ∑ x : Fin dX, (σ_XB_cq.stateMap x).trace = 1) : Prop :=
  σ_XB.toOp =
      Matrix.reindex (cqJointSwapEquiv dX dB) (cqJointSwapEquiv dX dB)
        (σ_XB_cq.toJointDensityOp hρ_norm).toOp ∧
    (DensityOp.partialTraceA σ_XB).toOp = (σ_XB_cq.quantumMarginalDensityOp hρ_norm).toOp

end InfoTheory.SmoothMinEntropy.SymmetricAEP

end -- noncomputable section
