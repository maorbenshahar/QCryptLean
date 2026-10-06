import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP
import QCryptLean.Math.Combinatorics.PermutationAction
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Quantum.TensorProducts.KetCast

/-!
# `lem:symspacebin` — the binomial-superposition decomposition of `SymR`

This module is the low-level combinatorial/linear-algebra core of Renner's
`lem:symspacebin` (arXiv:quant-ph/0512258v2, `main.tex:5298-5347`): from a normalized
ket `|Ψ⟩` lying in the restricted symmetric subspace `SymR(ℂ^d, n, θ, n−r)`
(`InfoTheory.SmoothMinEntropy.SymmetricAEP.InRestrictedSymSpace`) it produces a
`RestrictedSymSpaceWitness` — an orthonormal family `{|Ψ^s⟩}_{s∈S}` of `Vrep`
vectors with the genuine Hartley count `|S| ≤ C(n, n−r) ≤ 2^{n·h(r/n)}` and
`|Ψ⟩ ∈ span{|Ψ^s⟩}`.

The top-level result `restrictedSymSpaceWitness_nonempty_of_mem` is a **short assembly**
over four named sub-lemmas, one per stage of Renner's proof (`main.tex:5306-5347`):

* **Stage 1** (`exists_thetaAdaptedKetBasis`): fix a θ-adapted orthonormal basis
  `{|x⟩}_{x∈Fin d}` of `ℂ^d` with a distinguished letter `x̄` so that `|x̄⟩ = |θ⟩`.
  (`main.tex:5307-5308`.) The companion basis-permutation action identity
  `permutationRepresentation_mulVec_tupleProductVec` records `U_π|bx⟩ = |bx∘π⁻¹⟩`.
* **Stage 2** (`inRestrictedSymSpace_computationalBasisExpansion`): expand the membership
  representation in the basis of Stage 1; the permutation content forces the support
  condition `freq(x̄) ≥ n−r`, giving `|Ψ⟩ = Σ_{freq(x̄)≥m} β_bx |bx⟩` (`eq:Psisum`,
  `main.tex:5310-5318`).
* **Stage 3** (`exists_placementAssignment`): group the support tuples by an
  `m`-placement subset `s(bx) ⊆ {k : bx k = x̄}`, obtaining a partition
  `Σ_s |Ψ^s⟩ = |Ψ⟩` over the `C(n,m)`-element index set `placementSubsets n m`
  (`eq:Psisdef`, `main.tex:5320-5328`). The count `|placementSubsets n m| = C(n,m)`
  is `placementSubsets_card`.
* **Stage 4** (`restrictedSymSpaceWitness_of_placementPartition`): each `|Ψ^s⟩` is a
  `Vrep` vector `U_{π_s}(|θ⟩^{⊗m} ⊗ |ψ̂^s⟩)`; distinct subsets give disjoint
  computational-basis supports hence orthogonality `⟨Ψ^s|Ψ^t⟩ = δ_{st}`; Pythagoras +
  normalization assemble the witness (`main.tex:5334-5346`).

The Hartley cardinality leg of the witness (`RestrictedSymSpaceWitness.hS_card`) is
discharged from `placementSubsets_card` together with the sorry-free bound
`Math.ClassicalEntropy.choose_le_two_pow_mul_binaryEntropyBits` and the binary-entropy
symmetry `binaryEntropy_symm` (`h(m/n) = h(r/n)` since `m = n−r`).

## Supporting results

The four stages use:
- `exists_thetaAdaptedKetBasis` (Gram–Schmidt basis extension of `θ`),
- `permutationRepresentation_mulVec_tupleProductVec` (`U_π|bx⟩ = |bx∘π⁻¹⟩`),
- `tupleProductVec_inner` / `tupleProductVec_completeness` (the tuple-product orthonormal
  basis: orthonormality and the resolution-of-identity expansion),
- `tupleProductVec_inner_permutationRepresentation` (the unitary-adjoint move),
- `finFunctionFinEquiv_symm_cast_finProdFinEquiv` / `tupleProductVec_split` /
  `tupleProductVec_inner_cast_tensor_eq_zero` (the mixed-radix slot split feeding the
  Stage 2 frequency-support bound).

Stage 4 (`restrictedSymSpaceWitness_of_placementPartition`) assembles the orthonormal `Vrep`
witness from the placement partition over the proved Stage-4 infrastructure:
- `placementPerm` / `placementPerm_high` / `placementPerm_high_mem` — the explicit per-subset
  permutation `π_s` placing `s` into the high `n−r` slots,
- `subsetVrepTail` / `tupleProductVec_eq_vrep_term` / `subsetPartialVec_eq_vrep` — the `Vrep`
  form `|Ψ^s⟩ = U_{π_s}(θ^{⊗(n−r)} ⊗ tail_s)` (`hprod_form`),
- `subsetPartialVec_inner` — the cross-subset orthogonality `⟨Ψ^s|Ψ^{s'}⟩ = δ`,
- `subsetPartialVec_normSq_sum` — the Pythagoras normalization `Σ|γ_s|² = ‖Ψ‖² = 1`,
- `permutationRepresentation_mulVec_normSq` / `tensorPowVec_normSq_eq_one` /
  `subsetVrepTail_normSq` — the tail normalization `‖tail_s‖² = ‖Ψ^s‖²`,
- `placementSubsets_card` + `choose_le_two_pow_mul_binaryEntropyBits` + `binaryEntropy_symm`
  — the Hartley cardinality `|S| ≤ C(n, n−r) ≤ 2^{n·h(r/n)}`.

The top-level assembly `restrictedSymSpaceWitness_nonempty_of_mem` chains the four stages.
The whole module is `sorry`-free.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open scoped Matrix BigOperators ComplexConjugate

noncomputable section

namespace InfoTheory.SmoothMinEntropy.RestrictedSymSpaceDecomp

/-! ## Explicit combinatorial data -/

/-- **Frequency of the distinguished letter `x̄` in a tensor word `bx`.**
The number of tensor slots `k : Fin n` at which the basis-letter index `bx k` equals the
distinguished letter `x̄`. Renner's `freq_bx(x̄)` (`main.tex:5310`). -/
def thetaFreq {d n : ℕ} (xbar : Fin d) (bx : Fin n → Fin d) : ℕ :=
  (Finset.univ.filter (fun k => bx k = xbar)).card

/-- **Computational-basis tuple ket.** For an indexed family of single-letter kets
`e : Fin d → Ket d` and a tensor word `bx : Fin n → Fin d`, this is the product vector
`|e(bx 0)⟩ ⊗ ⋯ ⊗ |e(bx (n-1))⟩ ∈ ℂ^{d^n}`, the tensor product `tensorFamilyVec` of the family
`k ↦ e (bx k)` in the digit coordinates of `finFunctionFinEquiv`. When every `e (bx k) = θ` it is
`tensorPowVec θ.vec`. Explicit; no `Classical.choose`. -/
def tupleProductVec {d n : ℕ} [NeZero d] (e : Fin d → Ket d) (bx : Fin n → Fin d) :
    Ket (d ^ n) :=
  ⟨tensorFamilyVec fun k => (e (bx k)).vec⟩

/-- **The `m`-placement index set.** The set of all `m`-element subsets of the `n`
tensor slots `Fin n`, i.e. `Finset.powersetCard m univ`. It indexes Renner's orthonormal
`Vrep` family `{|Ψ^s⟩}` (`main.tex:5320`); its cardinality is `C(n, m)`
(`placementSubsets_card`). Explicit. -/
def placementSubsets (n m : ℕ) : Finset (Finset (Fin n)) :=
  Finset.powersetCard m (Finset.univ : Finset (Fin n))

/-- **Per-subset partial sum `|Ψ^s⟩`.** Given coefficients `β`, a placement assignment
`assign : (Fin n → Fin d) → Finset (Fin n)`, and a subset `s`, this is the partial sum
`Σ_{bx : assign bx = s} β_bx |bx⟩` of the computational-basis expansion restricted to the
tuples assigned to `s` (`eq:Psisdef`, `main.tex:5320-5328`). Explicit. -/
def subsetPartialVec {d n : ℕ} [NeZero d] (e : Fin d → Ket d)
    (β : (Fin n → Fin d) → ℂ) (assign : (Fin n → Fin d) → Finset (Fin n))
    (s : Finset (Fin n)) : Ket (d ^ n) :=
  ⟨∑ bx : Fin n → Fin d, if assign bx = s then β bx • (tupleProductVec e bx).vec else 0⟩

/-- **The placement index set has the binomial cardinality `C(n, m)`.** This is the
Hartley count leg of `lem:symspacebin` at the genuine combinatorial size; combined with
`Math.ClassicalEntropy.choose_le_two_pow_mul_binaryEntropyBits` and `binaryEntropy_symm`
it discharges `RestrictedSymSpaceWitness.hS_card`. Proved. -/
theorem placementSubsets_card (n m : ℕ) :
    (placementSubsets n m).card = Nat.choose n m := by
  rw [placementSubsets, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Orthonormality of the tuple-product family.** If `{e i}` is an orthonormal family
in `ℂ^d` (`⟨e i | e j⟩ = δ_{ij}`), the tuple products `{tupleProductVec e bx}` are
orthonormal: `⟨tupleProductVec e bx | tupleProductVec e by⟩ = δ_{bx, by}`. The inner
product of product vectors factors slotwise (`dotProduct_tensorFamilyVec`) into
`∏ k ⟨e (bx k) | e (by k)⟩ = ∏ k δ_{bx k, by k}`. -/
theorem tupleProductVec_inner {d n : ℕ} [NeZero d] (e : Fin d → Ket d)
    (he_on : ∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0)
    (bx by' : Fin n → Fin d) :
    Ket.inner (tupleProductVec e bx) (tupleProductVec e by') =
      if bx = by' then 1 else 0 := by
  classical
  have hinner : ∀ {m : ℕ} (u v : Ket m), Ket.inner u v = star u.vec ⬝ᵥ v.vec := fun u v => by
    simp [Ket.inner, bra_mul_ket_eq, dotProduct, Ket.dag_vec]
  calc Ket.inner (tupleProductVec e bx) (tupleProductVec e by')
      = ∏ k, Ket.inner (e (bx k)) (e (by' k)) := by
        simp only [hinner, tupleProductVec, star_tensorFamilyVec, dotProduct_tensorFamilyVec]
    _ = if bx = by' then 1 else 0 := by
        simp only [he_on, Fintype.prod_boole, funext_iff]
        split_ifs <;> rfl

/-- **Completeness of the tuple-product family.** When `{e i}` is an orthonormal family
in `ℂ^d`, the `d^n` tuple-product vectors `{tupleProductVec e bx}_{bx : Fin n → Fin d}` form
an orthonormal basis of `ℂ^{d^n}`, so any ket `v` expands as
`v = Σ_bx ⟨bx | v⟩ • |bx⟩` (`OrthonormalBasis.sum_repr'`). This is the resolution-of-identity
that turns the membership representation into a computational-basis expansion (Stage 2). -/
theorem tupleProductVec_completeness {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (e : Fin d → Ket d)
    (he_on : ∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0)
    (v : Ket (d ^ n)) :
    v.vec = ∑ bx : Fin n → Fin d,
      (Ket.inner (tupleProductVec e bx) v) • (tupleProductVec e bx).vec := by
  classical
  -- Transport the tuple-product family to `EuclideanSpace ℂ (Fin (d^n))`.
  set E := EuclideanSpace ℂ (Fin (d ^ n))
  set w : (Fin n → Fin d) → E :=
    fun bx => (WithLp.equiv 2 (Fin (d ^ n) → ℂ)).symm (tupleProductVec e bx).vec with hw
  -- The `Ket.inner`/EuclideanSpace bridge (second argument an arbitrary ket).
  have hbridge : ∀ (bx : Fin n → Fin d) (u : Ket (d ^ n)),
      @inner ℂ _ _ (w bx) (WithLp.toLp 2 u.vec)
        = Ket.inner (tupleProductVec e bx) u := by
    intro bx u
    rw [EuclideanSpace.inner_eq_star_dotProduct, Ket.inner, bra_mul_ket_eq]
    simp only [Ket.dag_vec, starRingEnd_apply, dotProduct, hw, WithLp.equiv_symm_apply,
      WithLp.ofLp_toLp, Pi.star_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  -- The family `w` is orthonormal.
  have hortho : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro bx by'
    have : w by' = WithLp.toLp 2 (tupleProductVec e by').vec := by rw [hw]; rfl
    rw [this, hbridge, tupleProductVec_inner e he_on]
  -- Cardinality matches the dimension, so `w` is an orthonormal basis.
  have hcard : Fintype.card (Fin n → Fin d) = Module.finrank ℂ E := by
    rw [finrank_euclideanSpace, Fintype.card_fin, Fintype.card_pi]
    simp
  haveI : Nonempty (Fin n → Fin d) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  let b : OrthonormalBasis (Fin n → Fin d) ℂ E :=
    (basisOfOrthonormalOfCardEqFinrank hortho hcard).toOrthonormalBasis
      (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hortho)
  have hb_coe : ⇑b = w := by
    rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  -- Expand the EuclideanSpace image of `v` in this basis.
  have hexp := b.sum_repr' ((WithLp.equiv 2 (Fin (d ^ n) → ℂ)).symm v.vec)
  rw [hb_coe] at hexp
  -- `hexp : ∑ bx, ⟨w bx, toLp v.vec⟩ • w bx = toLp v.vec`; take `.ofLp` (= the Ket vec).
  have hexp' := congrArg (WithLp.equiv 2 (Fin (d ^ n) → ℂ)) hexp
  simp only [WithLp.equiv_symm_apply, WithLp.equiv_apply] at hexp'
  rw [← hexp', WithLp.ofLp_sum]
  refine Finset.sum_congr rfl (fun bx _ => ?_)
  rw [WithLp.ofLp_smul, hbridge bx v, hw]
  rfl

/-! ## Stage 1 — θ-adapted orthonormal basis -/

/-- **Stage 1: a θ-adapted orthonormal basis of `ℂ^d`** (`main.tex:5307-5308`).

Since `θ` is a unit vector, it extends to an orthonormal basis `{|x⟩}_{x∈Fin d}` of `ℂ^d`
with a distinguished letter `x̄` such that `|x̄⟩ = |θ⟩`. Orthonormality is stated through
the complex ket inner product `⟨x|y⟩ = δ_{xy}` (`Ket.inner`). Proved via Gram–Schmidt
(`InnerProductSpace.gramSchmidtOrthonormalBasis` with `θ` in slot `0`, surviving as
`b 0 = θ` since `‖θ‖ = 1`), transported between `EuclideanSpace ℂ (Fin d)` and the
`Ket` model through `WithLp.equiv` and `EuclideanSpace.inner_eq_star_dotProduct`. -/
theorem exists_thetaAdaptedKetBasis (d : ℕ) [NeZero d] (θ : NormKet d) :
    ∃ (xbar : Fin d) (e : Fin d → Ket d),
      (∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0) ∧
      e xbar = θ.toKet := by
  classical
  haveI : NeZero d := ‹_›
  -- Work in `EuclideanSpace ℂ (Fin d)`, whose inner product matches `Ket.inner`.
  have hn : ∑ i, ‖θ.toKet.vec i‖ ^ 2 = 1 := by
    have hθ := θ.normalized
    unfold Ket.IsNormalized at hθ
    rw [bra_mul_ket_eq] at hθ
    simp only [Ket.dag_vec, starRingEnd_apply] at hθ
    have hre : ∑ i, ‖θ.toKet.vec i‖ ^ 2 = (∑ i, star (θ.toKet.vec i) * θ.toKet.vec i).re := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have : star (θ.toKet.vec i) * θ.toKet.vec i = ((‖θ.toKet.vec i‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [this, Complex.ofReal_re]
    rw [hre, hθ]; simp
  have hθnorm : ‖((WithLp.equiv 2 (Fin d → ℂ)).symm θ.toKet.vec :
      EuclideanSpace ℂ (Fin d))‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : (∑ x, ‖((WithLp.equiv 2 (Fin d → ℂ)).symm θ.toKet.vec).ofLp x‖ ^ 2)
        = ∑ i, ‖θ.toKet.vec i‖ ^ 2 := rfl
    rw [this, hn]; simp
  -- Set up a Gram–Schmidt input with `θ` in slot `0`.
  set v0 : EuclideanSpace ℂ (Fin d) := (WithLp.equiv 2 (Fin d → ℂ)).symm θ.toKet.vec with hv0
  set f : Fin d → EuclideanSpace ℂ (Fin d) :=
    fun i => if i = 0 then v0 else EuclideanSpace.single i (1 : ℂ) with hf
  have hfrank : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = Fintype.card (Fin d) := by
    simp
  set b := InnerProductSpace.gramSchmidtOrthonormalBasis hfrank f with hb
  -- The first basis vector is `θ`, since `‖θ‖ = 1` and `gramSchmidt 0 = f 0`.
  have hgs0 : InnerProductSpace.gramSchmidt ℂ f (0 : Fin d) = v0 := by
    have hbt := InnerProductSpace.gramSchmidt_bot ℂ f
    have hbot : (⊥ : Fin d) = 0 := rfl
    rw [hbot] at hbt
    rw [show InnerProductSpace.gramSchmidt ℂ f (0 : Fin d) = f 0 by
      convert hbt using 3; exact Subsingleton.elim _ _, hf]
    simp
  have hnormed0 : InnerProductSpace.gramSchmidtNormed ℂ f 0 = v0 := by
    rw [InnerProductSpace.gramSchmidtNormed, hgs0, hθnorm]
    simp
  have hnormed0_ne : InnerProductSpace.gramSchmidtNormed ℂ f 0 ≠ 0 := by
    rw [hnormed0]
    intro hcontra
    have : ‖v0‖ = 0 := by rw [hcontra]; simp
    rw [hθnorm] at this; norm_num at this
  have hb0 : b 0 = v0 := by
    rw [hb, InnerProductSpace.gramSchmidtOrthonormalBasis_apply hfrank hnormed0_ne, hnormed0]
  -- Transport `b` to `Ket d` via `WithLp.equiv`.
  refine ⟨0, fun i => ⟨(WithLp.equiv 2 (Fin d → ℂ)) (b i)⟩, ?_, ?_⟩
  · intro i j
    -- `Ket.inner (e i) (e j) = ⟪b i, b j⟫_ℂ = δ_{ij}`.
    have hortho := b.orthonormal
    -- Bridge: the `Ket.inner` sum equals the EuclideanSpace inner product `⟪b i, b j⟫_ℂ`.
    have hbridge : Ket.inner (⟨(WithLp.equiv 2 (Fin d → ℂ)) (b i)⟩ : Ket d)
        (⟨(WithLp.equiv 2 (Fin d → ℂ)) (b j)⟩ : Ket d) = @inner ℂ _ _ (b i) (b j) := by
      rw [Ket.inner, bra_mul_ket_eq]
      simp only [Ket.dag_vec, starRingEnd_apply]
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [WithLp.equiv_apply, Pi.star_apply, mul_comm]
    rw [hbridge]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K, hortho.1 i]
      simp
    · rw [if_neg h, hortho.2 h]
  · ext k
    simp only [hb0, hv0, WithLp.equiv_apply, WithLp.equiv_symm_apply]

/-- **Stage 1 (companion): basis-tuple permutation action** `U_π |bx⟩ = |bx ∘ π⁻¹⟩`
(`main.tex:5311`, used in Stage 4). The permutation representation
`U_π = permutationRepresentation d n π` permutes the tensor factors, sending the
computational-basis tuple ket `tupleProductVec e bx` to `tupleProductVec e (bx ∘ π.symm)`
(the factor at slot `k` becomes `e (bx (π⁻¹ k))`). This is the product-vector permutation law
`permutationRepresentation_mulVec_tensorFamilyVec`. -/
theorem permutationRepresentation_mulVec_tupleProductVec {d n : ℕ} [NeZero d]
    (e : Fin d → Ket d) (π : Equiv.Perm (Fin n)) (bx : Fin n → Fin d) :
    (permutationRepresentation d n π).mulVec (tupleProductVec e bx).vec
      = (tupleProductVec e (bx ∘ π.symm)).vec :=
  permutationRepresentation_mulVec_tensorFamilyVec (fun k => (e (bx k)).vec) π

/-- **Adjoint move for the permutation action under the tuple inner product.**
`⟨tupleProductVec e bx | U_π v⟩ = ⟨tupleProductVec e (bx ∘ π) | v⟩`. Since `U_π` is a
real permutation matrix, its adjoint is `U_{π⁻¹}`, and `U_{π⁻¹}|bx⟩ = |bx ∘ π⟩` by the
companion lemma (`(π⁻¹).symm = π`). -/
theorem tupleProductVec_inner_permutationRepresentation {d n : ℕ} [NeZero d]
    (e : Fin d → Ket d) (π : Equiv.Perm (Fin n)) (bx : Fin n → Fin d) (v : Ket (d ^ n)) :
    Ket.inner (tupleProductVec e bx)
        ⟨(permutationRepresentation d n π).mulVec v.vec⟩
      = Ket.inner (tupleProductVec e (bx ∘ π)) v := by
  classical
  rw [Ket.inner, Ket.inner, bra_mul_ket_eq, bra_mul_ket_eq]
  simp only [Ket.dag_vec, starRingEnd_apply]
  -- Expand the matrix action and swap the order of summation.
  have hswap : (∑ i, star ((tupleProductVec e bx).vec i) *
        (permutationRepresentation d n π).mulVec v.vec i)
      = ∑ j, (∑ i, star ((tupleProductVec e bx).vec i) *
          permutationRepresentation d n π i j) * v.vec j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  rw [hswap]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- The inner coefficient is `conj((U_{π⁻¹}·|bx⟩)_j) = conj(|bx ∘ π⟩_j)`.
  have hadj : (∑ i, star ((tupleProductVec e bx).vec i) *
        permutationRepresentation d n π i j)
      = star ((tupleProductVec e (bx ∘ π)).vec j) := by
    -- Permutation entries are real {0,1}; pull `star` out.
    have hreal : ∀ i, star (permutationRepresentation d n π i j)
        = permutationRepresentation d n π i j := by
      intro i
      simp only [permutationRepresentation, Matrix.of_apply]
      split_ifs <;> simp
    have : (∑ i, star ((tupleProductVec e bx).vec i) *
          permutationRepresentation d n π i j)
        = star (∑ i, (tupleProductVec e bx).vec i *
            permutationRepresentation d n π i j) := by
      rw [star_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [star_mul', hreal i, mul_comm]
    rw [this]
    congr 1
    -- `∑ i, |bx⟩_i U_π(i,j) = (U_πᵀ ·ᵥ |bx⟩)_j = (U_{π⁻¹}·|bx⟩)_j = |bx ∘ π⟩_j`.
    have hvm : (∑ i, (tupleProductVec e bx).vec i * permutationRepresentation d n π i j)
        = ((permutationRepresentation d n π)ᵀ).mulVec (tupleProductVec e bx).vec j := by
      simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hvm, permutationRepresentation_transpose,
      permutationRepresentation_mulVec_tupleProductVec]
    have : ((π⁻¹ : Equiv.Perm (Fin n)).symm) = π := by
      ext x; simp [Equiv.Perm.inv_def]
    rw [this]
  rw [hadj]

/-- **Mixed-radix digit split.** For `a : Fin (d^(n-r))`, `b : Fin (d^r)`, the `m`-th
base-`d` digit of the flat index `Fin.cast h_dim (finProdFinEquiv (a, b))` is the
`m`-th digit of `b` when `m < r` (low block) and the `(m−r)`-th digit of `a` when `m ≥ r`
(high block). This is finProdFinEquiv_apply_val (`val = b + d^r·a`) read through the
digit formula finFunctionFinEquiv_symm_apply_val (`digit m = val / d^m % d`). -/
theorem finFunctionFinEquiv_symm_cast_finProdFinEquiv {d n r : ℕ} [NeZero d]
    (hr : r ≤ n) (a : Fin (d ^ (n - r))) (b : Fin (d ^ r))
    (h_dim : d ^ (n - r) * d ^ r = d ^ n) (m : Fin n) :
    ((finFunctionFinEquiv.symm
        (Fin.cast h_dim (finProdFinEquiv (a, b)))) m : ℕ)
      = if hm : (m : ℕ) < r then (finFunctionFinEquiv.symm b ⟨m, hm⟩ : ℕ)
        else (finFunctionFinEquiv.symm a ⟨(m : ℕ) - r, by omega⟩ : ℕ) := by
  rw [finFunctionFinEquiv_symm_apply_val, Fin.val_cast, finProdFinEquiv_apply_val]
  -- `val = b.val + d^r * a.val`.
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  by_cases hm : (m : ℕ) < r
  · rw [dif_pos hm, finFunctionFinEquiv_symm_apply_val]
    -- Low block: `(b + d^r·a) / d^m % d = b / d^m % d` since `d | d^(r-m)` past `b`.
    have hpow : d ^ r = d ^ (m : ℕ) * (d * d ^ (r - (m : ℕ) - 1)) := by
      rw [← mul_assoc, ← pow_succ, ← pow_add]
      congr 1
      omega
    have hbge : (b : ℕ) + d ^ r * (a : ℕ)
        = (b : ℕ) + d ^ (m : ℕ) * (d * (d ^ (r - (m : ℕ) - 1) * (a : ℕ))) := by
      have : d ^ r * (a : ℕ) = d ^ (m : ℕ) * (d * (d ^ (r - (m : ℕ) - 1) * (a : ℕ))) := by
        rw [hpow]; ring
      omega
    rw [hbge, Nat.add_mul_div_left _ _ (pow_pos hdpos (m : ℕ)),
      Nat.add_mul_mod_self_left]
  · rw [dif_neg hm, finFunctionFinEquiv_symm_apply_val]
    -- High block: digit `m` of `(b + d^r·a)` equals digit `m-r` of `a`.
    push_neg at hm
    -- `(b + d^r·a) / d^m = a / d^(m-r)` since `b < d^r ≤ d^m`.
    have hdiv : ((b : ℕ) + d ^ r * (a : ℕ)) / d ^ (m : ℕ) = (a : ℕ) / d ^ ((m : ℕ) - r) := by
      have hbr : ((b : ℕ) + d ^ r * (a : ℕ)) / d ^ r = (a : ℕ) := by
        rw [Nat.add_mul_div_left _ _ (pow_pos hdpos r),
          Nat.div_eq_of_lt b.isLt, zero_add]
      have hmr : d ^ r * d ^ ((m : ℕ) - r) = d ^ (m : ℕ) := by
        rw [← pow_add]; congr 1; omega
      rw [show d ^ (m : ℕ) = d ^ r * d ^ ((m : ℕ) - r) from hmr.symm,
        ← Nat.div_div_eq_div_mul, hbr]
    rw [hdiv]

/-- **Slot split of a tuple-product vector.** With `n = (n−r) + r`, the tuple-product
vector `tupleProductVec e cx` factors as a cast of a tensor product of its restriction to
the high slots `[r, n)` (first `Ket.tensor` factor, matching `finProdFinEquiv`'s high
component) and its restriction to the low slots `[0, r)`. This is the mixed-radix digit
split finProdFinEquiv_apply_val/finFunctionFinEquiv_apply_val: a flat index of
`Fin (d^n)` splits into `(a, b) ∈ Fin (d^(n-r)) × Fin (d^r)` whose digits are the high and
low slot digits respectively. -/
theorem tupleProductVec_split {d n r : ℕ} [NeZero d] (hr : r ≤ n)
    (e : Fin d → Ket d) (cx : Fin n → Fin d)
    (h_dim : d ^ (n - r) * d ^ r = d ^ n) :
    tupleProductVec e cx
      = Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor
          (tupleProductVec e (fun j : Fin (n - r) => cx ⟨r + (j : ℕ), by omega⟩))
          (tupleProductVec e (fun j : Fin r => cx ⟨(j : ℕ), by omega⟩))) := by
  classical
  ext i
  rw [Quantum.TensorProducts.ket_cast_vec]
  -- Decode `Fin.cast h_dim.symm i` into the product index `(a, b)`, so
  -- `i = Fin.cast h_dim (finProdFinEquiv (a, b))`.
  set a := (finProdFinEquiv.symm (Fin.cast h_dim.symm i)).1 with ha
  set b := (finProdFinEquiv.symm (Fin.cast h_dim.symm i)).2 with hb
  have hi : i = Fin.cast h_dim (finProdFinEquiv (a, b)) := by
    rw [ha, hb, Prod.mk.eta, Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_eq_self]
  have hRHS : (Quantum.TensorProducts.Ket.tensor
        (tupleProductVec e (fun j : Fin (n - r) => cx ⟨r + (j : ℕ), by omega⟩))
        (tupleProductVec e (fun j : Fin r => cx ⟨(j : ℕ), by omega⟩))).vec
        (Fin.cast h_dim.symm i)
      = (tupleProductVec e (fun j : Fin (n - r) => cx ⟨r + (j : ℕ), by omega⟩)).vec a
          * (tupleProductVec e (fun j : Fin r => cx ⟨(j : ℕ), by omega⟩)).vec b := by
    unfold Quantum.TensorProducts.Ket.tensor
    change (match finProdFinEquiv.symm (Fin.cast h_dim.symm i) with
      | (i₁, j) => (tupleProductVec e (fun j : Fin (n - r) => cx ⟨r + (j : ℕ), by omega⟩)).vec i₁
        * (tupleProductVec e (fun j : Fin r => cx ⟨(j : ℕ), by omega⟩)).vec j) = _
    rw [show finProdFinEquiv.symm (Fin.cast h_dim.symm i) = (a, b) from by
      rw [ha, hb]]
  rw [hRHS]
  simp only [tupleProductVec, tensorFamilyVec_apply]
  -- LHS product over all `n` slots; split into high slots `[r,n)` (matching `a`) and
  -- low slots `[0,r)` (matching `b`) via the mixed-radix digit lemma.
  have hdigit := fun m : Fin n =>
    finFunctionFinEquiv_symm_cast_finProdFinEquiv hr a b h_dim m
  -- Reindex each slot's letter index through the digit split.
  rw [show (∏ m : Fin n, (e (cx m)).vec ((finFunctionFinEquiv.symm i) m))
      = ∏ m : Fin n, (e (cx m)).vec
          (if hm : (m : ℕ) < r then finFunctionFinEquiv.symm b ⟨m, hm⟩
            else finFunctionFinEquiv.symm a ⟨(m : ℕ) - r, by omega⟩) by
    refine Finset.prod_congr rfl (fun m _ => ?_)
    congr 1
    apply Fin.ext
    rw [hi, hdigit m]
    rw [apply_dite (Fin.val : Fin d → ℕ)]]
  -- Split the product over `Fin n` into the low block `[0,r)` and high block `[r,n)`.
  have hn : r + (n - r) = n := by omega
  set g : Fin n → ℂ := fun m => (e (cx m)).vec
    (if hm : (m : ℕ) < r then finFunctionFinEquiv.symm b ⟨m, hm⟩
      else finFunctionFinEquiv.symm a ⟨(m : ℕ) - r, by omega⟩) with hg
  rw [← Fin.prod_congr' g hn, Fin.prod_univ_add, mul_comm]
  -- High block `[r, n)` matches `a`; low block `[0, r)` matches `b`.
  congr 1
  · -- High block: `Fin.natAdd r j` has value `r + j ≥ r`.
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [hg, Fin.val_cast, Fin.val_natAdd]
    rw [dif_neg (by omega)]
    -- Match `cx (cast (natAdd r j)) = cx ⟨r+j,_⟩` and the index `⟨r+j-r,_⟩ = j`.
    congr 2
    apply Fin.ext; simp
  · -- Low block: `Fin.castAdd (n-r) j` has value `j < r`.
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [hg, Fin.val_cast, Fin.val_castAdd]
    rw [dif_pos (by omega)]
    congr 2

/-- **A tuple vector is orthogonal to a `θ^{⊗(n−r)} ⊗ tail` generator off the
θ-placement.** Splitting `tupleProductVec e cx` into its high/low slot factors
(`tupleProductVec_split`) and factoring the inner product (`Ket.inner_tensor`), the high
factor pairs `tupleProductVec e cx_hi` against `θ^{⊗(n−r)} = tupleProductVec e (const x̄)`,
giving `∏_{j} ⟨e (cx_hi j) | e xbar⟩ = ∏_j δ_{cx_hi j, xbar}` (`tupleProductVec_inner`).
If some high slot `m ≥ r` carries `cx m ≠ xbar`, that product — hence the whole inner
product — vanishes. This is the frequency-support fact feeding Stage 2. -/
theorem tupleProductVec_inner_cast_tensor_eq_zero {d n r : ℕ} [NeZero d] [NeZero (d ^ n)]
    (hr : r ≤ n) (e : Fin d → Ket d) (xbar : Fin d)
    (he_on : ∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0)
    (cx : Fin n → Fin d) (tail : Ket (d ^ r))
    (h_dim : d ^ (n - r) * d ^ r = d ^ n)
    (hsupp : ∃ m : Fin n, (r ≤ (m : ℕ)) ∧ cx m ≠ xbar) :
    Ket.inner (tupleProductVec e cx)
        (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor
          (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r))) tail)) = 0 := by
  classical
  -- `θ^{⊗(n−r)}` is the tuple-product vector at the constant tuple `xbar`.
  have hθpow : (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
      = tupleProductVec e (fun _ : Fin (n - r) => xbar) := by
    ext k; rfl
  rw [hθpow]
  -- Split `tupleProductVec e cx` into its high and low slot factors.
  rw [tupleProductVec_split hr e cx h_dim]
  -- Cast preserves the inner product (`Fin.cast` is just a reindexing).
  have hcast : Ket.inner
      (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor
        (tupleProductVec e (fun j : Fin (n - r) => cx ⟨r + (j : ℕ), by omega⟩))
        (tupleProductVec e (fun j : Fin r => cx ⟨(j : ℕ), by omega⟩))))
      (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor
        (tupleProductVec e (fun _ : Fin (n - r) => xbar)) tail))
    = Ket.inner
      (Quantum.TensorProducts.Ket.tensor
        (tupleProductVec e (fun j : Fin (n - r) => cx ⟨r + (j : ℕ), by omega⟩))
        (tupleProductVec e (fun j : Fin r => cx ⟨(j : ℕ), by omega⟩)))
      (Quantum.TensorProducts.Ket.tensor
        (tupleProductVec e (fun _ : Fin (n - r) => xbar)) tail) := by
    rw [Ket.inner, Ket.inner, bra_mul_ket_eq, bra_mul_ket_eq]
    refine (Equiv.sum_comp (finCongr h_dim) _).symm.trans ?_
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Ket.dag_vec, Quantum.TensorProducts.ket_cast_vec, finCongr_apply, Fin.cast_cast,
        Fin.cast_eq_self]
  rw [hcast]
  -- Factor the tensor inner product and vanish via the high factor.
  rw [show Ket.inner
      (Quantum.TensorProducts.Ket.tensor
        (tupleProductVec e (fun j : Fin (n - r) => cx ⟨r + (j : ℕ), by omega⟩))
        (tupleProductVec e (fun j : Fin r => cx ⟨(j : ℕ), by omega⟩)))
      (Quantum.TensorProducts.Ket.tensor
        (tupleProductVec e (fun _ : Fin (n - r) => xbar)) tail)
    = Ket.inner (tupleProductVec e (fun j : Fin (n - r) => cx ⟨r + (j : ℕ), by omega⟩))
        (tupleProductVec e (fun _ : Fin (n - r) => xbar))
      • Ket.inner (tupleProductVec e (fun j : Fin r => cx ⟨(j : ℕ), by omega⟩)) tail from
    Ket.inner_tensor _ _ _ _]
  -- The high factor is `∏ δ`, which vanishes by `hsupp`.
  obtain ⟨m, hm_ge, hm_ne⟩ := hsupp
  have hhi : Ket.inner (tupleProductVec e (fun j : Fin (n - r) => cx ⟨r + (j : ℕ), by omega⟩))
      (tupleProductVec e (fun _ : Fin (n - r) => xbar)) = 0 := by
    rw [tupleProductVec_inner e he_on, if_neg]
    intro hcontra
    apply hm_ne
    have := congr_fun hcontra ⟨(m : ℕ) - r, by omega⟩
    simpa only [show r + ((m : ℕ) - r) = (m : ℕ) by omega, Fin.eta] using this
  rw [hhi, zero_smul]

/-! ## Stage 2 — computational-basis expansion supported on `freq(x̄) ≥ n−r` -/

/-- **Stage 2: computational-basis expansion of `Ψ`, supported on `freq(x̄) ≥ n−r`**
(`eq:Psisum`, `main.tex:5310-5318`).

Expanding the membership representation `hmem` of `Ψ` in the θ-adapted basis of Stage 1
(each permuted product generator `U_{π_t}(θ^{⊗(n−r)} ⊗ tail_t)` becomes a sum of basis
tuples `|bx⟩`, all carrying `x̄` in at least the `n−r` slots `π_t({1,…,n−r})`), yields
coefficients `β_bx` with `|Ψ⟩ = Σ_bx β_bx |bx⟩` and the **support condition**: `β_bx = 0`
whenever the `x̄`-frequency of `bx` is below `m = n−r`. This is the only place the
per-component permutation content of `InRestrictedSymSpace` is consumed.

Proved: the coefficients are the basis overlaps `β_bx := ⟨bx | Ψ⟩`; the decomposition is
`tupleProductVec_completeness`, and the frequency support follows by expanding `Ψ` through
`hmem`, the adjoint move `tupleProductVec_inner_permutationRepresentation`, and the
generator orthogonality `tupleProductVec_inner_cast_tensor_eq_zero` (an `xbar`-deficient
`bx` is orthogonal to every permuted `θ^{⊗(n−r)} ⊗ tail` generator). -/
theorem inRestrictedSymSpace_computationalBasisExpansion
    {d n r : ℕ} [NeZero d] [NeZero (d ^ n)] (hr : r ≤ n)
    (θ : NormKet d) (Ψ : NormKet (d ^ n))
    (hmem : InRestrictedSymSpace d n r θ Ψ)
    (xbar : Fin d) (e : Fin d → Ket d)
    (he_on : ∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0)
    (he_theta : e xbar = θ.toKet) :
    ∃ β : (Fin n → Fin d) → ℂ,
      (∀ bx, thetaFreq xbar bx < n - r → β bx = 0) ∧
      Ψ.toKet.vec = ∑ bx : Fin n → Fin d, β bx • (tupleProductVec e bx).vec := by
  classical
  -- The coefficient of `|bx⟩` is the basis overlap `⟨bx | Ψ⟩`.
  refine ⟨fun bx => Ket.inner (tupleProductVec e bx) Ψ.toKet, ?_, ?_⟩
  · -- Support: `⟨bx | Ψ⟩ = 0` when `bx` carries `x̄` in fewer than `n−r` slots.
    intro bx hfreq
    simp only
    -- Expand `Ψ` through the membership representation.
    obtain ⟨T, coeffs, perms, tails, h_dim, hΨeq⟩ := hmem
    rw [Ket.inner, bra_mul_ket_eq]
    simp only [Ket.dag_vec, starRingEnd_apply]
    -- `⟨bx | Ψ⟩ = ∑_t coeffs t · ⟨bx | generator_t⟩`, each term `= 0`.
    have hsum : (∑ i, star ((tupleProductVec e bx).vec i) * Ψ.toKet.vec i)
        = ∑ t ∈ T, coeffs t *
            Ket.inner (tupleProductVec e bx)
              ⟨(Math.RepresentationTheory.permutationRepresentation d n (perms t)).mulVec
                (Ket.cast h_dim
                  (Quantum.TensorProducts.Ket.tensor
                    (⟨Quantum.TensorProducts.tensorPowVec θ.toKet.vec⟩ : Ket (d ^ (n - r)))
                    (tails t).toKet)).vec⟩ := by
      rw [hΨeq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [Ket.inner, bra_mul_ket_eq]
      simp only [Ket.dag_vec, starRingEnd_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum]
    apply Finset.sum_eq_zero
    intro t _
    -- Adjoint move + cast-tensor orthogonality (`θ = e xbar`).
    rw [tupleProductVec_inner_permutationRepresentation]
    rw [show θ.toKet.vec = (e xbar).vec from by rw [he_theta]]
    rw [tupleProductVec_inner_cast_tensor_eq_zero hr e xbar he_on _ _ h_dim, mul_zero]
    -- Some high slot `m ≥ r` of `bx ∘ perms t` carries a non-`xbar` letter.
    by_contra hall
    push_neg at hall
    -- `hall : ∀ m, r ≤ m → bx (perms t m) = xbar` (the high block all carry `xbar`).
    refine Nat.not_lt.mpr ?_ hfreq
    -- The `n − r` high slots `⟨r+j, _⟩` map injectively by `perms t` into the
    -- `xbar`-support of `bx`.
    set hiSet : Finset (Fin n) :=
      Finset.image (fun j : Fin (n - r) => (⟨r + (j : ℕ), by omega⟩ : Fin n)) Finset.univ
      with hhi
    have hinj : Function.Injective (fun j : Fin (n - r) => (⟨r + (j : ℕ), by omega⟩ : Fin n)) := by
      intro j₁ j₂ h
      apply Fin.ext
      have := Fin.mk.injEq .. ▸ h
      simpa using congrArg Fin.val h
    have hhiCard : hiSet.card = n - r := by
      rw [hhi, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    calc (n - r) = hiSet.card := hhiCard.symm
      _ = (hiSet.image (perms t)).card :=
          (Finset.card_image_of_injective _ (perms t).injective).symm
      _ ≤ (Finset.univ.filter (fun k => bx k = xbar)).card := by
          apply Finset.card_le_card
          intro k hk
          rw [Finset.mem_image] at hk
          obtain ⟨k₀, hk₀, hk₀k⟩ := hk
          rw [hhi, Finset.mem_image] at hk₀
          obtain ⟨j, _, hjk₀⟩ := hk₀
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [← hk₀k, ← hjk₀]
          exact hall ⟨r + (j : ℕ), by omega⟩ (by simp)
      _ = thetaFreq xbar bx := rfl
  · -- Decomposition: completeness of the tuple-product orthonormal basis.
    exact tupleProductVec_completeness e he_on Ψ.toKet

/-! ## Stage 3 — grouping by `m`-placement subset -/

/-- **Stage 3: group the support tuples by an `m`-placement subset** (`eq:Psisdef`,
`main.tex:5320-5328`).

For each tuple `bx` carrying `x̄` in `≥ m` slots (`m = n−r`) there is an `m`-element subset
`s(bx) ⊆ {k : bx k = x̄}` of slots that all carry `x̄`. The resulting assignment
`assign : (Fin n → Fin d) → Finset (Fin n)` lands every support tuple in
`placementSubsets n m`, places `x̄` on the chosen slots, and partitions the expansion:
`Σ_bx β_bx |bx⟩ = Σ_{s ∈ placementSubsets n m} |Ψ^s⟩` with
`|Ψ^s⟩ = subsetPartialVec e β assign s`.

Proved: the assignment picks (via `Finset.exists_subset_card_eq`) an `m`-element subset of
the `xbar`-support `{k : bx k = x̄}` for each support tuple `bx`; the partition identity is
a sum swap collapsing the `assign bx = s` indicator. -/
theorem exists_placementAssignment
    {d n : ℕ} [NeZero d] (m : ℕ) (xbar : Fin d)
    (e : Fin d → Ket d) (β : (Fin n → Fin d) → ℂ)
    (hβ_supp : ∀ bx, thetaFreq xbar bx < m → β bx = 0) :
    ∃ assign : (Fin n → Fin d) → Finset (Fin n),
      (∀ bx, β bx ≠ 0 → assign bx ∈ placementSubsets n m) ∧
      (∀ bx k, β bx ≠ 0 → k ∈ assign bx → bx k = xbar) ∧
      (∑ bx : Fin n → Fin d, β bx • (tupleProductVec e bx).vec)
        = ∑ s ∈ placementSubsets n m, (subsetPartialVec e β assign s).vec := by
  classical
  -- For each `bx` with `β bx ≠ 0`, the slot-set carrying `x̄` has `≥ m` elements,
  -- so it has an `m`-element subset. Choose one such subset per `bx`.
  set slots : (Fin n → Fin d) → Finset (Fin n) :=
    fun bx => Finset.univ.filter (fun k => bx k = xbar) with hslots
  have hcard : ∀ bx, β bx ≠ 0 → m ≤ (slots bx).card := by
    intro bx hβ
    by_contra hlt
    push_neg at hlt
    exact hβ (hβ_supp bx (by rw [thetaFreq]; exact hlt))
  -- The canonical `m`-subset of `slots bx` (chosen via `exists_subset_card_eq`).
  have hchoice : ∀ bx, ∃ t : Finset (Fin n), t ⊆ slots bx ∧
      (β bx ≠ 0 → t.card = m) := by
    intro bx
    by_cases hβ : β bx = 0
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd hβ h⟩
    · obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq (hcard bx hβ)
      exact ⟨t, ht_sub, fun _ => ht_card⟩
  choose assign hassign_sub hassign_card using hchoice
  refine ⟨assign, ?_, ?_, ?_⟩
  · -- `assign bx ∈ placementSubsets n m`: it is an `m`-subset of `univ`.
    intro bx hβ
    rw [placementSubsets, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hassign_card bx hβ⟩
  · -- Slots in `assign bx` carry `x̄`.
    intro bx k hβ hk
    have := hassign_sub bx hk
    rw [hslots, Finset.mem_filter] at this
    exact this.2
  · -- Partition identity: swap sums and collapse the indicator.
    rw [show (∑ s ∈ placementSubsets n m, (subsetPartialVec e β assign s).vec)
        = ∑ s ∈ placementSubsets n m,
            ∑ bx : Fin n → Fin d,
              (if assign bx = s then β bx • (tupleProductVec e bx).vec else 0) by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rfl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun bx _ => ?_)
    by_cases hβ : β bx = 0
    · simp only [hβ, zero_smul, ite_self, Finset.sum_const_zero]
    · rw [Finset.sum_ite_eq (placementSubsets n m) (assign bx)
        (fun _ => β bx • (tupleProductVec e bx).vec)]
      rw [if_pos]
      · rw [placementSubsets, Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hassign_card bx hβ⟩

/-! ## Stage 4 — `Vrep` form, orthogonality, normalization -/

/-- **Inner product of two placement partial sums.** With `{e i}` orthonormal, the
computational-basis tuples are orthonormal (`tupleProductVec_inner`), so
`⟨Ψ^s | Ψ^{s'}⟩ = ∑_{bx : assign bx = s ∧ assign bx = s'} |β bx|²`. For `s ≠ s'` no tuple is
assigned to both, so the inner product vanishes; for `s = s'` it is the squared norm
`∑_{assign bx = s} |β bx|²`. -/
theorem subsetPartialVec_inner {d n : ℕ} [NeZero d] (e : Fin d → Ket d)
    (he_on : ∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0)
    (β : (Fin n → Fin d) → ℂ) (assign : (Fin n → Fin d) → Finset (Fin n))
    (s s' : Finset (Fin n)) :
    Ket.inner (subsetPartialVec e β assign s) (subsetPartialVec e β assign s')
      = ((if s = s' then
          ∑ bx : Fin n → Fin d, if assign bx = s then Complex.normSq (β bx) else 0
        else 0 : ℝ) : ℂ) := by
  classical
  -- Abbreviate the per-tuple coefficients of the two partial sums.
  set c : (Fin n → Fin d) → ℂ := fun bx => if assign bx = s then β bx else 0 with hc
  set c' : (Fin n → Fin d) → ℂ := fun by' => if assign by' = s' then β by' else 0 with hc'
  -- The inner product expands into a double sum over `(bx, by')` of
  -- `star (c bx) * c' by' * ⟨bx | by'⟩`.
  have hexpand : Ket.inner (subsetPartialVec e β assign s) (subsetPartialVec e β assign s')
      = ∑ bx : Fin n → Fin d, ∑ by' : Fin n → Fin d,
          star (c bx) * c' by' *
            Ket.inner (tupleProductVec e bx) (tupleProductVec e by') := by
    rw [Ket.inner, bra_mul_ket_eq]
    simp only [Ket.dag_vec, starRingEnd_apply, subsetPartialVec, Finset.sum_apply,
      ite_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    -- Rewrite the components as `c`/`c'`-weighted sums of tuple vectors at each index `i`.
    have hcs : ∀ i, (∑ bx : Fin n → Fin d,
          if assign bx = s then β bx * (tupleProductVec e bx).vec i else 0)
        = ∑ bx : Fin n → Fin d, c bx * (tupleProductVec e bx).vec i := by
      intro i; refine Finset.sum_congr rfl (fun bx _ => ?_)
      rw [hc]; split_ifs with h <;> simp [h]
    have hcs' : ∀ i, (∑ by' : Fin n → Fin d,
          if assign by' = s' then β by' * (tupleProductVec e by').vec i else 0)
        = ∑ by' : Fin n → Fin d, c' by' * (tupleProductVec e by').vec i := by
      intro i; refine Finset.sum_congr rfl (fun by' _ => ?_)
      rw [hc']; split_ifs with h <;> simp [h]
    simp_rw [hcs, hcs']
    -- Per index `i`: `star(∑_bx ...) * (∑_by ...) = ∑_bx ∑_by star(c bx) c' by' v w`.
    have hperi : ∀ i, star (∑ bx, c bx * (tupleProductVec e bx).vec i) *
          (∑ by', c' by' * (tupleProductVec e by').vec i)
        = ∑ bx, ∑ by', star (c bx) * c' by' *
            (star ((tupleProductVec e bx).vec i) * (tupleProductVec e by').vec i) := by
      intro i
      rw [star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun bx _ => Finset.sum_congr rfl (fun by' _ => ?_))
      rw [star_mul']; ring
    simp_rw [hperi]
    -- Swap `∑_i` inside the double `∑_bx ∑_by` and recognize the inner product.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun bx _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun by' _ => ?_)
    rw [← Finset.mul_sum]
    congr 1
  rw [hexpand]
  -- Collapse the off-diagonal terms via orthonormality `⟨bx|by'⟩ = δ`.
  simp_rw [tupleProductVec_inner e he_on]
  -- Only the diagonal `by' = bx` survives.
  have hdiag : (∑ bx, ∑ by', star (c bx) * c' by' * if bx = by' then 1 else 0)
      = ∑ bx, star (c bx) * c' bx := by
    refine Finset.sum_congr rfl (fun bx _ => ?_)
    rw [Finset.sum_eq_single bx]
    · simp
    · intro by' _ hby'; rw [if_neg (Ne.symm hby'), mul_zero]
    · intro h; exact absurd (Finset.mem_univ bx) h
  rw [hdiag]
  -- Reduce `star (c bx) * c' bx` to the indicator-weighted `|β bx|²`.
  by_cases hss' : s = s'
  · subst hss'
    rw [if_pos rfl, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun bx _ => ?_)
    rw [apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_zero]
    change star (if assign bx = s then β bx else 0) * (if assign bx = s then β bx else 0)
      = if assign bx = s then ((Complex.normSq (β bx) : ℝ) : ℂ) else 0
    split_ifs with h
    · rw [Complex.normSq_eq_conj_mul_self]; simp
    · simp
  · rw [if_neg hss', Complex.ofReal_zero]
    -- `s ≠ s'`: each term vanishes since `assign bx` cannot equal both.
    apply Finset.sum_eq_zero
    intro bx _
    change star (if assign bx = s then β bx else 0) * (if assign bx = s' then β bx else 0) = 0
    by_cases h : assign bx = s
    · rw [h, if_neg hss', mul_zero]
    · rw [if_neg h, star_zero, zero_mul]

/-- **Per-subset placement permutation `π_s`.** Given an `(n−r)`-element subset
`s ⊆ Fin n` (so `s.card = n − r` and `sᶜ.card = r`), this permutation of the `n` tensor
slots sends the **high block** `[r, n)` order-isomorphically onto `s` and the **low block**
`[0, r)` order-isomorphically onto `sᶜ`. Concretely, slot `⟨r + j, _⟩` (the `j`-th high
slot, `j : Fin (n − r)`) maps to the `j`-th element of `s` in increasing order
(`s.orderEmbOfFin`), and slot `⟨j, _⟩` (low, `j : Fin r`) maps to the `j`-th element of `sᶜ`.

It is built by composing the canonical block split `Fin n ≃ Fin (n−r) ⊕ Fin r` (high block
`↦ inl`, low block `↦ inr`, via `finCongr`/`finSumFinEquiv`/`Equiv.sumComm`) with the
order-embedding placement `finSumEquivOfFinset : Fin (n−r) ⊕ Fin r ≃ Fin n` of `s`/`sᶜ`.
Explicit; no `Classical.choose`. Used as the `Vrep` reordering in `hprod_form`: applying
`U_{π_s}` to `θ^{⊗(n−r)} ⊗ tail` (θ in the high slots after the cast) places `θ` onto the
slots of `s`, matching the per-subset partial sum `|Ψ^s⟩`. -/
def placementPerm {n r : ℕ} (hr : r ≤ n) (s : Finset (Fin n))
    (hs_card : s.card = n - r) : Equiv.Perm (Fin n) :=
  let hsc_card : sᶜ.card = r := by
    rw [Finset.card_compl, Fintype.card_fin, hs_card]; omega
  -- Canonical split of `Fin n` into the high block (`[r,n)`, `↦ inl : Fin (n−r)`) and the
  -- low block (`[0,r)`, `↦ inr : Fin r`).
  let split : Fin n ≃ Fin (n - r) ⊕ Fin r :=
    (finCongr (show n = r + (n - r) by omega)).trans
      ((finSumFinEquiv (m := r) (n := n - r)).symm.trans (Equiv.sumComm (Fin r) (Fin (n - r))))
  split.trans (finSumEquivOfFinset hs_card hsc_card)

/-- **`placementPerm` on the high block.** The `j`-th high slot `⟨r + j, _⟩` is sent to the
`j`-th element of `s` in increasing order (`s.orderEmbOfFin`). In particular its image lies
in `s`. -/
theorem placementPerm_high {n r : ℕ} (hr : r ≤ n) (s : Finset (Fin n))
    (hs_card : s.card = n - r) (j : Fin (n - r)) :
    placementPerm hr s hs_card ⟨r + (j : ℕ), by omega⟩ = s.orderEmbOfFin hs_card j := by
  have hsc_card : sᶜ.card = r := by
    rw [Finset.card_compl, Fintype.card_fin, hs_card]; omega
  rw [placementPerm]
  simp only [Equiv.trans_apply, finCongr_apply]
  -- `split` sends the high slot to `Sum.inl j`.
  rw [show (Fin.cast (show n = r + (n - r) by omega) ⟨r + (j : ℕ), by omega⟩)
      = Fin.natAdd r j by apply Fin.ext; simp]
  rw [finSumFinEquiv_symm_apply_natAdd, Equiv.sumComm_apply, Sum.swap_inr,
    finSumEquivOfFinset_inl]

/-- **`placementPerm` maps the high block `[r, n)` onto `s`.** Consequently a tuple word
that is constant `xbar` on `s` becomes, after reindexing by `placementPerm`, constant `xbar`
on the high slots `[r, n)`. -/
theorem placementPerm_high_mem {n r : ℕ} (hr : r ≤ n) (s : Finset (Fin n))
    (hs_card : s.card = n - r) (j : Fin (n - r)) :
    placementPerm hr s hs_card ⟨r + (j : ℕ), by omega⟩ ∈ s := by
  rw [placementPerm_high]; exact Finset.orderEmbOfFin_mem _ _ _

/-- **Unnormalized `Vrep` tail of the per-subset partial sum.** For an `(n−r)`-subset `s`,
this is the low-slot (`[0, r)`) factor obtained by reindexing each support tuple `bx` of
`|Ψ^s⟩` by the placement permutation `π_s`: `tail_s = Σ_{assign bx = s} β bx |bx ∘ π_s|_{[0,r)}⟩`.
Together with `θ^{⊗(n−r)}` in the high slots it reconstructs `U_{π_s}(θ^{⊗(n−r)} ⊗ tail_s) = |Ψ^s⟩`
(`subsetPartialVec_eq_vrep`). Explicit. -/
def subsetVrepTail {d n r : ℕ} [NeZero d] (hr : r ≤ n) (e : Fin d → Ket d)
    (β : (Fin n → Fin d) → ℂ) (assign : (Fin n → Fin d) → Finset (Fin n))
    (s : Finset (Fin n)) (hs_card : s.card = n - r) : Ket (d ^ r) :=
  ⟨∑ bx : Fin n → Fin d, if assign bx = s then
      β bx • (tupleProductVec e
        (fun j : Fin r => bx (placementPerm hr s hs_card ⟨(j : ℕ), by omega⟩))).vec
    else 0⟩

/-- **Per-tuple `Vrep` reconstruction.** A single support tuple `bx` that carries `xbar`
on `s` is recovered from its `π_s`-reindexed `θ^{⊗(n−r)} ⊗ low` form: the high restriction of
`bx ∘ π_s` is constant `xbar` (since `π_s` maps the high block into `s`), so by
`tupleProductVec_split` and `permutationRepresentation_mulVec_tupleProductVec`
`U_{π_s}(θ^{⊗(n−r)} ⊗ |bx ∘ π_s|_{[0,r)}⟩) = |bx⟩`. -/
theorem tupleProductVec_eq_vrep_term {d n r : ℕ} [NeZero d] (hr : r ≤ n)
    (xbar : Fin d) (e : Fin d → Ket d)
    (s : Finset (Fin n)) (hs_card : s.card = n - r)
    (h_dim : d ^ (n - r) * d ^ r = d ^ n)
    (bx : Fin n → Fin d) (hbx : ∀ k ∈ s, bx k = xbar) :
    (Math.RepresentationTheory.permutationRepresentation d n
          (placementPerm hr s hs_card)).mulVec
        (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor
          (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
          (tupleProductVec e
            (fun j : Fin r => bx (placementPerm hr s hs_card ⟨(j : ℕ), by omega⟩))))).vec
      = (tupleProductVec e bx).vec := by
  classical
  set π := placementPerm hr s hs_card with hπ
  -- `θ^{⊗(n−r)}` is the constant-`xbar` tuple vector.
  have hθpow : (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
      = tupleProductVec e (fun _ : Fin (n - r) => xbar) := by ext k; rfl
  -- The tuple `bx ∘ π` is `xbar` on the high block and `bx ∘ π` on the low block.
  have hsplit := tupleProductVec_split hr e (bx ∘ π) h_dim
  -- High restriction is constant `xbar`.
  have hhi : (fun j : Fin (n - r) => (bx ∘ π) ⟨r + (j : ℕ), by omega⟩)
      = (fun _ : Fin (n - r) => xbar) := by
    funext j
    exact hbx (π ⟨r + (j : ℕ), by omega⟩) (placementPerm_high_mem hr s hs_card j)
  -- Low restriction is the recorded `low` tuple.
  have hlo : (fun j : Fin r => (bx ∘ π) ⟨(j : ℕ), by omega⟩)
      = (fun j : Fin r => bx (π ⟨(j : ℕ), by omega⟩)) := by funext j; rfl
  rw [hθpow]
  -- Rebuild `tupleProductVec e (bx ∘ π)` from its split factors.
  rw [show (Quantum.TensorProducts.Ket.tensor
        (tupleProductVec e (fun _ : Fin (n - r) => xbar))
        (tupleProductVec e (fun j : Fin r => bx (π ⟨(j : ℕ), by omega⟩))))
      = (Quantum.TensorProducts.Ket.tensor
          (tupleProductVec e (fun j : Fin (n - r) => (bx ∘ π) ⟨r + (j : ℕ), by omega⟩))
          (tupleProductVec e (fun j : Fin r => (bx ∘ π) ⟨(j : ℕ), by omega⟩)))
      by rw [hhi, hlo]]
  rw [← hsplit]
  -- Apply the permutation action: `U_π |bx ∘ π⟩ = |bx ∘ π ∘ π.symm| = |bx⟩`.
  rw [permutationRepresentation_mulVec_tupleProductVec]
  rw [show (bx ∘ ⇑π) ∘ ⇑(Equiv.symm π) = bx by
    funext k; simp only [Function.comp_apply, Equiv.apply_symm_apply]]

/-- **The per-subset partial sum is a `Vrep` vector.** With `s` an `(n−r)`-placement subset
on which every support tuple carries `xbar` (`hsplace`), reindexing by `π_s = placementPerm`
moves the `xbar`-slots `s` into the high block `[r, n)`, so each generator splits as
`θ^{⊗(n−r)} ⊗ (low factor)` (`tupleProductVec_split` and
`permutationRepresentation_mulVec_tupleProductVec`).
Summing, `|Ψ^s⟩ = U_{π_s}(θ^{⊗(n−r)} ⊗ tail_s)` with `tail_s = subsetVrepTail` and
`θ = e xbar`. This is the `hprod_form` content of the witness. -/
theorem subsetPartialVec_eq_vrep {d n r : ℕ} [NeZero d] (hr : r ≤ n)
    (xbar : Fin d) (e : Fin d → Ket d)
    (β : (Fin n → Fin d) → ℂ) (assign : (Fin n → Fin d) → Finset (Fin n))
    (s : Finset (Fin n)) (hs_card : s.card = n - r)
    (hsplace : ∀ bx k, assign bx = s → β bx ≠ 0 → k ∈ s → bx k = xbar)
    (h_dim : d ^ (n - r) * d ^ r = d ^ n) :
    (subsetPartialVec e β assign s).vec
      = (Math.RepresentationTheory.permutationRepresentation d n
            (placementPerm hr s hs_card)).mulVec
          (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor
            (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
            (subsetVrepTail hr e β assign s hs_card))).vec := by
  classical
  set π := placementPerm hr s hs_card with hπ
  set θpow : Ket (d ^ (n - r)) := ⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ with hθpow
  -- `U_π ∘ cast ∘ (θ^{⊗(n−r)} ⊗ ·)` is linear in the tail ket `w`.
  set Φ : Ket (d ^ r) → (Fin (d ^ n) → ℂ) := fun w =>
    (Math.RepresentationTheory.permutationRepresentation d n π).mulVec
      (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor θpow w)).vec with hΦ
  have hΦ_zero : Φ ⟨0⟩ = 0 := by
    simp only [hΦ]
    rw [show (⟨(0 : Fin (d ^ r) → ℂ)⟩ : Ket (d ^ r)) = (0 : Ket (d ^ r)) from rfl,
      Quantum.TensorProducts.Ket.tensor_zero_right]
    rw [show Ket.cast h_dim (0 : Ket (d ^ (n - r) * d ^ r)) = (0 : Ket (d ^ n)) from by
      ext k; simp [Quantum.TensorProducts.ket_cast_vec]]
    rw [show (0 : Ket (d ^ n)).vec = 0 from by funext j; exact Ket.zero_vec j,
      Matrix.mulVec_zero]
  have hΦ_smul : ∀ (c : ℂ) (w : Ket (d ^ r)), Φ ⟨c • w.vec⟩ = c • Φ w := by
    intro c w
    simp only [hΦ]
    rw [show (⟨c • w.vec⟩ : Ket (d ^ r)) = c • w from rfl,
      Quantum.TensorProducts.Ket.tensor_smul_right]
    rw [show Ket.cast h_dim (c • Quantum.TensorProducts.Ket.tensor θpow w)
        = c • Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor θpow w) from by
      ext k; simp [Quantum.TensorProducts.ket_cast_vec]]
    rw [Ket.smul_vec, Matrix.mulVec_smul]
  -- Per-tuple value of `Φ` at the recorded low factor.
  have hkey : ∀ bx : Fin n → Fin d,
      Φ ⟨if assign bx = s then
            β bx • (tupleProductVec e
              (fun j : Fin r => bx (π ⟨(j : ℕ), by omega⟩))).vec
          else 0⟩
        = if assign bx = s then β bx • (tupleProductVec e bx).vec else 0 := by
    intro bx
    by_cases hbxs : assign bx = s
    · by_cases hβ : β bx = 0
      · rw [if_pos hbxs, if_pos hbxs, hβ, zero_smul, zero_smul]
        exact hΦ_zero
      · rw [if_pos hbxs, if_pos hbxs]
        rw [hΦ_smul (β bx) (tupleProductVec e
              (fun j : Fin r => bx (π ⟨(j : ℕ), by omega⟩)))]
        simp only [hΦ]
        rw [hπ, tupleProductVec_eq_vrep_term hr xbar e s hs_card h_dim bx
          (fun k hk => hsplace bx k hbxs hβ hk)]
    · rw [if_neg hbxs, if_neg hbxs]; exact hΦ_zero
  -- Assemble: the tail is a sum of single-tuple kets; `Φ` distributes over it.
  rw [subsetPartialVec]
  -- The goal RHS is exactly `Φ (subsetVrepTail …)`.
  rw [show (Math.RepresentationTheory.permutationRepresentation d n π).mulVec
        (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor θpow
          (subsetVrepTail hr e β assign s hs_card))).vec
      = Φ (subsetVrepTail hr e β assign s hs_card) from by simp only [hΦ]]
  -- `Φ` distributes over the sum of single-tuple tail kets.
  have hdistr : Φ (subsetVrepTail hr e β assign s hs_card)
      = ∑ bx : Fin n → Fin d, Φ ⟨if assign bx = s then
            β bx • (tupleProductVec e
              (fun j : Fin r => bx (π ⟨(j : ℕ), by omega⟩))).vec
          else 0⟩ := by
    simp only [hΦ, subsetVrepTail, hπ]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext k
    simp only [Quantum.TensorProducts.ket_cast_vec, Quantum.TensorProducts.Ket.tensor,
        Finset.sum_apply]
    rw [Finset.mul_sum]
  rw [hdistr]
  refine Finset.sum_congr rfl (fun bx _ => (hkey bx).symm)

/-- **A permutation representation preserves the squared norm.**
`‖U_π v‖² = ‖v‖²`, since `U_π† U_π = 1` (`permutationRepresentation_unitary`). -/
theorem permutationRepresentation_mulVec_normSq {d n : ℕ} [NeZero d]
    (π : Equiv.Perm (Fin n)) (v : Ket (d ^ n)) :
    Ket.normSq ⟨(Math.RepresentationTheory.permutationRepresentation d n π).mulVec v.vec⟩
      = Ket.normSq v := by
  rw [Ket.normSq, Ket.realInner, Ket.inner, bra_mul_ket_eq, Ket.normSq, Ket.realInner,
    Ket.inner, bra_mul_ket_eq]
  congr 1
  simp only [Ket.dag_vec, starRingEnd_apply]
  -- `∑ star(Uv)_i (Uv)_i = dotProduct (star (U·v)) (U·v) = dotProduct (star v) v`.
  rw [show (∑ i, star ((Math.RepresentationTheory.permutationRepresentation d n π).mulVec v.vec i)
        * (Math.RepresentationTheory.permutationRepresentation d n π).mulVec v.vec i)
      = dotProduct (star ((Math.RepresentationTheory.permutationRepresentation d n π).mulVec v.vec))
          ((Math.RepresentationTheory.permutationRepresentation d n π).mulVec v.vec) from rfl]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [show (Math.RepresentationTheory.permutationRepresentation d n π)ᴴ *
        Math.RepresentationTheory.permutationRepresentation d n π = 1 from
    (Math.RepresentationTheory.permutationRepresentation_unitary d n π).1]
  rw [Matrix.vecMul_one]
  rfl

/-- **The θ-power generator is normalized.** `‖θ^{⊗(n−r)}‖² = 1` for an orthonormal family
`{e i}` (`tupleProductVec_inner` at the constant tuple). -/
theorem tensorPowVec_normSq_eq_one {d n r : ℕ} [NeZero d] (e : Fin d → Ket d)
    (he_on : ∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0) (xbar : Fin d) :
    Ket.normSq (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r))) = 1 := by
  have hθpow : (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
      = tupleProductVec e (fun _ : Fin (n - r) => xbar) := by ext k; rfl
  rw [hθpow, Ket.normSq, Ket.realInner, tupleProductVec_inner e he_on, if_pos rfl]
  rfl

/-- **The `Vrep` tail has the squared norm of its partial sum.** Since
`|Ψ^s⟩ = U_{π_s}(θ^{⊗(n−r)} ⊗ tail_s)` (`subsetPartialVec_eq_vrep`), with `U_{π_s}` unitary,
the cast a reindexing, `θ^{⊗(n−r)}` normalized, and the tensor norm factoring, the tail
carries the full norm: `‖tail_s‖² = ‖Ψ^s‖²`. -/
theorem subsetVrepTail_normSq {d n r : ℕ} [NeZero d] (hr : r ≤ n)
    (xbar : Fin d) (e : Fin d → Ket d)
    (he_on : ∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0)
    (β : (Fin n → Fin d) → ℂ) (assign : (Fin n → Fin d) → Finset (Fin n))
    (s : Finset (Fin n)) (hs_card : s.card = n - r)
    (hsplace : ∀ bx k, assign bx = s → β bx ≠ 0 → k ∈ s → bx k = xbar)
    (h_dim : d ^ (n - r) * d ^ r = d ^ n) :
    Ket.normSq (subsetVrepTail hr e β assign s hs_card)
      = Ket.normSq (subsetPartialVec e β assign s) := by
  -- `‖Ψ^s‖² = ‖U_{π_s}(cast(θ^{⊗(n−r)} ⊗ tail))‖² = ‖θ^{⊗(n−r)} ⊗ tail‖² = ‖θ^{⊗(n−r)}‖²·‖tail‖²`.
  rw [show subsetPartialVec e β assign s
      = ⟨(Math.RepresentationTheory.permutationRepresentation d n
          (placementPerm hr s hs_card)).mulVec
        (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor
          (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
          (subsetVrepTail hr e β assign s hs_card))).vec⟩ from by
    ext k; rw [subsetPartialVec_eq_vrep hr xbar e β assign s hs_card hsplace h_dim]]
  rw [permutationRepresentation_mulVec_normSq]
  -- Cast preserves the squared norm.
  rw [show Ket.normSq (Ket.cast h_dim (Quantum.TensorProducts.Ket.tensor
        (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
        (subsetVrepTail hr e β assign s hs_card)))
      = Ket.normSq (Quantum.TensorProducts.Ket.tensor
        (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
        (subsetVrepTail hr e β assign s hs_card)) from by
    rw [Ket.normSq, Ket.realInner, Ket.inner, bra_mul_ket_eq, Ket.normSq, Ket.realInner,
      Ket.inner, bra_mul_ket_eq]
    congr 1
    refine (Equiv.sum_comp (finCongr h_dim) _).symm.trans ?_
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Ket.dag_vec, Quantum.TensorProducts.ket_cast_vec, finCongr_apply, Fin.cast_cast,
        Fin.cast_eq_self]]
  -- Tensor norm factors; the θ-power factor is `1`.
  have htensor : Ket.normSq (Quantum.TensorProducts.Ket.tensor
        (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
        (subsetVrepTail hr e β assign s hs_card))
      = (Ket.inner (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
            (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩)
          * Ket.inner (subsetVrepTail hr e β assign s hs_card)
            (subsetVrepTail hr e β assign s hs_card)).re := by
    rw [Ket.normSq, Ket.realInner]
    congr 1
    rw [show Ket.inner (Quantum.TensorProducts.Ket.tensor
          (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
          (subsetVrepTail hr e β assign s hs_card))
          (Quantum.TensorProducts.Ket.tensor
          (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
          (subsetVrepTail hr e β assign s hs_card))
        = (Ket.inner (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
            (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩))
          • (Ket.inner (subsetVrepTail hr e β assign s hs_card)
            (subsetVrepTail hr e β assign s hs_card)) from
      Ket.inner_tensor _ _ _ _]
    rw [smul_eq_mul]
  rw [htensor]
  have hθ1 : Ket.inner (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
        (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩) = 1 := by
    have hval := tensorPowVec_normSq_eq_one (d := d) (n := n) (r := r) e he_on xbar
    rw [Ket.normSq, Ket.realInner] at hval
    apply Complex.ext
    · rw [hval]; rfl
    · rw [show ((⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ :
            Ket (d ^ (n - r))).inner ⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩).im = 0
        from Ket.inner_self_im_eq_zero _]
      rfl
  rw [hθ1, one_mul, Ket.normSq, Ket.realInner]

/-- **Pythagoras for the placement partition.** The partial sums `{|Ψ^s⟩}` are pairwise
orthogonal (`subsetPartialVec_inner`), so the squared norm of their sum is the sum of squared
norms: `‖Σ_s Ψ^s‖² = Σ_s ‖Ψ^s‖²` over any finset `P` of placement subsets. -/
theorem subsetPartialVec_normSq_sum {d n : ℕ} [NeZero d] (e : Fin d → Ket d)
    (he_on : ∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0)
    (β : (Fin n → Fin d) → ℂ) (assign : (Fin n → Fin d) → Finset (Fin n))
    (P : Finset (Finset (Fin n))) :
    Ket.normSq ⟨∑ s ∈ P, (subsetPartialVec e β assign s).vec⟩
      = ∑ s ∈ P, Ket.normSq (subsetPartialVec e β assign s) := by
  classical
  -- Expand `‖Σ_s Ψ^s‖² = Σ_s Σ_{s'} ⟨Ψ^s|Ψ^{s'}⟩` and collapse off-diagonal terms.
  rw [Ket.normSq, Ket.realInner, Ket.inner, bra_mul_ket_eq]
  simp only [Ket.dag_vec, starRingEnd_apply, Finset.sum_apply]
  rw [show (∑ i, star (∑ s ∈ P, (subsetPartialVec e β assign s).vec i) *
        ∑ s' ∈ P, (subsetPartialVec e β assign s').vec i)
      = ∑ s ∈ P, ∑ s' ∈ P,
          Ket.inner (subsetPartialVec e β assign s) (subsetPartialVec e β assign s') by
    rw [show (∑ i, star (∑ s ∈ P, (subsetPartialVec e β assign s).vec i) *
          ∑ s' ∈ P, (subsetPartialVec e β assign s').vec i)
        = ∑ i, (∑ s ∈ P, star ((subsetPartialVec e β assign s).vec i)) *
          (∑ s' ∈ P, (subsetPartialVec e β assign s').vec i) by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [star_sum]]
    simp_rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    rw [Ket.inner, bra_mul_ket_eq]
    simp only [Ket.dag_vec, starRingEnd_apply]]
  -- Diagonal: `⟨Ψ^s|Ψ^{s'}⟩ = 0` for `s ≠ s'`; `Re ⟨Ψ^s|Ψ^s⟩ = ‖Ψ^s‖²`.
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [show (∑ s' ∈ P, Ket.inner (subsetPartialVec e β assign s)
        (subsetPartialVec e β assign s'))
      = Ket.inner (subsetPartialVec e β assign s) (subsetPartialVec e β assign s) by
    rw [Finset.sum_eq_single s]
    · intro s' _ hs'
      rw [subsetPartialVec_inner e he_on, if_neg (Ne.symm hs'), Complex.ofReal_zero]
    · intro h; exact absurd hs h]
  rfl

/-- **`Ket.normSq` is the sum of pointwise squared moduli**, hence nonnegative. -/
theorem ket_normSq_eq_sum {N : ℕ} (ψ : Ket N) :
    Ket.normSq ψ = ∑ i, Complex.normSq (ψ.vec i) := by
  rw [Ket.normSq, Ket.realInner, Ket.inner, bra_mul_ket_eq]
  simp only [Ket.dag_vec, starRingEnd_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Complex.normSq_apply, Complex.mul_re]

/-- **A nonzero ket has positive squared norm.** -/
theorem ket_normSq_pos {N : ℕ} (ψ : Ket N) (hψ : ψ.vec ≠ 0) : 0 < Ket.normSq ψ := by
  rw [ket_normSq_eq_sum]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hψ
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact (Complex.normSq_pos).mpr (by simpa using hi)

/-- **Normalizing a nonzero ket.** For `ψ ≠ 0` with `γ = √‖ψ‖²`, the rescaled ket
`(1/γ) • ψ` is normalized. -/
theorem ket_normalized_of_ne_zero {N : ℕ} (ψ : Ket N) (hψ : ψ.vec ≠ 0) :
    Ket.IsNormalized ⟨((1 : ℝ) / Real.sqrt (Ket.normSq ψ) : ℂ) • ψ.vec⟩ := by
  have hpos := ket_normSq_pos ψ hψ
  have hsqrt_pos : 0 < Real.sqrt (Ket.normSq ψ) := Real.sqrt_pos.mpr hpos
  have hscalar : ((1 : ℝ) / Real.sqrt (Ket.normSq ψ) : ℂ)
      = (((1 : ℝ) / Real.sqrt (Ket.normSq ψ) : ℝ) : ℂ) := by push_cast; ring
  have hnorm : Ket.normSq (⟨((1 : ℝ) / Real.sqrt (Ket.normSq ψ) : ℂ) • ψ.vec⟩ : Ket N)
      = 1 := by
    rw [show (⟨((1 : ℝ) / Real.sqrt (Ket.normSq ψ) : ℂ) • ψ.vec⟩ : Ket N)
        = ((1 : ℝ) / Real.sqrt (Ket.normSq ψ) : ℂ) • ψ from rfl]
    rw [Ket.normSq_smul, hscalar, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
    field_simp
  -- `IsNormalized` is `⟨ψ|ψ⟩ = 1`; `normSq = Re⟨ψ|ψ⟩ = 1` plus `Im = 0` gives this.
  rw [Ket.IsNormalized]
  rw [Ket.normSq, Ket.realInner, Ket.inner] at hnorm
  apply Complex.ext
  · rw [hnorm]; rfl
  · exact Ket.inner_self_im_eq_zero _

/-- **Stage 4: assemble the orthonormal `Vrep` witness from the placement partition**
(`main.tex:5334-5346`).

Given the θ-adapted orthonormal basis (`he_on`, `he_theta`), coefficients `β`, and a valid
`m`-placement assignment (`hassign_mem`, hassign_place) partitioning `Ψ` into the
per-subset partial sums `|Ψ^s⟩` (`hΨ`, with `m = n−r`):

* each `|Ψ^s⟩`, permuted by a `π_s` with `π_s(s) = {1,…,m}`, factors as
  `|θ⟩^{⊗(n−r)} ⊗ |ψ̂^s⟩`, i.e. it is a `Vrep` vector (`hprod_form` with `perm_s = π_s⁻¹`);
* distinct subsets `s ≠ s'` give disjoint computational-basis supports, hence
  `⟨Ψ^s|Ψ^{s'}⟩ = 0`;
* dropping the zero components and normalizing by `γ_s = ‖Ψ^s‖` gives `Σ|γ_s|² = ‖Ψ‖² = 1`
  (Pythagoras) and the cardinality `|S| ≤ |placementSubsets n (n−r)| = C(n, n−r)`, which
  discharges `hS_card` via `placementSubsets_card`,
  `choose_le_two_pow_mul_binaryEntropyBits`, and `binaryEntropy_symm`.

This is the main Stage-4 result; the other stages feed it. The witness index set is the
encoding (`Fintype.equivFin`) of the placement subsets whose partial sum `|Ψ^s⟩` is nonzero,
each `basis_vec s = |Ψ^s⟩ / ‖Ψ^s‖` with coefficient `γ_s = ‖Ψ^s‖`. Proved. -/
theorem restrictedSymSpaceWitness_of_placementPartition
    {d n r : ℕ} [NeZero d] [NeZero (d ^ n)] (hr : r ≤ n)
    (θ : NormKet d) (Ψ : NormKet (d ^ n))
    (xbar : Fin d) (e : Fin d → Ket d)
    (he_on : ∀ i j, Ket.inner (e i) (e j) = if i = j then 1 else 0)
    (he_theta : e xbar = θ.toKet)
    (β : (Fin n → Fin d) → ℂ)
    (assign : (Fin n → Fin d) → Finset (Fin n))
    (hassign_mem : ∀ bx, β bx ≠ 0 → assign bx ∈ placementSubsets n (n - r))
    (hassign_place : ∀ bx k, β bx ≠ 0 → k ∈ assign bx → bx k = xbar)
    (hΨ : Ψ.toKet.vec
      = ∑ s ∈ placementSubsets n (n - r), (subsetPartialVec e β assign s).vec) :
    Nonempty (RestrictedSymSpaceWitness d n r θ Ψ) := by
  classical
  -- Abbreviations: the partial sums, their squared norms, and the nonzero index set.
  set Pset : Finset (Finset (Fin n)) := placementSubsets n (n - r) with hPset
  set Ψv : Finset (Fin n) → Ket (d ^ n) := fun s => subsetPartialVec e β assign s with hΨv
  set γ : Finset (Fin n) → ℝ := fun s => Real.sqrt (Ket.normSq (Ψv s)) with hγ
  set P : Finset (Finset (Fin n)) := Pset.filter (fun s => (Ψv s).vec ≠ 0) with hP
  -- Encoding `Finset (Fin n) ↪ ℕ` (via `Fintype.equivFin`), and its partial inverse.
  set enc : Finset (Fin n) → ℕ := fun s => ((Fintype.equivFin (Finset (Fin n))) s : ℕ)
    with henc
  set dec : ℕ → Finset (Fin n) := fun m =>
    if h : m < Fintype.card (Finset (Fin n)) then
      (Fintype.equivFin (Finset (Fin n))).symm ⟨m, h⟩ else ∅ with hdec
  have hdec_enc : ∀ s, dec (enc s) = s := by
    intro s
    simp only [hdec, henc, dif_pos (Fin.isLt _)]
    simp
  have henc_inj : Function.Injective enc := by
    intro s t hst
    have := congrArg dec hst
    rwa [hdec_enc, hdec_enc] at this
  -- `normSq (↑γ_s) = ‖Ψ^s‖²` and `γ_s ≥ 0`.
  have hnormSq_nonneg : ∀ s, 0 ≤ Ket.normSq (Ψv s) := by
    intro s; rw [ket_normSq_eq_sum]
    exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hγsq : ∀ s, Complex.normSq ((γ s : ℝ) : ℂ) = Ket.normSq (Ψv s) := by
    intro s
    rw [Complex.normSq_ofReal, hγ]
    simp only
    rw [Real.mul_self_sqrt (hnormSq_nonneg s)]
  -- `‖Ψ^s‖² = 0` for `s ∉ P`.
  have hzero_off : ∀ s ∈ Pset, s ∉ P → Ket.normSq (Ψv s) = 0 := by
    intro s hs hsP
    by_contra hne
    apply hsP
    rw [hP, Finset.mem_filter]
    refine ⟨hs, ?_⟩
    intro hv
    apply hne
    rw [ket_normSq_eq_sum, hv]; simp
  -- The squared coefficients sum to `‖Ψ‖² = 1`.
  have hsum_P : ∑ s ∈ P, Ket.normSq (Ψv s) = 1 := by
    have hsub : P ⊆ Pset := hP ▸ Finset.filter_subset _ _
    rw [Finset.sum_subset hsub (fun s hs hsP => hzero_off s hs hsP)]
    rw [← subsetPartialVec_normSq_sum e he_on β assign Pset]
    have hΨket : (⟨∑ s ∈ Pset, (subsetPartialVec e β assign s).vec⟩ : Ket (d ^ n)) = Ψ.toKet := by
      ext k; rw [← hΨ]
    rw [show (⟨∑ s ∈ Pset, (Ψv s).vec⟩ : Ket (d ^ n))
        = ⟨∑ s ∈ Pset, (subsetPartialVec e β assign s).vec⟩ from rfl, hΨket]
    have hΨnorm := Ψ.normalized
    rw [Ket.IsNormalized] at hΨnorm
    rw [Ket.normSq, Ket.realInner, Ket.inner, hΨnorm]; rfl
  -- Index set of the witness: encodings of the nonzero placement subsets.
  refine ⟨{
    S := P.image enc
    basis_vecs := fun m =>
      if hne : (Ψv (dec m)).vec ≠ 0 then
        ⟨⟨((1 : ℝ) / γ (dec m) : ℂ) • (Ψv (dec m)).vec⟩,
          ket_normalized_of_ne_zero (Ψv (dec m)) hne⟩
      else stdNormKet (d ^ n) ⟨0, Nat.pos_of_ne_zero (NeZero.ne (d ^ n))⟩
    coefficients := fun m => (γ (dec m) : ℂ)
    hS_card := ?_
    hcoeffs_norm := ?_
    hdecomp := ?_
    horthonormal := ?_
    hprod_form := ?_ }⟩
  -- `hS_card`: `|S| = |P| ≤ |Pset| = C(n, n−r) ≤ 2^{n·h(r/n)}`.
  · rw [Finset.card_image_of_injective P henc_inj]
    have hcard_le : (P.card : ℝ) ≤ (Nat.choose n (n - r) : ℝ) := by
      rw [← placementSubsets_card n (n - r), ← hPset]
      exact_mod_cast Finset.card_le_card (hP ▸ Finset.filter_subset _ _)
    refine hcard_le.trans ?_
    -- `h(r/n) = h((n−r)/n)` since `(n−r)/n = 1 − r/n`, plus the Hartley bound at `n−r`.
    have hsymm : Math.ClassicalEntropy.binaryEntropyBits ((r : ℝ) / (n : ℝ))
        = Math.ClassicalEntropy.binaryEntropyBits (((n - r : ℕ) : ℝ) / (n : ℝ)) := by
      rw [Math.ClassicalEntropy.binaryEntropyBits, Math.ClassicalEntropy.binaryEntropyBits]
      congr 1
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · rw [show (((n - r : ℕ) : ℝ) / (n : ℝ)) = 1 - (r : ℝ) / (n : ℝ) by
          rw [Nat.cast_sub hr]; field_simp]
        exact Math.ClassicalEntropy.binaryEntropy_symm _
    rw [hsymm]
    exact Math.ClassicalEntropy.choose_le_two_pow_mul_binaryEntropyBits n (n - r) (by omega)
  -- `hcoeffs_norm`: `Σ_{s∈image} normSq γ_{dec s} = Σ_{s∈P} ‖Ψ^s‖² = 1`.
  · rw [Finset.sum_image (fun s _ t _ h => henc_inj h)]
    rw [← hsum_P]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hdec_enc, hγsq]
  -- `hdecomp`: `Ψ = Σ_{s∈P} γ_s • (Ψ^s/γ_s) = Σ_{s∈Pset} Ψ^s = Ψ`.
  · rw [Finset.sum_image (fun s _ t _ h => henc_inj h)]
    rw [hΨ]
    have hPset_split : (∑ s ∈ Pset, (subsetPartialVec e β assign s).vec)
        = ∑ s ∈ P, (Ψv s).vec := by
      have hsub : P ⊆ Pset := hP ▸ Finset.filter_subset _ _
      rw [← Finset.sum_subset hsub (fun s _ hsP => ?_)]
      by_contra hv
      apply hsP
      rw [hP, Finset.mem_filter]; exact ⟨‹s ∈ Pset›, hv⟩
    rw [hPset_split]
    refine Finset.sum_congr rfl (fun s hsP => ?_)
    have hsne : (Ψv (dec (enc s))).vec ≠ 0 := by
      rw [hdec_enc]
      rw [hP, Finset.mem_filter] at hsP; exact hsP.2
    rw [dif_pos hsne]
    simp only [hdec_enc]
    rw [smul_smul]
    have hγne : (γ s : ℂ) ≠ 0 := by
      rw [hP, Finset.mem_filter] at hsP
      have : 0 < Ket.normSq (Ψv s) := ket_normSq_pos (Ψv s) hsP.2
      rw [hγ]; simp only
      exact_mod_cast (Real.sqrt_pos.mpr this).ne'
    rw [show ((γ s : ℂ) * (((1 : ℝ) : ℂ) / (γ s : ℂ))) = 1 by push_cast; field_simp, one_smul]
  -- `horthonormal`: the rescaled partial sums are orthonormal.
  · intro m hm m' hm'
    rw [Finset.mem_image] at hm hm'
    obtain ⟨s, hsP, rfl⟩ := hm
    obtain ⟨t, htP, rfl⟩ := hm'
    have hsne : (Ψv (dec (enc s))).vec ≠ 0 := by
      rw [hdec_enc]; rw [hP, Finset.mem_filter] at hsP; exact hsP.2
    have htne : (Ψv (dec (enc t))).vec ≠ 0 := by
      rw [hdec_enc]; rw [hP, Finset.mem_filter] at htP; exact htP.2
    rw [dif_pos hsne, dif_pos htne]
    simp only [hdec_enc]
    -- The real inner product of the two rescaled partial sums.
    have hγs_pos : 0 < γ s := by
      rw [hγ]; simp only
      rw [hP, Finset.mem_filter] at hsP
      exact Real.sqrt_pos.mpr (ket_normSq_pos (Ψv s) hsP.2)
    have hγt_pos : 0 < γ t := by
      rw [hγ]; simp only
      rw [hP, Finset.mem_filter] at htP
      exact Real.sqrt_pos.mpr (ket_normSq_pos (Ψv t) htP.2)
    -- `realInner (a•Ψ^s) (b•Ψ^t) = (1/γ_s)·(1/γ_t)·Re ⟨Ψ^s|Ψ^t⟩`.
    have hscaled : Ket.realInner
        (⟨(((1 : ℝ) : ℂ) / (γ s : ℂ)) • (Ψv s).vec⟩ : Ket (d ^ n))
        (⟨(((1 : ℝ) : ℂ) / (γ t : ℂ)) • (Ψv t).vec⟩ : Ket (d ^ n))
      = ((1 : ℝ) / γ s) * ((1 : ℝ) / γ t) * (Ket.inner (Ψv s) (Ψv t)).re := by
      rw [Ket.realInner, Ket.inner, bra_mul_ket_eq, Ket.inner, bra_mul_ket_eq]
      simp only [Ket.dag_vec, Pi.smul_apply, smul_eq_mul, starRingEnd_apply]
      rw [show (∑ i, star ((((1 : ℝ) : ℂ) / (γ s : ℂ)) * (Ψv s).vec i) *
            ((((1 : ℝ) : ℂ) / (γ t : ℂ)) * (Ψv t).vec i))
          = (star (((1 : ℝ) : ℂ) / (γ s : ℂ)) * (((1 : ℝ) : ℂ) / (γ t : ℂ))) *
            ∑ i, star ((Ψv s).vec i) * (Ψv t).vec i by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [star_mul']; ring]
      rw [show star (((1 : ℝ) : ℂ) / (γ s : ℂ)) * (((1 : ℝ) : ℂ) / (γ t : ℂ))
          = (((1 : ℝ) / γ s) * ((1 : ℝ) / γ t) : ℝ) by
        rw [Complex.star_def, map_div₀, Complex.conj_ofReal, Complex.conj_ofReal]
        push_cast; ring]
      rw [Complex.re_ofReal_mul]
    rw [hscaled]
    -- `⟨Ψ^s|Ψ^t⟩ = if s=t then γ_s² else 0` and `enc s = enc t ↔ s = t`.
    rw [hΨv, subsetPartialVec_inner e he_on]
    by_cases hst : s = t
    · subst hst
      rw [if_pos rfl, if_pos rfl]
      rw [Complex.ofReal_re]
      rw [show (∑ bx, if assign bx = s then Complex.normSq (β bx) else 0)
          = Ket.normSq (Ψv s) by
        have hii := subsetPartialVec_inner e he_on β assign s s
        rw [if_pos rfl] at hii
        rw [hΨv, Ket.normSq, Ket.realInner, hii, Complex.ofReal_re]]
      rw [hγ]; simp only
      rw [hP, Finset.mem_filter] at hsP
      have hpos := ket_normSq_pos (Ψv s) hsP.2
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hpos.le]
      rw [one_div, inv_mul_cancel₀ hpos.ne']
    · rw [if_neg (fun h => hst (henc_inj h)), if_neg hst, Complex.ofReal_zero, Complex.zero_re,
        mul_zero]
  -- `hprod_form`: each rescaled partial sum is a `Vrep` vector `U_{π_s}(θ^{⊗(n−r)} ⊗ tail_s)`.
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨s, hsP, rfl⟩ := hm
    have hs_card : s.card = n - r := by
      rw [hP, Finset.mem_filter, hPset, placementSubsets, Finset.mem_powersetCard] at hsP
      exact hsP.1.2
    have h_dim : d ^ (n - r) * d ^ r = d ^ n := by
      rw [← pow_add]; congr 1; omega
    have hsne : (Ψv (dec (enc s))).vec ≠ 0 := by
      rw [hdec_enc]; rw [hP, Finset.mem_filter] at hsP; exact hsP.2
    -- `hsplace`: every support tuple of `Ψ^s` carries `xbar` on `s`.
    have hsplace : ∀ bx k, assign bx = s → β bx ≠ 0 → k ∈ s → bx k = xbar := by
      intro bx k hbxs hβ hk
      exact hassign_place bx k hβ (hbxs ▸ hk)
    -- `‖Ψ^s‖ > 0`, so the tail rescaling is normalized.
    have hpos : 0 < Ket.normSq (Ψv s) := by
      rw [hP, Finset.mem_filter] at hsP; exact ket_normSq_pos (Ψv s) hsP.2
    have htail_ne : (subsetVrepTail hr e β assign s hs_card).vec ≠ 0 := by
      intro hv
      have hz : Ket.normSq (subsetVrepTail hr e β assign s hs_card) = 0 := by
        rw [ket_normSq_eq_sum, hv]; simp
      rw [subsetVrepTail_normSq hr xbar e he_on β assign s hs_card hsplace h_dim] at hz
      have hpos' : 0 < Ket.normSq (subsetPartialVec e β assign s) := hpos
      exact hpos'.ne' hz
    have hγeq : γ s = Real.sqrt (Ket.normSq (subsetVrepTail hr e β assign s hs_card)) := by
      rw [hγ]; simp only
      rw [subsetVrepTail_normSq hr xbar e he_on β assign s hs_card hsplace h_dim]
    refine ⟨placementPerm hr s hs_card,
      ⟨⟨((1 : ℝ) / (γ s : ℝ) : ℂ) • (subsetVrepTail hr e β assign s hs_card).vec⟩, ?_⟩,
      h_dim, ?_⟩
    · -- tail normalization
      rw [hγeq]
      exact ket_normalized_of_ne_zero (subsetVrepTail hr e β assign s hs_card) htail_ne
    · -- the Vrep equation, rescaled by `1/γ_s`
      rw [dif_pos hsne]
      simp only [hdec_enc]
      -- `θ_pow = θ^{⊗(n−r)}` with `θ = e xbar`.
      rw [show (⟨Quantum.TensorProducts.tensorPowVec θ.toKet.vec⟩ : Ket (d ^ (n - r)))
          = ⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ from by rw [he_theta]]
      rw [show (⟨((1 : ℝ) / (γ s : ℝ) : ℂ) • (subsetVrepTail hr e β assign s hs_card).vec⟩
            : Ket (d ^ r))
          = ((1 : ℝ) / (γ s : ℝ) : ℂ) • (subsetVrepTail hr e β assign s hs_card) from rfl]
      rw [Quantum.TensorProducts.Ket.tensor_smul_right]
      rw [show Ket.cast h_dim (((1 : ℝ) / (γ s : ℝ) : ℂ) •
            Quantum.TensorProducts.Ket.tensor
              (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
              (subsetVrepTail hr e β assign s hs_card))
          = ((1 : ℝ) / (γ s : ℝ) : ℂ) • Ket.cast h_dim
              (Quantum.TensorProducts.Ket.tensor
                (⟨Quantum.TensorProducts.tensorPowVec (e xbar).vec⟩ : Ket (d ^ (n - r)))
                (subsetVrepTail hr e β assign s hs_card)) from by
        ext k; simp [Quantum.TensorProducts.ket_cast_vec]]
      rw [Ket.smul_vec, Matrix.mulVec_smul]
      congr 1
      rw [hΨv]
      exact subsetPartialVec_eq_vrep hr xbar e β assign s hs_card hsplace h_dim

/-! ## Top-level assembly -/

/-- **`lem:symspacebin` (general `d`).** Any normalized `Ψ ∈ SymR(ℂ^d, n, θ, n−r)`
(`hmem : InRestrictedSymSpace d n r θ Ψ`) admits a `RestrictedSymSpaceWitness`: the
binomial-superposition orthonormal decomposition with the Hartley count
`|S| ≤ 2^{n·h(r/n)}`.

This is a short assembly over the four stage lemmas above:
Stage 1 (basis) → Stage 2 (computational-basis expansion) → Stage 3 (placement partition)
→ Stage 4 (orthonormal `Vrep` witness). All four stages are `sorry`-free, so this assembly
and the whole module are `sorry`-free. -/
theorem restrictedSymSpaceWitness_nonempty_of_mem
    {d n r : ℕ} [NeZero d] [NeZero (d ^ n)] (hr : r ≤ n)
    (θ : NormKet d) (Ψ : NormKet (d ^ n))
    (hmem : InRestrictedSymSpace d n r θ Ψ) :
    Nonempty (RestrictedSymSpaceWitness d n r θ Ψ) := by
  obtain ⟨xbar, e, he_on, he_theta⟩ := exists_thetaAdaptedKetBasis d θ
  obtain ⟨β, hβ_supp, hβ_expand⟩ :=
    inRestrictedSymSpace_computationalBasisExpansion hr θ Ψ hmem xbar e he_on he_theta
  obtain ⟨assign, hassign_mem, hassign_place, hpartition⟩ :=
    exists_placementAssignment (n - r) xbar e β hβ_supp
  exact restrictedSymSpaceWitness_of_placementPartition hr θ Ψ xbar e he_on he_theta
    β assign hassign_mem hassign_place (hβ_expand.trans hpartition)

end InfoTheory.SmoothMinEntropy.RestrictedSymSpaceDecomp

end -- noncomputable section
