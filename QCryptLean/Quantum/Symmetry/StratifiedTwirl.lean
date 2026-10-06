import QCryptLean.Quantum.Symmetry.RandomizedBlocking
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Subgroup

/-!
# The stratified (Young-subgroup) blocking twirl

The stratified compiler partitions the `N` protocol rounds into
`k` public strata of *fixed* sizes `n j` (composition `n : Fin k → ℕ`, `N = ∑ j n j`),
and averages a fixed post-processing map `F` over the **Young subgroup**
`Π_j S_{n_j} ↪ S_N` — permutations that only shuffle rounds *within* a stratum.

This mirrors the single-block `randomizedBlockingTwirl`
(`Quantum.Symmetry.randomizedBlockingTwirl`, which averages over the *full*
`S_N`), replacing `S_N` by the image of the Young subgroup and the normalization `N!⁻¹`
by `(∏_j n_j!)⁻¹`. The invariance and covariance proofs lift verbatim: they only use the
group-homomorphism property of `permutationRepresentation` and the reindexing
`Equiv.mulRight` of a group average by an element of the group summed over.

This is general quantum-symmetry infrastructure (no QKD-protocol content).

## Consumption route
The twirled map `stratifiedBlockingTwirl n F` is **Young-subgroup covariant**
(`StratifiedPermutationCovariant`, identity correction). This covariance, together with the
product reference `⊗_j bb84BellDeFinettiDensity (n j)` (`StratifiedDeFinettiDomination.lean`),
runs the per-stratum CKR/postselection lift at the product prefactor
`∏_j C(n_j + x_j − 1, x_j − 1)`.
The covariance is *not* full `S_N` covariance: the stratified twirl is invariant only under
within-stratum permutations, which is exactly the symmetry the product reference respects.

## Main definitions
- `permCongrHom`: conjugation of permutations by an equivalence, as a monoid hom.
- `youngPermHom`: the Young-subgroup embedding `Π_j S_{n_j} ↪ S_N` (block-wise action),
  built as `permCongr finSigmaFinEquiv ∘ sigmaCongrRightHom`.
- `stratifiedBlockingTwirl`: the Young-subgroup average
  `(∏_j n_j!)⁻¹ • ∑_{g ∈ Π_j S_{n_j}} F ∘ permConjLin d N (youngPermHom n g)`.
- `StratifiedPermutationCovariant`: Nahar, Tupkary, Zhao, Lütkenhaus, Tan Def-5 covariance
restricted to the Young subgroup.

## Main statements
- `youngPermHom_injective`: the Young-subgroup map is a genuine embedding.
- `stratifiedBlockingTwirl_perm_invariant`: exact invariance under within-stratum conjugation.
- `stratifiedBlockingTwirl_permutationCovariant`: Young-subgroup covariance, identity correction.
- `stratifiedBlockingTwirl_preserves_conjTranspose`: Hermiticity is inherited from `F`.
- `stratifiedBlockingTwirl_of_youngInvariant`: the twirl fixes already-Young-invariant maps.
- `stratifiedBlockingTwirl_eq_randomizedBlockingTwirl_of_k_eq_one`: for `k = 1` the Young
  subgroup is all of `S_N`, so the stratified twirl is the full randomized-blocking twirl.
-/

open Quantum.Operators Matrix Quantum.Channels
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Symmetry

/-!
## The Young-subgroup embedding `Π_j S_{n_j} ↪ S_N`
-/

/-- Conjugation of permutations by a fixed equivalence `e : α ≃ β`, packaged as a monoid
    homomorphism `Perm α →* Perm β`, `p ↦ e ∘ p ∘ e⁻¹`.

    This is the bundled form of `Equiv.permCongr`; it is used to transport the fibre-wise
    Young action along `finSigmaFinEquiv` into `Perm (Fin N)`. -/
def permCongrHom {α β : Type*} (e : α ≃ β) : Equiv.Perm α →* Equiv.Perm β where
  toFun := e.permCongr
  map_one' := by ext x; simp [Equiv.permCongr_apply]
  map_mul' := e.permCongr_mul

@[simp] lemma permCongrHom_apply {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) :
    permCongrHom e p = e.permCongr p := rfl

/-- `permCongrHom e` is injective (it is the underlying map of the equivalence
    `Equiv.permCongr e`). -/
lemma permCongrHom_injective {α β : Type*} (e : α ≃ β) :
    Function.Injective (permCongrHom e) :=
  e.permCongr.injective

/-- **The Young-subgroup embedding.** For a composition `n : Fin k → ℕ` with `N = ∑ j n j`,
    the product group `Π_j S_{n_j}` embeds into `S_N` by the block-wise action: a tuple
    `g` of within-stratum permutations acts on `Σ_j Fin (n j) ≃ Fin N` (via `finSigmaFinEquiv`)
    fibre-wise, permuting only the indices inside each stratum.

    Concretely `youngPermHom n = permCongr finSigmaFinEquiv ∘ sigmaCongrRightHom`. It is a
    monoid homomorphism, so `permutationRepresentation d N` of a product is the product of
    the representations — the single fact the invariance proof needs. -/
def youngPermHom {k : ℕ} (n : Fin k → ℕ) :
    (∀ j, Equiv.Perm (Fin (n j))) →* Equiv.Perm (Fin (∑ j, n j)) :=
  (permCongrHom finSigmaFinEquiv).comp (Equiv.Perm.sigmaCongrRightHom fun j => Fin (n j))

/-- The Young-subgroup map is a genuine embedding: distinct tuples of within-stratum
    permutations give distinct permutations of `Fin N`. -/
theorem youngPermHom_injective {k : ℕ} (n : Fin k → ℕ) :
    Function.Injective (youngPermHom n) :=
  (permCongrHom_injective finSigmaFinEquiv).comp Equiv.Perm.sigmaCongrRightHom_injective

/-!
## The stratified blocking twirl
-/

variable {k d dimOut : ℕ} [NeZero d]

/-- **The stratified (Young-subgroup) blocking twirl.** The average of a fixed
    post-processing map `F` over the Young subgroup `Π_j S_{n_j} ↪ S_N`, applied by
    conjugation before `F`, normalized by the subgroup order `∏_j n_j!`.

    This is the stratified analogue of `randomizedBlockingTwirl`: it symmetrizes only
    *within* each public stratum, so the downstream CKR lift pays the *product* de Finetti
    prefactor `∏_j C(n_j + x_j − 1, x_j − 1)` rather than the single-block `C(N + x − 1, x − 1)`. -/
def stratifiedBlockingTwirl (n : Fin k → ℕ)
    (F : Op (d ^ (∑ j, n j)) →ₗ[ℂ] Op dimOut) : Op (d ^ (∑ j, n j)) →ₗ[ℂ] Op dimOut :=
  ((∏ j, Nat.factorial (n j) : ℕ) : ℂ)⁻¹ •
    ∑ g : (∀ j, Equiv.Perm (Fin (n j))),
      F ∘ₗ permConjLin d (∑ j, n j) (youngPermHom n g)

/-- Pointwise form of `stratifiedBlockingTwirl`, exposing the conjugation sandwich. -/
lemma stratifiedBlockingTwirl_apply (n : Fin k → ℕ)
    (F : Op (d ^ (∑ j, n j)) →ₗ[ℂ] Op dimOut) (ρ : Op (d ^ (∑ j, n j))) :
    stratifiedBlockingTwirl n F ρ =
      ((∏ j, Nat.factorial (n j) : ℕ) : ℂ)⁻¹ •
        ∑ g : (∀ j, Equiv.Perm (Fin (n j))),
          F (permutationRepresentation d (∑ j, n j) (youngPermHom n g) * ρ *
              (permutationRepresentation d (∑ j, n j) (youngPermHom n g))ᴴ) := by
  simp only [stratifiedBlockingTwirl, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.comp_apply, permConjLin_apply]

/-- Conjugating the input by any *within-stratum* permutation `U_{youngPermHom n h}` leaves
    the stratified average unchanged: the Young-subgroup average absorbs `h` by reindexing.

    This is the *exact* invariance `Φ(U_h ρ U_h†) = Φ(ρ)` for `h` in the Young subgroup —
    the correction channel of the covariance hypothesis is the identity. -/
theorem stratifiedBlockingTwirl_perm_invariant (n : Fin k → ℕ)
    (F : Op (d ^ (∑ j, n j)) →ₗ[ℂ] Op dimOut) (h : ∀ j, Equiv.Perm (Fin (n j)))
    (ρ : Op (d ^ (∑ j, n j))) :
    stratifiedBlockingTwirl n F
        (permutationRepresentation d (∑ j, n j) (youngPermHom n h) * ρ *
          (permutationRepresentation d (∑ j, n j) (youngPermHom n h))ᴴ) =
      stratifiedBlockingTwirl n F ρ := by
  rw [stratifiedBlockingTwirl_apply, stratifiedBlockingTwirl_apply]
  -- Both sides are the same scalar times a Young-subgroup sum; compare the sums.
  refine congrArg (HSMul.hSMul _) ?_
  -- Each summand at `g` equals the plain summand at the product `g * h`.
  have key : ∀ g : (∀ j, Equiv.Perm (Fin (n j))),
      permutationRepresentation d (∑ j, n j) (youngPermHom n g) *
          (permutationRepresentation d (∑ j, n j) (youngPermHom n h) * ρ *
            (permutationRepresentation d (∑ j, n j) (youngPermHom n h))ᴴ) *
          (permutationRepresentation d (∑ j, n j) (youngPermHom n g))ᴴ =
        permutationRepresentation d (∑ j, n j) (youngPermHom n (g * h)) * ρ *
          (permutationRepresentation d (∑ j, n j) (youngPermHom n (g * h)))ᴴ := by
    intro g
    rw [map_mul, ← permutationRepresentation_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp_rw [key]
  -- Reindex the Young-subgroup sum by right multiplication with `h`.
  exact Equiv.sum_comp (Equiv.mulRight h)
    (fun g => F (permutationRepresentation d (∑ j, n j) (youngPermHom n g) * ρ *
      (permutationRepresentation d (∑ j, n j) (youngPermHom n g))ᴴ))

/-- **Young-subgroup covariance** (Nahar et al. Definition 5 restricted to the Young subgroup
    `Π_j S_{n_j} ↪ S_N`). A linear map `Δ : T(Aᴺ, B)` is Young-subgroup covariant for the
    composition `n` if every within-stratum permutation `h ∈ Π_j S_{n_j}` can be transferred
    through `Δ` using a CPTP correction on the output.

    This is *weaker* than full `PermutationCovariant` (covariance under all of `S_N`): the
    stratified twirl only symmetrizes within strata, so only within-stratum conjugations are
    intertwined. It is the exact hypothesis the per-stratum (product-reference) CKR lift needs. -/
structure StratifiedPermutationCovariant [NeZero dimOut] (n : Fin k → ℕ)
    (Δ : Op (d ^ (∑ j, n j)) →ₗ[ℂ] Op dimOut) : Prop where
  /-- For each within-stratum permutation tuple `h`, a CPTP correction `K_h` intertwines
      conjugation by `U_{youngPermHom n h}` through `Δ`. -/
  covariance : ∀ (h : ∀ j, Equiv.Perm (Fin (n j))),
    ∃ (K_h : Op dimOut → Op dimOut), IsCPTP K_h ∧
      ∀ (ρ : Op (d ^ (∑ j, n j))),
        Δ (permutationRepresentation d (∑ j, n j) (youngPermHom n h) * ρ *
            (permutationRepresentation d (∑ j, n j) (youngPermHom n h))ᴴ) = K_h (Δ ρ)

/-- **Covariance of the stratified blocking average.** The stratified blocking average of any fixed
post-processing
    map is Young-subgroup covariant, with the identity channel as the correction for every
    within-stratum permutation.

    Consequence: the per-stratum CKR/postselection lift applies to stratified-blocked
    protocols at the *product* de Finetti prefactor; the block structure of `F` never enters. -/
theorem stratifiedBlockingTwirl_permutationCovariant [NeZero dimOut] (n : Fin k → ℕ)
    (F : Op (d ^ (∑ j, n j)) →ₗ[ℂ] Op dimOut) :
    StratifiedPermutationCovariant n (stratifiedBlockingTwirl n F) where
  covariance h :=
    ⟨id, id_is_cptp dimOut,
      fun ρ => stratifiedBlockingTwirl_perm_invariant n F h ρ⟩

/-- The stratified blocking average preserves conjugate transposition whenever the underlying
    post-processing map does. Together with `stratifiedBlockingTwirl_permutationCovariant` this
    discharges the Hermiticity-preservation and covariance hypotheses of the CKR reduction for
    stratified-blocked protocols. -/
theorem stratifiedBlockingTwirl_preserves_conjTranspose (n : Fin k → ℕ)
    (F : Op (d ^ (∑ j, n j)) →ₗ[ℂ] Op dimOut)
    (hF : ∀ M : Op (d ^ (∑ j, n j)), F Mᴴ = (F M)ᴴ) (M : Op (d ^ (∑ j, n j))) :
    stratifiedBlockingTwirl n F Mᴴ = (stratifiedBlockingTwirl n F M)ᴴ := by
  rw [stratifiedBlockingTwirl_apply, stratifiedBlockingTwirl_apply,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  have hstar : star (((∏ j, Nat.factorial (n j) : ℕ) : ℂ))⁻¹ =
      (((∏ j, Nat.factorial (n j) : ℕ) : ℂ))⁻¹ := by
    rw [star_inv₀, star_natCast]
  rw [hstar]
  -- Compare the two Young-subgroup sums summand by summand; `hF` moves `ᴴ` inside `F`.
  refine congrArg (HSMul.hSMul _) (Finset.sum_congr rfl fun g _ => ?_)
  rw [← hF]
  refine congrArg F ?_
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-!
## Degenerate-case sanity lemmas
-/

/-- Cardinality of the Young subgroup: `|Π_j S_{n_j}| = ∏_j n_j!`. -/
lemma card_youngGroup (n : Fin k → ℕ) :
    Fintype.card (∀ j, Equiv.Perm (Fin (n j))) = ∏ j, Nat.factorial (n j) := by
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun j _ => by
    rw [Fintype.card_perm, Fintype.card_fin]

/-- **Sanity: idempotence on Young-invariant maps.** If `F` is already invariant under every
    within-stratum conjugation (`F ∘ permConjLin d N (youngPermHom n g) = F`), then averaging
    over the Young subgroup returns `F` unchanged. -/
theorem stratifiedBlockingTwirl_of_youngInvariant (n : Fin k → ℕ)
    (F : Op (d ^ (∑ j, n j)) →ₗ[ℂ] Op dimOut)
    (hF : ∀ g : (∀ j, Equiv.Perm (Fin (n j))),
      F ∘ₗ permConjLin d (∑ j, n j) (youngPermHom n g) = F) :
    stratifiedBlockingTwirl n F = F := by
  unfold stratifiedBlockingTwirl
  simp_rw [hF]
  rw [Finset.sum_const, Finset.card_univ, card_youngGroup]
  have hc : (0 : ℂ) < ((∏ j, Nat.factorial (n j) : ℕ) : ℂ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]

/-- **Sanity: `k = 1` recovers the full randomized-blocking twirl.** With a single stratum the
    Young subgroup `Π_{j : Fin 1} S_{n_j}` is all of `S_N` (`N = ∑ j n j = n 0`), so the
    stratified twirl coincides with the single-block `randomizedBlockingTwirl` at dimension
    `d ^ N` — the Young-subgroup reindexing collapses to the identity on `S_N`. -/
theorem stratifiedBlockingTwirl_eq_randomizedBlockingTwirl_of_k_eq_one [NeZero dimOut]
    (n : Fin 1 → ℕ) [NeZero (∑ j, n j)]
    (F : Op (d ^ (∑ j, n j)) →ₗ[ℂ] Op dimOut) :
    stratifiedBlockingTwirl n F = randomizedBlockingTwirl F := by
  have hcard : Fintype.card (∀ j, Equiv.Perm (Fin (n j))) =
      Fintype.card (Equiv.Perm (Fin (∑ j, n j))) := by
    rw [card_youngGroup, Fintype.card_perm, Fintype.card_fin, Fin.prod_univ_one,
      Fin.sum_univ_one]
  have hbij : Function.Bijective (youngPermHom n) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨youngPermHom_injective n, hcard⟩
  have hsum : (∑ g : (∀ j, Equiv.Perm (Fin (n j))),
        F ∘ₗ permConjLin d (∑ j, n j) (youngPermHom n g)) =
      ∑ π : Equiv.Perm (Fin (∑ j, n j)), F ∘ₗ permConjLin d (∑ j, n j) π :=
    Fintype.sum_bijective (youngPermHom n) hbij _ _ (fun _ => rfl)
  have hcoef : (∏ j, Nat.factorial (n j)) = Nat.factorial (∑ j, n j) := by
    rw [Fin.prod_univ_one, Fin.sum_univ_one]
  unfold stratifiedBlockingTwirl randomizedBlockingTwirl
  rw [hsum, hcoef]

end Quantum.Symmetry
