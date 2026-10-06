import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination
import QCryptLean.Quantum.Symmetry.OpTensorProdFin
import QCryptLean.InfoTheory.DeFinetti.Purification
import QCryptLean.Quantum.Symmetry.StratifiedTwirl
import QCryptLean.InfoTheory.DeFinetti.DeFinettiPrefactor

/-!
# The stratified de Finetti reference and its marginal domination

For the product-group (stratified) postselection compiler: it partitions the `N = ∑_j n_j`
protocol rounds into `k` public strata of *fixed* sizes `n : Fin k → ℕ` (a composition), and the
protocol is permutation-covariant only *within* each stratum (the Young subgroup
`Π_j S_{n_j} ↪ S_N`, `youngPermHom` in `StratifiedTwirl.lean`).  The domination target is then the
**product of per-stratum universal de Finetti references** (C1), and the postselection
prefactor is the *product* `∏_j C(n_j + 3, 3)` rather than the single-block
`C(N + 3, 3)`.

## The C1 reference (explicit)
- `stratifiedBellDeFinettiDensity n` : the `k`-fold tensor product
  `⊗_j bb84BellDeFinettiDensity (n j)` of the per-stratum universal Bell references
  (`Quantum.Symmetry.bb84BellDeFinettiDensity`), presented as an explicit `DensityOp`
  on `Op (4 ^ (∑ j, n j))` via the dimension identity `∏_j 4^{n_{rev j}} = 4^{∑_j n_j}`.
  The blocks are fed to `DensityOp.tensorProdFin` in **reversed** order (`Fin.rev`) so that
  stratum `j` lands on the low `finSigmaFinEquiv` positions `[∑_{i<j} n i, ∑_{i≤j} n i)` —
  the block partition the Young subgroup `youngPermHom` actually symmetrizes.
  This alignment is load-bearing for non-constant `n` (the reversal compensates
  `tensorProdFin`'s quotient-peeling recursion; see the def docstring for the `n = ![2,1]`
  counterexample it rules out).
  This is the C1 product reference: the classical shadow is a product of per-stratum
  universal references, **not** a correlated-`ν` joint mixture and **not** an
  empirical-marginal product.
- `stratifiedCKRPurification n` : the square-root/vectorization purification
  `purificationDensityOp (stratifiedBellDeFinettiDensity n)` of the product reference,
  the faithful stratified analogue of the single-block
  `bb84BellCKRDeFinettiPurification n = purificationDensityOp (bb84BellDeFinettiDensity n)`.
- `IsStratifiedCKRDeFinettiPurification` : the stratified analogue of
  `IsBellCKRDeFinettiPurification` (pure, with `4^{∑ n_j}` marginal equal to the product
  reference).

## The domination
- `stratified_domination_trace_one` : for a Young-invariant,
  jointly-Bell-diagonal density `ρ` on `(ℂ⁴)^{⊗N}` (trace `1`), the product reference
  dominates: `ρ ≤ (∏_j C(n_j+3,3)) · stratifiedBellDeFinettiDensity n`.  This is the
  tensor-lift of the single-block `bb84_bellSym_deFinetti_domination`.
- `stratified_marginal_dominated` : proved from `stratified_domination_trace_one`. The
  subnormalized form (the stratified analogue of
  `bb84_bellSym_subnormalized_marginal_dominated`): for a
  sub-normalized PSD `W`, `(∏_j C(n_j+3,3)) · stratifiedBellDeFinettiDensity n − W ⪰ 0`.

## The product prefactor
- `stratifiedDeFinettiPrefactor n = ∏_j deFinettiPrefactor 4 (n j) = ∏_j C(n_j+3,3)`.
- `stratifiedDeFinettiPrefactor_le_prod_pow` : `∏_j C(n_j+3,3) ≤ ∏_j (n_j+1)^3`.

Reference: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) Thm 3, Lemma 2 (`x = 4`,
joint Bell `ℤ₂×ℤ₂`
symmetry); CKR 2009 (arXiv:0809.3019) main.tex:268–:401 (\emph{Main Result}: Theorem
`\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328).  The single-stratum
objects tensored here
are `Quantum.Symmetry.bb84BellDeFinettiDensity`,
`InfoTheory.DeFinetti.deFinettiPrefactor`, and `youngPermHom` (`StratifiedTwirl.lean`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Math.RepresentationTheory InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Symmetry

/-! ## 1. The `k`-fold tensor product of density operators (varying dimension)

The state product `Quantum.Operators.DensityOp.tensorProdFin` (factor `0` first, on the high
digits) and its operator counterpart `Quantum.TensorProducts.Op.tensorProdFin`, with the bridge
`DensityOp.tensorProdFin_toOp`, are in `TensorProdFin.lean`. -/

/-! ## 2. The C1 product reference density -/

/-- Reindexing helper for the reference's block alignment: `∏_j 4^{n(rev j)} = 4^{∑_j n_j}`.
The block product commutes over the reversal `Fin.rev`, so building the reference with the
blocks fed to `DensityOp.tensorProdFin` in reversed order (to compensate its quotient-peeling
recursion and land stratum `j` on the low `finSigmaFinEquiv` positions) leaves the total
dimension `4^N` unchanged. -/
private lemma prod_pow_rev_eq (d : ℕ) {k : ℕ} (n : Fin k → ℕ) :
    (∏ j, d ^ n (Fin.rev j)) = d ^ (∑ j, n j) := by
  rw [show (∏ j, d ^ n (Fin.rev j)) = ∏ j, d ^ n j from
      Fintype.prod_equiv Fin.revPerm _ _ (fun j => by rw [Fin.revPerm_apply])]
  exact Finset.prod_pow_eq_pow_sum Finset.univ n d

/-- **The stratified Bell de Finetti reference** `⊗_j τ_Bell(n_j)` on `(ℂ⁴)^{⊗N}`,
`N = ∑_j n_j` (C1).  The `k`-fold tensor product of the per-stratum universal Bell
references `bb84BellDeFinettiDensity (n j)`, presented on `Op (4 ^ (∑ j, n j))` via the
dimension identity `∏_j 4^{n_{rev j}} = 4^{∑_j n_j}` (`prod_pow_rev_eq`).

**Block-order alignment (load-bearing).**  `DensityOp.tensorProdFin` peels index `0` onto the
Kronecker *quotient* (high positions) by its recursion, whereas the Young subgroup `youngPermHom`
(via `finSigmaFinEquiv`) places stratum `0` on the *low* positions `[0, n 0)`.  To make
this reference invariant under the assumed `youngPermHom` symmetry the two must agree, so the
blocks are fed to `tensorProdFin` in **reversed** order (`Fin.rev`): stratum `j` then lands on
Young block `j`.  The reversal is load-bearing for non-constant `n`: without it, at `n = ![2,1]`
the reference would be `τ(2)` on sites `{1,2}` ⊗ `τ(1)` on site `{0}` (partition `{1,2},{0}`)
while the Young symmetry acts on `{0,1},{2}`, and the Young-invariant Bell-diagonal state
`|β₀β₀⟩⟨β₀β₀|_{0,1} ⊗ |β₁⟩⟨β₁|_{2}` would violate the product-prefactor domination.

This is the C1 domination target: a *product* of per-stratum universal references.  The
cross-stratum correlation of the actual attacked state lives in Eve's purification, never
in this signal reference (which is a full product).  Explicit; no `Classical.choose`.

Reference: Nahar et al. 2024 (arXiv:2403.11851) Lemma 2 (`x = 4`), tensorized over strata. -/
def stratifiedBellDeFinettiDensity {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)] :
    DensityOp (4 ^ (∑ j, n j)) :=
  DensityOp.castDim (prod_pow_rev_eq 4 n)
    (DensityOp.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
      (fun j => bb84BellDeFinettiDensity (n (Fin.rev j))))

/-! ## 3. The purification reference -/

/-- **The stratified Bell de Finetti purification reference** on the paired
`(4^{∑ n_j})·(4^{∑ n_j})` register: the explicit square-root/vectorization purification
`(√τ ⊗ 𝟙)|Ω⟩⟨Ω|(√τ ⊗ 𝟙)†` of the stratified product reference
`stratifiedBellDeFinettiDensity n`.

This is the faithful stratified analogue of the single-block
`bb84BellCKRDeFinettiPurification n = purificationDensityOp (bb84BellDeFinettiDensity n)`
(EveVisibleBaseScheme/BellReference.lean): each single-stratum purification is itself the
square-root purification of `τ_Bell(n_j)`, and the square-root purification of the product
reference purifies the same product density.  Explicit; no `Classical.choose`. -/
def stratifiedCKRPurification {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)]
    [NeZero (∑ j, n j)] : DensityOp ((4 ^ (∑ j, n j)) * (4 ^ (∑ j, n j))) :=
  haveI : NeZero ((4 : ℕ) ^ (∑ j, n j)) := ⟨pow_ne_zero _ (by norm_num)⟩
  purificationDensityOp (stratifiedBellDeFinettiDensity n)

/-- **A pure state whose `4^{∑ n_j}` marginal is the stratified product reference.**  The
stratified analogue of `IsBellCKRDeFinettiPurification`, with the single-block Bell
reference replaced by the product reference `stratifiedBellDeFinettiDensity n`. -/
structure IsStratifiedCKRDeFinettiPurification {k : ℕ} {n : Fin k → ℕ} [∀ j, NeZero (n j)]
    {dimR : ℕ} (τ : DensityOp ((4 ^ (∑ j, n j)) * dimR)) : Prop where
  isPure : τ.IsPure
  marginal : τ.partialTraceB = stratifiedBellDeFinettiDensity n

/-- The explicit `stratifiedCKRPurification` is a stratified CKR de Finetti purification:
it is pure and its `4^{∑ n_j}` marginal equals the product reference.  Both fields are
discharged by the general square-root purification lemmas
`purificationDensityOp_isPure` / `purificationDensityOp_partialTraceB`. -/
theorem stratifiedCKRPurification_isPurification {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)]
    [NeZero (∑ j, n j)] :
    IsStratifiedCKRDeFinettiPurification (stratifiedCKRPurification n) := by
  haveI : NeZero ((4 : ℕ) ^ (∑ j, n j)) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact ⟨purificationDensityOp_isPure _, purificationDensityOp_partialTraceB _⟩

/-- **Existence of a stratified CKR de Finetti purification** on a reference register of
dimension `4^{∑ n_j}`.  Witnessed explicitly by `stratifiedCKRPurification`. -/
theorem stratified_ckrPurification_exists {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)]
    [NeZero (∑ j, n j)] :
    ∃ (dimR : ℕ) (_ : NeZero dimR) (τ : DensityOp ((4 ^ (∑ j, n j)) * dimR)),
      IsStratifiedCKRDeFinettiPurification τ := by
  haveI : NeZero ((4 : ℕ) ^ (∑ j, n j)) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact ⟨4 ^ (∑ j, n j), inferInstance, stratifiedCKRPurification n,
    stratifiedCKRPurification_isPurification n⟩

/-! ## 4. The product de Finetti prefactor `∏_j C(n_j+3,3)` -/

/-- **The stratified de Finetti prefactor** `∏_j g_{n_j,4} = ∏_j C(n_j + 3, 3)`, the product
over strata of the per-stratum Bell symmetric-subspace dimensions
`deFinettiPrefactor 4 (n j) = dim Sym^{n_j}(ℂ⁴)`.  This is the *product* postselection
factor of the stratified compiler, in place of the single-block `C(N + 3, 3)`. -/
def stratifiedDeFinettiPrefactor {k : ℕ} (n : Fin k → ℕ) : ℕ :=
  ∏ j, deFinettiPrefactor 4 (n j)

/-- The stratified prefactor written out as a product of binomial coefficients
`∏_j C(n_j + 3, 3)`. -/
theorem stratifiedDeFinettiPrefactor_eq_prod_choose {k : ℕ} (n : Fin k → ℕ) :
    stratifiedDeFinettiPrefactor n = ∏ j, Nat.choose (n j + 3) 3 := by
  unfold stratifiedDeFinettiPrefactor
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : n j + 4 - 1 = n j + 3 := by omega
  have h2 : (4 : ℕ) - 1 = 3 := rfl
  rw [deFinettiPrefactor, h1, h2]

/-- The stratified prefactor is positive. -/
theorem stratifiedDeFinettiPrefactor_pos {k : ℕ} (n : Fin k → ℕ) :
    0 < stratifiedDeFinettiPrefactor n :=
  Finset.prod_pos fun j _ => deFinettiPrefactor_pos 4 (n j)

/-- **The product CKR bound dominates the product prefactor:**
`∏_j C(n_j+3,3) ≤ ∏_j (n_j+1)^3`.  The per-stratum CKR bound `deFinettiPrefactor_le_pow`
tensored over strata, giving the polynomial degree gain of the product route. -/
theorem stratifiedDeFinettiPrefactor_le_prod_pow {k : ℕ} (n : Fin k → ℕ) :
    stratifiedDeFinettiPrefactor n ≤ ∏ j, (n j + 1) ^ 3 := by
  unfold stratifiedDeFinettiPrefactor
  refine Finset.prod_le_prod' fun j => ?_
  have h := deFinettiPrefactor_le_pow 4 (n j)
  simpa using h

/-! ## 5. The marginal domination -/

/-- Scaling by a scalar preserves joint-Bell-diagonality (the IID Bell twirl is linear). -/
theorem isIIDBellDiagonal_smul {N : ℕ} (c : ℂ) {M : Op (4 ^ N)}
    (hM : IsIIDBellDiagonal M) : IsIIDBellDiagonal (c • M) := by
  unfold IsIIDBellDiagonal at hM ⊢
  rw [bb84BellTwirl_smul, hM]

/-- Conjugation by the (unitary) `N`-fold Bell rotation preserves positive semidefiniteness
(the general-`N` companion of the single-block `posSemidef_conj_iff`). -/
private theorem bellRotation_posSemidef_conj_iff (N : ℕ) (M : Op (4 ^ N)) :
    (bellRotation N * M * (bellRotation N)ᴴ).PosSemidef ↔ M.PosSemidef := by
  constructor
  · intro hM
    have h2 := hM.mul_mul_conjTranspose_same (bellRotation N)ᴴ
    rw [Matrix.conjTranspose_conjTranspose] at h2
    have he : (bellRotation N)ᴴ * (bellRotation N * M * (bellRotation N)ᴴ) * bellRotation N
        = M := by
      rw [show (bellRotation N)ᴴ * (bellRotation N * M * (bellRotation N)ᴴ) * bellRotation N
            = ((bellRotation N)ᴴ * bellRotation N) * M * ((bellRotation N)ᴴ * bellRotation N)
          from by noncomm_ring, bellRotation_unitary, Matrix.one_mul, Matrix.mul_one]
    rwa [he] at h2
  · intro hM
    exact hM.mul_mul_conjTranspose_same (bellRotation N)

/-- A joint-Bell-diagonal operator is diagonal in the joint Bell basis: the Bell-rotated
operator equals its own diagonal (general-`N` companion of the single-block `rho_conj_diag`). -/
private theorem bellDiag_conj_diag (N : ℕ) (M : Op (4 ^ N)) (hM : IsIIDBellDiagonal M) :
    bellRotation N * M * (bellRotation N)ᴴ
      = Matrix.diagonal (fun i => (bellRotation N * M * (bellRotation N)ᴴ) i i) := by
  ext i j
  rw [Matrix.diagonal_apply]
  by_cases hij : i = j
  · rw [if_pos hij, hij]
  · rw [if_neg hij]
    exact (iidBellDiagonal_iff_bellBasis_diagonal M).mp hM i j hij

/-- Reindexing helper: `∑_j n(rev j) = ∑_j n j`. -/
private lemma sum_rev_eq {k : ℕ} (n : Fin k → ℕ) :
    (∑ j, n (Fin.rev j)) = ∑ j, n j := by
  rw [← Equiv.sum_comp Fin.revPerm (fun j => n j)]
  exact Finset.sum_congr rfl fun j _ => by rw [Fin.revPerm_apply]

/-- Naturality of the Bell twirl under a dimension cast (`m = m'`). -/
private lemma bb84BellTwirl_castDim {m m' : ℕ} (h : m = m') (A : Op (4 ^ m)) :
    bb84BellTwirl m' (Op.castDim (by rw [h]) A) =
      Op.castDim (by rw [h]) (bb84BellTwirl m A) := by
  subst h; rfl

/-- **The stratified product reference is jointly Bell-diagonal** (crux (a) of the domination):
the `k`-fold tensor product `⊗_j τ_Bell(n_j)` is a fixed point of the joint `N`-pair Bell twirl.

Each factor `bb84BellDeFinettiDensity (n j)` is Bell-diagonal (it is a Bell twirl), and the joint
`N`-pair Bell twirl factorizes across strata (`bb84BellTwirl` averages conjugations by tensor
families of single-pair twirls, which respect the block structure of `finSigmaFinEquiv`), so the
product of the per-stratum fixed points is a joint fixed point.  This is the tensor-factorization
content that underlies the reference-diagonal identity; it rests on the Young/tensor naturality of
`bellRotation` across the
`Fin (4^N) ≃ ∏_j Fin (4^{n_j})` decomposition. -/
theorem stratifiedBellDeFinettiDensity_isIIDBellDiagonal {k : ℕ} (n : Fin k → ℕ)
    [∀ j, NeZero (n j)] :
    IsIIDBellDiagonal (stratifiedBellDeFinettiDensity n).toOp := by
  have key := bb84BellTwirl_tensorProdFin (fun j => n (Fin.rev j))
    (fun j => (bb84BellDeFinettiDensity (n (Fin.rev j))).toOp)
  have hfix : (fun j => bb84BellTwirl (n (Fin.rev j))
        ((bb84BellDeFinettiDensity (n (Fin.rev j))).toOp))
      = (fun j => (bb84BellDeFinettiDensity (n (Fin.rev j))).toOp) := by
    funext j
    exact bb84BellDeFinettiDensity_isIIDBellDiagonal (n (Fin.rev j))
  rw [hfix] at key
  set Y' : Op (4 ^ (∑ j, n (Fin.rev j))) :=
    Op.castDim (Finset.prod_pow_eq_pow_sum Finset.univ (fun j => n (Fin.rev j)) 4)
      (Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
        (fun j => (bb84BellDeFinettiDensity (n (Fin.rev j))).toOp)) with hY'
  -- key : bb84BellTwirl (∑ n(rev)) Y' = Y'
  unfold IsIIDBellDiagonal stratifiedBellDeFinettiDensity
  rw [Quantum.Operators.densityOp_castDim_toOp, DensityOp.tensorProdFin_toOp]
  -- goal : bb84BellTwirl (∑ n j) (castDim _ (tpf M)) = castDim _ (tpf M)
  have hXeq : Op.castDim (prod_pow_rev_eq 4 n)
        (Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
          (fun j => (bb84BellDeFinettiDensity (n (Fin.rev j))).toOp))
      = Op.castDim (by rw [sum_rev_eq n]) Y' := by
    rw [hY', Op.castDim_trans]
  rw [hXeq, bb84BellTwirl_castDim (sum_rev_eq n) Y', key]

/-! ### Generic linear-algebra helpers for the per-index domination -/

/-! The multilinearity and diagonal laws of the varying-dimension product used below are
`Quantum.TensorProducts.Op.tensorProdFin_sum`, `Op.tensorProdFin_smul` and
`Op.tensorProdFin_diag_congr`; the cast transport is `Op.castDim_trans`/`Op.castDim_sum` in
`CastDim.lean`. -/

/-! ### Bell-rotation commutes with permutation representations (general `N`) -/

/-- The Bell rotation commutes with every permutation representation. -/
private theorem bellRotation_comm_permRep (N : ℕ) (τ : Equiv.Perm (Fin N)) :
    bellRotation N * permutationRepresentation 4 N τ =
      permutationRepresentation 4 N τ * bellRotation N :=
  tensorFamily_mul_permutationRepresentation _ τ

/-- Bell-rotation conjugation commutes with a dimension cast. -/
private lemma bellRotation_conj_castDim {m m' : ℕ} (h : m = m') (A : Op (4 ^ m)) :
    bellRotation m' * Op.castDim (by rw [h]) A * (bellRotation m')ᴴ =
      Op.castDim (by rw [h]) (bellRotation m * A * (bellRotation m)ᴴ) := by
  subst h; rfl

/-! ### The Young symmetric projector and its factorization -/

/-- **The Young (product) symmetric projector**
`P_Y = (1/|G|) ∑_{g ∈ Π_j S_{n_j}} U_{youngPermHom g}`: the average of the joint permutation
representation over the Young subgroup.  Its joint-Bell diagonal is the domination bound. -/
private def youngProjector {k : ℕ} (n : Fin k → ℕ) : Op (4 ^ (∑ j, n j)) :=
  (1 / (Fintype.card (∀ j, Equiv.Perm (Fin (n j))) : ℂ)) •
    ∑ g : (∀ j, Equiv.Perm (Fin (n j))),
      permutationRepresentation 4 (∑ j, n j) (youngPermHom n g)

/-- `|Π_j S_{n_j}| = ∏_j n_j!`. -/
private lemma card_young {k : ℕ} (n : Fin k → ℕ) :
    Fintype.card (∀ j, Equiv.Perm (Fin (n j))) = ∏ j, Nat.factorial (n j) := by
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun j _ => by rw [Fintype.card_perm, Fintype.card_fin]

/-- `∏_j (n_{rev j})! = ∏_j n_j!`. -/
private lemma prod_factorial_rev {k : ℕ} (n : Fin k → ℕ) :
    (∏ j, Nat.factorial (n (Fin.rev j))) = ∏ j, Nat.factorial (n j) :=
  Fintype.prod_equiv Fin.revPerm _ _ (fun j => by rw [Fin.revPerm_apply])

/-- The un-normalized permutation-sum is `m! · P_sym`. -/
private lemma sum_permRep_eq (m : ℕ) [NeZero m] :
    (∑ s : Equiv.Perm (Fin m), permutationRepresentation 4 m s) =
      (Nat.factorial m : ℂ) • symmetricProjector 4 m := by
  rw [symmetricProjector, symmetricProjectorRep, smul_smul, mul_one_div,
    div_self (by exact_mod_cast (Nat.factorial_pos m).ne'), one_smul]

/-- Rescaling the single-stratum Bell reference by its prefactor gives the twirled projector. -/
private lemma bb84BellDeFinettiDensity_smul_eq_twirl (m : ℕ) [NeZero m] :
    (Nat.choose (m + 3) 3 : ℂ) • (bb84BellDeFinettiDensity m).toOp =
      bb84BellTwirl m (symmetricProjector 4 m) := by
  change (Nat.choose (m + 3) 3 : ℂ) •
      bb84BellTwirl m ((Nat.choose (m + 3) 3 : ℂ)⁻¹ • symmetricProjector 4 m) = _
  rw [← bb84BellTwirl_smul, smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast (Nat.choose_pos (show 3 ≤ m + 3 by omega)).ne'), one_smul]

/-- **The Young projector factorizes across strata** as the reversed product of the per-stratum
symmetric projectors: `P_Y = ⊗_j P_sym^{(n_{rev j})}`.  This is crux (a) distributed over the
group average, using multilinearity of `tensorProdFin` (`Op.tensorProdFin_sum`,
`Op.tensorProdFin_smul`). -/
private theorem youngProjector_eq_tensorProdFin {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)] :
    youngProjector n =
      Op.castDim (prod_pow_rev_eq 4 n)
        (Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
          (fun j => symmetricProjector 4 (n (Fin.rev j)))) := by
  have hstep : ∀ g : (∀ j, Equiv.Perm (Fin (n j))),
      permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) =
        Op.castDim (prod_pow_rev_eq 4 n) (Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
          (fun j => permutationRepresentation 4 (n (Fin.rev j)) (g (Fin.rev j)))) :=
    fun g => permutationRepresentation_youngPermHom_tensorProdFin n 4 g
  unfold youngProjector
  simp_rw [hstep]
  rw [← Op.castDim_sum]
  -- reindex the group average by `Fin.rev`
  rw [show (∑ g : (∀ j, Equiv.Perm (Fin (n j))),
        Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
          (fun j => permutationRepresentation 4 (n (Fin.rev j)) (g (Fin.rev j))))
      = ∑ h : (∀ j, Equiv.Perm (Fin (n (Fin.rev j)))),
          Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
            (fun j => permutationRepresentation 4 (n (Fin.rev j)) (h j)) from
    (Fintype.sum_equiv
      (Equiv.piCongrLeft' (fun j => Equiv.Perm (Fin (n j))) Fin.revPerm) _ _
      (fun _ => rfl))]
  rw [← Op.tensorProdFin_sum k (fun j => 4 ^ n (Fin.rev j))
      (fun j => fun s => permutationRepresentation 4 (n (Fin.rev j)) s)]
  simp_rw [sum_permRep_eq]
  rw [Op.tensorProdFin_smul, Op.castDim_smul, smul_smul]
  rw [show (fun j => (Nat.factorial (n (Fin.rev j)) : ℂ)) = fun j =>
      ((Nat.factorial (n (Fin.rev j)) : ℕ) : ℂ) from rfl]
  rw [← Nat.cast_prod, prod_factorial_rev, ← card_young]
  rw [one_div, inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos).ne'), one_smul]

/-- **The prefactor-scaled reference factorizes** as the reversed product of the per-stratum
Bell-twirled symmetric projectors `⊗_j bb84BellTwirl(P_sym^{(n_{rev j})})` (crux (a)/reference
structure + per-block `deFinetti_smul_eq`). -/
private theorem prefactor_smul_ref_eq {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)] :
    (stratifiedDeFinettiPrefactor n : ℂ) • (stratifiedBellDeFinettiDensity n).toOp =
      Op.castDim (prod_pow_rev_eq 4 n)
        (Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
          (fun j => bb84BellTwirl (n (Fin.rev j)) (symmetricProjector 4 (n (Fin.rev j))))) := by
  have hpref : (stratifiedDeFinettiPrefactor n : ℂ) =
      ∏ j, (Nat.choose (n (Fin.rev j) + 3) 3 : ℂ) := by
    rw [stratifiedDeFinettiPrefactor_eq_prod_choose, Nat.cast_prod]
    exact (Fintype.prod_equiv Fin.revPerm _ _ (fun j => by rw [Fin.revPerm_apply])).symm
  have href : (stratifiedBellDeFinettiDensity n).toOp =
      Op.castDim (prod_pow_rev_eq 4 n) (Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
        (fun j => (bb84BellDeFinettiDensity (n (Fin.rev j))).toOp)) := by
    rw [stratifiedBellDeFinettiDensity, Quantum.Operators.densityOp_castDim_toOp,
      DensityOp.tensorProdFin_toOp]
  rw [href, ← Op.castDim_smul, hpref, ← Op.tensorProdFin_smul]
  refine congrArg _ (congrArg _ (funext fun j => ?_))
  exact bb84BellDeFinettiDensity_smul_eq_twirl (n (Fin.rev j))

/-- **The prefactor-scaled reference diagonal equals the Young-projector diagonal** (Lemma C):
`∏_j C(n_j+3,3) · ⟨β_i|τ_ref|β_i⟩ = ⟨i|P_Y|i⟩`.  Both are the product
`∏_j ⟨i_j|P_sym^{(n_{rev j})}|i_j⟩` via crux (b) + the single-block `twirl_symProj_diag`; the
Kronecker diagonal only sees factor diagonals (`Op.tensorProdFin_diag_congr`). -/
private theorem ref_diag_eq_youngProjector {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)]
    (i : Fin (4 ^ (∑ j, n j))) :
    (stratifiedDeFinettiPrefactor n : ℂ) *
        (bellRotation (∑ j, n j) * (stratifiedBellDeFinettiDensity n).toOp *
          (bellRotation (∑ j, n j))ᴴ) i i =
      youngProjector n i i := by
  rw [show (stratifiedDeFinettiPrefactor n : ℂ) *
          (bellRotation (∑ j, n j) * (stratifiedBellDeFinettiDensity n).toOp *
            (bellRotation (∑ j, n j))ᴴ) i i
        = (bellRotation (∑ j, n j) *
            ((stratifiedDeFinettiPrefactor n : ℂ) • (stratifiedBellDeFinettiDensity n).toOp) *
            (bellRotation (∑ j, n j))ᴴ) i i
      from by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]]
  rw [prefactor_smul_ref_eq]
  rw [show Op.castDim (prod_pow_rev_eq 4 n)
          (Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
            (fun j => bb84BellTwirl (n (Fin.rev j)) (symmetricProjector 4 (n (Fin.rev j)))))
        = Op.castDim (by rw [sum_rev_eq n])
            (Op.castDim (Finset.prod_pow_eq_pow_sum Finset.univ (fun j => n (Fin.rev j)) 4)
              (Op.tensorProdFin k (fun j => 4 ^ n (Fin.rev j))
                (fun j => bb84BellTwirl (n (Fin.rev j)) (symmetricProjector 4 (n (Fin.rev j))))))
      from by rw [Op.castDim_trans]]
  rw [bellRotation_conj_castDim (sum_rev_eq n),
    bellRotation_tensorProdFin_conj (fun j => n (Fin.rev j))
      (fun j => bb84BellTwirl (n (Fin.rev j)) (symmetricProjector 4 (n (Fin.rev j))))]
  simp_rw [twirl_symProj_diag]
  rw [Op.castDim_trans, youngProjector_eq_tensorProdFin, Op.castDim_apply, Op.castDim_apply]
  exact congrFun (Op.tensorProdFin_diag_congr k (fun j => 4 ^ n (Fin.rev j))
    (A := fun j => Matrix.diagonal (fun a => symmetricProjector 4 (n (Fin.rev j)) a a))
    (B := fun j => symmetricProjector 4 (n (Fin.rev j)))
    (fun j => Matrix.diag_diagonal _)) _

/-- **The per-joint-Bell-index domination bound** (crux (b)+(c) of the domination; the orbit-sum
core): the joint-Bell diagonal entry `λ_i = ⟨β_i|ρ|β_i⟩` is dominated by the reference diagonal
scaled by the product prefactor.

Mirrors the single-block `domination_per_index` with "type" → "joint type tuple across strata".
Young-invariance makes `λ` constant on each *product* type-orbit; the orbit size is the product
multinomial `∏_j multinomial(T_j)` (the per-stratum coset/stabilizer count), and single-term-≤-trace
gives `∏_j multinomial(T_j) · λ_i ≤ 1`.  The reference diagonal is exactly
`∏_j C(n_j+3,3)⁻¹ / multinomial(T_j)`, so `λ_i ≤ ∏_j C(n_j+3,3) · ref_diag(i)`.  This rests on the
Young permutation factorizing across strata (`youngPermHom` block structure) and the reference
diagonal factorizing (crux (a)).  Bell-diagonality of `ρ` is not needed for this per-index bound;
it enters only when the diagonal bounds are reassembled into the operator inequality
(`stratified_domination_trace_one`). -/
theorem stratified_domination_per_index {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)]
    (ρ : Op (4 ^ (∑ j, n j))) (hρ_psd : ρ.PosSemidef) (hρ_trace : ρ.trace = 1)
    (hρ_young : ∀ h : ∀ j, Equiv.Perm (Fin (n j)),
      permutationRepresentation 4 (∑ j, n j) (youngPermHom n h) * ρ =
        ρ * permutationRepresentation 4 (∑ j, n j) (youngPermHom n h))
    (i : Fin (4 ^ (∑ j, n j))) :
    (bellRotation (∑ j, n j) * ρ * (bellRotation (∑ j, n j))ᴴ) i i ≤
      (stratifiedDeFinettiPrefactor n : ℂ) *
        (bellRotation (∑ j, n j) * (stratifiedBellDeFinettiDensity n).toOp *
          (bellRotation (∑ j, n j))ᴴ) i i := by
  -- Reduce the RHS to the Young-projector diagonal (Lemma C), then run the coset counting.
  rw [ref_diag_eq_youngProjector]
  set W := bellRotation (∑ j, n j) with hWdef
  set e := @finFunctionFinEquiv 4 (∑ j, n j) with hedef
  set M := W * ρ * Wᴴ with hMdef
  have hMpsd : M.PosSemidef := (bellRotation_posSemidef_conj_iff (∑ j, n j) ρ).mpr hρ_psd
  have hMtr : M.trace = 1 := by
    rw [hMdef, Matrix.trace_mul_comm, ← Matrix.mul_assoc, bellRotation_unitary, Matrix.one_mul,
      hρ_trace]
  have hMinv : ∀ g : (∀ j, Equiv.Perm (Fin (n j))),
      permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) * M *
        (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ = M := by
    intro g
    have c1 : permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) * W =
        W * permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) :=
      (bellRotation_comm_permRep (∑ j, n j) (youngPermHom n g)).symm
    have c2 : Wᴴ * (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ =
        (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ * Wᴴ := by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, c1]
    have huu : permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) *
        (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ = 1 :=
      (permutationRepresentation_unitary 4 (∑ j, n j) (youngPermHom n g)).2
    rw [hMdef]
    calc permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) * (W * ρ * Wᴴ) *
            (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ
        = (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) * W) * ρ *
            (Wᴴ * (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ) := by noncomm_ring
      _ = (W * permutationRepresentation 4 (∑ j, n j) (youngPermHom n g)) * ρ *
            ((permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ * Wᴴ) := by rw [c1, c2]
      _ = W * (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) * ρ) *
            (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ * Wᴴ := by noncomm_ring
      _ = W * (ρ * permutationRepresentation 4 (∑ j, n j) (youngPermHom n g)) *
            (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ * Wᴴ := by rw [hρ_young g]
      _ = W * ρ * (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) *
            (permutationRepresentation 4 (∑ j, n j) (youngPermHom n g))ᴴ) * Wᴴ := by noncomm_ring
      _ = W * ρ * Wᴴ := by rw [huu, Matrix.mul_one]
  have horb : ∀ g : (∀ j, Equiv.Perm (Fin (n j))),
      M i i = M (e (e.symm i ∘ youngPermHom n g)) (e (e.symm i ∘ youngPermHom n g)) := by
    intro g
    have hp := permRep_conj_entry (youngPermHom n g) M i i
    rw [hMinv g] at hp
    exact hp
  classical
  set pidx : (∀ j, Equiv.Perm (Fin (n j))) → Fin (4 ^ (∑ j, n j)) :=
    fun g => e (e.symm i ∘ youngPermHom n g) with hpidx
  set cnt : Fin (4 ^ (∑ j, n j)) → ℕ :=
    fun kk => (Finset.univ.filter (fun g : (∀ j, Equiv.Perm (Fin (n j))) => pidx g = kk)).card
      with hcnt
  have hcoset : ∀ kk, cnt kk ≤ cnt i := by
    intro kk
    rcases Finset.eq_empty_or_nonempty
        (Finset.univ.filter (fun g : (∀ j, Equiv.Perm (Fin (n j))) => pidx g = kk)) with hemp | hne
    · simp only [hcnt, hemp, Finset.card_empty]; exact Nat.zero_le _
    · obtain ⟨τ, hτ⟩ := hne
      rw [Finset.mem_filter] at hτ
      simp only [hcnt]
      apply Finset.card_le_card_of_injOn (fun g => g * τ⁻¹)
      · intro g hg
        rw [Finset.mem_coe, Finset.mem_filter] at hg
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hcomp : e.symm i ∘ ⇑(youngPermHom n g) = e.symm i ∘ ⇑(youngPermHom n τ) := by
          have h1 : pidx g = pidx τ := hg.2.trans hτ.2.symm
          simp only [hpidx] at h1
          exact e.injective h1
        change pidx (g * τ⁻¹) = i
        simp only [hpidx]
        have hfix : e.symm i ∘ ⇑(youngPermHom n (g * τ⁻¹)) = e.symm i := by
          rw [map_mul, map_inv]
          funext a
          simp only [Function.comp_apply, Equiv.Perm.coe_mul, Equiv.Perm.inv_def]
          have h2 := congr_fun hcomp ((youngPermHom n τ).symm a)
          simp only [Function.comp_apply, Equiv.apply_symm_apply] at h2
          exact h2
        rw [hfix, Equiv.apply_symm_apply]
      · intro a _ b _ hab
        exact mul_right_cancel hab
  have hMsum : (∑ g : (∀ j, Equiv.Perm (Fin (n j))), M (pidx g) (pidx g))
      = ∑ kk, cnt kk • M kk kk := by
    have hexp : ∀ g : (∀ j, Equiv.Perm (Fin (n j))),
        M (pidx g) (pidx g) = ∑ kk, (if pidx g = kk then M kk kk else 0) := by
      intro g
      rw [Finset.sum_ite_eq Finset.univ (pidx g) (fun kk => M kk kk), if_pos (Finset.mem_univ _)]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro kk _
    rw [← Finset.sum_filter, Finset.sum_const]
  have hMii : (Fintype.card (∀ j, Equiv.Perm (Fin (n j)))) • M i i = ∑ kk, cnt kk • M kk kk := by
    rw [← hMsum,
      show (∑ g : (∀ j, Equiv.Perm (Fin (n j))), M (pidx g) (pidx g))
          = ∑ _g : (∀ j, Equiv.Perm (Fin (n j))), M i i from
        Finset.sum_congr rfl (fun g _ => (horb g).symm),
      Finset.sum_const, Finset.card_univ]
  have hbound : (∑ kk, cnt kk • M kk kk) ≤ (cnt i) • (1 : ℂ) := by
    calc (∑ kk, cnt kk • M kk kk) ≤ ∑ kk, cnt i • M kk kk :=
          Finset.sum_le_sum (fun kk _ => nsmul_le_nsmul_left hMpsd.diag_nonneg (hcoset kk))
      _ = cnt i • ∑ kk, M kk kk := by rw [← Finset.smul_sum]
      _ = cnt i • M.trace := rfl
      _ = cnt i • (1 : ℂ) := by rw [hMtr]
  have hcard_ne : (Fintype.card (∀ j, Equiv.Perm (Fin (n j))) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos).ne'
  have hPii : (Fintype.card (∀ j, Equiv.Perm (Fin (n j)))) • youngProjector n i i
      = (cnt i : ℂ) := by
    rw [nsmul_eq_mul, youngProjector, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      ← mul_assoc, one_div, mul_inv_cancel₀ hcard_ne, one_mul]
    have hbridge : ∀ g : (∀ j, Equiv.Perm (Fin (n j))),
        permutationRepresentation 4 (∑ j, n j) (youngPermHom n g) i i =
          (if pidx g⁻¹ = i then (1 : ℂ) else 0) := by
      intro g
      simp only [permutationRepresentation, Matrix.of_apply, ← hedef]
      have hiff : (e.symm i = e.symm i ∘ ⇑(youngPermHom n g).symm) ↔ (pidx g⁻¹ = i) := by
        simp only [hpidx, map_inv, Equiv.Perm.inv_def]
        constructor
        · intro h; rw [← h]; exact Equiv.apply_symm_apply e i
        · intro h
          exact (e.injective (h.trans (Equiv.apply_symm_apply e i).symm)).symm
      simp only [hiff]
    rw [Finset.sum_congr rfl (fun g _ => hbridge g)]
    rw [Fintype.sum_bijective (fun g : (∀ j, Equiv.Perm (Fin (n j))) => g⁻¹)
        inv_involutive.bijective
        (fun g => if pidx g⁻¹ = i then (1 : ℂ) else 0)
        (fun g => if pidx g = i then (1 : ℂ) else 0) (fun g => by simp)]
    rw [Finset.sum_boole]
  have hcmp : (Fintype.card (∀ j, Equiv.Perm (Fin (n j)))) • M i i ≤
      (Fintype.card (∀ j, Equiv.Perm (Fin (n j)))) • youngProjector n i i := by
    rw [hMii, hPii]
    calc (∑ kk, cnt kk • M kk kk) ≤ (cnt i) • (1 : ℂ) := hbound
      _ = (cnt i : ℂ) := by rw [nsmul_eq_mul, mul_one]
  rw [nsmul_eq_mul, nsmul_eq_mul] at hcmp
  exact le_of_mul_le_mul_left hcmp (by exact_mod_cast Fintype.card_pos)

/-- **The stratified Bell de Finetti domination, trace-`1` form** (tensor-lift
of `bb84_bellSym_deFinetti_domination`).

For a density `ρ` on `(ℂ⁴)^{⊗N}`, `N = ∑_j n_j`, that is
- jointly-Bell-diagonal across every pair (`IsIIDBellDiagonal ρ`), and
- invariant under every *within-stratum* permutation of the Young subgroup
  `Π_j S_{n_j} ↪ S_N` (conjugation by `permutationRepresentation 4 N (youngPermHom n h)`),

the product reference dominates in the Löwner order:
`ρ ≤ (∏_j C(n_j+3,3)) · stratifiedBellDeFinettiDensity n`.

**Proof by tensor lifting.**  Conjugate both sides by the joint Bell
rotation `bellRotation N`.  Both `ρ` and the product reference are jointly Bell-diagonal
(the reference by `bb84BellTwirl`-invariance of each factor), so the inequality collapses to
a per-joint-Bell-index scalar bound, indexed by `i : Fin (4^N)`.  Decompose the index across
strata via the tensor structure `Fin (4^N) ≃ ∀ j, Fin (4^{n_j})` (compatible with
`finSigmaFinEquiv`, hence with `youngPermHom`), writing `i ↦ (i_j)_j`.

(a) *Reference diagonal factorizes:* the joint-Bell-diagonal entry of
`stratifiedBellDeFinettiDensity n` at `i` is `∏_j C(n_j+3,3)⁻¹ · ⟨i_j|P_sym^{(n_j)}|i_j⟩`
(the per-stratum symmetric-projector diagonals of the single-block reference, multiplied).

(b) *Young orbit / product type-count:* Young-invariance makes the Bell-rotated `ρ`
diagonal constant on each *within-stratum type orbit*, and the orbit is a product of the
per-stratum type orbits.  The single-block coset argument (`domination_per_index`) applied
per stratum, with the product multinomial count `∏_j multinomial(T_j)` (Burnside via
`Quantum.Symmetry.symmetricProjectorDirectSum_trace` and
`sum_card_fixedBy_perm_fun_eq_of_fintype`), gives the
per-index bound `(bellRotation N · ρ · bellRotation N†) i i ≤ ∏_j ⟨i_j|P_sym^{(n_j)}|i_j⟩`.

(c) *Combine:* the classical core is near-trivial with the universal product reference —
`p/u = P(type-pair) · ∏_j C(n_j+3,3) ≤ ∏_j C(n_j+3,3)` (tight).  Substituting
(a) into (b) yields the diagonal domination, and `Matrix.posSemidef_diagonal_iff` reassembles
it into the operator inequality. -/
theorem stratified_domination_trace_one {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)]
    (ρ : Op (4 ^ (∑ j, n j))) (hρ_psd : ρ.PosSemidef) (hρ_trace : ρ.trace = 1)
    (hρ_young : ∀ h : ∀ j, Equiv.Perm (Fin (n j)),
      permutationRepresentation 4 (∑ j, n j) (youngPermHom n h) * ρ =
        ρ * permutationRepresentation 4 (∑ j, n j) (youngPermHom n h))
    (hρ_bell : IsIIDBellDiagonal ρ) :
    ρ ≤ (stratifiedDeFinettiPrefactor n : ℂ) • (stratifiedBellDeFinettiDensity n).toOp := by
  rw [Matrix.le_iff, ← bellRotation_posSemidef_conj_iff (∑ j, n j)]
  have hSdiag := bellDiag_conj_diag (∑ j, n j) (stratifiedBellDeFinettiDensity n).toOp
    (stratifiedBellDeFinettiDensity_isIIDBellDiagonal n)
  have hρdiag := bellDiag_conj_diag (∑ j, n j) ρ hρ_bell
  have hdiff : bellRotation (∑ j, n j) *
        ((stratifiedDeFinettiPrefactor n : ℂ) • (stratifiedBellDeFinettiDensity n).toOp - ρ) *
        (bellRotation (∑ j, n j))ᴴ =
      Matrix.diagonal (fun i =>
        (stratifiedDeFinettiPrefactor n : ℂ) *
          (bellRotation (∑ j, n j) * (stratifiedBellDeFinettiDensity n).toOp *
            (bellRotation (∑ j, n j))ᴴ) i i -
        (bellRotation (∑ j, n j) * ρ * (bellRotation (∑ j, n j))ᴴ) i i) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hSdiag, hρdiag]
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [smul_eq_mul]
    · simp [hij]
  rw [hdiff, Matrix.posSemidef_diagonal_iff]
  intro i
  rw [sub_nonneg]
  exact stratified_domination_per_index n ρ hρ_psd hρ_trace hρ_young i

/-- **The stratified Bell de Finetti marginal domination, subnormalized form**
(tensor-lift of `bb84_bellSym_subnormalized_marginal_dominated`).

For any PSD `W` on `(ℂ⁴)^{⊗N}`, `N = ∑_j n_j`, that is
- jointly-Bell-diagonal across every pair (`IsIIDBellDiagonal W`),
- invariant under the Young subgroup `Π_j S_{n_j}` (within-stratum conjugation), and
- sub-normalized (`Tr W ≤ 1`),

the product reference dominates `W`:
`(∏_j C(n_j+3,3)) · stratifiedBellDeFinettiDensity n − W ⪰ 0`.

Proved from the trace-`1` core `stratified_domination_trace_one` by the standard
normalize-dominate-rescale argument: `(1/Tr W) · W` is a Young-invariant, jointly
Bell-diagonal density dominated by the reference, and scaling by `Tr W ≤ 1` against the PSD
reference recovers the subnormalized bound (the `(1−Tr W)·(prefactor)·reference` slack is
PSD). -/
theorem stratified_marginal_dominated {k : ℕ} (n : Fin k → ℕ) [∀ j, NeZero (n j)]
    (W : Op (4 ^ (∑ j, n j))) (hW_psd : W.PosSemidef) (hW_trace : W.trace.re ≤ 1)
    (hW_young : ∀ h : ∀ j, Equiv.Perm (Fin (n j)),
      permutationRepresentation 4 (∑ j, n j) (youngPermHom n h) * W =
        W * permutationRepresentation 4 (∑ j, n j) (youngPermHom n h))
    (hW_bell : IsIIDBellDiagonal W) :
    ((stratifiedDeFinettiPrefactor n : ℂ) • (stratifiedBellDeFinettiDensity n).toOp
      - W).PosSemidef := by
  set C : ℂ := (stratifiedDeFinettiPrefactor n : ℂ) with hC
  set S : Op (4 ^ (∑ j, n j)) := (stratifiedBellDeFinettiDensity n).toOp with hS
  have hS_psd : S.PosSemidef :=
    posSemidefOp_implies_mathlib (stratifiedBellDeFinettiDensity n).toPosSemidefOp
  have hCS_psd : (C • S).PosSemidef :=
    hS_psd.smul (by rw [hC]; exact_mod_cast Nat.cast_nonneg _)
  have hW_tr_nonneg : (0 : ℂ) ≤ W.trace := hW_psd.trace_nonneg
  have hW_re_nn : 0 ≤ W.trace.re := by
    have h := hW_tr_nonneg; rw [Complex.le_def] at h; simpa using h.1
  have hWim : W.trace.im = 0 := by
    have h := hW_tr_nonneg; rw [Complex.le_def] at h; simpa using h.2.symm
  by_cases hW0 : W = 0
  · rw [hW0, sub_zero]; exact hCS_psd
  · have ht_pos : (0 : ℝ) < W.trace.re := by
      rcases lt_or_eq_of_le hW_re_nn with h | h
      · exact h
      · exact absurd (hW_psd.trace_eq_zero_iff.mp (Complex.ext h.symm hWim)) hW0
    have ht_ne : W.trace ≠ 0 := by
      intro h; rw [h] at ht_pos; simp at ht_pos
    set ρn : Op (4 ^ (∑ j, n j)) := (1 / W.trace) • W with hρn
    have hinv_nonneg : (0 : ℂ) ≤ 1 / W.trace := by
      rw [Complex.le_def]
      refine ⟨?_, ?_⟩
      · simp only [Complex.zero_re, one_div, Complex.inv_re]
        exact div_nonneg ht_pos.le (Complex.normSq_nonneg _)
      · simp only [Complex.zero_im, one_div, Complex.inv_im, hWim]; simp
    have hρn_psd : ρn.PosSemidef := hW_psd.smul hinv_nonneg
    have hρn_trace : ρn.trace = 1 := by
      rw [hρn, Matrix.trace_smul, smul_eq_mul, one_div, inv_mul_cancel₀ ht_ne]
    have hρn_young : ∀ h : ∀ j, Equiv.Perm (Fin (n j)),
        permutationRepresentation 4 (∑ j, n j) (youngPermHom n h) * ρn =
          ρn * permutationRepresentation 4 (∑ j, n j) (youngPermHom n h) := by
      intro h
      rw [hρn, Matrix.mul_smul, Matrix.smul_mul, hW_young h]
    have hρn_bell : IsIIDBellDiagonal ρn := isIIDBellDiagonal_smul (1 / W.trace) hW_bell
    have hdom := stratified_domination_trace_one n ρn hρn_psd hρn_trace hρn_young hρn_bell
    rw [Matrix.le_iff] at hdom
    have hW_eq : W = W.trace • ρn := by
      rw [hρn, smul_smul, mul_one_div, div_self ht_ne, one_smul]
    have h1mt_nonneg : (0 : ℂ) ≤ 1 - W.trace := by
      rw [Complex.le_def]
      refine ⟨?_, ?_⟩
      · simp only [Complex.zero_re, Complex.sub_re, Complex.one_re]; linarith
      · simp only [Complex.zero_im, Complex.sub_im, Complex.one_im, hWim]; ring
    rw [hW_eq]
    have hsplit : C • S - W.trace • ρn =
        (1 - W.trace) • (C • S) + W.trace • (C • S - ρn) := by
      module
    rw [hsplit]
    exact (hCS_psd.smul h1mt_nonneg).add (hdom.smul hW_tr_nonneg)

/-! ## 6. `k = 1` sanity: recovering the single-block objects -/

/-- **Sanity: `k = 1` recovers the single-block prefactor** `C(n_0 + 3, 3)`.  With a single
stratum the product over `Fin 1` collapses to the one factor. -/
theorem stratifiedDeFinettiPrefactor_eq_of_k_eq_one (n : Fin 1 → ℕ) :
    stratifiedDeFinettiPrefactor n = deFinettiPrefactor 4 (n 0) := by
  unfold stratifiedDeFinettiPrefactor
  rw [Fin.prod_univ_one]

/-- **Sanity: `k = 1` recovers the single-block reference** `bb84BellDeFinettiDensity (n 0)`.
With a single stratum the product tensor is the one factor (tensored with the trivial state),
so `stratifiedBellDeFinettiDensity n` is the single-block reference up to the dimension cast
`4^{∑_{j : Fin 1} n_j} = 4^{n_0}`. -/
theorem stratifiedBellDeFinettiDensity_eq_of_k_eq_one (n : Fin 1 → ℕ) [∀ j, NeZero (n j)] :
    stratifiedBellDeFinettiDensity n =
      DensityOp.castDim (by rw [Fin.sum_univ_one]) (bb84BellDeFinettiDensity (n 0)) := by
  refine DensityOp.ext ?_
  apply Matrix.ext
  intro i j
  simp only [stratifiedBellDeFinettiDensity, DensityOp.tensorProdFin,
    DensityOp.castDim_toOp_apply, DensityOp.tensor, Quantum.TensorProducts.Op.tensor,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  simp only [DensityOp.trivial, finProdFinEquiv, Matrix.of_apply, Matrix.cons_val_fin_one,
    mul_one]
  congr 1 <;> (apply Fin.ext; simp [Fin.divNat, Nat.div_one]; rfl)

end Quantum.Symmetry

end -- noncomputable section
