import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination
import QCryptLean.Quantum.TensorProducts.TensorProdFin
import QCryptLean.Quantum.Symmetry.StratifiedTwirl
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.ConditioningIsometryInvariance

/-!
# Naturality of the joint symmetry operators across strata

For the product-group (stratified) postselection compiler: over a split of the `N = ∑ⱼ nⱼ` sites
into strata, the joint-`N` symmetry operators (`bellRotation`, `bb84BellTwirl`, and the
permutation representation of the Young subgroup) factorize across the varying-dimension tensor
product `Quantum.TensorProducts.Op.tensorProdFin` of the per-stratum blocks.

## Consumption route
Two statements in `StratifiedDeFinettiDomination.lean` rest on this layer:
- `stratifiedBellDeFinettiDensity_isIIDBellDiagonal` (consumer 1) needs the **Bell-twirl
  factorization** `bb84BellTwirl_tensorProdFin` (crux (c)): the joint `N`-pair twirl of a
  `tensorProdFin` factorizes as the `tensorProdFin` of the per-stratum twirls.  This is
  provable because the twirl is a *site-wise* (IID) channel and factorizes over any block
  grouping without the reversal.
- `stratified_domination_per_index` (consumer 2) needs the **permutation factorization**
  `permutationRepresentation_youngPermHom_tensorProdFin` (crux (a)) and the **Bell-rotation
  factorization** `bellRotation_tensorProdFin_conj` (crux (b)).

## Block-order convention (load-bearing)
`Op.tensorProdFin` recurses `(f 0) ⊗ tensorProdFin (tail)` (matching
`DensityOp.tensorProdFin`), so **block `0` lands on the Kronecker quotient side (the high
mixed-radix digits)**.  By contrast `finSigmaFinEquiv` is *contiguous ascending*, so
`youngPermHom` places **block `0` on the low positions `[0, n 0)`** (the low digits of
`finFunctionFinEquiv`, where `tensorFamily` puts site `0`).  These two conventions are
**reversed** (`Quantum.TensorProducts.tensorFamily_append`).
For *site-wise* operators (`bellRotation`, `bb84BellTwirl`) the reversal is invisible — the
per-site action respects any block grouping — so cruxes (b), (c) hold with block `j` on
slot `j`.  For *block-structured* `youngPermHom` (crux (a)) the reversal is genuine: the
factorization is over the reversed block index `Fin.rev`; at `n = ![2,1]`, `d = 2` it gives
(support permutation `[0,2,1,3,4,6,5,7] = id₂ ⊗ perm(swap 0 1)₄`).

The reference `stratifiedBellDeFinettiDensity` feeds its blocks to `tensorProdFin` in `Fin.rev`
order, so stratum `j` lands on Young block `j`; for non-constant `n` the non-reversed order would
give a different partition of `Fin N` (`n = ![2,1]`: `{1,2},{0}` against the Young `{0,1},{2}`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Symmetry

/-! ## Naturality of the joint-`N` symmetry operators across strata

These are the three cruxes the two statements above need.  All rest on the binary split
`Quantum.TensorProducts.tensorFamily_append` of the flat `N`-site tensor product across
`N = a + b`.

**Block-order reversal (load-bearing).**  `tensorFamily`/`finFunctionFinEquiv` place site `0`
on the *low* mixed-radix digit (the Kronecker *remainder* side), whereas `Op.tensorProdFin`
places block `0` on the *quotient* side.  Hence the flat append factorizes with the two halves
**swapped**: the high-position half lands on the quotient and the low-position half on the
remainder. At `n = ![2,1]`, `d = 2`: the support permutation of
`permutationRepresentation 2 3 (youngPermHom ![2,1] ![swap 0 1, 1])` is `[0,2,1,3,4,6,5,7]`,
which equals `id_{2} ⊗ perm(swap 0 1)_{2²}` (block 1 on the quotient), NOT
`perm(swap 0 1)_{2²} ⊗ id_{2} = [0,1,4,5,2,3,6,7]` that a non-reversed `Op.tensorProdFin`
would produce. -/

/-- The dimension identity `d ^ b * d ^ a = d ^ (a + b)` underlying the append reversal. -/
private lemma pow_mul_pow_add_comm (d a b : ℕ) : d ^ b * d ^ a = d ^ (a + b) := by
  rw [← pow_add, Nat.add_comm]

/-- Low-digit split: the `Fin.castAdd` (position `< a`) digit of `i : Fin (d ^ (a+b))` is the
`modNat` (remainder) digit under `Fin (d ^ (a+b)) ≃ Fin (d ^ b * d ^ a)`. -/
private lemma digit_castAdd {d a b : ℕ} (i : Fin (d ^ (a + b))) (c : Fin a) :
    finFunctionFinEquiv.symm i (Fin.castAdd b c) =
      finFunctionFinEquiv.symm
        (Fin.cast (pow_mul_pow_add_comm d a b).symm i : Fin (d ^ b * d ^ a)).modNat c := by
  obtain ⟨f, rfl⟩ := finFunctionFinEquiv.surjective i
  have h := congrArg Prod.snd
    (finProdFinEquiv_symm_cast_finFunctionFinEquiv_add f (pow_mul_pow_add_comm d a b).symm)
  simp only [finProdFinEquiv_symm_apply] at h
  rw [h]
  simp

/-- High-digit split: the `Fin.natAdd` (position `≥ a`) digit of `i : Fin (d ^ (a+b))` is the
`divNat` (quotient) digit under `Fin (d ^ (a+b)) ≃ Fin (d ^ b * d ^ a)`. -/
private lemma digit_natAdd {d a b : ℕ} (i : Fin (d ^ (a + b))) (c : Fin b) :
    finFunctionFinEquiv.symm i (Fin.natAdd a c) =
      finFunctionFinEquiv.symm
        (Fin.cast (pow_mul_pow_add_comm d a b).symm i : Fin (d ^ b * d ^ a)).divNat c := by
  obtain ⟨f, rfl⟩ := finFunctionFinEquiv.surjective i
  have h := congrArg Prod.fst
    (finProdFinEquiv_symm_cast_finFunctionFinEquiv_add f (pow_mul_pow_add_comm d a b).symm)
  simp only [finProdFinEquiv_symm_apply] at h
  rw [h]
  simp

/-- Reindexing helper: `∏ⱼ d ^ n(rev j) = d ^ (∑ⱼ n j)` (the block product commutes). -/
private lemma prodPow_rev (d : ℕ) {k : ℕ} (n : Fin k → ℕ) :
    (∏ j, d ^ n (Fin.rev j)) = d ^ (∑ j, n j) := by
  rw [show (∏ j, d ^ n (Fin.rev j)) = ∏ j, d ^ n j from
      Fintype.prod_equiv Fin.revPerm _ _ (fun j => by rw [Fin.revPerm_apply])]
  exact Finset.prod_pow_eq_pow_sum Finset.univ n d

/-! The dimension-cast transport used below — composition, finite sums and the two tensor
factors — is the shared family in `CastDim.lean`: `Op.castDim_trans`,
`Op.castDim_sum` and `Op.tensor_castDim_left`/`_right`. -/

/-! ### Append-form factorization of the site-wise twirl / rotation unitaries -/

/-- The per-string twirl unitary of a concatenated string factorizes (reversed) as the tensor
of the per-half twirl unitaries. -/
private lemma bellTwirlUnitary_append {a b : ℕ} (p : Fin a → Fin 4) (q : Fin b → Fin 4) :
    bellTwirlUnitary (a + b) (Fin.append p q) =
      Op.castDim (pow_mul_pow_add_comm 4 a b)
        (Op.tensor (bellTwirlUnitary b q) (bellTwirlUnitary a p)) := by
  have happ : (fun s => bb84BellSinglePairTwirlGroup ((Fin.append p q) s)) =
      Fin.append (fun i => bb84BellSinglePairTwirlGroup (p i))
        (fun i => bb84BellSinglePairTwirlGroup (q i)) := by
    funext s
    refine Fin.addCases ?_ ?_ s
    · intro i; rw [Fin.append_left, Fin.append_left]
    · intro i; rw [Fin.append_right, Fin.append_right]
  simp only [bellTwirlUnitary]
  rw [happ, tensorFamily_append_castDim]

/-- **Reversed twirl-factorization for a binary split.**  The IID Bell twirl of a tensor
product factorizes into the per-half twirls (with the halves swapped, matching the
`tensorFamily`/`Op.tensor` convention).  Proved by reindexing the `∑_{g}` twirl average as
`∑_{p} ∑_{q}` over the two halves, using `bellTwirlUnitary_append`. -/
private theorem bb84BellTwirl_tensor_append {a b : ℕ} (C : Op (4 ^ b)) (D : Op (4 ^ a)) :
    bb84BellTwirl (a + b) (Op.castDim (pow_mul_pow_add_comm 4 a b) (Op.tensor C D)) =
      Op.castDim (pow_mul_pow_add_comm 4 a b)
        (Op.tensor (bb84BellTwirl b C) (bb84BellTwirl a D)) := by
  set hc := pow_mul_pow_add_comm 4 a b with hc_def
  -- reindex the twirl average over the two halves
  have hreindex : ∀ F : (Fin (a + b) → Fin 4) → Op (4 ^ (a + b)),
      ∑ g : Fin (a + b) → Fin 4, F g =
        ∑ p : Fin a → Fin 4, ∑ q : Fin b → Fin 4, F (Fin.append p q) := by
    intro F
    rw [← Equiv.sum_comp (Fin.appendEquiv a b) F, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    congr 1
  -- expand each summand
  have hsummand : ∀ (p : Fin a → Fin 4) (q : Fin b → Fin 4),
      bellTwirlUnitary (a + b) (Fin.append p q) *
          Op.castDim hc (Op.tensor C D) *
          (bellTwirlUnitary (a + b) (Fin.append p q))ᴴ =
        Op.castDim hc
          (Op.tensor (bellTwirlUnitary b q * C * (bellTwirlUnitary b q)ᴴ)
            (bellTwirlUnitary a p * D * (bellTwirlUnitary a p)ᴴ)) := by
    intro p q
    rw [bellTwirlUnitary_append, Op.castDim_conjTranspose, Op.tensor_conjTranspose,
      Op.castDim_mul, Op.castDim_mul, Op.tensor_mul, Op.tensor_mul]
  unfold bb84BellTwirl
  rw [hreindex]
  simp_rw [hsummand, ← Op.castDim_sum]
  rw [← Op.castDim_smul]
  congr 1
  -- reduce to the untwisted scalar/bilinearity identity inside the cast
  rw [Op.tensor_smul_left, Op.tensor_smul_right, smul_smul, Op.tensor_finsetSum_left]
  simp_rw [Op.tensor_finsetSum_right]
  rw [Finset.sum_comm]
  congr 1
  rw [pow_add, mul_inv, mul_comm]

/-- The empty-string twirl unitary is the identity. -/
private lemma bellTwirlUnitary_zero (g : Fin 0 → Fin 4) : bellTwirlUnitary 0 g = 1 :=
  tensorFamily_zero _

/-- The Bell twirl on `0` pairs is the identity map. -/
private lemma bb84BellTwirl_zero (x : Op (4 ^ 0)) : bb84BellTwirl 0 x = x := by
  unfold bb84BellTwirl
  rw [Fintype.sum_unique]
  simp [bellTwirlUnitary_zero]

/-- The empty-string Bell rotation is the identity. -/
private lemma bellRotation_zero : bellRotation 0 = 1 :=
  tensorFamily_zero _

/-- The `(a+b)`-fold Bell rotation factorizes (reversed) as the tensor of the per-half
rotations. -/
private lemma bellRotation_append (a b : ℕ) :
    bellRotation (a + b) =
      Op.castDim (pow_mul_pow_add_comm 4 a b)
        (Op.tensor (bellRotation b) (bellRotation a)) := by
  have happ : (fun _ : Fin (a + b) => bellSinglePairRotation) =
      Fin.append (fun _ : Fin a => bellSinglePairRotation)
        (fun _ : Fin b => bellSinglePairRotation) := by
    funext s
    refine Fin.addCases ?_ ?_ s
    · intro i; rw [Fin.append_left]
    · intro i; rw [Fin.append_right]
  simp only [bellRotation]
  rw [happ, tensorFamily_append_castDim]

/-- Conjugation by the `N`-fold Bell rotation, as a map on `Op (4^N)`. -/
private def bellRotationConj (N : ℕ) (A : Op (4 ^ N)) : Op (4 ^ N) :=
  bellRotation N * A * (bellRotation N)ᴴ

/-- **Reversed rotation-conjugation factorization for a binary split.** -/
private theorem bellRotation_tensor_append {a b : ℕ} (C : Op (4 ^ b)) (D : Op (4 ^ a)) :
    bellRotation (a + b) * Op.castDim (pow_mul_pow_add_comm 4 a b) (Op.tensor C D) *
        (bellRotation (a + b))ᴴ =
      Op.castDim (pow_mul_pow_add_comm 4 a b)
        (Op.tensor (bellRotation b * C * (bellRotation b)ᴴ)
          (bellRotation a * D * (bellRotation a)ᴴ)) := by
  rw [bellRotation_append, Op.castDim_conjTranspose, Op.tensor_conjTranspose,
    Op.castDim_mul, Op.castDim_mul, Op.tensor_mul, Op.tensor_mul]

/-- **Site-wise factorization engine.**  Any family of maps `Φ N : Op (4^N) → Op (4^N)` that
(i) fixes the trivial `N = 0` operator and (ii) factorizes across a binary `Op.tensor` split
(reversed, matching `tensorFamily_append`) automatically factorizes across the `k`-fold
`Op.tensorProdFin` block grouping.  Both crux (b) (Bell-rotation conjugation) and crux (c)
(the Bell twirl) are instances. -/
private theorem opTensorProdFin_siteWise
    (Φ : (N : ℕ) → Op (4 ^ N) → Op (4 ^ N))
    (hΦ0 : ∀ x : Op (4 ^ 0), Φ 0 x = x)
    (hfact : ∀ (a b : ℕ) (C : Op (4 ^ b)) (D : Op (4 ^ a)),
      Φ (a + b) (Op.castDim (pow_mul_pow_add_comm 4 a b) (Op.tensor C D)) =
        Op.castDim (pow_mul_pow_add_comm 4 a b) (Op.tensor (Φ b C) (Φ a D)))
    {k : ℕ} (n : Fin k → ℕ) (M : ∀ j, Op (4 ^ n j)) :
    Φ (∑ j, n j)
        (Op.castDim (Finset.prod_pow_eq_pow_sum Finset.univ n 4)
          (Op.tensorProdFin k (fun j => 4 ^ n j) M)) =
      Op.castDim (Finset.prod_pow_eq_pow_sum Finset.univ n 4)
        (Op.tensorProdFin k (fun j => 4 ^ n j) (fun j => Φ (n j) (M j))) := by
  -- generalized-total version of `hfact`
  have hfact' : ∀ (a b N : ℕ) (hN : N = a + b) (C : Op (4 ^ b)) (D : Op (4 ^ a)),
      Φ N (Op.castDim (by rw [hN]; exact pow_mul_pow_add_comm 4 a b) (Op.tensor C D)) =
        Op.castDim (by rw [hN]; exact pow_mul_pow_add_comm 4 a b) (Op.tensor (Φ b C) (Φ a D)) := by
    intro a b N hN C D; subst hN; exact hfact a b C D
  induction k with
  | zero =>
    simp only [Op.tensorProdFin_zero, Fin.sum_univ_zero, hΦ0]
  | succ k ih =>
    set sk := ∑ j : Fin k, n (Fin.succ j) with hsk
    have hsum : (∑ j, n j) = sk + n 0 := by rw [Fin.sum_univ_succ n, Nat.add_comm]
    have hQ : (∏ j : Fin k, 4 ^ n (Fin.succ j)) = 4 ^ sk :=
      Finset.prod_pow_eq_pow_sum Finset.univ (fun j => n (Fin.succ j)) 4
    -- peel the first block on both sides
    rw [Op.tensorProdFin_succ, Op.tensorProdFin_succ,
      Op.castDim_trans, Op.castDim_trans]
    -- move the block-`k` product cast inside the tensor's right factor
    rw [show Op.tensor (M 0)
            (Op.tensorProdFin k (fun j => 4 ^ n (Fin.succ j)) (fun j => M (Fin.succ j)))
          = Op.castDim (by rw [hQ])
              (Op.tensor (M 0)
                (Op.castDim hQ
                  (Op.tensorProdFin k (fun j => 4 ^ n (Fin.succ j)) (fun j => M (Fin.succ j)))))
        from by rw [Op.tensor_castDim_right, Op.castDim_trans]; rfl,
      Op.castDim_trans]
    rw [show Op.tensor (Φ (n 0) (M 0))
            (Op.tensorProdFin k (fun j => 4 ^ n (Fin.succ j))
              (fun j => Φ (n (Fin.succ j)) (M (Fin.succ j))))
          = Op.castDim (by rw [hQ])
              (Op.tensor (Φ (n 0) (M 0))
                (Op.castDim hQ
                  (Op.tensorProdFin k (fun j => 4 ^ n (Fin.succ j))
                    (fun j => Φ (n (Fin.succ j)) (M (Fin.succ j))))))
        from by rw [Op.tensor_castDim_right, Op.castDim_trans]; rfl,
      Op.castDim_trans]
    -- apply the binary factorization and the induction hypothesis
    rw [hfact' sk (n 0) (∑ j, n j) hsum, ih (fun j => n (Fin.succ j)) (fun j => M (Fin.succ j))]

/-- **Crux (b): Bell-rotation conjugation factorizes across strata (clean, site-wise).**

Because `bellRotation N` is a *site-wise constant* tensor (`tensorFamily` of the single-pair
rotation), conjugation by it respects the block grouping of any `tensorProdFin`, without the
`tensorFamily_append` reversal (each site's rotation stays with that site's factor).  This
is the form consumer 2 (`stratified_domination_per_index`) uses to reduce the reference
diagonal to a product of per-stratum diagonals.

Reduces to `tensorFamily_append` (site-wise) plus `Op.tensor_mul`. -/
theorem bellRotation_tensorProdFin_conj {k : ℕ} (n : Fin k → ℕ)
    (M : ∀ j, Op (4 ^ n j)) :
    bellRotation (∑ j, n j) *
        Op.castDim (Finset.prod_pow_eq_pow_sum Finset.univ n 4)
          (Op.tensorProdFin k (fun j => 4 ^ n j) M) *
        (bellRotation (∑ j, n j))ᴴ =
      Op.castDim (Finset.prod_pow_eq_pow_sum Finset.univ n 4)
        (Op.tensorProdFin k (fun j => 4 ^ n j)
          (fun j => bellRotation (n j) * M j * (bellRotation (n j))ᴴ)) := by
  refine opTensorProdFin_siteWise bellRotationConj ?_ ?_ n M
  · intro x
    simp only [bellRotationConj]
    rw [bellRotation_zero, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · intro a b C D
    simp only [bellRotationConj]
    exact bellRotation_tensor_append C D

/-- **Crux (c): the joint `N`-pair Bell twirl factorizes across strata (clean, site-wise).**

`bb84BellTwirl N` is the IID (site-wise) Bell-dephasing channel; being a product of per-site
channels it factorizes over the block grouping of any `tensorProdFin` into the per-stratum
twirls `bb84BellTwirl (n j)`, without the `tensorFamily_append` reversal.  Consumer 1
(`stratifiedBellDeFinettiDensity_isIIDBellDiagonal`) instantiates this crux at `n ∘ Fin.rev`
to match the realigned reference, reconciling `∑ (n ∘ Fin.rev) = ∑ n` (routine glue); each
factor `bb84BellDeFinettiDensity (n j)` is a `bb84BellTwirl (n j)` fixed point, so the product
is a joint fixed point.

Reduces to `tensorFamily_append` (for the per-string twirl unitaries) plus the
`finSigmaFinEquiv`-reindexing of the `∑_{g : Fin N → Fin 4}` twirl average into
`∏_j ∑_{g_j : Fin (n j) → Fin 4}`. -/
theorem bb84BellTwirl_tensorProdFin {k : ℕ} (n : Fin k → ℕ)
    (M : ∀ j, Op (4 ^ n j)) :
    bb84BellTwirl (∑ j, n j)
        (Op.castDim (Finset.prod_pow_eq_pow_sum Finset.univ n 4)
          (Op.tensorProdFin k (fun j => 4 ^ n j) M)) =
      Op.castDim (Finset.prod_pow_eq_pow_sum Finset.univ n 4)
        (Op.tensorProdFin k (fun j => 4 ^ n j) (fun j => bb84BellTwirl (n j) (M j))) := by
  exact opTensorProdFin_siteWise bb84BellTwirl bb84BellTwirl_zero
    (fun a b C D => bb84BellTwirl_tensor_append C D) n M

/-- **Binary append factorization for the permutation representation (block-diagonal case).**

If `τ : Perm (Fin (a+b))` is the block-diagonal permutation acting as `π` on the low positions
`[0, a)` and as `σ` on the high positions `[a, a+b)` (i.e. `τ = finSumFinEquiv.permCongr
(π.sumCongr σ)`), then its permutation-matrix representation factorizes as the Kronecker product
with the two halves **swapped** (high block `σ` on the quotient, low block `π` on the remainder),
exactly matching the `tensorFamily_append` convention.

Proved pointwise from the digit-split lemmas `digit_castAdd`/`digit_natAdd`: the block-diagonal
`τ.symm` sends low positions to low positions (via `π.symm`) and high to high (via `σ.symm`), so
the 0/1 index bi-implication `e.symm i = e.symm j ∘ τ.symm` factors as the conjunction of the two
per-block bi-implications. -/
private lemma permutationRepresentation_sumCongr_append {d a b : ℕ} [NeZero d]
    (π : Equiv.Perm (Fin a)) (σ : Equiv.Perm (Fin b)) :
    permutationRepresentation d (a + b)
        (finSumFinEquiv.permCongr (Equiv.sumCongr π σ)) =
      Op.castDim (pow_mul_pow_add_comm d a b)
        (Op.tensor (permutationRepresentation d b σ) (permutationRepresentation d a π)) := by
  have hτl : ∀ c : Fin a,
      (finSumFinEquiv.permCongr (Equiv.sumCongr π σ)).symm (Fin.castAdd b c)
        = Fin.castAdd b (π.symm c) := by
    intro c
    rw [Equiv.symm_apply_eq, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.apply_symm_apply, finSumFinEquiv_apply_left]
  have hτr : ∀ c : Fin b,
      (finSumFinEquiv.permCongr (Equiv.sumCongr π σ)).symm (Fin.natAdd a c)
        = Fin.natAdd a (σ.symm c) := by
    intro c
    rw [Equiv.symm_apply_eq, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.apply_symm_apply, finSumFinEquiv_apply_right]
  ext i j
  rw [Op.castDim_apply]
  simp only [permutationRepresentation, Op.tensor, Matrix.of_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    finProdFinEquiv_symm_apply]
  set τ := finSumFinEquiv.permCongr (Equiv.sumCongr π σ) with hτ
  -- The two per-block conditions
  set condB : Prop := finFunctionFinEquiv.symm (Fin.cast (pow_mul_pow_add_comm d a b).symm i).divNat
      = finFunctionFinEquiv.symm (Fin.cast (pow_mul_pow_add_comm d a b).symm j).divNat ∘ σ.symm
    with hcondB
  set condA : Prop := finFunctionFinEquiv.symm (Fin.cast (pow_mul_pow_add_comm d a b).symm i).modNat
      = finFunctionFinEquiv.symm (Fin.cast (pow_mul_pow_add_comm d a b).symm j).modNat ∘ π.symm
    with hcondA
  have hiff : (finFunctionFinEquiv.symm i = finFunctionFinEquiv.symm j ∘ ⇑τ.symm)
      ↔ (condB ∧ condA) := by
    constructor
    · intro hh
      refine ⟨?_, ?_⟩
      · funext c
        have hh2 := congrFun hh (Fin.natAdd a c)
        simp only [Function.comp_apply] at hh2 ⊢
        rw [hτr] at hh2
        rw [digit_natAdd i c, digit_natAdd j (σ.symm c)] at hh2
        exact hh2
      · funext c
        have hh2 := congrFun hh (Fin.castAdd b c)
        simp only [Function.comp_apply] at hh2 ⊢
        rw [hτl] at hh2
        rw [digit_castAdd i c, digit_castAdd j (π.symm c)] at hh2
        exact hh2
    · rintro ⟨hB, hA⟩
      funext p
      refine Fin.addCases ?_ ?_ p
      · intro c
        simp only [Function.comp_apply]
        rw [hτl, digit_castAdd i c, digit_castAdd j (π.symm c)]
        exact congrFun hA c
      · intro c
        simp only [Function.comp_apply]
        rw [hτr, digit_natAdd i c, digit_natAdd j (σ.symm c)]
        exact congrFun hB c
  by_cases hcond : finFunctionFinEquiv.symm i = finFunctionFinEquiv.symm j ∘ ⇑τ.symm
  · rw [if_pos hcond]
    obtain ⟨hB, hA⟩ := hiff.mp hcond
    rw [hcondB] at hB
    rw [hcondA] at hA
    rw [if_pos hB, if_pos hA, mul_one]
  · rw [if_neg hcond, eq_comm]
    by_cases hB : condB
    · by_cases hA : condA
      · exact absurd (hiff.mpr ⟨hB, hA⟩) hcond
      · rw [hcondA] at hA
        rw [if_neg hA, mul_zero]
    · rw [hcondB] at hB
      rw [if_neg hB, zero_mul]

/-- The Young embedding acts fibre-wise: on the flat index `finSigmaFinEquiv ⟨j, r⟩` it applies
`h j` to the offset `r`, keeping the stratum `j` fixed. -/
private lemma youngPermHom_apply_finSigmaFinEquiv {k : ℕ} (n : Fin k → ℕ)
    (h : ∀ j, Equiv.Perm (Fin (n j))) (s : (j : Fin k) × Fin (n j)) :
    youngPermHom n h (finSigmaFinEquiv s) = finSigmaFinEquiv ⟨s.1, h s.1 s.2⟩ := by
  rw [youngPermHom]
  simp only [MonoidHom.comp_apply, permCongrHom_apply, Equiv.Perm.sigmaCongrRightHom_apply,
    Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.sigmaCongrRight_apply]

/-- **Last-stratum glue.**  Conjugating `youngPermHom n h` by the dimension identity
`∑ n = (∑_{j<k} n(castSucc j)) + n(last)` turns it into the block-diagonal `sumCongr` of the
Young embedding of the first `k` strata (low block) and the last stratum's permutation `h last`
(high block).  This is the honest content that lets the append lemma
`permutationRepresentation_sumCongr_append` peel the last stratum in the descent.

Proved by `Equiv.ext`, splitting `Fin (a+b)` via `finSumFinEquiv` and using the flat-placement
identities: `finSigmaFinEquiv ⟨castSucc j₀, r⟩` lands on the low block (value unchanged, i.e.
`castAdd`), and `finSigmaFinEquiv ⟨last, r⟩` lands on the high block at offset `r` (i.e. `natAdd`),
both by `finSigmaFinEquiv_apply` value bookkeeping. -/
private lemma youngPermHom_castSucc_last {k : ℕ} (n : Fin (k + 1) → ℕ)
    (h : ∀ j, Equiv.Perm (Fin (n j)))
    (hN : (∑ j, n j) = (∑ j : Fin k, n j.castSucc) + n (Fin.last k)) :
    (finCongr hN).permCongr (youngPermHom n h) =
      finSumFinEquiv.permCongr
        (Equiv.sumCongr (youngPermHom (fun j => n j.castSucc) (fun j => h j.castSucc))
          (h (Fin.last k))) := by
  -- flat placement of the first-`k` strata (low block)
  have hplaceA : ∀ (j₀ : Fin k) (r : Fin (n (Fin.castSucc j₀))),
      (finCongr hN) (finSigmaFinEquiv (⟨Fin.castSucc j₀, r⟩ : (j : Fin (k + 1)) × Fin (n j)))
        = Fin.castAdd (n (Fin.last k))
            (finSigmaFinEquiv (⟨j₀, r⟩ : (j : Fin k) × Fin (n j.castSucc))) := by
    intro j₀ r
    apply Fin.ext
    simp only [finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply, Fin.val_castAdd,
      Fin.val_castSucc]
    congr 1
  -- flat placement of the last stratum (high block)
  have hplaceB : ∀ (r : Fin (n (Fin.last k))),
      (finCongr hN) (finSigmaFinEquiv (⟨Fin.last k, r⟩ : (j : Fin (k + 1)) × Fin (n j)))
        = Fin.natAdd (∑ j : Fin k, n j.castSucc) r := by
    intro r
    apply Fin.ext
    simp only [finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply, Fin.val_natAdd, Fin.val_last]
    congr 1
  refine Equiv.ext fun x => ?_
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective x
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rcases s with c | c
  · -- low block: `c : Fin (∑_{j<k} n(castSucc j))`
    obtain ⟨⟨j₀, r⟩, rfl⟩ := finSigmaFinEquiv.surjective c
    rw [finSumFinEquiv_apply_left, ← hplaceA j₀ r, Equiv.symm_apply_apply,
      youngPermHom_apply_finSigmaFinEquiv, hplaceA,
      Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left,
      youngPermHom_apply_finSigmaFinEquiv]
  · -- high block: `c : Fin (n (last k))`
    rw [finSumFinEquiv_apply_right, ← hplaceB c, Equiv.symm_apply_apply,
      youngPermHom_apply_finSigmaFinEquiv, hplaceB,
      Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

/-- A `tensor`-of-`tensorProdFin` block is heterogeneously unchanged when the block-index
reindexing function is replaced by a pointwise-equal one (used to bridge `Fin.rev_succ`:
`j.succ.rev = j.rev.castSucc`). -/
private lemma tensor_tensorProdFin_reindex_heq {k K m : ℕ} (A : Op m) {N : Fin K → ℕ}
    (Hp : ∀ j, Equiv.Perm (Fin (N j))) (d : ℕ) [NeZero d] {g₁ g₂ : Fin k → Fin K}
    (hg : g₁ = g₂) :
    HEq
      (Op.tensor A (Op.tensorProdFin k (fun j => d ^ N (g₁ j))
        (fun j => permutationRepresentation d (N (g₁ j)) (Hp (g₁ j)))))
      (Op.tensor A (Op.tensorProdFin k (fun j => d ^ N (g₂ j))
        (fun j => permutationRepresentation d (N (g₂ j)) (Hp (g₂ j))))) := by
  subst hg; rfl

/-- Transporting the permutation representation along a dimension identity `M = N` conjugates the
permutation by `finCongr` and casts the matrix. -/
private lemma permutationRepresentation_finCongr {d M N : ℕ} [NeZero d] (hM : M = N)
    (τ : Equiv.Perm (Fin M)) :
    permutationRepresentation d N ((finCongr hM).permCongr τ) =
      Op.castDim (by rw [hM]) (permutationRepresentation d M τ) := by
  subst hM
  simp only [finCongr_refl]
  rfl

/-- **Crux (a): the Young permutation representation factorizes across strata (REVERSED).**

Because `youngPermHom` permutes sites *within* the `finSigmaFinEquiv` blocks (block `j` on the
low positions `[∑_{i<j} n i, ∑_{i≤j} n i)`) while `Op.tensorProdFin` places block `j` on the
quotient (high digits), the flat permutation representation factorizes as a `tensorProdFin`
over the **reversed** block index `Fin.rev`.  For example, at
`n = ![2,1]` (see the module docstring), a *non-reversed* factorization is false for
non-constant compositions.

Reduces, by induction over the strata, to the binary block-diagonal split
`permutationRepresentation_sumCongr_append` plus `finSigmaFinEquiv`/`Fin.rev` bookkeeping.

**Downstream note.**  The reference `stratifiedBellDeFinettiDensity n` feeds its blocks to
`tensorProdFin` in the *same* `Fin.rev` order as this lemma (same `prodPow_rev`-style cast), so
stratum `j` lands on Young block `j` for both.  Consumer 2 (`stratified_domination_per_index`)
therefore composes this factorization with the reference block-wise via `Op.tensorProdFin_mul`,
without a second flip. -/
theorem permutationRepresentation_youngPermHom_tensorProdFin {k : ℕ} (n : Fin k → ℕ)
    (d : ℕ) [NeZero d] (h : ∀ j, Equiv.Perm (Fin (n j))) :
    permutationRepresentation d (∑ j, n j) (youngPermHom n h) =
      Op.castDim (prodPow_rev d n)
        (Op.tensorProdFin k (fun j => d ^ n (Fin.rev j))
          (fun j => permutationRepresentation d (n (Fin.rev j)) (h (Fin.rev j)))) := by
  revert n h
  induction k with
  | zero =>
    intro n h
    have h0 : (∑ j : Fin 0, n j) = 0 := by simp
    haveI : Subsingleton (Equiv.Perm (Fin (∑ j : Fin 0, n j))) := by
      rw [h0]; infer_instance
    rw [Op.tensorProdFin_zero, Op.castDim_trans, Op.castDim_one,
      show youngPermHom n h = 1 from Subsingleton.elim _ _, permutationRepresentation_one]
  | succ k ih =>
    intro n h
    have hN : (∑ j, n j) = (∑ j : Fin k, n j.castSucc) + n (Fin.last k) :=
      Fin.sum_univ_castSucc n
    have hyoung : (finCongr hN.symm).permCongr
          (finSumFinEquiv.permCongr (Equiv.sumCongr
            (youngPermHom (fun j => n j.castSucc) (fun j => h j.castSucc)) (h (Fin.last k))))
        = youngPermHom n h := by
      rw [← finCongr_symm, ← Equiv.permCongr_symm, Equiv.symm_apply_eq]
      exact (youngPermHom_castSucc_last n h hN).symm
    rw [← hyoung, permutationRepresentation_finCongr hN.symm,
      permutationRepresentation_sumCongr_append, Op.castDim_trans, Op.tensorProdFin_succ]
    rw [ih (fun j => n j.castSucc) (fun j => h j.castSucc)]
    simp only [Op.tensor_castDim_right, Op.castDim_trans]
    congr 1
    · rw [Fin.rev_zero]
      simp only [Fin.rev_succ]
    · exact proof_irrel_heq _ _
    · rw [Fin.rev_zero]
      exact tensor_tensorProdFin_reindex_heq
        (permutationRepresentation d (n (Fin.last k)) (h (Fin.last k))) h d
        (funext fun j => (Fin.rev_succ j).symm)

end Quantum.Symmetry

end -- noncomputable section
