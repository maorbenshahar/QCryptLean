import QCryptLean.InfoTheory.Postselection.SchurWeylFlatten
import QCryptLean.Math.Combinatorics.RoundRegrouping
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.Matrix.Reindex

/-!
# QKD postselection — the paired ↔ blocked register equivalence

Infrastructure isolating the register-regrouping (Nahar, Tupkary, Zhao, Lütkenhaus, Tan
Theorem 1 transport) on the **blocked** register `Aⁿ ⊗ Rⁿ`
(`dR = dA·dB²`), starting from hypotheses stated on the **paired** register
`(dA·dB)ⁿ ⊗ (dA·dB)ⁿ` (`deFinetti_fixedMarginal_purified_op_le`,
`FixedMarginalDeFinetti.lean`).

Both registers are regroupings of the same per-round dimension `dA²dB² = (dA·dB)·(dA·dB) =
dA·(dA·dB²)`, reachable from the flat interleaved register `symmetricProjector (dA²dB²) n`
via `InfoTheory.Postselection.interleavingEquivGen` (`SchurWeylTwirl.lean`).

## Main definitions
- `InfoTheory.Postselection.pairedToBlockedEquiv dA dB n` : the composed index equivalence
  `Fin ((dA·dB)ⁿ · (dA·dB)ⁿ) ≃ Fin (dAⁿ · (dA·dB²)ⁿ)`.

## Main statements
- `InfoTheory.Postselection.pairedToBlockedEquiv_conjugates_projector` : the composed
  equivalence conjugates the paired symmetric projector to the blocked one.
-/

open Equiv

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory
open Quantum.Symmetry InfoTheory.DeFinetti Quantum.Channels MeasureTheory Math.HaarMeasure
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-! ## The per-round dimension identity -/

/-- The per-round dimension identity bridging the paired and blocked registers:
    `(dA·dB)·(dA·dB) = dA·(dA·dB²)` (both `= dA²dB²`). -/
private lemma pairedBlocked_dim_eq (dA dB : ℕ) :
    (dA * dB) * (dA * dB) = dA * (dA * dB ^ 2) := by ring

/-! ## The composed register equivalence -/

/-- **Paired → blocked register equivalence.**

    Composes the already-proven `interleavingEquivGen (dA·dB) (dA·dB) n` (paired register
    `(dA·dB)ⁿ⊗(dA·dB)ⁿ` → flat `((dA·dB)·(dA·dB))ⁿ`) with the `Nat`-equality bridge
    `(dA·dB)·(dA·dB) = dA·(dA·dB²)` and the inverse of `interleavingEquivGen dA (dA·dB²) n`
    (flat `(dA·(dA·dB²))ⁿ` → blocked register `Aⁿ⊗Rⁿ`, `dR = dA·dB²`). -/
def pairedToBlockedEquiv (dA dB n : ℕ) :
    Fin ((dA * dB) ^ n * (dA * dB) ^ n) ≃ Fin (dA ^ n * (dA * dB ^ 2) ^ n) :=
  (interleavingEquivGen (dA * dB) (dA * dB) n).trans <|
    (finCongr (congrArg (· ^ n) (pairedBlocked_dim_eq dA dB))).trans <|
      (interleavingEquivGen dA (dA * dB ^ 2) n).symm

/-! The relabelling composition and round-trip laws used below are `Matrix.reindex_trans_apply`
and `Matrix.reindex_symm_reindex` in the Quantum.Matrix.Reindex module. -/

/-- The `Nat`-equality cast bridges `symmetricProjector` across the per-round dimension
    identity: reindexing along `finCongr` (induced by `X = Y`) sends `symmetricProjector X n`
    to `symmetricProjector Y n`. -/
private lemma reindex_finCongr_symmetricProjector {X Y n : ℕ} [NeZero n] [NeZero X] [NeZero Y]
    (h : X = Y) :
    Matrix.reindex (finCongr (congrArg (· ^ n) h)) (finCongr (congrArg (· ^ n) h))
      (symmetricProjector X n) = symmetricProjector Y n := by
  subst h
  simp

/-- **The composed equivalence conjugates the paired symmetric projector to the blocked
    one.** -/
theorem pairedToBlockedEquiv_conjugates_projector (dA dB n : ℕ)
    [NeZero dA] [NeZero dB] [NeZero n] :
    let e := pairedToBlockedEquiv dA dB n
    Matrix.reindex e e (symmetricProjectorPaired (dA * dB) n) =
      symmetricProjectorPairedGen dA (dA * dB ^ 2) n := by
  intro e
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  haveI : NeZero ((dA * dB) * (dA * dB)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (dA * dB)) (NeZero.ne (dA * dB))⟩
  rw [symmetricProjectorPaired_eq_gen, show e = (interleavingEquivGen (dA * dB) (dA * dB) n).trans
    ((finCongr (congrArg (· ^ n) (pairedBlocked_dim_eq dA dB))).trans
      (interleavingEquivGen dA (dA * dB ^ 2) n).symm) from rfl,
    Matrix.reindex_trans_apply, Matrix.reindex_trans_apply,
    interleavingEquivGen_conjugates_projector,
    reindex_finCongr_symmetricProjector (pairedBlocked_dim_eq dA dB)]
  -- unwind the inverse equivalence: `reindex e'.symm e'.symm (symmetricProjector (dA*dR) n) =
  -- symmetricProjectorPairedGen dA dR n`, from `interleavingEquivGen_conjugates_projector`
  -- applied to `e' = interleavingEquivGen dA (dA*dB^2) n`.
  have hconj : Matrix.reindex (interleavingEquivGen dA (dA * dB ^ 2) n)
      (interleavingEquivGen dA (dA * dB ^ 2) n)
      (symmetricProjectorPairedGen dA (dA * dB ^ 2) n) =
      symmetricProjector (dA * (dA * dB ^ 2)) n := interleavingEquivGen_conjugates_projector
  rw [← hconj, Matrix.reindex_symm_reindex]

/-! ## Ψ-hypothesis transport across `pairedToBlockedEquiv` -/

/-- **Purity transports across `pairedToBlockedEquiv`.** Reindexing by an equivalence is
    conjugation by the associated permutation matrix, so it carries `Ψ.toOp * Ψ.toOp = Ψ.toOp`
    to the analogous equation on the reindexed operator. -/
theorem pairedToBlockedEquiv_transports_isPure (dA dB n : ℕ) [NeZero dA] [NeZero dB] [NeZero n]
    (Ψ : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n)) (hΨ_pure : Ψ.IsPure) :
    (densityOp_reindex (pairedToBlockedEquiv dA dB n) Ψ).IsPure := by
  set e := pairedToBlockedEquiv dA dB n
  unfold DensityOp.IsPure at hΨ_pure ⊢
  change Matrix.reindex e e Ψ.toOp * Matrix.reindex e e Ψ.toOp = Matrix.reindex e e Ψ.toOp
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) hΨ_pure
  simpa only [Matrix.coe_reindexAlgEquiv, map_mul] using h

/-- **The paired symmetric-projector support hypothesis transports (paired → blocked)
    across `pairedToBlockedEquiv`.** Conjugating `hΨ_supp` by the composed equivalence and
    using `pairedToBlockedEquiv_conjugates_projector` turns the paired-register support
    equation into the analogous equation for `symmetricProjectorPairedGen` on the blocked
    register. -/
theorem pairedToBlockedEquiv_transports_support (dA dB n : ℕ) [NeZero dA] [NeZero dB] [NeZero n]
    (Ψ : Op ((dA * dB) ^ n * (dA * dB) ^ n))
    (hΨ_supp : symmetricProjectorPaired (dA * dB) n * Ψ * symmetricProjectorPaired (dA * dB) n
      = Ψ) :
    let e := pairedToBlockedEquiv dA dB n
    symmetricProjectorPairedGen dA (dA * dB ^ 2) n * Matrix.reindex e e Ψ *
      symmetricProjectorPairedGen dA (dA * dB ^ 2) n = Matrix.reindex e e Ψ := by
  intro e
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) hΨ_supp
  simp only [Matrix.coe_reindexAlgEquiv, map_mul] at h
  rwa [pairedToBlockedEquiv_conjugates_projector] at h

/-- **The blocked-register `symmetricProjectorPairedGen`-support hypothesis transports
    back (blocked → paired) across `pairedToBlockedEquiv`.** The reverse direction of
    `pairedToBlockedEquiv_transports_support`, obtained by conjugating with `e.symm` and
    unwinding `pairedToBlockedEquiv_conjugates_projector` via `Matrix.reindex_symm_reindex`.
    Supplies the paired-register form of the support equation needed to restate a
    blocked-register PSD conclusion back on the paired register. -/
theorem pairedToBlockedEquiv_transports_support_symm (dA dB n : ℕ)
    [NeZero dA] [NeZero dB] [NeZero n]
    (X : Op (dA ^ n * (dA * dB ^ 2) ^ n))
    (hX_supp : symmetricProjectorPairedGen dA (dA * dB ^ 2) n * X *
      symmetricProjectorPairedGen dA (dA * dB ^ 2) n = X) :
    let e := pairedToBlockedEquiv dA dB n
    symmetricProjectorPaired (dA * dB) n * Matrix.reindex e.symm e.symm X *
      symmetricProjectorPaired (dA * dB) n = Matrix.reindex e.symm e.symm X := by
  intro e
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e.symm) hX_supp
  simp only [Matrix.coe_reindexAlgEquiv, map_mul] at h
  have hproj : Matrix.reindex e.symm e.symm (symmetricProjectorPairedGen dA (dA * dB ^ 2) n) =
      symmetricProjectorPaired (dA * dB) n := by
    have hc := pairedToBlockedEquiv_conjugates_projector dA dB n
    have hc' := congrArg (Matrix.reindex e.symm e.symm) hc
    rw [Matrix.reindex_symm_reindex] at hc'
    exact hc'.symm
  rwa [hproj] at h

/-! ## Invertible-conjugation preserves the PSD order (Nahar et al. Thm 1 proof, App. A, Step 1) -/

/-- Conjugation by an invertible operator preserves the Hermitian property. -/
private lemma isHermitian_conj_of_isHermitian {n : ℕ} {S A : Op n} (hA : A.IsHermitian) :
    (S * A * Sᴴ).IsHermitian := by
  change (S * A * Sᴴ)ᴴ = S * A * Sᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA,
    mul_assoc]

/-- **Conjugation by an invertible operator preserves the PSD order.** Thin wrapper
    around Mathlib's `Matrix.IsUnit.posSemidef_star_right_conjugate_iff`, restated with
    `Sᴴ` (this project's `conjTranspose` notation) in place of `star S`. -/
theorem sub_conj_psd_iff {n : ℕ} {S M : Op n} (hS : IsUnit S) :
    (S * M * Sᴴ).PosSemidef ↔ M.PosSemidef := by
  rw [show Sᴴ = star S from (Matrix.star_eq_conjTranspose S).symm]
  exact hS.posSemidef_star_right_conjugate_iff

/-- **`opLe`-phrased corollary of `sub_conj_psd_iff`.** Conjugation by an invertible
    operator preserves the operator-semidefinite order on Hermitian operators — the form
    Nahar et al. Thm 1 Part A Step 1 actually chains. -/
theorem opLe_conj_iff_of_isUnit {n : ℕ} {S A B : Op n} (hS : IsUnit S)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    opLe A B ↔ opLe (S * A * Sᴴ) (S * B * Sᴴ) := by
  have hSA : (S * A * Sᴴ).IsHermitian := isHermitian_conj_of_isHermitian hA
  have hSB : (S * B * Sᴴ).IsHermitian := isHermitian_conj_of_isHermitian hB
  have hdiff : S * B * Sᴴ - S * A * Sᴴ = S * (B - A) * Sᴴ := by
    simp [Matrix.mul_sub, Matrix.sub_mul]
  constructor
  · intro h
    apply opLe_of_posSemidef_sub
    rw [hdiff]
    exact (sub_conj_psd_iff (S := S) (M := B - A) hS).mpr (h.posSemidef_sub hA hB)
  · intro h
    apply opLe_of_posSemidef_sub
    have hsub := h.posSemidef_sub hSA hSB
    rw [hdiff] at hsub
    exact (sub_conj_psd_iff (S := S) (M := B - A) hS).mp hsub

/-! ## Tensor-power-of-a-commuting-operator preserves `symmetricProjectorPairedGen`-support
    (Nahar et al. Thm 1 proof, App. A, Step 1 and Step 2) -/

/-- **`M ⊗ id_R` commutes with `symmetricProjectorPairedGen`, provided `M` commutes with
    every `Sₙ`-permutation representation on the `A`-register.** Both sides expand
    `symmetricProjectorPairedGen` as `(1/n!) Σ_σ U_σ^A ⊗ U_σ^R`, distribute the tensor
    product through `Op.tensor_mul`, and use `hM` termwise. -/
theorem tensor_one_commute_symmetricProjectorPairedGen {dA dR n : ℕ}
    [NeZero dA] [NeZero dR] [NeZero n] (M : Op (dA ^ n))
    (hM : ∀ σ : Equiv.Perm (Fin n),
      permutationRepresentation dA n σ * M = M * permutationRepresentation dA n σ) :
    Op.tensor M (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n =
      symmetricProjectorPairedGen dA dR n * Op.tensor M (1 : Op (dR ^ n)) := by
  unfold symmetricProjectorPairedGen
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [Op.tensor_mul, Op.tensor_mul, one_mul, mul_one, hM σ]

/-- **`M ⊗ id_R` preserves `symmetricProjectorPairedGen`-support, provided `M` commutes
    with every `Sₙ`-permutation representation on the `A`-register.** Combines
    `tensor_one_commute_symmetricProjectorPairedGen` (to move `P_Sym` through the
    conjugating operator) with the support hypothesis `hX`. -/
theorem tensor_one_preserves_symmetricProjectorPairedGen_support {dA dR n : ℕ}
    [NeZero dA] [NeZero dR] [NeZero n] (M : Op (dA ^ n))
    (hM : ∀ σ : Equiv.Perm (Fin n),
      permutationRepresentation dA n σ * M = M * permutationRepresentation dA n σ)
    (X : Op (dA ^ n * dR ^ n))
    (hX : symmetricProjectorPairedGen dA dR n * X * symmetricProjectorPairedGen dA dR n = X) :
    symmetricProjectorPairedGen dA dR n *
      (Op.tensor M (1 : Op (dR ^ n)) * X * (Op.tensor M (1 : Op (dR ^ n)))ᴴ) *
      symmetricProjectorPairedGen dA dR n =
    Op.tensor M (1 : Op (dR ^ n)) * X * (Op.tensor M (1 : Op (dR ^ n)))ᴴ := by
  have hcomm := tensor_one_commute_symmetricProjectorPairedGen (dR := dR) M hM
  have hcommH : (Op.tensor M (1 : Op (dR ^ n)))ᴴ * symmetricProjectorPairedGen dA dR n =
      symmetricProjectorPairedGen dA dR n * (Op.tensor M (1 : Op (dR ^ n)))ᴴ := by
    have := congrArg Matrix.conjTranspose hcomm
    simpa [(symmetricProjectorPairedGen_is_projector dA dR n).2] using this.symm
  calc symmetricProjectorPairedGen dA dR n *
        (Op.tensor M (1 : Op (dR ^ n)) * X * (Op.tensor M (1 : Op (dR ^ n)))ᴴ) *
        symmetricProjectorPairedGen dA dR n
      = (symmetricProjectorPairedGen dA dR n * Op.tensor M (1 : Op (dR ^ n))) * X *
          ((Op.tensor M (1 : Op (dR ^ n)))ᴴ * symmetricProjectorPairedGen dA dR n) := by
        simp [mul_assoc]
    _ = (Op.tensor M (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n) * X *
          (symmetricProjectorPairedGen dA dR n * (Op.tensor M (1 : Op (dR ^ n)))ᴴ) := by
        rw [← hcomm, hcommH]
    _ = Op.tensor M (1 : Op (dR ^ n)) *
          (symmetricProjectorPairedGen dA dR n * X * symmetricProjectorPairedGen dA dR n) *
          (Op.tensor M (1 : Op (dR ^ n)))ᴴ := by
        simp [mul_assoc]
    _ = Op.tensor M (1 : Op (dR ^ n)) * X * (Op.tensor M (1 : Op (dR ^ n)))ᴴ := by rw [hX]

/-! ## The round-regrouping equivalence and the blocked-Alice-marginal bridge

`roundGroupEquiv` and the Ψ-generic **blocked-Alice-marginal bridge**
`pairedToBlockedEquiv_partialTraceB_eq_roundGroup`: tracing out the blocked reference
register `Rⁿ` (`dR = dA·dB²`) after regrouping by `pairedToBlockedEquiv` equals first
tracing out the second paired copy and then the round-wise `Bⁿ` block via
`roundGroupEquiv`. -/

/-- `dB·(dA·dB) = dA·dB²`: the per-round dimension identity splitting the blocked
    reference digit `Fin (dA·dB²)` as a round-wise `(B, second-paired-copy)` pair. -/
private lemma pairedBlocked_dimR_eq (dA dB : ℕ) : dB * (dA * dB) = dA * dB ^ 2 := by ring

/-- `roundGroupEquiv` is the inverse of the generalized interleaving equivalence: both
    are the digit-wise regrouping between the interleaved `(dA·dB)ⁿ` register and the
    blocked `dAⁿ ⊗ dBⁿ` register. -/
lemma roundGroupEquiv_eq_interleavingEquivGen_symm (dA dB n : ℕ) :
    roundGroupEquiv dA dB n = (interleavingEquivGen dA dB n).symm :=
  Equiv.ext fun _ => rfl

/-- `interleavingEquivGen` on a packed pair: the per-round digits pair up. -/
private lemma interleavingEquivGen_apply_finProd {dA dR n : ℕ}
    (a : Fin (dA ^ n)) (r : Fin (dR ^ n)) :
    interleavingEquivGen dA dR n (finProdFinEquiv (a, r))
      = finFunctionFinEquiv (fun t =>
          finProdFinEquiv (finFunctionFinEquiv.symm a t, finFunctionFinEquiv.symm r t)) := by
  simp only [interleavingEquivGen, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

/-- Digit extraction commutes with a `finCongr` base change, entrywise up to `Fin.cast`. -/
private lemma finFunctionFinEquiv_symm_finCongr {X Y : ℕ} (h : X = Y) {n : ℕ}
    (v : Fin (X ^ n)) (t : Fin n) :
    finFunctionFinEquiv.symm (finCongr (congrArg (· ^ n) h) v) t
      = Fin.cast h (finFunctionFinEquiv.symm v t) := by
  subst h; rfl

/-- Digit packing commutes with a `finCongr` base change. -/
private lemma finFunctionFinEquiv_cast_pack {X Y : ℕ} (h : X = Y) {n : ℕ}
    (f : Fin n → Fin X) :
    finFunctionFinEquiv (fun t => Fin.cast h (f t))
      = finCongr (congrArg (· ^ n) h) (finFunctionFinEquiv f) := by
  subst h; rfl

/-- The per-round digit split: regrouping `((a,x),m) ↦ (a,(x,m))` across the two
    per-round dimension casts (`finProdFinEquiv` associativity). -/
private lemma pairedBlocked_digit_split {dA dB : ℕ}
    (a : Fin dA) (x : Fin dB) (m : Fin (dA * dB)) :
    Fin.cast (pairedBlocked_dim_eq dA dB)
        (finProdFinEquiv (finProdFinEquiv (a, x), m))
      = finProdFinEquiv
          (a, Fin.cast (pairedBlocked_dimR_eq dA dB) (finProdFinEquiv (x, m))) := by
  apply Fin.ext
  simp only [Fin.val_cast, finProdFinEquiv_apply_val]
  ring

/-- **The paired↔blocked per-round index identity**: splitting the blocked reference
    index round-wise as a `(Bⁿ, second-paired-copy)` pair, `pairedToBlockedEquiv.symm`
    acts as `interleavingEquivGen dA dB n` (= `roundGroupEquiv.symm`) on the first paired
    copy and passes the second paired copy through. -/
private lemma pairedToBlockedEquiv_symm_finProd (dA dB n : ℕ)
    (i : Fin (dA ^ n)) (x : Fin (dB ^ n)) (m : Fin ((dA * dB) ^ n)) :
    (pairedToBlockedEquiv dA dB n).symm
        (finProdFinEquiv (i,
          finCongr (congrArg (· ^ n) (pairedBlocked_dimR_eq dA dB))
            (interleavingEquivGen dB (dA * dB) n (finProdFinEquiv (x, m)))))
      = finProdFinEquiv (interleavingEquivGen dA dB n (finProdFinEquiv (i, x)), m) := by
  rw [Equiv.symm_apply_eq]
  simp only [pairedToBlockedEquiv, Equiv.trans_apply]
  rw [Equiv.eq_symm_apply]
  simp only [interleavingEquivGen_apply_finProd, Equiv.symm_apply_apply,
    finFunctionFinEquiv_symm_finCongr (pairedBlocked_dimR_eq dA dB)]
  rw [← finFunctionFinEquiv_cast_pack (pairedBlocked_dim_eq dA dB)]
  exact congrArg finFunctionFinEquiv
    (funext fun t => (pairedBlocked_digit_split _ _ _).symm)

/-- **The blocked-Alice-marginal bridge (Ψ-generic).** Tracing out the blocked reference
    register `Rⁿ` (`dR = dA·dB²`) after regrouping by `pairedToBlockedEquiv` equals first
    tracing out the second paired copy and then the round-wise `Bⁿ` block via
    `roundGroupEquiv`.  No density/purity hypotheses: this is a pure index-reindexing
    identity, valid for every `M`. -/
theorem pairedToBlockedEquiv_partialTraceB_eq_roundGroup (dA dB n : ℕ)
    [NeZero dA] [NeZero dB] [NeZero n]
    (M : Op ((dA * dB) ^ n * (dA * dB) ^ n)) :
    partialTraceB
        (Matrix.reindex (pairedToBlockedEquiv dA dB n) (pairedToBlockedEquiv dA dB n) M)
      = partialTraceB
          (Matrix.reindex (roundGroupEquiv dA dB n) (roundGroupEquiv dA dB n)
            (partialTraceB M)) := by
  ext i j
  simp only [partialTraceB, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    roundGroupEquiv_eq_interleavingEquivGen_symm, Equiv.symm_symm]
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv
    ((finProdFinEquiv (m := dB ^ n) (n := (dA * dB) ^ n)).trans
      ((interleavingEquivGen dB (dA * dB) n).trans
        (finCongr (congrArg (· ^ n) (pairedBlocked_dimR_eq dA dB)))))
    _ _ fun p => ?_).symm
  simp only [Equiv.trans_apply]
  rw [pairedToBlockedEquiv_symm_finProd dA dB n i p.1 p.2,
    pairedToBlockedEquiv_symm_finProd dA dB n j p.1 p.2]

end InfoTheory.Postselection

end
