import QCryptLean.Quantum.Symmetry.BellPairedDeFinetti
import QCryptLean.InfoTheory.DeFinetti.Theorem.Interleaving

/-!
# Bell de Finetti — the `Wembed`/`f_Bell` W-conjugation Dicke core

Part of the Bell reference/floor construction (with `BellPairedDeFinetti.lean`,
`BellHaarIntegral.lean`).  Carries the Bell embedding `bellWembed`/`f_Bell`, the Bell-doubling
rectangular tensor-power machinery, and the W-conjugation Dicke resolution of the symmetric
projector (`bb84BellPairedDeFinettiState_eq_Wconj_symProj`).  Protocol-independent (no BB84 or
QKD-protocol object beyond the pure scalar dimension `bb84PolyDimTight`).

## The exported Bell-frame facts

`bellDeFinetti_bellRot_diag` (`R·τ_Bell·Rᴴ = diag(C(n+3,3)⁻¹⟨i|P_sym|i⟩)`),
`sqrtOp_bellDeFinetti_diag` (`√τ_Bell = Rᴴ·diag(√(C(n+3,3)⁻¹·mult_T⁻¹))·R`) and the two realness
facts `bellSinglePairRotation_star` / `bellRotation_star` are **public**: any readout of a reference
built from `bellPairedKraus = √τ_Bell · Q_T` needs the eigen*value* (not just block-diagonality)
and, because the vec-correspondence produces a transpose, the realness of `R`. -/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Engine

noncomputable section

namespace Quantum.Symmetry

/-! ## The Bell embedding `Wembed` and the Bell per-σ family `f_Bell`

`Wembed φ = W·φ·Wᴴ` is the Bell-doubling conjugation of a single-pair state; `f_Bell` is the CKR
per-σ family pre-composed with `Wembed`, so every CKR lemma quantifying over the source `ψ` re-keys
to the Bell family at `ψ := Wembed φ`. -/

/-- **The Bell-doubling state embedding** `Wembed φ = W·φ·Wᴴ` as a density operator on
`(ℂ⁴ ⊗ ℂ⁴)` (`4 · 4 = 16`).  PSD and trace `1` follow from the isometry
property `Wᴴ·W = 𝟙` (`bellDoublingIsometry_isometry`).  Explicit; no `Classical.choose`. -/
noncomputable def bellWembed (φ : DensityOp 4) : DensityOp (4 * 4) where
  toOp := bellDoublingIsometry * φ.toOp * (bellDoublingIsometry)ᴴ
  isHermitian :=
    ((posSemidefOp_implies_mathlib φ.toPosSemidefOp).mul_mul_conjTranspose_same
      bellDoublingIsometry).isHermitian
  pos_semidef := fun v =>
    posSemidef_re_quadraticForm_nonneg
      ((posSemidefOp_implies_mathlib φ.toPosSemidefOp).mul_mul_conjTranspose_same
        bellDoublingIsometry) v
  trace_one := by
    rw [Matrix.trace_mul_comm (bellDoublingIsometry * φ.toOp) (bellDoublingIsometry)ᴴ,
      ← Matrix.mul_assoc, bellDoublingIsometry_isometry, Matrix.one_mul]
    exact φ.trace_one

/-! ## The single-round Bell-diagonal state `σ_φ` and its tensor-power facts

`σ_φ = bb84BellTwirl 1 |φ⟩⟨φ|` (`= partialTraceB (W·φ·Wᴴ)` by `bellDoublingIsometry_partialTraceB`).
The L4 reference-change of the Bell floor needs `σ_φ^{⊗n}` to be PSD, trace-1,
permutation-invariant, and jointly Bell-diagonal so the domination
`bb84_bellSym_deFinetti_domination` applies. -/

/-! ## The W-conjugation Dicke core identity

The rectangular `n`-fold Kronecker power `W^{⊗n}` of the Bell-doubling isometry, the Dicke
resolution of the symmetric projector, and the core operator identity
`bb84BellPairedDeFinettiStateOp n = rdx(W^{⊗n}·(C(n+3,3)⁻¹•symProj 4 n)·(W^{⊗n})ᴴ)` that
discharges the joint Haar integral. -/

/-- **The rectangular `n`-fold Bell-doubling isometry** `W^{⊗n} = bellDoublingIsometry^{⊗n}`,
a `(16^n) × (4^n)` matrix: the tensor family of the constant `16 × 4` family `W`.  Explicit; no
`Classical.choose`. -/
noncomputable def bellDoublingIsometryPow (n : ℕ) : Matrix (Fin ((4 * 4) ^ n)) (Fin (4 ^ n)) ℂ :=
  tensorFamily fun _ : Fin n => bellDoublingIsometry

/-- **Tensor functoriality of the Bell embedding**:
`((bellWembed φ).tensorPowGen n).toOp = W^{⊗n}·(φ.tensorPowGen n).toOp·(W^{⊗n})ᴴ`. -/
theorem bellWembed_tensorPow_eq_Wconj {n : ℕ} [NeZero n] [NeZero (4 ^ n)] (φ : DensityOp 4) :
    ((bellWembed φ).tensorPowGen n).toOp =
      bellDoublingIsometryPow n * (φ.tensorPowGen n).toOp * (bellDoublingIsometryPow n)ᴴ := by
  rw [DensityOp.tensorPowGen_toOp_eq_tensorFamily, DensityOp.tensorPowGen_toOp_eq_tensorFamily,
    bellDoublingIsometryPow, conjTranspose_tensorFamily, tensorFamily_mul, tensorFamily_mul]
  rfl

/-- **The Bell type multiplicity** `mult_T = #{k : type(k) = T}` (the size of the type-orbit). -/
def bellTypeMult (n : ℕ) (T : Sym (Fin 4) n) : ℕ :=
  (Finset.univ.filter (fun k : Fin (4 ^ n) => bellTypeOfIndex n k = T)).card

/-- **The doubled Dicke vector** `|D_T⟩ = ∑_{k : type(k)=T} |β_k⟩ = (bellRotation n)ᴴ·𝟙[type=T]`. -/
noncomputable def bellDickeKet (n : ℕ) (T : Sym (Fin 4) n) : Fin (4 ^ n) → ℂ :=
  (bellRotation n)ᴴ *ᵥ (fun k => if bellTypeOfIndex n k = T then (1 : ℂ) else 0)

/-! ### Helpers for the Dicke resolution: `bellRotation` commutes with the symmetric projector,
and the rank-one `M·|u⟩⟨u|·Mᴴ = |Mu⟩⟨Mu|` sandwich. -/

/-- The rank-one mulVec sandwich `M·|u⟩⟨u|·Mᴴ = |M u⟩⟨M u|` (mirror of
`op_sandwich_maxEntangled_eq_vecMulVec` for a general vector `u`). -/
theorem vecMulVec_mulVec_sandwich {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) (u : Fin q → ℂ) :
    M * Matrix.vecMulVec u (star u) * Mᴴ = Matrix.vecMulVec (M *ᵥ u) (star (M *ᵥ u)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

/-- `bellRotation n` commutes with every permutation representation matrix. -/
theorem bellRotation_commPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    bellRotation n * permutationRepresentation 4 n σ
      = permutationRepresentation 4 n σ * bellRotation n :=
  tensorFamily_mul_permutationRepresentation _ σ

/-- `bellRotation n` commutes with the symmetric projector. -/
theorem bellRotation_commSymProj (n : ℕ) [NeZero n] :
    bellRotation n * symmetricProjector 4 n = symmetricProjector 4 n * bellRotation n := by
  simp only [symmetricProjector, symmetricProjectorRep, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => bellRotation_commPerm n σ)

/-- `Rᴴ·P_sym·R = P_sym`: the symmetric projector is invariant under conjugation by `Rᴴ`. -/
theorem bellRotation_conjT_symProj (n : ℕ) [NeZero n] :
    (bellRotation n)ᴴ * symmetricProjector 4 n * bellRotation n = symmetricProjector 4 n := by
  rw [Matrix.mul_assoc, (bellRotation_commSymProj n).symm, ← Matrix.mul_assoc,
    bellRotation_unitary, Matrix.one_mul]

/-! ### Combinatorial helpers for the type-indicator identity.

The symmetric-projector entry `⟨i|P_sym|j⟩` is `1/n!` times the number of permutations `σ` with `g ∘
σ = f`, where `f = finFunctionFinEquiv⁻¹ i` and `g = finFunctionFinEquiv⁻¹ j` are the Bell strings.
The count is `0` unless `f` and `g` share a value-multiset, and then it equals `n! / mult_T` by the
orbit–stabilizer identity for the `Sₙ`-action `σ · g = g ∘ σ` on `Fin n → Fin 4` (Harrow, *Church of
the Symmetric Subspace* §2). -/

/-- Mapping the universal multiset of `Fin n` by a permutation leaves it unchanged. -/
private lemma univ_val_map_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset.univ.val.map ⇑σ = Finset.univ.val := by
  have h := congrArg Finset.val (Finset.map_univ_equiv σ)
  rwa [Finset.map_val, Equiv.coe_toEmbedding] at h

/-- Composing with a permutation on the domain preserves the value-multiset over `Fin n`. -/
private lemma univ_val_map_comp_perm {n : ℕ} (g : Fin n → Fin 4) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.val.map (g ∘ ⇑σ) = Finset.univ.val.map g := by
  rw [← Multiset.map_map, univ_val_map_perm]

/-- Two functions on `Fin n` with the same value-multiset differ by a permutation of the domain. -/
private lemma exists_perm_comp_of_map_eq {n : ℕ} {f g : Fin n → Fin 4}
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ σ : Equiv.Perm (Fin n), g ∘ ⇑σ = f := by
  classical
  have hcard : ∀ c : Fin 4, Fintype.card {x // f x = c} = Fintype.card {x // g x = c} := by
    intro c
    have hbridge : ∀ h2 : Fin n → Fin 4,
        Fintype.card {x // h2 x = c} = Multiset.count c (Finset.univ.val.map h2) := by
      intro h2
      rw [Multiset.count_map, Fintype.card_subtype]
      change (Multiset.filter (fun x => h2 x = c) Finset.univ.val).card
        = (Multiset.filter (fun a => c = h2 a) Finset.univ.val).card
      congr 1
      exact Multiset.filter_congr (fun x _ => eq_comm)
    rw [hbridge f, hbridge g, h]
  let φ : ∀ c : Fin 4, {x // f x = c} ≃ {x // g x = c} :=
    fun c => Fintype.equivOfCardEq (hcard c)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
            ((Equiv.sigmaCongrRight φ).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  funext x
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaFiberEquiv_apply]
  rw [(φ _ _).2, Equiv.sigmaFiberEquiv_symm_apply_fst]

/-- The fibers of `σ ↦ g ∘ σ` over any two functions reachable from `g` have equal cardinality
(a coset of the stabilizer under right multiplication by a fixed permutation). -/
private lemma fiber_card_const {n : ℕ} {g f f' : Fin n → Fin 4}
    (hf : ∃ σ : Equiv.Perm (Fin n), g ∘ ⇑σ = f)
    (hf' : ∃ σ : Equiv.Perm (Fin n), g ∘ ⇑σ = f') :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f')).card
      = (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hf
  obtain ⟨σ', hσ'⟩ := hf'
  apply Finset.card_nbij' (fun σ => σ * σ'⁻¹ * σ₀) (fun σ => σ * σ₀⁻¹ * σ')
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
    funext y
    change g ((σ * σ'⁻¹ * σ₀) y) = f y
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have h1 : g (σ (σ'⁻¹ (σ₀ y))) = f' (σ'⁻¹ (σ₀ y)) := congrFun hσ _
    have h2 : f' (σ'⁻¹ (σ₀ y)) = g (σ₀ y) := by
      have hz := congrFun hσ' (σ'⁻¹ (σ₀ y))
      simp only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hz
      exact hz.symm
    rw [h1, h2]
    exact congrFun hσ₀ y
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
    funext y
    change g ((σ * σ₀⁻¹ * σ') y) = f' y
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have h1 : g (σ (σ₀⁻¹ (σ' y))) = f (σ₀⁻¹ (σ' y)) := congrFun hσ _
    have h2 : f (σ₀⁻¹ (σ' y)) = g (σ' y) := by
      have hz := congrFun hσ₀ (σ₀⁻¹ (σ' y))
      simp only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hz
      exact hz.symm
    rw [h1, h2]
    exact congrFun hσ' y
  · intro σ _; dsimp only; group
  · intro σ _; dsimp only; group

/-- Same value-multiset ⟹ the permutation count times the multiset-orbit size is `n!`
(orbit–stabilizer, via `Finset.card_eq_sum_card_fiberwise` and constant fiber cardinality). -/
lemma bellPerm_count_mul_orbit {n : ℕ} {f g : Fin n → Fin 4}
    (hfg : Finset.univ.val.map f = Finset.univ.val.map g) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card *
      (Finset.univ.filter (fun f' : Fin n → Fin 4 =>
        Finset.univ.val.map f' = Finset.univ.val.map g)).card
      = Nat.factorial n := by
  classical
  set orbit := Finset.univ.filter (fun f' : Fin n → Fin 4 =>
    Finset.univ.val.map f' = Finset.univ.val.map g) with horbit
  have hmaps : Set.MapsTo (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ)
      ↑(Finset.univ : Finset (Equiv.Perm (Fin n))) ↑orbit := by
    intro σ _
    simp only [horbit, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact univ_val_map_comp_perm g σ
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
  have hconst : ∀ f' ∈ orbit,
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f')).card
        = (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card := by
    intro f' hf'
    rw [horbit, Finset.mem_filter] at hf'
    exact fiber_card_const (exists_perm_comp_of_map_eq hfg)
      (exists_perm_comp_of_map_eq hf'.2)
  have hsum2 : Nat.factorial n
      = ∑ _f' ∈ orbit, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card := by
    rw [hsum]; exact Finset.sum_congr rfl hconst
  rw [Finset.sum_const, smul_eq_mul] at hsum2
  rw [mul_comm]; exact hsum2.symm

/-- Different value-multiset ⟹ no permutation relates the two Bell strings. -/
private lemma bellPerm_count_zero {n : ℕ} {f g : Fin n → Fin 4}
    (hfg : Finset.univ.val.map f ≠ Finset.univ.val.map g) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => g ∘ ⇑σ = f)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _ heq
  exact hfg (by rw [← heq]; exact univ_val_map_comp_perm g σ)

/-- The Bell type equals iff the underlying value-multisets of the Bell strings agree. -/
private lemma bellType_eq_iff_map_eq {n : ℕ} (a b : Fin (4 ^ n)) :
    bellTypeOfIndex n a = bellTypeOfIndex n b ↔
      Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm a)
        = Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm b) := by
  unfold bellTypeOfIndex
  exact Subtype.mk_eq_mk

/-- The Bell type multiplicity is the size of the multiset-orbit of the Bell string. -/
lemma bellTypeMult_eq_orbit {n : ℕ} (i : Fin (4 ^ n)) :
    bellTypeMult n (bellTypeOfIndex n i)
      = (Finset.univ.filter (fun f' : Fin n → Fin 4 =>
          Finset.univ.val.map f' = Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm i))).card :=
              by
  classical
  unfold bellTypeMult
  apply Finset.card_nbij' (fun k => (@finFunctionFinEquiv 4 n).symm k)
    (fun f' => @finFunctionFinEquiv 4 n f')
  · intro k hk
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hk ⊢
    exact (bellType_eq_iff_map_eq k i).mp hk
  · intro f' hf'
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf' ⊢
    apply (bellType_eq_iff_map_eq (@finFunctionFinEquiv 4 n f') i).mpr
    rw [Equiv.symm_apply_apply]
    exact hf'
  · intro k _; exact Equiv.apply_symm_apply _ _
  · intro f' _; exact Equiv.symm_apply_apply _ _

/-- **The symmetric-projector matrix element is the Bell-type indicator**
(Harrow, *Church of the Symmetric Subspace* §2 / Watrous §7.1).

`⟨i|P_sym|j⟩ = if type(i) = type(j) then mult_T⁻¹ else 0`, where `type = bellTypeOfIndex n` and
`mult_T = bellTypeMult n T` is the type-orbit size.  The orbit-sum count
`#{σ : e⁻¹i = e⁻¹j ∘ σ⁻¹} = n!/mult_T` over a single type orbit is the Sₙ orbit–stabilizer identity
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` for the action `f ↦ f ∘ σ⁻¹` on
`Fin n → Fin 4`, transported through `finFunctionFinEquiv`; the off-orbit entries vanish because
`e⁻¹j ∘ σ⁻¹` always has the multiset of `e⁻¹j`.

The per-orbit fiber count is `n!/mult_T`, and `P_sym·|D_T⟩ = |D_T⟩`. -/
theorem symmetricProjector_apply_eq_typeIndicator (n : ℕ) [NeZero n] (i j : Fin (4 ^ n)) :
    symmetricProjector 4 n i j =
      if bellTypeOfIndex n i = bellTypeOfIndex n j
        then (bellTypeMult n (bellTypeOfIndex n i) : ℂ)⁻¹ else 0 := by
  classical
  have hentry : symmetricProjector 4 n i j
      = (1 / (Nat.factorial n : ℂ)) *
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (@finFunctionFinEquiv 4 n).symm j ∘ ⇑σ = (@finFunctionFinEquiv 4 n).symm i)).card : ℂ) :=
              by
    simp only [symmetricProjector, symmetricProjectorRep, Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul]
    congr 1
    rw [show (fun σ : Equiv.Perm (Fin n) => permutationRepresentation 4 n σ i j)
          = (fun σ : Equiv.Perm (Fin n) =>
              if (@finFunctionFinEquiv 4 n).symm i = (@finFunctionFinEquiv 4 n).symm j ∘ ⇑σ.symm
                then (1 : ℂ) else 0) from by
        funext σ; simp only [permutationRepresentation, Matrix.of_apply]]
    rw [Finset.sum_boole]
    congr 1
    apply Finset.card_nbij' (fun σ => σ⁻¹) (fun σ => σ⁻¹)
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
      rw [Equiv.Perm.inv_def]
      exact hσ.symm
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
      rw [Equiv.Perm.inv_def, Equiv.symm_symm]
      exact hσ.symm
    · intro σ _; simp
    · intro σ _; simp
  rw [hentry]
  by_cases htype : bellTypeOfIndex n i = bellTypeOfIndex n j
  · rw [if_pos htype]
    have hmap : Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm i)
        = Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm j) :=
      (bellType_eq_iff_map_eq i j).mp htype
    have hNmult := bellPerm_count_mul_orbit hmap
    have hmult : (Finset.univ.filter (fun f' : Fin n → Fin 4 =>
          Finset.univ.val.map f' = Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm j))).card
        = bellTypeMult n (bellTypeOfIndex n i) := by
      rw [bellTypeMult_eq_orbit i]
      simp only [hmap]
    rw [← hmult]
    have hcast : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (@finFunctionFinEquiv 4 n).symm j ∘ ⇑σ = (@finFunctionFinEquiv 4 n).symm i)).card : ℂ)
        * ((Finset.univ.filter (fun f' : Fin n → Fin 4 =>
          Finset.univ.val.map f' = Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm j))).card :
              ℂ)
        = (Nat.factorial n : ℂ) := by exact_mod_cast hNmult
    have hfac : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
    have hNz : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (@finFunctionFinEquiv 4 n).symm j ∘ ⇑σ = (@finFunctionFinEquiv 4 n).symm i)).card : ℂ) ≠ 0
              :=
      left_ne_zero_of_mul (hcast ▸ hfac)
    have hoz : ((Finset.univ.filter (fun f' : Fin n → Fin 4 =>
          Finset.univ.val.map f' = Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm j))).card :
              ℂ)
          ≠ 0 :=
      right_ne_zero_of_mul (hcast ▸ hfac)
    rw [← hcast]
    field_simp
  · rw [if_neg htype]
    have hmap : Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm i)
        ≠ Finset.univ.val.map ((@finFunctionFinEquiv 4 n).symm j) := by
      intro h; exact htype ((bellType_eq_iff_map_eq i j).mpr h)
    rw [bellPerm_count_zero hmap]
    simp

/-- **The Dicke resolution of the symmetric projector**:
`P_sym = ∑_T mult_T⁻¹·|D_T⟩⟨D_T|`, the orthogonal Dicke-type decomposition of `Sym^n(ℂ⁴)`. -/
theorem symmetricProjector_eq_bellDicke_resolution (n : ℕ) [NeZero n] :
    symmetricProjector 4 n =
      ∑ T : Sym (Fin 4) n, (bellTypeMult n T : ℂ)⁻¹ •
        Matrix.vecMulVec (bellDickeKet n T) (star (bellDickeKet n T)) := by
  -- The computational-basis type-indicator resolution `∑_T mult_T⁻¹·|χ_T⟩⟨χ_T| = P_sym` (by 3.3),
  -- conjugated back to the Bell basis by `Rᴴ ⬝ R` (which fixes `P_sym`).
  have hcomp : ∑ T : Sym (Fin 4) n, (bellTypeMult n T : ℂ)⁻¹ •
        Matrix.vecMulVec (fun k => if bellTypeOfIndex n k = T then (1 : ℂ) else 0)
          (star (fun k => if bellTypeOfIndex n k = T then (1 : ℂ) else 0))
      = symmetricProjector 4 n := by
    ext i j
    rw [symmetricProjector_apply_eq_typeIndicator, Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
    have hstar : ∀ (T : Sym (Fin 4) n) (k : Fin (4 ^ n)),
        star (if bellTypeOfIndex n k = T then (1 : ℂ) else 0)
          = if bellTypeOfIndex n k = T then (1 : ℂ) else 0 := by
      intro T k; split <;> simp
    simp_rw [hstar]
    by_cases hij : bellTypeOfIndex n i = bellTypeOfIndex n j
    · rw [if_pos hij]
      rw [Finset.sum_eq_single (bellTypeOfIndex n i)]
      · simp [hij]
      · intro T _ hT
        rcases eq_or_ne (bellTypeOfIndex n i) T with h | h
        · exact absurd h.symm hT
        · simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hij, Finset.sum_eq_zero]
      intro T _
      by_cases hiT : bellTypeOfIndex n i = T
      · have hjT : bellTypeOfIndex n j ≠ T := fun h => hij (hiT.trans h.symm)
        simp [hjT]
      · simp [hiT]
  -- Each Bell-Dicke ketbra is the `Rᴴ ⬝ R`-conjugate of the computational indicator ketbra.
  symm
  calc ∑ T : Sym (Fin 4) n, (bellTypeMult n T : ℂ)⁻¹ •
          Matrix.vecMulVec (bellDickeKet n T) (star (bellDickeKet n T))
         = (bellRotation n)ᴴ * (∑ T : Sym (Fin 4) n, (bellTypeMult n T : ℂ)⁻¹ •
            Matrix.vecMulVec (fun k => if bellTypeOfIndex n k = T then (1 : ℂ) else 0)
              (star (fun k => if bellTypeOfIndex n k = T then (1 : ℂ) else 0)))
          * bellRotation n := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl (fun T _ => ?_)
        rw [Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        rw [bellDickeKet,
          ← vecMulVec_mulVec_sandwich (bellRotation n)ᴴ
            (fun k => if bellTypeOfIndex n k = T then (1 : ℂ) else 0),
          Matrix.conjTranspose_conjTranspose]
    _ = (bellRotation n)ᴴ * symmetricProjector 4 n * bellRotation n := by rw [hcomp]
    _ = symmetricProjector 4 n := bellRotation_conjT_symProj n

/-! ### Helpers for the per-type Kraus vector and the final assembly. -/

/-- Reindexing a rank-one outer product `|v⟩⟨v|` precomposes the vector with the (inverse)
    relabel. -/
theorem reindex_symm_vecMulVec {a b : ℕ} (f : Fin a ≃ Fin b) (v : Fin b → ℂ) :
    Matrix.reindex f.symm f.symm (Matrix.vecMulVec v (star v))
      = Matrix.vecMulVec (v ∘ ⇑f) (star (v ∘ ⇑f)) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Matrix.vecMulVec_apply, Function.comp_apply, Pi.star_apply]

/-- Pulling a scalar out of a rank-one outer product `|c·v⟩⟨c·v| = (c·c̄)·|v⟩⟨v|`. -/
theorem vecMulVec_smul_self {a : ℕ} (c : ℂ) (v : Fin a → ℂ) :
    Matrix.vecMulVec (c • v) (star (c • v)) = (c * star c) • Matrix.vecMulVec v (star v) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
    star_mul']
  ring

/-- **(β real)** The single-pair Bell rotation `V = bellSinglePairRotation` has real entries. -/
theorem bellSinglePairRotation_star (i j : Fin 4) :
    star (bellSinglePairRotation i j) = bellSinglePairRotation i j := by
  -- `V i j = conj β_i(j)`, and every Bell ket is `(√2)⁻¹` times a vector with entries in
  -- `{0, 1, -1}`, hence real.
  have hc : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have h0 : star (0 : ℂ) = 0 := star_zero ℂ
  have h1 : star (1 : ℂ) = 1 := star_one ℂ
  have hneg : star (-1 : ℂ) = -1 := by rw [star_neg, h1]
  have hvec {a b e f : ℂ} (ha : star a = a) (hb : star b = b) (he : star e = e)
      (hf : star f = f) :
      star ((Real.sqrt 2 : ℂ)⁻¹ • ![a, b, e, f]) = (Real.sqrt 2 : ℂ)⁻¹ • ![a, b, e, f] := by
    rw [star_smul, hc]
    congr 1
    funext k
    fin_cases k <;> assumption
  have hβ : star (bellKet i).vec = (bellKet i).vec := by
    fin_cases i
    · change star Quantum.Basis.BellStates.bellState00.vec =
        Quantum.Basis.BellStates.bellState00.vec
      rw [Quantum.Basis.BellStates.bellState00_vec]
      exact hvec h1 h0 h0 h1
    · change star Quantum.Basis.BellStates.bellState01.vec =
        Quantum.Basis.BellStates.bellState01.vec
      rw [Quantum.Basis.BellStates.bellState01_vec]
      exact hvec h0 h1 h1 h0
    · change star Quantum.Basis.BellStates.bellState10.vec =
        Quantum.Basis.BellStates.bellState10.vec
      rw [Quantum.Basis.BellStates.bellState10_vec]
      exact hvec h1 h0 h0 hneg
    · change star Quantum.Basis.BellStates.bellState11.vec =
        Quantum.Basis.BellStates.bellState11.vec
      rw [Quantum.Basis.BellStates.bellState11_vec]
      exact hvec h0 h1 hneg h0
  rw [bellSinglePairRotation, Matrix.of_apply, starRingEnd_apply, star_star]
  exact (congrFun hβ j).symm

/-- **(β real, `n`-fold)** The joint Bell rotation `R = bellRotation n = V^{⊗n}` has real
    entries. -/
theorem bellRotation_star (n : ℕ) (a b : Fin (4 ^ n)) :
    star (bellRotation n a b) = bellRotation n a b := by
  simp only [bellRotation, tensorFamily_apply, star_prod]
  exact Finset.prod_congr rfl (fun p _ => bellSinglePairRotation_star _ _)

/-- **(A′) The `(M ⊗ 𝟙)·|ω⟩` vectorization**: applying the tensored-with-identity operator to the
canonical maximally entangled ket vectorizes `M` along the `finProdFinEquiv` index. -/
theorem tensor_one_mulVec_maxEnt {N : ℕ} (M : Op N) :
    Op.tensor M 1 *ᵥ (maxEntangledKet N).vec
      = fun I => M (finProdFinEquiv.symm I).1 (finProdFinEquiv.symm I).2 := by
  funext I
  simp only [Matrix.mulVec, dotProduct, maxEntangledKet]
  rw [show (∑ J, Op.tensor M 1 I J *
        (if (finProdFinEquiv.symm J).1 = (finProdFinEquiv.symm J).2 then (1 : ℂ) else 0))
      = ∑ J, (if (finProdFinEquiv.symm J).1 = (finProdFinEquiv.symm J).2
                then Op.tensor M 1 I J else 0) from by
      refine Finset.sum_congr rfl (fun J _ => ?_); split <;> simp]
  rw [sum_finProdFinEquiv_diag (fun J => Op.tensor M 1 I J)]
  simp only [Op_tensor_apply_finProd, Equiv.symm_apply_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (finProdFinEquiv.symm I).2]
  · simp
  · intro k _ hk; rw [if_neg (Ne.symm hk), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `W·Vᴴ` maps `e_c` to the doubled Bell ket `|β_c⟩ ⊗ |β_c⟩`. -/
private theorem bellDoubling_bellRot_entry (K : Fin (4 * 4)) (c : Fin 4) :
    (bellDoublingIsometry * (bellSinglePairRotation)ᴴ) K c
      = (Ket.tensor (bellKet c) (bellKet c)).vec K := by
  have hcol : (fun a => (bellSinglePairRotation)ᴴ a c) = (bellKet c).vec := by
    funext a
    simp only [Matrix.conjTranspose_apply, bellSinglePairRotation, Matrix.of_apply,
      starRingEnd_apply, star_star]
  have hmv : (bellDoublingIsometry * (bellSinglePairRotation)ᴴ) K c
      = (bellDoublingIsometry *ᵥ (fun a => (bellSinglePairRotation)ᴴ a c)) K := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hmv, hcol, bellDoublingIsometry_bellDouble c]

/-- `W^{⊗n}·Rᴴ = (W·Vᴴ)^{⊗n}` (rectangular tensor-power multiplicativity). -/
private theorem bellDoublingIsometryPow_mul_bellRotationConjT (n : ℕ) :
    bellDoublingIsometryPow n * (bellRotation n)ᴴ
      = tensorFamily fun _ : Fin n => bellDoublingIsometry * (bellSinglePairRotation)ᴴ := by
  rw [bellDoublingIsometryPow, bellRotation, conjTranspose_tensorFamily, tensorFamily_mul]

/-- The `(interleave I, k)` entry of `(W·Vᴴ)^{⊗n}` factors, via the
interleaving digit maps, into the product `Rᴴ_{i₁ k}·Rᴴ_{i₂ k}` of two Bell-rotation columns. -/
private theorem bellDoubling_tensorFamily_entry (n : ℕ) (I : Fin (4 ^ n * 4 ^ n))
    (k : Fin (4 ^ n)) :
    (tensorFamily fun _ : Fin n => bellDoublingIsometry * (bellSinglePairRotation)ᴴ)
        (interleavingEquiv 4 n I) k
      = (bellRotation n)ᴴ (finProdFinEquiv.symm I).1 k *
          (bellRotation n)ᴴ (finProdFinEquiv.symm I).2 k := by
  simp only [tensorFamily_apply]
  simp_rw [bellDoubling_bellRot_entry, Ket.tensor_vec]
  rw [Finset.prod_mul_distrib]
  have hRconjT : (bellRotation n)ᴴ = tensorFamily (fun _ : Fin n => (bellSinglePairRotation)ᴴ) :=
    conjTranspose_tensorFamily _
  congr 1
  · rw [hRconjT]
    simp only [tensorFamily_apply]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [show ((finProdFinEquiv.symm ((@finFunctionFinEquiv (4 * 4) n).symm
          (interleavingEquiv 4 n I) p)).1) = (@finFunctionFinEquiv 4 n).symm
              (finProdFinEquiv.symm I).1 p
        from by
          have h := interleavingEquiv_digit_fst (d := 4) (n := n) (interleavingEquiv 4 n I) p
          rw [Equiv.symm_apply_apply] at h
          exact h.symm]
    rw [Matrix.conjTranspose_apply, bellSinglePairRotation, Matrix.of_apply, starRingEnd_apply,
      star_star]
  · rw [hRconjT]
    simp only [tensorFamily_apply]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [show ((finProdFinEquiv.symm ((@finFunctionFinEquiv (4 * 4) n).symm
          (interleavingEquiv 4 n I) p)).2) = (@finFunctionFinEquiv 4 n).symm
              (finProdFinEquiv.symm I).2 p
        from by
          have h := interleavingEquiv_digit_snd (d := 4) (n := n) (interleavingEquiv 4 n I) p
          rw [Equiv.symm_apply_apply] at h
          exact h.symm]
    rw [Matrix.conjTranspose_apply, bellSinglePairRotation, Matrix.of_apply, starRingEnd_apply,
      star_star]

/-- **(RHS entry)** The Bell-type sector projector `Q_T` in the joint Bell basis: its `(i₁, i₂)`
entry is `∑_{k : type k = T} Rᴴ_{i₁ k}·Rᴴ_{i₂ k}` (using that `R` has real entries). -/
private theorem bellTypeProjector_entry (n : ℕ) (T : Sym (Fin 4) n) (i₁ i₂ : Fin (4 ^ n)) :
    bellTypeProjector n T i₁ i₂
      = ∑ k, (if bellTypeOfIndex n k = T
                then (bellRotation n)ᴴ i₁ k * (bellRotation n)ᴴ i₂ k else 0) := by
  have hdiag : ∀ a, bellTypeDiagProjector n T a a =
      (if bellTypeOfIndex n a = T then (1 : ℂ) else 0) := by
    intro a; simp [bellTypeDiagProjector, Matrix.diagonal_apply_eq]
  unfold bellTypeProjector
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_eq_single a]
  · rw [hdiag]
    have hRi : (bellRotation n) a i₂ = (bellRotation n)ᴴ i₂ a := by
      rw [Matrix.conjTranspose_apply, bellRotation_star]
    rw [hRi]
    by_cases hT : bellTypeOfIndex n a = T
    · rw [if_pos hT, if_pos hT, mul_one]
    · rw [if_neg hT, if_neg hT, mul_zero, zero_mul]
  · intro b _ hb
    simp [bellTypeDiagProjector, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **(C) The doubled Dicke vector is the vectorization of `Q_T`**: the interleaved image of
`W^{⊗n}·|D_T⟩` equals the `finProdFinEquiv`-vectorization of the Bell-type sector projector. -/
private theorem bellDoubling_dicke_vec (n : ℕ) [NeZero n] (T : Sym (Fin 4) n) :
    (bellDoublingIsometryPow n *ᵥ bellDickeKet n T) ∘ ⇑(interleavingEquiv 4 n)
      = fun I => bellTypeProjector n T (finProdFinEquiv.symm I).1 (finProdFinEquiv.symm I).2 := by
  funext I
  change (bellDoublingIsometryPow n *ᵥ bellDickeKet n T) (interleavingEquiv 4 n I)
      = bellTypeProjector n T (finProdFinEquiv.symm I).1 (finProdFinEquiv.symm I).2
  rw [bellDickeKet, Matrix.mulVec_mulVec, bellDoublingIsometryPow_mul_bellRotationConjT]
  simp only [Matrix.mulVec, dotProduct]
  rw [bellTypeProjector_entry]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [bellDoubling_tensorFamily_entry]
  split <;> simp

/-- In the joint Bell basis `τ_Bell` is the diagonal Dirichlet-moment
operator: `R·τ_Bell·Rᴴ = diag(C(n+3,3)⁻¹·⟨i|P_sym|i⟩)` (from `twirl_symProj_diag`). -/
theorem bellDeFinetti_bellRot_diag (n : ℕ) [NeZero n] :
    bellRotation n * (bb84BellDeFinettiDensity n).toOp * (bellRotation n)ᴴ
      = Matrix.diagonal (fun i => (bb84PolyDimTight n : ℂ)⁻¹ * symmetricProjector 4 n i i) := by
  have h1 : (bb84BellDeFinettiDensity n).toOp
      = (Nat.choose (n + 3) 3 : ℂ)⁻¹ • bb84BellTwirl n (symmetricProjector 4 n) :=
    bb84BellTwirl_smul n _ _
  rw [h1, Matrix.mul_smul, Matrix.smul_mul, twirl_symProj_diag]
  ext i j
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul, bb84PolyDimTight]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij, hij]
  · rw [if_neg hij, if_neg hij, mul_zero]

/-- **The Bell-diagonal form of `√τ_Bell`**:
`√τ_Bell = Rᴴ·diag(√(C(n+3,3)⁻¹·mult(type i)⁻¹))·R`.  The RHS is PSD and squares to `τ_Bell` (by the
diagonalization `bellDeFinetti_bellRot_diag` and the type-indicator diagonal
`symmetricProjector_apply_eq_typeIndicator`); by PSD square-root uniqueness (`CFC.sqrt_eq_iff`) it
is `sqrtOp τ_Bell`. -/
theorem sqrtOp_bellDeFinetti_diag (n : ℕ) [NeZero n] :
    sqrtOp (bb84BellDeFinettiDensity n)
      = (bellRotation n)ᴴ *
          Matrix.diagonal (fun i => (Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ *
            (bellTypeMult n (bellTypeOfIndex n i) : ℝ)⁻¹) : ℂ)) * bellRotation n := by
  letI : PartialOrder (Op (4 ^ n)) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op (4 ^ n)) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op (4 ^ n)) := Matrix.instNonnegSpectrumClass
  set sDg : Fin (4 ^ n) → ℂ := fun i => (Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ *
    (bellTypeMult n (bellTypeOfIndex n i) : ℝ)⁻¹) : ℂ) with hsDgdef
  set S : Op (4 ^ n) := (bellRotation n)ᴴ * Matrix.diagonal sDg * bellRotation n with hSdef
  have hnn : (0 : Fin (4 ^ n) → ℂ) ≤ sDg := by
    intro i; exact Complex.zero_le_real.mpr (Real.sqrt_nonneg _)
  have hSpsd : S.PosSemidef := by
    have h := (Matrix.PosSemidef.diagonal hnn).mul_mul_conjTranspose_same (bellRotation n)ᴴ
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hDD : Matrix.diagonal sDg * Matrix.diagonal sDg
      = Matrix.diagonal (fun i => (bb84PolyDimTight n : ℂ)⁻¹ * symmetricProjector 4 n i i) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [symmetricProjector_apply_eq_typeIndicator, if_pos rfl, hsDgdef]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  have hSS : S * S = (bb84BellDeFinettiDensity n).toOp := by
    have hRRc : bellRotation n * (bellRotation n)ᴴ = 1 := bellRotation_mul_conjTranspose n
    have hcalc : S * S = (bellRotation n)ᴴ *
        (Matrix.diagonal sDg * Matrix.diagonal sDg) * bellRotation n := by
      rw [hSdef]
      rw [show (bellRotation n)ᴴ * Matrix.diagonal sDg * bellRotation n *
            ((bellRotation n)ᴴ * Matrix.diagonal sDg * bellRotation n)
          = (bellRotation n)ᴴ * Matrix.diagonal sDg * (bellRotation n * (bellRotation n)ᴴ) *
              Matrix.diagonal sDg * bellRotation n from by noncomm_ring,
        hRRc, Matrix.mul_one]
      noncomm_ring
    rw [hcalc, hDD]
    have hdiag := bellDeFinetti_bellRot_diag n
    rw [show (bellRotation n)ᴴ *
          Matrix.diagonal (fun i => (bb84PolyDimTight n : ℂ)⁻¹ * symmetricProjector 4 n i i) *
          bellRotation n
        = (bellRotation n)ᴴ * (bellRotation n * (bb84BellDeFinettiDensity n).toOp *
            (bellRotation n)ᴴ) * bellRotation n from by rw [hdiag]]
    rw [show (bellRotation n)ᴴ * (bellRotation n * (bb84BellDeFinettiDensity n).toOp *
            (bellRotation n)ᴴ) * bellRotation n
          = ((bellRotation n)ᴴ * bellRotation n) * (bb84BellDeFinettiDensity n).toOp *
              ((bellRotation n)ᴴ * bellRotation n) from by noncomm_ring,
      bellRotation_unitary, Matrix.one_mul, Matrix.mul_one]
  unfold sqrtOp
  rw [CFC.sqrt_eq_iff _ _
    (posSemidefOp_implies_mathlib (bb84BellDeFinettiDensity n).toPosSemidefOp).nonneg hSpsd.nonneg]
  exact hSS

/-- **`B_T = √τ_T·Q_T`**: the type-coherent Kraus operator is the scalar `√τ_T` times the Bell-type
sector projector. -/
private theorem bellPairedKraus_eq_smul (n : ℕ) [NeZero n] (T : Sym (Fin 4) n) :
    bellPairedKraus n T
      = (Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ * (bellTypeMult n T : ℝ)⁻¹) : ℂ) •
          bellTypeProjector n T := by
  rw [bellPairedKraus, sqrtOp_bellDeFinetti_diag, bellTypeProjector]
  set sDg : Fin (4 ^ n) → ℂ := fun i => (Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ *
    (bellTypeMult n (bellTypeOfIndex n i) : ℝ)⁻¹) : ℂ) with hsDgdef
  have hRRc : bellRotation n * (bellRotation n)ᴴ = 1 := bellRotation_mul_conjTranspose n
  have hDP : Matrix.diagonal sDg * bellTypeDiagProjector n T
      = (Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ * (bellTypeMult n T : ℝ)⁻¹) : ℂ) •
          bellTypeDiagProjector n T := by
    ext i j
    simp only [bellTypeDiagProjector, Matrix.diagonal_mul_diagonal, Matrix.smul_apply,
      Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with hij hT
    · simp only [hsDgdef, hT, mul_one]
    · simp only [mul_zero]
    · simp only [mul_zero]
  calc (bellRotation n)ᴴ * Matrix.diagonal sDg * bellRotation n *
          ((bellRotation n)ᴴ * bellTypeDiagProjector n T * bellRotation n)
         = (bellRotation n)ᴴ * Matrix.diagonal sDg * (bellRotation n * (bellRotation n)ᴴ) *
          bellTypeDiagProjector n T * bellRotation n := by noncomm_ring
    _ = (bellRotation n)ᴴ * (Matrix.diagonal sDg * bellTypeDiagProjector n T) *
          bellRotation n := by rw [hRRc, Matrix.mul_one]; noncomm_ring
    _ = (bellRotation n)ᴴ * ((Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ *
            (bellTypeMult n T : ℝ)⁻¹) : ℂ) • bellTypeDiagProjector n T) * bellRotation n := by
          rw [hDP]
    _ = (Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ * (bellTypeMult n T : ℝ)⁻¹) : ℂ) •
          ((bellRotation n)ᴴ * bellTypeDiagProjector n T * bellRotation n) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **The per-type Kraus vector identity** (Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
`arXiv:2403.11851` Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry).

`(B_T ⊗ 𝟙)|ω⟩ = √τ_T · W̃|D_T⟩`, where `B_T = bellPairedKraus n T = √τ_Bell · Q_T`,
`|ω⟩ = maxEntangledKet (4ⁿ)`, `τ_T = (C(n+3,3)·mult_T)⁻¹`, `|D_T⟩ = bellDickeKet n T`, and
`W̃ = rdx ∘ (W^{⊗n} · )` is the doubled-Bell embedding (`bellDoublingIsometryPow`, interleaved by
`interleavingEquiv 4 n`).

Content: `|ω⟩ = ∑_m |β_m⟩⊗|β_m⟩` (Bell states real), `B_T|β_m⟩ = √τ_T·𝟙[m∈T]·|β_m⟩`
(the `√τ_Bell` Bell-diagonal form `sqrtOp_bellDeFinetti_diag` × the type indicator), and
`W̃|β_m⟩ = |β_m⟩⊗|β_m⟩` (the tensorized doubling `bellDoublingIsometry_bellDouble`).
-/
theorem bb84_bellPairedKraus_maxEnt_vec (n : ℕ) [NeZero n] (T : Sym (Fin 4) n) :
    Op.tensor (bellPairedKraus n T) 1 *ᵥ (maxEntangledKet (4 ^ n)).vec
      = (Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ * (bellTypeMult n T : ℝ)⁻¹) : ℂ) •
        ((bellDoublingIsometryPow n *ᵥ bellDickeKet n T) ∘ ⇑(interleavingEquiv 4 n)) := by
  rw [bellPairedKraus_eq_smul, Op.tensor_smul_left, Matrix.smul_mulVec,
    tensor_one_mulVec_maxEnt, bellDoubling_dicke_vec]

/-- **The per-type Kraus sandwich** (the squared, outer-product form of the per-type Kraus vector
identity that the core assembly consumes): `(B_T⊗𝟙)·Ω·(B_T⊗𝟙)ᴴ = τ_T ·
rdx(W^{⊗n}·|D_T⟩⟨D_T|·(W^{⊗n})ᴴ)` with `τ_T = (C(n+3,3)·mult_T)⁻¹`.  Derived from
`bb84_bellPairedKraus_maxEnt_vec` by `op_sandwich`. -/
theorem bb84_bellPairedKraus_maxEnt_outer (n : ℕ) [NeZero n] (T : Sym (Fin 4) n) :
    Op.tensor (bellPairedKraus n T) 1 * maxEntangledOp (4 ^ n) *
        (Op.tensor (bellPairedKraus n T) 1)ᴴ
      = ((bb84PolyDimTight n : ℂ)⁻¹ * (bellTypeMult n T : ℂ)⁻¹) •
        Matrix.reindex (interleavingEquiv 4 n).symm (interleavingEquiv 4 n).symm
          (bellDoublingIsometryPow n *
            Matrix.vecMulVec (bellDickeKet n T) (star (bellDickeKet n T)) *
            (bellDoublingIsometryPow n)ᴴ) := by
  rw [op_sandwich_maxEntangled_eq_vecMulVec, bb84_bellPairedKraus_maxEnt_vec n T,
    vecMulVec_smul_self, ← reindex_symm_vecMulVec (interleavingEquiv 4 n)
      (bellDoublingIsometryPow n *ᵥ bellDickeKet n T),
    ← vecMulVec_mulVec_sandwich (bellDoublingIsometryPow n) (bellDickeKet n T)]
  congr 1
  -- the scalar `√τ_T · conj(√τ_T) = τ_T = (C·mult_T)⁻¹`
  have hx : (0 : ℝ) ≤ (bb84PolyDimTight n : ℝ)⁻¹ * (bellTypeMult n T : ℝ)⁻¹ := by positivity
  rw [show star (Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ * (bellTypeMult n T : ℝ)⁻¹) : ℂ)
        = (Real.sqrt ((bb84PolyDimTight n : ℝ)⁻¹ * (bellTypeMult n T : ℝ)⁻¹) : ℂ) from
      Complex.conj_ofReal _,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hx]
  push_cast
  ring

/-- **The W-conjugation Dicke identity** (Nahar et al. 2024 `arXiv:2403.11851` Lemma 2, `x = 4`,
joint Bell `ℤ₂×ℤ₂` symmetry).

The finite type-coherent Kraus sum `bb84BellPairedDeFinettiStateOp n`
equals the `W`-conjugation of the normalized symmetric projector,
re-keyed from the interleaved `(16^n)`-index to the concatenated `(4^n·4^n)` A⊗B index by the CKR
device `Matrix.reindex (interleavingEquiv 4 n).symm`.  Here `W^{⊗n} = bellDoublingIsometryPow n` and
`C(n+3,3) = bb84PolyDimTight n = dim Symⁿ(ℂ⁴)`.

Its content is the per-type Kraus-vector
identity `bb84_bellPairedKraus_maxEnt_vec`, `(B_T⊗𝟙)|ω⟩ = √τ_T·W̃|D_T⟩`, together with the Dicke
resolution `symmetricProjector_eq_bellDicke_resolution`, `symProj 4 n = ∑_T mult_T⁻¹·|D_T⟩⟨D_T|`. -/
theorem bb84BellPairedDeFinettiState_eq_Wconj_symProj (n : ℕ) [NeZero n] :
    bb84BellPairedDeFinettiStateOp n =
      Matrix.reindex (interleavingEquiv 4 n).symm (interleavingEquiv 4 n).symm
        ( bellDoublingIsometryPow n
            * ( ((bb84PolyDimTight n : ℂ)⁻¹) • symmetricProjector 4 n )
            * (bellDoublingIsometryPow n)ᴴ ) := by
  -- Expand the `(C⁻¹•P_sym)` conjugation into the per-type Dicke sum.
  have key : bellDoublingIsometryPow n
        * ((bb84PolyDimTight n : ℂ)⁻¹ • symmetricProjector 4 n) * (bellDoublingIsometryPow n)ᴴ
      = ∑ T : Sym (Fin 4) n, ((bb84PolyDimTight n : ℂ)⁻¹ * (bellTypeMult n T : ℂ)⁻¹) •
          (bellDoublingIsometryPow n *
            Matrix.vecMulVec (bellDickeKet n T) (star (bellDickeKet n T)) *
            (bellDoublingIsometryPow n)ᴴ) := by
    rw [symmetricProjector_eq_bellDicke_resolution n, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [bb84BellPairedDeFinettiStateOp]
  simp_rw [bb84_bellPairedKraus_maxEnt_outer n]
  rw [key, Matrix.reindex_sum]
  simp_rw [Matrix.reindex_smul]

end Quantum.Symmetry

end -- noncomputable section
