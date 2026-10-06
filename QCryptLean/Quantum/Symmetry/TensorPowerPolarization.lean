import QCryptLean.Math.Combinatorics.PermutationAction
import QCryptLean.Quantum.Symmetry.SymmetricSubspace
import QCryptLean.Quantum.TensorProducts.TensorFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum

/-!
# The polarization identity and `span{Aⁿ} = Com(perm)`

The multilinear polarization identity for `n`-th tensor powers, and its consequence that the
span of the `n`-th tensor powers `{Aⁿ : A ∈ Op dR}` is exactly the commutant of the
site-permutation representation `{P_R(π) : π ∈ Sₙ}`.

## Main statements
- `Quantum.Symmetry.tensorFamily_polarization` : the inclusion–exclusion polarization
  identity `∑_{S⊆[n]}(-1)^{n-|S|}(∑_{i∈S}A_i)^{⊗n} = ∑_{σ∈Sₙ} ⊗ₖ A_{σ(k)}`.
- `Quantum.Symmetry.span_tensorPow_eq_permCommutant` : `span{A^{⊗n}} = permCommutant`, with
  `A^{⊗n} = Quantum.TensorProducts.Op.tensorPow A n`.

## Design constraints
For `dR < n` the `P_R(π)` are linearly **dependent**: NO `LinearIndependent` claim, NO
dimension count, NO unique-coefficient claim. All span statements are over `Set.range`.
The identity holds for all `dR, n ≥ 1`; no `dA ≤ dR` hypothesis, no A-register.
-/

open Matrix Math.RepresentationTheory Quantum.Operators Quantum.TensorProducts
open scoped Matrix BigOperators

noncomputable section

namespace Quantum.Symmetry

/-! ## The scalar inclusion–exclusion (polarization) identity -/

/-- **Scalar polarization / inclusion–exclusion identity.**

For a matrix `x : Fin n → Fin n → ℂ` (`x i k` = the `k`-th factor of the `i`-th operator),

  `∑_{S ⊆ [n]} (-1)^{n-|S|} ∏ₖ (∑_{i∈S} x i k) = ∑_{σ ∈ Sₙ} ∏ₖ x (σ k) k`.

Expanding each product of sums over functions `p : [n] → S`, the coefficient of
`∏ₖ x (p k) k` is `∑_{S ⊇ image p} (-1)^{n-|S|}`, which is `1` if `p` is surjective (a
permutation) and `0` otherwise, by the alternating-sign powerset sum. -/
private lemma scalar_polarization {n : ℕ} (x : Fin n → Fin n → ℂ) :
    (∑ S : Finset (Fin n), (-1 : ℂ) ^ (n - S.card) * ∏ k : Fin n, ∑ i ∈ S, x i k)
      = ∑ σ : Equiv.Perm (Fin n), ∏ k : Fin n, x (σ k) k := by
  classical
  -- The complement involution on `Finset (Fin n)`.
  set cE : Finset (Fin n) ≃ Finset (Fin n) :=
    ⟨fun s => sᶜ, fun s => sᶜ, fun s => compl_compl s, fun s => compl_compl s⟩ with hcE
  -- Step 1: expand each product of sums over `p ∈ piFinset (const S)`.
  have hstep1 : ∀ S : Finset (Fin n),
      (∏ k : Fin n, ∑ i ∈ S, x i k)
        = ∑ p ∈ Fintype.piFinset (fun _ : Fin n => S), ∏ k : Fin n, x (p k) k := by
    intro S
    exact Finset.prod_univ_sum (fun _ : Fin n => S) (fun k i => x i k)
  -- The inner-coefficient computation `∑_{S ⊇ image p} (-1)^{n-|S|} = [image p = univ]`.
  have hcoef : ∀ p : Fin n → Fin n,
      (∑ S : Finset (Fin n), if (∀ k, p k ∈ S) then (-1 : ℂ) ^ (n - S.card) else 0)
        = if Finset.image p Finset.univ = Finset.univ then 1 else 0 := by
    intro p
    set R : Finset (Fin n) := Finset.image p Finset.univ with hR
    -- rewrite the condition `∀ k, p k ∈ S` as `R ⊆ S`, and `(-1)^{n-|S|}` as `(-1)^{|Sᶜ|}`.
    have hcond : ∀ S : Finset (Fin n), (∀ k, p k ∈ S) ↔ R ⊆ S := by
      intro S
      rw [hR, Finset.image_subset_iff]
      constructor
      · intro h k _; exact h k
      · intro h k; exact h k (Finset.mem_univ k)
    have hsign : ∀ S : Finset (Fin n),
        (-1 : ℂ) ^ (n - S.card) = (-1 : ℂ) ^ (Sᶜ.card) := by
      intro S
      rw [Finset.card_compl, Fintype.card_fin]
    calc (∑ S : Finset (Fin n), if (∀ k, p k ∈ S) then (-1 : ℂ) ^ (n - S.card) else 0)
        = ∑ S : Finset (Fin n), if R ⊆ S then (-1 : ℂ) ^ (Sᶜ.card) else 0 := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [hsign S]; simp only [hcond S]
      _ = ∑ S : Finset (Fin n), if R ⊆ Sᶜ then (-1 : ℂ) ^ (S.card) else 0 := by
          rw [← Equiv.sum_comp cE
            (fun S => if R ⊆ Sᶜ then (-1 : ℂ) ^ (S.card) else 0)]
          refine Finset.sum_congr rfl fun S _ => ?_
          simp only [hcE, Equiv.coe_fn_mk, compl_compl]
      _ = ∑ S ∈ Rᶜ.powerset, (-1 : ℂ) ^ (S.card) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext S
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
            Finset.subset_compl_comm]
      _ = if Rᶜ = ∅ then 1 else 0 := by
          have h := Finset.sum_powerset_neg_one_pow_card (x := Rᶜ)
          have hc := congrArg (fun z : ℤ => (z : ℂ)) h
          simp only [Int.cast_sum, Int.cast_pow, Int.cast_neg, Int.cast_one,
            apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero] at hc
          exact hc
      _ = if R = Finset.univ then 1 else 0 := by
          simp only [Finset.compl_eq_empty_iff]
  -- Step 2: substitute, swap the order of summation, and collapse the coefficient.
  calc (∑ S : Finset (Fin n), (-1 : ℂ) ^ (n - S.card) * ∏ k : Fin n, ∑ i ∈ S, x i k)
      = ∑ S : Finset (Fin n), ∑ p : Fin n → Fin n,
          (if (∀ k, p k ∈ S) then (-1 : ℂ) ^ (n - S.card) * ∏ k : Fin n, x (p k) k else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [hstep1 S, Finset.mul_sum, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    _ = ∑ p : Fin n → Fin n, (∏ k : Fin n, x (p k) k) *
          (∑ S : Finset (Fin n), if (∀ k, p k ∈ S) then (-1 : ℂ) ^ (n - S.card) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        by_cases h : (∀ k, p k ∈ S) <;> simp [h, mul_comm]
    _ = ∑ p : Fin n → Fin n, (∏ k : Fin n, x (p k) k) *
          (if Finset.image p Finset.univ = Finset.univ then 1 else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hcoef p]
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ k : Fin n, x (σ k) k := by
        have hsurj : ∀ p : Fin n → Fin n,
            Finset.image p Finset.univ = Finset.univ ↔ Function.Surjective p := by
          intro p
          rw [Finset.eq_univ_iff_forall]
          constructor
          · intro h y
            have hy := h y
            rw [Finset.mem_image] at hy
            obtain ⟨a, _, ha⟩ := hy
            exact ⟨a, ha⟩
          · intro h y
            rw [Finset.mem_image]
            obtain ⟨a, ha⟩ := h y
            exact ⟨a, Finset.mem_univ a, ha⟩
        simp only [mul_ite, mul_one, mul_zero]
        rw [← Finset.sum_filter]
        refine Finset.sum_bij'
          (fun p hp => Equiv.ofBijective p
            (Finite.injective_iff_bijective.mp
              (Finite.injective_iff_surjective.mpr
                ((hsurj p).mp (Finset.mem_filter.mp hp).2))))
          (fun σ _ => (⇑σ : Fin n → Fin n))
          (fun p _ => Finset.mem_univ _)
          (fun σ _ => ?_) (fun p _ => ?_) (fun σ _ => ?_) (fun p _ => ?_)
        · -- j σ ∈ filter-set: ⇑σ has full image
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (hsurj _).mpr σ.surjective⟩
        · -- left inverse on the filter-set: `⇑(ofBijective p _) = p`
          rfl
        · -- right inverse on Perm: `ofBijective ⇑σ _ = σ`
          exact Equiv.ext (fun y => rfl)
        · -- the summands agree
          rfl

/-! ## Theorem (a): the polarization identity -/

/-- **Polarization identity for `n`-th tensor powers** (part (a)).

`∑_{S⊆[n]} (-1)^{n-|S|} (∑_{i∈S} A_i)^{⊗n} = ∑_{σ∈Sₙ} ⊗ₖ A_{σ(k)}`.

Both sides reduce entrywise (via `Op.tensorPow_apply` / `tensorFamily_apply`) to the scalar
inclusion–exclusion identity `scalar_polarization`. -/
theorem tensorFamily_polarization {dR n : ℕ} (A : Fin n → Op dR) :
    (∑ S : Finset (Fin n), ((-1 : ℂ) ^ (n - S.card)) • Op.tensorPow (∑ i ∈ S, A i) n)
      = ∑ σ : Equiv.Perm (Fin n), tensorFamily fun k => A (σ k) := by
  classical
  ext I J
  rw [Matrix.sum_apply, Matrix.sum_apply]
  -- set the scalar data `x i k := (A i)_{(e⁻¹ I) k, (e⁻¹ J) k}`
  set fI := (@finFunctionFinEquiv dR n).symm I with hfI
  set fJ := (@finFunctionFinEquiv dR n).symm J with hfJ
  have hLHS : ∀ S : Finset (Fin n),
      (((-1 : ℂ) ^ (n - S.card)) • Op.tensorPow (∑ i ∈ S, A i) n) I J
        = (-1 : ℂ) ^ (n - S.card) * ∏ k : Fin n, ∑ i ∈ S, (A i) (fI k) (fJ k) := by
    intro S
    rw [Matrix.smul_apply, smul_eq_mul, Op.tensorPow_apply]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Matrix.sum_apply]
  have hRHS : ∀ σ : Equiv.Perm (Fin n),
      (tensorFamily fun k => A (σ k)) I J = ∏ k : Fin n, (A (σ k)) (fI k) (fJ k) :=
    fun σ => tensorFamily_apply _ I J
  rw [Finset.sum_congr rfl (fun S _ => hLHS S),
      Finset.sum_congr rfl (fun σ _ => hRHS σ)]
  exact scalar_polarization (fun i k => (A i) (fI k) (fJ k))

/-! ## Theorem (b): `span{A^{⊗n}} = Com(perm)` -/

/-- `c • single i j 1 = single i j c`. -/
private lemma single_one_smul {N : ℕ} (i j : Fin N) (c : ℂ) :
    c • Matrix.single i j (1 : ℂ) = Matrix.single i j c := by
  ext i' j'
  simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- The **commutant of the site-permutation representation**, packaged as a `Submodule`
(same shape as `repCommutant`): the operators on `Rⁿ` commuting with every `P_R(π)`. -/
def permCommutant (dR n : ℕ) [NeZero dR] : Submodule ℂ (Op (dR ^ n)) where
  carrier := { M | ∀ π : Equiv.Perm (Fin n),
    permutationRepresentation dR n π * M = M * permutationRepresentation dR n π }
  add_mem' := by
    intro a b ha hb π
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_add, add_mul, ha π, hb π]
  zero_mem' := by
    intro π
    simp only [mul_zero, zero_mul]
  smul_mem' := by
    intro c M hM π
    simp only [Set.mem_setOf_eq] at hM ⊢
    rw [mul_smul_comm, smul_mul_assoc, hM π]

/-- **Span-of-tensor-powers conclusion:** the span of the `n`-th tensor powers is exactly the
commutant of the site-permutation representation.

`span{A^{⊗n} : A ∈ Op dR} = { M | ∀ π, P_R(π) · M = M · P_R(π) }`.

`⊆`: each `A^{⊗n}` commutes with every `P_R(π)`
(`Op.commute_tensorPow_permutationRepresentation`).
`⊇`: any `M` commuting with all `P_R(π)` has entries constant on diagonal `Sₙ`-orbits
(`permRep_conj_entry`), so its symmetrization equals `M`; each orbit-symmetrization of a
matrix unit lies in the span by the polarization identity (a). -/
theorem span_tensorPow_eq_permCommutant (dR n : ℕ) [NeZero dR] [NeZero n] :
    Submodule.span ℂ (Set.range (fun A : Op dR => Op.tensorPow A n)) = permCommutant dR n := by
  classical
  set e := @finFunctionFinEquiv dR n with he
  apply le_antisymm
  · -- ⊆ : each tensor power lies in the commutant
    rw [Submodule.span_le]
    rintro _ ⟨A, rfl⟩ π
    exact (Op.commute_tensorPow_permutationRepresentation A π).symm.eq
  · -- ⊇ : the commutant lies in the span
    intro M hM
    -- entries are constant on diagonal `Sₙ`-orbits
    have hEntry : ∀ (τ : Equiv.Perm (Fin n)) (a b : Fin n → Fin dR),
        M (e (a ∘ τ)) (e (b ∘ τ)) = M (e a) (e b) := by
      intro τ a b
      have hU := permutationRepresentation_unitary dR n τ
      have hconj : permutationRepresentation dR n τ * M
          * (permutationRepresentation dR n τ)ᴴ = M := by
        calc permutationRepresentation dR n τ * M * (permutationRepresentation dR n τ)ᴴ
            = M * permutationRepresentation dR n τ * (permutationRepresentation dR n τ)ᴴ := by
              rw [hM τ]
          _ = M * (permutationRepresentation dR n τ * (permutationRepresentation dR n τ)ᴴ) := by
              rw [Matrix.mul_assoc]
          _ = M * 1 := by rw [hU.2]
          _ = M := Matrix.mul_one M
      have hpe := Quantum.Symmetry.permRep_conj_entry τ M (e a) (e b)
      rw [hconj, ← he] at hpe
      simpa only [Equiv.symm_apply_apply] using hpe.symm
    -- orbit-symmetrizations of matrix units lie in the span
    have horbit : ∀ a b : Fin n → Fin dR,
        (∑ σ : Equiv.Perm (Fin n), Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ))
          ∈ Submodule.span ℂ (Set.range (fun A : Op dR => Op.tensorPow A n)) := by
      intro a b
      have hpol := tensorFamily_polarization fun i => Matrix.single (a i) (b i) (1 : ℂ)
      have hswt : ∀ σ : Equiv.Perm (Fin n),
          (tensorFamily fun k => Matrix.single (a (σ k)) (b (σ k)) (1 : ℂ))
            = Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ) := by
        intro σ
        have h := tensorFamily_single (a ∘ σ) (b ∘ σ) fun _ => (1 : ℂ)
        rw [Finset.prod_const_one] at h
        exact h
      have hrw : (∑ σ : Equiv.Perm (Fin n),
            Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ))
          = ∑ S : Finset (Fin n), ((-1 : ℂ) ^ (n - S.card)) •
              Op.tensorPow (∑ i ∈ S, Matrix.single (a i) (b i) (1 : ℂ)) n := by
        rw [hpol]
        exact Finset.sum_congr rfl fun σ _ => (hswt σ).symm
      rw [hrw]
      refine Submodule.sum_mem _ fun S _ => ?_
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    -- averaging: `M` is the symmetrization of its own matrix-unit expansion
    have hfac : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    have hterm : ∀ σ : Equiv.Perm (Fin n),
        (∑ a : Fin n → Fin dR, ∑ b : Fin n → Fin dR,
           M (e a) (e b) • Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ)) = M := by
      intro σ
      set q : (Fin n → Fin dR) ≃ (Fin n → Fin dR) :=
        Equiv.arrowCongr σ.symm (Equiv.refl (Fin dR)) with hq
      have hqa : ∀ c : Fin n → Fin dR, q c = c ∘ σ := by
        intro c; ext k; simp [hq, Equiv.arrowCongr_apply]
      set E : (Fin n → Fin dR) ≃ Fin (dR ^ n) := q.trans e with hE
      have hEa : ∀ c : Fin n → Fin dR, E c = e (c ∘ σ) := by
        intro c; rw [hE, Equiv.trans_apply, hqa c]
      have hsum : (∑ a : Fin n → Fin dR, ∑ b : Fin n → Fin dR,
            M (e a) (e b) • Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ))
          = ∑ a : Fin n → Fin dR, ∑ b : Fin n → Fin dR,
              Matrix.single (E a) (E b) (M (E a) (E b)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [single_one_smul, ← hEntry σ a b, ← hEa a, ← hEa b]
      rw [hsum,
        Equiv.sum_comp E (fun I => ∑ b, Matrix.single I (E b) (M I (E b)))]
      conv_rhs => rw [Matrix.matrix_eq_sum_single M]
      refine Finset.sum_congr rfl fun I _ => ?_
      exact Equiv.sum_comp E (fun J => Matrix.single I J (M I J))
    have hMspan : M = ∑ a : Fin n → Fin dR, ∑ b : Fin n → Fin dR,
        (M (e a) (e b) / (Nat.factorial n : ℂ)) •
          (∑ σ : Equiv.Perm (Fin n), Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ)) := by
      symm
      calc (∑ a : Fin n → Fin dR, ∑ b : Fin n → Fin dR,
              (M (e a) (e b) / (Nat.factorial n : ℂ)) •
                (∑ σ : Equiv.Perm (Fin n), Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ)))
          = ∑ a : Fin n → Fin dR, ∑ b : Fin n → Fin dR, ∑ σ : Equiv.Perm (Fin n),
              (M (e a) (e b) / (Nat.factorial n : ℂ)) •
                Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ) := by
            simp only [Finset.smul_sum]
        _ = ∑ σ : Equiv.Perm (Fin n), ∑ a : Fin n → Fin dR, ∑ b : Fin n → Fin dR,
              (M (e a) (e b) / (Nat.factorial n : ℂ)) •
                Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ) := by
            rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
            rw [Finset.sum_comm]
        _ = ∑ _σ : Equiv.Perm (Fin n), (1 / (Nat.factorial n : ℂ)) • M := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            have hfactor : (∑ a : Fin n → Fin dR, ∑ b : Fin n → Fin dR,
                  (M (e a) (e b) / (Nat.factorial n : ℂ)) •
                    Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ))
                = (1 / (Nat.factorial n : ℂ)) •
                    (∑ a : Fin n → Fin dR, ∑ b : Fin n → Fin dR,
                      M (e a) (e b) • Matrix.single (e (a ∘ σ)) (e (b ∘ σ)) (1 : ℂ)) := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [smul_smul]
              congr 1
              rw [one_div, ← div_eq_inv_mul]
            rw [hfactor, hterm σ]
        _ = M := by
            rw [← Finset.sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
              Fintype.card_fin, nsmul_eq_mul, mul_one_div, div_self hfac, one_smul]
    rw [hMspan]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    exact Submodule.smul_mem _ _ (horbit a b)

end Quantum.Symmetry
