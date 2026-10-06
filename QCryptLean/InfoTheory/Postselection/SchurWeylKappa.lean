import QCryptLean.InfoTheory.Postselection.SchurWeylTwirl
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Quantum.Channels.CPTP.CKRBound.HermitianContractivity
import QCryptLean.Quantum.Operators.BraKet.Projector

/-!
# QKD postselection — the Schur–Weyl `κ`-construction, Ω-layer (SP1, steps 1–3)

The **Ω-layer** of the duality-free route to SP1 (`SchurWeylTwirl.lean`):
`Ω := Tr_R(P_Sym)`, the partial trace of the
generalized paired symmetric projector `symmetricProjectorPairedGen dA dR n` over the `R`-factor.
`Ω` is the natural PSD/Hermitian, `Sₙ`-central object that the eventual SP1 flattening `κ`
(`SchurWeylTwirl.lean`'s `exists_flatten_maxEntangledUnitaryTwirl`) must be built from/around; this
file proves exactly the three structural facts required of it, and no more (the SP1
assembly itself — invertibility, the twirl-flattening identity — is out of scope here).

## Main definitions
- `InfoTheory.Postselection.symmetricProjectorPairedTraceR dA dR n` : `Ω := Tr_R(P_Sym)`, the
partial
  trace of `symmetricProjectorPairedGen dA dR n` (`SchurWeylTwirl.lean`) over the `R`-factor.

## Main statements
- `InfoTheory.Postselection.symmetricProjectorPairedTraceR_eq_traceWeightedSum` (step 1): the
  **class-function expansion** `Ω = (1/n!) Σ_σ Tr(U_σ^{dR}) • U_σ^{dA}`. `Tr(U_σ^{dR})` is the
  standard `Sₙ` character of the permutation representation — the fixed-tensor-word count
  `permutationRepresentation_trace_eq_fixed_card`,
  equal to `dR ^ (number of cycles of σ)` (Burnside); we work with
  the trace directly (the reusable form) rather than re-deriving the cycle-count
  combinatorics, which is not needed for steps 2–3 below.
- `InfoTheory.Postselection.symmetricProjectorPairedTraceR_posSemidef` /
  `symmetricProjectorPairedTraceR_isHermitian` (step 2): `Ω` is PSD and Hermitian — the partial
  trace of the PSD, Hermitian projector `symmetricProjectorPairedGen`
  (`symmetricProjectorPairedGen_posSemidef`), via the `partialTraceB_posSemidef_mathlib` /
  `partialTraceB_hermitian` (from the Quantum.TensorProducts.Trace module).
- `InfoTheory.Postselection.symmetricProjectorPairedTraceR_commute` (step 3): `Ω` is
**`Sₙ`-central**:
  `Commute (permutationRepresentation dA n π) Ω` for every `π`. Follows from the class-function
  expansion (step 1): reindexing the character-weighted sum along the conjugation bijection
  `σ ↦ π·σ·π⁻¹` (`mul_conj_bijective`, `PermutationAction.lean`) and using that `Tr(U_σ^{dR})` is a
  class function (`permutationRepresentation_trace_conj`) turns
  `U_π^{dA}·Ω` into `Ω·U_π^{dA}` term by term (`permutationRepresentation_mul`) — the standard
  "class-function-weighted sums are central in the group algebra" argument.
-/

open Quantum.Symmetry

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-- **`Ω := Tr_R(P_Sym)`**: the partial trace, over the `R`-factor, of the generalized paired
symmetric projector `symmetricProjectorPairedGen dA dR n` (`SchurWeylTwirl.lean`). The natural
PSD/Hermitian, `Sₙ`-central object underlying the Ω-layer of the SP1 duality-free route. -/
def symmetricProjectorPairedTraceR (dA dR n : ℕ) [NeZero dA] [NeZero dR] [NeZero n] :
    Op (dA ^ n) :=
  partialTraceB (symmetricProjectorPairedGen dA dR n)

/-- **Step 1 (class-function expansion).** `Ω = (1/n!) Σ_σ Tr(U_σ^{dR}) • U_σ^{dA}`: tracing out
`R` from `P_Sym = (1/n!) Σ_σ U_σ^{dA} ⊗ U_σ^{dR}` collapses each tensor term
(`partialTraceB_tensor_op`, `Tr_R(A⊗B) = Tr(B)·A`). -/
theorem symmetricProjectorPairedTraceR_eq_traceWeightedSum (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] :
    symmetricProjectorPairedTraceR dA dR n
      = (1 / (Nat.factorial n : ℂ)) •
          ∑ σ : Equiv.Perm (Fin n),
            (permutationRepresentation dR n σ).trace • permutationRepresentation dA n σ := by
  unfold symmetricProjectorPairedTraceR symmetricProjectorPairedGen
  rw [partialTraceB_smul, partialTraceB_finset_sum]
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact partialTraceB_tensor_op (permutationRepresentation dA n σ)
    (permutationRepresentation dR n σ)

/-- **Step 2a.** `Ω` is positive semidefinite: the partial trace of the PSD projector `P_Sym`
(`symmetricProjectorPairedGen_posSemidef`) is PSD (`partialTraceB_posSemidef_mathlib`). -/
theorem symmetricProjectorPairedTraceR_posSemidef (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] :
    (symmetricProjectorPairedTraceR dA dR n).PosSemidef :=
  Quantum.Channels.partialTraceB_posSemidef_mathlib _
    (symmetricProjectorPairedGen_posSemidef dA dR n)

/-- **Step 2b.** `Ω` is Hermitian: the partial trace of the Hermitian projector `P_Sym`
(`symmetricProjectorPairedGen_isHermitian`) is Hermitian (`partialTraceB_hermitian`). -/
theorem symmetricProjectorPairedTraceR_isHermitian (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] :
    (symmetricProjectorPairedTraceR dA dR n).IsHermitian :=
  partialTraceB_hermitian _ (symmetricProjectorPairedGen_isHermitian dA dR n)

/-- **Step 3 (`Sₙ`-centrality).** `Ω` commutes with every `permutationRepresentation dA n π`:
`Tr(U_σ^{dR})` is a class function of `σ` (`permutationRepresentation_trace_conj`), so the
character-weighted sum `Ω` (step 1) commutes with the whole representation
(`permutationRepresentation_trace_weighted_sum_commutes_of_commutes`). -/
theorem symmetricProjectorPairedTraceR_commute (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] (π : Equiv.Perm (Fin n)) :
    Commute (permutationRepresentation dA n π) (symmetricProjectorPairedTraceR dA dR n) := by
  rw [symmetricProjectorPairedTraceR_eq_traceWeightedSum]
  have hsum : (∑ σ : Equiv.Perm (Fin n), (permutationRepresentation dR n σ).trace •
        (permutationRepresentation dA n π * permutationRepresentation dA n σ))
      = ∑ τ : Equiv.Perm (Fin n), (permutationRepresentation dR n τ).trace •
        (permutationRepresentation dA n τ * permutationRepresentation dA n π) := by
    apply Fintype.sum_bijective (fun σ => π * σ * π⁻¹) (mul_conj_bijective π)
    intro σ
    rw [permutationRepresentation_trace_conj dR n π σ, permutationRepresentation_mul,
      permutationRepresentation_mul]
    congr 2
    group
  unfold Commute SemiconjBy
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul] at hsum ⊢
  rw [hsum]

/-! ## Step 4 (`E4`): `Ω` is invertible when `dA ≤ dR`

The combinatorial witness route (avoiding Schur–Weyl duality / isotypic dimensions): the
maximally entangled paired vector `|θ⟩^{⊗n}` (`maxEntangledProjectorPaired`'s defining ket) is
itself **symmetric** (fixed by every `U_σ^{dA} ⊗ U_σ^{dR}`, since it is a diagonal tensor power),
hence lies in `P_Sym`'s range; `P_Sym` therefore dominates the (normalized) rank-one projector
onto it, and tracing out `R` turns this domination into `Ω ⪰ (1/dA^n) • 1`, which is enough for
`Ω.PosDef` without ever touching the isotypic/Weyl-dimension machinery. -/

/-- The defining vector of `maxEntangledProjectorPaired`, bundled as a `Ket`: `|θ⟩^{⊗n}` in the
blocked convention. Bundling it separately exposes `maxEntangledProjectorPaired` as the rank-one
ket-bra `ψ * ψ.dag` (`maxEntangledProjectorPaired_eq_ketbra`), which is what makes the `Ω`-layer
positivity witness below elementary. -/
def maxEntangledKetPaired (dA dR n : ℕ) (hdim : dA ≤ dR) : Ket (dA ^ n * dR ^ n) :=
  ⟨fun i =>
    let emb : Fin (dA ^ n) → Fin (dR ^ n) := fun a =>
      finFunctionFinEquiv (fun j => Fin.castLE hdim (finFunctionFinEquiv.symm a j))
    if (finProdFinEquiv.symm i).2 = emb (finProdFinEquiv.symm i).1 then 1 else 0⟩

/-- `Θₙ = |θ⟩^{⊗n}⟨θ|^{⊗n}` is the rank-one ket-bra of `maxEntangledKetPaired`. -/
theorem maxEntangledProjectorPaired_eq_ketbra (dA dR n : ℕ) (hdim : dA ≤ dR) :
    maxEntangledProjectorPaired dA dR n hdim =
      maxEntangledKetPaired dA dR n hdim * (maxEntangledKetPaired dA dR n hdim).dag := by
  unfold maxEntangledProjectorPaired maxEntangledKetPaired
  ext i j
  simp [ket_mul_bra_apply, Ket.dag_vec]

/-- `Θₙ` is positive semidefinite (a rank-one ket-bra projector). -/
theorem maxEntangledProjectorPaired_posSemidef (dA dR n : ℕ) (hdim : dA ≤ dR) :
    (maxEntangledProjectorPaired dA dR n hdim).PosSemidef := by
  rw [maxEntangledProjectorPaired_eq_ketbra]
  exact ketbra_posSemidef _

/-- `Θₙ` is Hermitian (a rank-one ket-bra projector). -/
theorem maxEntangledProjectorPaired_isHermitian (dA dR n : ℕ) (hdim : dA ≤ dR) :
    (maxEntangledProjectorPaired dA dR n hdim).IsHermitian := by
  rw [maxEntangledProjectorPaired_eq_ketbra]
  exact ketbra_hermitian _

/-- `|θ⟩^{⊗n}` is fixed by every single paired permutation operator `U_σ^{dA} ⊗ U_σ^{dR}`
(it is a "diagonal" tensor power, hence trivially symmetric under simultaneously permuting the
`n` factors). -/
theorem maxEntangledKetPaired_perm_fixed (dA dR n : ℕ) [NeZero dA] [NeZero dR] [NeZero n]
    (hdim : dA ≤ dR) (σ : Equiv.Perm (Fin n)) :
    Op.tensor (permutationRepresentation dA n σ) (permutationRepresentation dR n σ) *
        maxEntangledKetPaired dA dR n hdim
      = maxEntangledKetPaired dA dR n hdim := by
  ext i
  rw [op_mul_ket_vec]
  unfold Matrix.mulVec dotProduct
  simp only [Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, maxEntangledKetPaired, permutationRepresentation,
    Matrix.of_apply]
  have hshift : ∀ {d : ℕ} (u v : Fin (d ^ n)),
      (finFunctionFinEquiv.symm u = finFunctionFinEquiv.symm v ∘ ⇑σ.symm) ↔
        v = finFunctionFinEquiv (finFunctionFinEquiv.symm u ∘ ⇑σ) := by
    intro d u v
    rw [eq_comp_perm_symm_iff_comp_perm_eq, ← Equiv.apply_eq_iff_eq finFunctionFinEquiv,
      Equiv.apply_symm_apply]
    exact eq_comm
  have hcancel : ∀ {d : ℕ} (f g : Fin n → Fin d), f ∘ ⇑σ = g ∘ ⇑σ ↔ f = g := by
    intro d f g
    constructor
    · intro h
      funext x
      have := congrFun h (σ.symm x)
      simpa using this
    · intro h; rw [h]
  simp only [hshift]
  set F1 := finFunctionFinEquiv.symm (finProdFinEquiv.symm i).1 with hF1
  set F2 := finFunctionFinEquiv.symm (finProdFinEquiv.symm i).2 with hF2
  set castLEfn : (Fin n → Fin dA) → Fin n → Fin dR :=
    fun f j => Fin.castLE hdim (f j) with hcastLEfn
  set a0 := finFunctionFinEquiv (F1 ∘ ⇑σ) with ha0
  set r0 := finFunctionFinEquiv (F2 ∘ ⇑σ) with hr0
  rw [Finset.sum_eq_single (a0, r0)]
  · simp only [ite_true, one_mul]
    have hiff :
        r0 = finFunctionFinEquiv (castLEfn F1 ∘ ⇑σ)
          ↔ (finProdFinEquiv.symm i).2 = finFunctionFinEquiv (castLEfn F1) := by
      rw [hr0]
      constructor
      · intro h
        have h2 : F2 ∘ ⇑σ = castLEfn F1 ∘ ⇑σ :=
          finFunctionFinEquiv.injective h
        have h3 : F2 = castLEfn F1 := (hcancel F2 (castLEfn F1)).mp h2
        rw [← h3, hF2, Equiv.apply_symm_apply]
      · intro h
        have h3 : F2 = castLEfn F1 := by
          have h' : finFunctionFinEquiv F2 = finFunctionFinEquiv (castLEfn F1) := by
            rw [hF2, Equiv.apply_symm_apply]; exact h
          exact finFunctionFinEquiv.injective h'
        rw [h3]
    have hgoal_eq : (fun j => Fin.castLE hdim (F1 j)) = castLEfn F1 := rfl
    rw [show (fun j => Fin.castLE hdim (finFunctionFinEquiv.symm a0 j))
          = castLEfn F1 ∘ ⇑σ from by rw [ha0, Equiv.symm_apply_apply]; rfl]
    by_cases h : r0 = finFunctionFinEquiv (castLEfn F1 ∘ ⇑σ)
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun hc => h (hiff.mpr hc))]
  · intro b _ hb
    rcases (Prod.ext_iff.not.mp hb) with hne
    by_cases h1 : b.1 = a0
    · by_cases h2 : b.2 = r0
      · exact absurd (Prod.ext h1 h2) hb
      · simp [h2]
    · simp [h1]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `P_Sym` fixes `|θ⟩^{⊗n}`: averaging `maxEntangledKetPaired_perm_fixed` over all `n!`
permutations. -/
theorem symmetricProjectorPairedGen_mul_maxEntangledKetPaired (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    symmetricProjectorPairedGen dA dR n * maxEntangledKetPaired dA dR n hdim
      = maxEntangledKetPaired dA dR n hdim := by
  ext i
  rw [op_mul_ket_vec]
  unfold symmetricProjectorPairedGen
  rw [Matrix.smul_mulVec]
  have hsum : (∑ σ : Equiv.Perm (Fin n),
        Op.tensor (permutationRepresentation dA n σ) (permutationRepresentation dR n σ))
        *ᵥ (maxEntangledKetPaired dA dR n hdim).vec
      = ∑ σ : Equiv.Perm (Fin n),
        (Op.tensor (permutationRepresentation dA n σ) (permutationRepresentation dR n σ)
          *ᵥ (maxEntangledKetPaired dA dR n hdim).vec) := by
    funext j
    unfold Matrix.mulVec dotProduct
    simp only [Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hsum]
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (Op.tensor (permutationRepresentation dA n σ) (permutationRepresentation dR n σ)
        *ᵥ (maxEntangledKetPaired dA dR n hdim).vec)
      = (maxEntangledKetPaired dA dR n hdim).vec := by
    intro σ
    have h2 := congrArg Ket.vec (maxEntangledKetPaired_perm_fixed dA dR n hdim σ)
    simpa [op_mul_ket_vec] using h2
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hn : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [show (1 / (Nat.factorial n : ℂ)) * (Nat.factorial n : ℂ) = 1 by field_simp]
  simp

/-- `P_Sym` fixes `Θₙ` under the sandwich `P_Sym · Θₙ · P_Sym = Θₙ` (i.e. `Θₙ` is supported in
`P_Sym`'s range): the ket-bra version of `symmetricProjectorPairedGen_mul_maxEntangledKetPaired`,
using that `P_Sym` is Hermitian to move it across the dagger. -/
theorem symmetricProjectorPairedGen_mul_maxEntangledProjectorPaired_mul_self (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    symmetricProjectorPairedGen dA dR n * maxEntangledProjectorPaired dA dR n hdim
        * symmetricProjectorPairedGen dA dR n
      = maxEntangledProjectorPaired dA dR n hdim := by
  rw [maxEntangledProjectorPaired_eq_ketbra, op_mul_ketbra,
    symmetricProjectorPairedGen_mul_maxEntangledKetPaired, ketbra_mul_op,
    ← Ket.dag_op_mul_of_isHermitian _ (symmetricProjectorPairedGen_isHermitian dA dR n),
    symmetricProjectorPairedGen_mul_maxEntangledKetPaired]

/-- **`Tr_R(Θₙ) = 1`.** Tracing `Θₙ = |θ⟩^{⊗n}⟨θ|^{⊗n}` out over `R` gives the identity on `Aⁿ`:
the surviving diagonal terms are exactly the `(a,a)` entries, since `r ↦ (a,r)` supported on
`Θₙ` (i.e. `r = emb a`) is a bijection onto its image (`emb` injective). -/
theorem maxEntangledProjectorPaired_partialTraceB_eq_one (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    Quantum.TensorProducts.partialTraceB (maxEntangledProjectorPaired dA dR n hdim)
      = (1 : Op (dA ^ n)) := by
  have hemb_inj : Function.Injective (fun a : Fin (dA ^ n) =>
      finFunctionFinEquiv (fun jj => Fin.castLE hdim (finFunctionFinEquiv.symm a jj))) := by
    intro a b hab
    have h1 := finFunctionFinEquiv.injective hab
    apply finFunctionFinEquiv.symm.injective
    funext jj
    exact Fin.castLE_injective hdim (congrFun h1 jj)
  unfold Quantum.TensorProducts.partialTraceB maxEntangledProjectorPaired
  ext i j
  simp only [Matrix.of_apply, Matrix.one_apply]
  have hstep : ∀ k : Fin (dR ^ n),
      ((if (finProdFinEquiv.symm (finProdFinEquiv (i, k))).2 =
            finFunctionFinEquiv (fun jj => Fin.castLE hdim
              (finFunctionFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv (i, k))).1 jj))
          then (1 : ℂ) else 0) *
        (starRingEnd ℂ) (if (finProdFinEquiv.symm (finProdFinEquiv (j, k))).2 =
            finFunctionFinEquiv (fun jj => Fin.castLE hdim
              (finFunctionFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv (j, k))).1 jj))
          then (1 : ℂ) else 0))
      = (if k = finFunctionFinEquiv (fun jj => Fin.castLE hdim (finFunctionFinEquiv.symm i jj))
          then (1 : ℂ) else 0) *
        (if k = finFunctionFinEquiv (fun jj => Fin.castLE hdim (finFunctionFinEquiv.symm j jj))
          then (1 : ℂ) else 0) := by
    intro k
    simp only [Equiv.symm_apply_apply]
    split_ifs <;> simp
  simp only [hstep]
  set A := finFunctionFinEquiv (fun jj => Fin.castLE hdim (finFunctionFinEquiv.symm i jj))
  set B := finFunctionFinEquiv (fun jj => Fin.castLE hdim (finFunctionFinEquiv.symm j jj))
  have : (∑ k : Fin (dR ^ n), (if k = A then (1 : ℂ) else 0) * (if k = B then (1 : ℂ) else 0))
      = if A = B then (1 : ℂ) else 0 := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [this]
  by_cases h : i = j
  · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (hemb_inj hc))]

/-- **`E4`: `Ω` is invertible when `dA ≤ dR`.** The combinatorial witness route: `Θₙ/dA^n`
(the normalized maximally-entangled paired projector) is a subnormalized PSD operator supported
in `P_Sym`'s range (`symmetricProjectorPairedGen_mul_maxEntangledProjectorPaired_mul_self`), so
`P_Sym` dominates it (`symmetricProjectorPairedGen_sub_psd_of_support`); tracing out `R` turns
this into `Ω ⪰ (1/dA^n) • 1` (`maxEntangledProjectorPaired_partialTraceB_eq_one`), which forces
`Ω.PosDef`. No isotypic/Weyl-dimension machinery is used. -/
theorem symmetricProjectorPairedTraceR_posDef (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    (symmetricProjectorPairedTraceR dA dR n).PosDef := by
  have hdA_ne : (dA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne dA)
  have hdApow_ne : (dA ^ n : ℂ) ≠ 0 := pow_ne_zero n hdA_ne
  set c : ℂ := 1 / (dA ^ n : ℂ) with hc
  have hdA_pos : (0 : ℂ) < (dA : ℂ) := by
    have : (0 : ℕ) < dA := Nat.pos_of_neZero dA
    exact_mod_cast this
  have hdApow_pos : (0 : ℂ) < (dA ^ n : ℂ) := pow_pos hdA_pos n
  have hc_pos : (0 : ℂ) < c := by
    rw [hc]
    exact one_div_pos.mpr hdApow_pos
  set ρ' := c • maxEntangledProjectorPaired dA dR n hdim with hρ'
  have hρ'_psd : ρ'.PosSemidef :=
    (maxEntangledProjectorPaired_posSemidef dA dR n hdim).smul hc_pos.le
  have htrace : (maxEntangledProjectorPaired dA dR n hdim).trace = (dA ^ n : ℂ) := by
    rw [← trace_partialTraceB, maxEntangledProjectorPaired_partialTraceB_eq_one]
    simp
  have hρ'_trace : ρ'.trace.re ≤ 1 := by
    rw [hρ', Matrix.trace_smul, htrace, hc, smul_eq_mul, one_div_mul_cancel hdApow_ne]
    simp
  have hρ'_support :
      symmetricProjectorPairedGen dA dR n * ρ' * symmetricProjectorPairedGen dA dR n = ρ' := by
    rw [hρ', Matrix.mul_smul, Matrix.smul_mul,
      symmetricProjectorPairedGen_mul_maxEntangledProjectorPaired_mul_self]
  have hsub := symmetricProjectorPairedGen_sub_psd_of_support dA dR n ρ' hρ'_psd hρ'_trace
    hρ'_support
  have hmono := Quantum.Channels.partialTraceB_posSemidef_mathlib _ hsub
  rw [Quantum.TensorProducts.partialTraceB_sub] at hmono
  have hTrRρ' : Quantum.TensorProducts.partialTraceB ρ' = c • (1 : Op (dA ^ n)) := by
    rw [hρ', Quantum.TensorProducts.partialTraceB_smul,
      maxEntangledProjectorPaired_partialTraceB_eq_one]
  rw [hTrRρ'] at hmono
  have hone_pd : (c • (1 : Op (dA ^ n))).PosDef := Matrix.PosDef.one.smul hc_pos
  have hsum := hone_pd.add_posSemidef hmono
  simpa [symmetricProjectorPairedTraceR] using hsum

end InfoTheory.Postselection

end
