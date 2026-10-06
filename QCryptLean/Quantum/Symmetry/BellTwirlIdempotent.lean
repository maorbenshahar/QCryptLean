import QCryptLean.Quantum.Symmetry.TwirlPermCommute
import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination
import QCryptLean.Quantum.Symmetry.StratifiedDeFinettiDomination

/-!
# The IID Bell twirl, and Bell de Finetti marginal domination

The idempotency of the IID bilateral-Pauli (Bell) twirl, and the Bell de Finetti marginal
domination bound this yields. This is protocol-independent (no BB84 or QKD-protocol object):
the Klein-four (`ℤ₂×ℤ₂`) group structure of the bilateral-Pauli twirl group, and the subnormalized
domination it feeds.

## Main results

* `bellTwirl_perm_conj` — the IID Bell twirl channel commutes with round-permutation
  conjugation.
* `bellTwirl_idempotent`, `bellTwirl_isIIDBellDiagonal` — the Bell twirl is idempotent
  (the group average over the abelian bilateral-Pauli group `(ℤ₂×ℤ₂)ⁿ`), hence its output is
  joint-Bell-diagonal.
* `bellSym_subnormalized_marginal_dominated` — the subnormalized Bell de Finetti marginal
  domination (Nahar et al. Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry): for any subnormalized,
  permutation-invariant, jointly-Bell-diagonal PSD `Y`, `C(n+3,3) · τ_Bell − Y ⪰ 0`.

## References

Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B, Thm 3, Lemma 2 (`x = 4`,
joint Bell `ℤ₂×ℤ₂` symmetry); Christandl–König–Renner (2009), `arXiv:0809.3019`, Thm 1, §III;
Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics Math.RepresentationTheory InfoTheory.SmoothMinEntropy Quantum.Gates
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Symmetry

/-- **The IID Bell twirl channel commutes with round-permutation conjugation.**

`bellTwirl n (U_π · M · U_π†) = U_π · (bellTwirl n M) · U_π†` with `U_π =
permutationRepresentation 4 n π`.  Each per-string conjugate transports through the permutation by
`bellTwirlUnitary_perm_conj`, and the string sum reindexes by the precomposition bijection `g
↦ g ∘ π`.  This is the structural fact that lets a perm symmetrization survive a Bell
symmetrization: the twirl of a permutation-invariant marginal stays permutation-invariant. -/
theorem bellTwirl_perm_conj (n : ℕ) (σ : Equiv.Perm (Fin n)) (M : Op (4 ^ n)) :
    bb84BellTwirl n
        (permutationRepresentation 4 n σ * M * (permutationRepresentation 4 n σ)ᴴ) =
      permutationRepresentation 4 n σ * bb84BellTwirl n M *
        (permutationRepresentation 4 n σ)ᴴ := by
  set U := permutationRepresentation 4 n σ with hU
  -- `U · U_g = U_{g∘σ} · U` (rearranged `bellTwirlUnitary_perm_conj`).
  have hslide : ∀ g : Fin n → Fin 4,
      bellTwirlUnitary n g * U = U * bellTwirlUnitary n (g ∘ ⇑σ) := by
    intro g
    have h := bellTwirlUnitary_perm_conj n σ (g ∘ ⇑σ)
    have hcomp : (g ∘ ⇑σ) ∘ ⇑σ⁻¹ = g := by
      funext a
      simp only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    rw [hcomp] at h
    -- h : U * U_{g∘σ} * U† = U_g
    have hUU : Uᴴ * U = 1 := (permutationRepresentation_unitary 4 n σ).1
    calc bellTwirlUnitary n g * U
           = (U * bellTwirlUnitary n (g ∘ ⇑σ) * Uᴴ) * U := by rw [h]
      _ = U * bellTwirlUnitary n (g ∘ ⇑σ) := by
          rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
  unfold bb84BellTwirl
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul]
  -- reindex `g ↦ g ∘ σ`
  rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin 4)))
      (fun g => U * (bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ) * Uᴴ)]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have hg : (Equiv.arrowCongr σ.symm (Equiv.refl (Fin 4))) g = g ∘ ⇑σ := by
    funext a
    simp [Equiv.arrowCongr_apply, Equiv.symm_symm]
  rw [hg]
  -- LHS term: U_g (U M U†) U_g†  ;  RHS term: U (U_{g∘σ} M U_{g∘σ}†) U†
  have hUg : bellTwirlUnitary n g * U = U * bellTwirlUnitary n (g ∘ ⇑σ) := hslide g
  have hUgH : Uᴴ * (bellTwirlUnitary n g)ᴴ = (bellTwirlUnitary n (g ∘ ⇑σ))ᴴ * Uᴴ := by
    have := congrArg Matrix.conjTranspose hUg
    simpa only [Matrix.conjTranspose_mul] using this
  calc bellTwirlUnitary n g * (U * M * Uᴴ) * (bellTwirlUnitary n g)ᴴ
         = (bellTwirlUnitary n g * U) * M * (Uᴴ * (bellTwirlUnitary n g)ᴴ) := by
        noncomm_ring
    _ = (U * bellTwirlUnitary n (g ∘ ⇑σ)) * M * ((bellTwirlUnitary n (g ∘ ⇑σ))ᴴ * Uᴴ) := by
        rw [hUg, hUgH]
    _ = U * (bellTwirlUnitary n (g ∘ ⇑σ) * M * (bellTwirlUnitary n (g ∘ ⇑σ))ᴴ) * Uᴴ := by
        noncomm_ring

/-! ### The Klein-four group structure of the bilateral-Pauli (Bell) twirl group

Idempotency of the twirl is the projection property of the group average over the abelian
bilateral-Pauli group `(ℤ₂×ℤ₂)ⁿ`. The single-pair group `{I⊗I, X⊗X, Y⊗Y, Z⊗Z}` is the diagonal
of the single-qubit Pauli group, so its multiplication is the Klein-four product `kleinFourAdd`
with a `±1` cocycle `bellSignCocycle` that cancels under conjugation. -/

/-- **The four single-qubit operators `[I, X, Y, Z]`** whose diagonal tensors are the Bell group. -/
def bellPauliOps : Fin 4 → Op 2 := ![1, pauliX, pauliY, pauliZ]

/-- **The Klein-four (`ℤ₂×ℤ₂`) addition table on `Fin 4`** (the index XOR). -/
def kleinFourAdd : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

/-- **The single-qubit Pauli cocycle** `ω(a,b) ∈ {1, i, -i}` with `P a · P b = ω(a,b) · P(a⊕b)`. -/
def bellPauliCocycle : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, Complex.I, -Complex.I], ![1, -Complex.I, 1, Complex.I],
    ![1, Complex.I, -Complex.I, 1]]

/-- **The bilateral-Pauli `±1` cocycle** `ω²` with `G a · G b = bellSignCocycle(a,b) · G(a⊕b)`. -/
def bellSignCocycle (a b : Fin 4) : ℂ := bellPauliCocycle a b * bellPauliCocycle a b

/-- The four single-qubit operators `[I, X, Y, Z]` as explicit `2×2` arrays. -/
private theorem bellPauliOps_eq_matrix : bellPauliOps =
    ![!![1, 0; 0, 1], !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]] := by
  rw [bellPauliOps, Matrix.one_fin_two, pauliX_eq_matrix, pauliY_eq_matrix, pauliZ_eq_matrix]

/-- Single-qubit Pauli multiplication: `P a · P b = ω(a,b) · P(a⊕b)`. -/
private theorem Pq_mul (a b : Fin 4) :
    bellPauliOps a * bellPauliOps b = bellPauliCocycle a b • bellPauliOps (kleinFourAdd a b) := by
  -- In each of the sixteen cases both sides are explicit `2×2` arrays: the left one a product
  -- (`mul_fin_two`), the right one a scalar multiple (`smul_of`); normalizing the entries (with
  -- `I * I = -1`) makes them equal.
  rw [bellPauliOps_eq_matrix]
  fin_cases a <;> fin_cases b <;>
    simp only [kleinFourAdd, bellPauliCocycle, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.mul_fin_two, Matrix.smul_of, Matrix.smul_vec2] <;>
    norm_num

/-- Each Bell group operator is the diagonal tensor `G a = P a ⊗ P a`. -/
private theorem bb84BellSinglePairTwirlGroup_eq_tensor (a : Fin 4) :
    bb84BellSinglePairTwirlGroup a = Op.tensor (bellPauliOps a) (bellPauliOps a) := by
  fin_cases a <;> simp [bellPauliOps, bb84BellSinglePairTwirlGroup, Op.tensor_one]

/-- A nonneg-scalar tensor identity `(c•A) ⊗ (c•B) = (c·c) • (A ⊗ B)`. -/
private lemma Op_tensor_smul_both {p q : ℕ} (c : ℂ) (A : Op p) (B : Op q) :
    Op.tensor (c • A) (c • B) = (c * c) • Op.tensor A B := by
  ext i j
  simp [Op.tensor, Matrix.smul_apply, Matrix.kroneckerMap, mul_mul_mul_comm]

/-- **Bell group multiplication law**: `G a · G b = bellSignCocycle(a,b) · G(a⊕b)` with
`bellSignCocycle ∈ {±1}`. -/
private theorem bellGroup_mul (a b : Fin 4) :
    bb84BellSinglePairTwirlGroup a * bb84BellSinglePairTwirlGroup b =
      bellSignCocycle a b • bb84BellSinglePairTwirlGroup (kleinFourAdd a b) := by
  rw [bb84BellSinglePairTwirlGroup_eq_tensor a, bb84BellSinglePairTwirlGroup_eq_tensor b,
    Op.tensor_mul, Pq_mul, bb84BellSinglePairTwirlGroup_eq_tensor (kleinFourAdd a b),
    Op_tensor_smul_both]
  rfl

/-- The Bell cocycle `bellSignCocycle` is a unit:
`bellSignCocycle(a,b) · conj(bellSignCocycle(a,b)) = 1`. -/
private theorem bellPh_unit (a b : Fin 4) :
    bellSignCocycle a b * (starRingEnd ℂ) (bellSignCocycle a b) = 1 := by
  fin_cases a <;> fin_cases b <;> simp [bellSignCocycle, bellPauliCocycle]

/-- `kleinFourAdd x ·` is an involution (`ℤ₂×ℤ₂` translation). -/
private theorem kleinAdd_klein (x y : Fin 4) : kleinFourAdd x (kleinFourAdd x y) = y := by
  fin_cases x <;> fin_cases y <;> rfl

/-- **The `n`-fold twirl-unitary product law**: `U_h · U_g = (∏ₐ bellSignCocycle) · U_{h⊕g}`. -/
private theorem bellTwirlUnitary_mul (n : ℕ) (h g : Fin n → Fin 4) :
    bellTwirlUnitary n h * bellTwirlUnitary n g =
      (∏ a : Fin n, bellSignCocycle (h a) (g a)) •
        bellTwirlUnitary n (fun a => kleinFourAdd (h a) (g a)) := by
  unfold bellTwirlUnitary
  rw [tensorFamily_mul]
  have hfam :
      (fun a => bb84BellSinglePairTwirlGroup (h a) * bb84BellSinglePairTwirlGroup (g a)) =
        (fun a => bellSignCocycle (h a) (g a) •
          bb84BellSinglePairTwirlGroup (kleinFourAdd (h a) (g a))) := by
    funext a; exact bellGroup_mul (h a) (g a)
  rw [hfam, tensorFamily_smul]

/-- Conjugating a `U_g`-conjugate by `U_h` is a `U_{h⊕g}`-conjugate (the `±1` phase cancels). -/
private theorem bellTwirlUnitary_conj_conj (n : ℕ) (h g : Fin n → Fin 4) (M : Op (4 ^ n)) :
    bellTwirlUnitary n h * (bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ) *
        (bellTwirlUnitary n h)ᴴ =
      bellTwirlUnitary n (fun a => kleinFourAdd (h a) (g a)) * M *
        (bellTwirlUnitary n (fun a => kleinFourAdd (h a) (g a)))ᴴ := by
  set s : ℂ := ∏ a : Fin n, bellSignCocycle (h a) (g a) with hs
  set k := (fun a => kleinFourAdd (h a) (g a)) with hk
  have hmul : bellTwirlUnitary n h * bellTwirlUnitary n g = s • bellTwirlUnitary n k :=
    bellTwirlUnitary_mul n h g
  have hsunit : s * (starRingEnd ℂ) s = 1 := by
    rw [hs, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun a _ => bellPh_unit (h a) (g a))
  calc bellTwirlUnitary n h * (bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ) *
          (bellTwirlUnitary n h)ᴴ
         = (bellTwirlUnitary n h * bellTwirlUnitary n g) * M *
          (bellTwirlUnitary n h * bellTwirlUnitary n g)ᴴ := by
        rw [Matrix.conjTranspose_mul]; noncomm_ring
    _ = (s • bellTwirlUnitary n k) * M * (s • bellTwirlUnitary n k)ᴴ := by rw [hmul]
    _ = ((starRingEnd ℂ) s * s) • (bellTwirlUnitary n k * M * (bellTwirlUnitary n k)ᴴ) := by
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        rfl
    _ = bellTwirlUnitary n k * M * (bellTwirlUnitary n k)ᴴ := by
        rw [show (starRingEnd ℂ) s * s = 1 by rw [mul_comm]; exact hsunit, one_smul]

/-- The involutive reindex `g ↦ (a ↦ (h a) ⊕ (g a))` on twirl strings. -/
private def kleinAddPerm (n : ℕ) (h : Fin n → Fin 4) : Equiv.Perm (Fin n → Fin 4) :=
  Function.Involutive.toPerm (fun g => fun a => kleinFourAdd (h a) (g a))
    (fun g => by funext a; exact kleinAdd_klein (h a) (g a))

/-- **The twirl output is invariant under conjugation by any twirl unitary** `U_h`. -/
private theorem bb84BellTwirl_unitary_invariant (n : ℕ) (h : Fin n → Fin 4) (M : Op (4 ^ n)) :
    bellTwirlUnitary n h * bb84BellTwirl n M * (bellTwirlUnitary n h)ᴴ = bb84BellTwirl n M := by
  unfold bb84BellTwirl
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul,
    ← Equiv.sum_comp (kleinAddPerm n h)
      (fun g => bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ)]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [bellTwirlUnitary_conj_conj n h g M]
  rfl

/-- **The IID Bell twirl is idempotent** — its output is a fixed point (joint-Bell-diagonal).

`bellTwirl n (bellTwirl n M) = bellTwirl n M`: the twirl is the group average over the
abelian bilateral-Pauli (Bell) group `(ℤ₂×ℤ₂)ⁿ`, hence the orthogonal projection onto its commutant
(the joint-Bell-diagonal operators), which is idempotent.  Equivalently (
`iidBellDiagonal_iff_bellBasis_diagonal`) the twirl dephases in the joint Bell basis, so a second
twirl acts as the identity on the already-diagonal output.

The proof is the Klein-four group-projection identity: for each string `h`, `U_h · U_g =
bellSignCocycle(h,g) · U_{h⊕g}` with `bellSignCocycle ∈ {±1}` the bilateral-Pauli cocycle and `⊕`
the pointwise `ℤ₂×ℤ₂` addition; the `±1` phase cancels in the conjugation `U M U†`
(`bb84BellTwirl_unitary_invariant`), and `g ↦ h⊕g` is a bijection, so the second average
collapses. -/
theorem bellTwirl_idempotent (n : ℕ) (M : Op (4 ^ n)) :
    bb84BellTwirl n (bb84BellTwirl n M) = bb84BellTwirl n M := by
  conv_lhs => rw [bb84BellTwirl]
  rw [Finset.sum_congr rfl (fun h _ => bb84BellTwirl_unitary_invariant n h M),
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    show ((4 : ℂ) ^ n)⁻¹ * ((4 ^ n : ℕ) : ℂ) = 1 by
      push_cast; rw [inv_mul_cancel₀ (pow_ne_zero n (by norm_num))],
    one_smul]

/-- The IID Bell twirl output is `IsIIDBellDiagonal` (immediate from idempotency). -/
theorem bellTwirl_isIIDBellDiagonal (n : ℕ) (M : Op (4 ^ n)) :
    IsIIDBellDiagonal (bb84BellTwirl n M) :=
  bellTwirl_idempotent n M

/-! ## The Bell de Finetti marginal domination (subnormalized) -/

/-- `(bb84BellDeFinettiState n).toOp` is positive semidefinite. -/
private theorem bb84BellDeFinettiState_posSemidef (n : ℕ) [NeZero n] :
    (bb84BellDeFinettiState n).toOp.PosSemidef := by
  rw [bb84BellDeFinettiState_toOp]
  exact bb84BellTwirl_posSemidef n (symmetricProjector_four_smul_posSemidef n)

/-- **The Bell de Finetti marginal domination, subnormalized form**
    (Nahar et al. Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry).

For any PSD `Y` on `(ℂ⁴)^{⊗n}` that is permutation-invariant, jointly-Bell-diagonal, and
subnormalized (`Tr Y ≤ 1`), the Bell de Finetti reference dominates `Y`:
`C(n+3,3) · τ_Bell − Y ⪰ 0`.

This wraps the trace-`1` domination `bb84_bellSym_deFinetti_domination`: the normalized state
`(1/Tr Y) · Y` is a perm-invariant Bell-diagonal density, so `(1/Tr Y) · Y ⪯ C(n+3,3) · τ_Bell`, and
scaling by `Tr Y ≤ 1` against the PSD reference recovers the subnormalized bound (the
`(1−Tr Y) · C(n+3,3) · τ_Bell` slack is PSD). -/
theorem bellSym_subnormalized_marginal_dominated (n : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Ymarg : Op (4 ^ n)) (hY_psd : Ymarg.PosSemidef) (hY_trace : Ymarg.trace.re ≤ 1)
    (hY_perm : ∀ σ : Equiv.Perm (Fin n),
      permutationRepresentation 4 n σ * Ymarg = Ymarg * permutationRepresentation 4 n σ)
    (hY_bell : IsIIDBellDiagonal Ymarg) :
    ((Nat.choose (n + 3) 3 : ℂ) • (bb84BellDeFinettiState n).toOp - Ymarg).PosSemidef := by
  set C : ℂ := (Nat.choose (n + 3) 3 : ℂ) with hC
  set S : Op (4 ^ n) := (bb84BellDeFinettiState n).toOp with hS
  have hS_psd : S.PosSemidef := bb84BellDeFinettiState_posSemidef n
  have hCS_psd : (C • S).PosSemidef := hS_psd.smul (by rw [hC]; exact_mod_cast Nat.cast_nonneg _)
  -- trace real-nonneg facts
  have hY_tr_nonneg : (0 : ℂ) ≤ Ymarg.trace := hY_psd.trace_nonneg
  have hY_re_nn : 0 ≤ Ymarg.trace.re := by
    have h := hY_tr_nonneg; rw [Complex.le_def] at h; simpa using h.1
  have hYim : Ymarg.trace.im = 0 := by
    have h := hY_tr_nonneg; rw [Complex.le_def] at h; simpa using h.2.symm
  by_cases hY0 : Ymarg = 0
  · -- subnormalized trivially: `C·S − 0 = C·S` PSD
    rw [hY0, sub_zero]; exact hCS_psd
  · -- `Ymarg ≠ 0`: positive trace, normalize, dominate, rescale.
    have ht_pos : (0 : ℝ) < Ymarg.trace.re := by
      rcases lt_or_eq_of_le hY_re_nn with h | h
      · exact h
      · exact absurd (hY_psd.trace_eq_zero_iff.mp (Complex.ext h.symm hYim)) hY0
    have ht_ne : Ymarg.trace ≠ 0 := by
      intro h; rw [h] at ht_pos; simp at ht_pos
    set ρn : Op (4 ^ n) := (1 / Ymarg.trace) • Ymarg with hρn
    -- `1/Tr Y` is a nonnegative real scalar
    have hinv_nonneg : (0 : ℂ) ≤ 1 / Ymarg.trace := by
      rw [Complex.le_def]
      refine ⟨?_, ?_⟩
      · simp only [Complex.zero_re, one_div, Complex.inv_re]
        exact div_nonneg ht_pos.le (Complex.normSq_nonneg _)
      · simp only [Complex.zero_im, one_div, Complex.inv_im, hYim]; simp
    -- `ρn` is a perm-invariant, Bell-diagonal density.
    have hρn_psd : ρn.PosSemidef := hY_psd.smul hinv_nonneg
    have hρn_trace : ρn.trace = 1 := by
      rw [hρn, Matrix.trace_smul, smul_eq_mul, one_div, inv_mul_cancel₀ ht_ne]
    have hρn_perm : ∀ σ : Equiv.Perm (Fin n),
        permutationRepresentation 4 n σ * ρn = ρn * permutationRepresentation 4 n σ := by
      intro σ
      rw [hρn, Matrix.mul_smul, Matrix.smul_mul, hY_perm σ]
    have hρn_bell : IsIIDBellDiagonal ρn :=
      Quantum.Symmetry.isIIDBellDiagonal_smul (1 / Ymarg.trace) hY_bell
    -- domination on the normalized state
    have hdom := bb84_bellSym_deFinetti_domination ρn hρn_psd hρn_trace hρn_perm hρn_bell
    rw [Matrix.le_iff] at hdom
    -- `hdom : (C • S - ρn).PosSemidef`,  and `Ymarg = Tr(Y) • ρn`
    have hY_eq : Ymarg = Ymarg.trace • ρn := by
      rw [hρn, smul_smul, mul_one_div, div_self ht_ne, one_smul]
    have ht_nonneg : (0 : ℂ) ≤ Ymarg.trace := hY_tr_nonneg
    have h1mt_nonneg : (0 : ℂ) ≤ 1 - Ymarg.trace := by
      rw [Complex.le_def]
      refine ⟨?_, ?_⟩
      · simp only [Complex.zero_re, Complex.sub_re, Complex.one_re]; linarith
      · simp only [Complex.zero_im, Complex.sub_im, Complex.one_im, hYim]; ring
    -- decompose `C•S − Ymarg = (1−Tr Y)•(C•S) + Tr Y•(C•S − ρn)`
    rw [hY_eq]
    have hsplit : C • S - Ymarg.trace • ρn =
        (1 - Ymarg.trace) • (C • S) + Ymarg.trace • (C • S - ρn) := by
      module
    rw [hsplit]
    exact (hCS_psd.smul h1mt_nonneg).add (hdom.smul ht_nonneg)

end Quantum.Symmetry

end -- noncomputable section
