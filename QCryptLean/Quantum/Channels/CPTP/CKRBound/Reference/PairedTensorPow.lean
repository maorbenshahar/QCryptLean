import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Order

/-!
# CKR paired reference — Löwner domination of the paired IID block at the constant `g`

`Reference/PairedLowner.lean` records the *marginal* (signal-register) CKR/Renner de Finetti
domination `σ^{⊗n} ⪯ g · ckrDeFinettiState d n` on `Op (d ^ n)`
(`ckrDeFinettiState_opGe_inv_choose_smul_tensorPow`), with
`g = C(n + d² − 1, d² − 1) = dim Sym^n(ℂ^{d²})`.

This file supplies the **joint (paired-register)** form on `Op (d ^ n * d ^ n)`, at the **same**
constant `g`: for a **pure** state `ψ` on `ℂ^d ⊗ ℂ^d`, the interleaved `n`-fold power
`densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)` — the `Aⁿ Eⁿ`-register block
consumed by the paired-Haar de Finetti decomposition — satisfies

  `ψ^{⊗n}(interleaved)  ⪯  g · pairedDeFinettiState d n`.

Since `g · pairedDeFinettiState d n = symmetricProjectorPaired d n` exactly
(`pairedDeFinettiState = (1 / tr P) • P` and `tr P = g`), the inequality is the projector
domination `X ⪯ P` of `symmetricProjectorPaired_sub_psd_of_support`, and the only content is that
a pure interleaved IID block is supported on the paired symmetric subspace.

## Scope of the constant

`g` is **exactly** the smallest constant that works, and it is exactly the constant of the
unpaired marginal form: the paired form costs nothing extra. For pure `ψ`,
the smallest admissible constant is `g · λ_max(P X P)`:

| `d` | `n` | `g = C(n+d²−1, d²−1)` | smallest working constant |
|-----|-----|-----------------------|---------------------------|
| 2   | 1   | 4                     | 4.000000000               |
| 2   | 2   | 10                    | 10.000000000              |
| 2   | 3   | 20                    | 20.000000000              |
| 4   | 1   | 16                    | 16.000000000              |
| 4   | 2   | 136                   | 136.000000000             |

(`d = 4` is `signalDim`, where `g = bb84PolyDim n = C(n + 15, 15)`.)

## Purity is required, not a convenience

For **mixed** `ψ` the interleaved power `ψ^{⊗n}` has support outside the paired symmetric subspace
as soon as `n ≥ 2`, so **no** finite constant works: the paired symmetric projector has a kernel and
the domination is false there.  Kernel leakage `tr(Q X Q)` with `Q = 1 − P` and `ψ = I/d²` is
`0.375` at
`d = 2`, `n = 2`, and approximately `0.47` at `d = 4`, `n = 2`.  The `n = 1` case is degenerate (`P
= 1`) and gives no information.
The hypothesis `ψ.IsPure` is therefore load-bearing, and it is exactly the regime of the
paired-Haar per-`σ` family the de Finetti decomposition integrates over.

References: Christandl–König–Renner 2009 (arXiv:0809.3019) `\label{lem:extractpart}`
(main.tex:319–:328); Renner 2005
(arXiv:quant-ph/0512258v2) §5.5 `lem:SymPOVM`; Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(arXiv:2403.11851) Theorem 3, `\label{eq:tausplit}` (main.tex:1356–:1362)/(B17).

## Main statements
- `permRep_mul_tensorPowGen_of_isPure` / `tensorPowGen_mul_permRep_of_isPure`: a pure IID power is
  fixed on either side by the tensor-factor permutation representation.
- `symmetricProjectorPaired_sandwich_pairedTensorPow`: the interleaved pure IID block is supported
  on the paired symmetric subspace.
- `pairedDeFinettiState_opGe_inv_choose_smul_pairedTensorPow`: the paired Löwner domination at `g`.
- `cp_pairedTensorPow_opLe_choose_smul_pairedDeFinettiState`: its completely-positive push-forward,
  the `ψ`-independent-reference form — applying the same CP map to both sides keeps the constant
  at `g`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-! ## A pure IID power is fixed by the permutation representation on both sides -/

/-- **A pure IID power is fixed on the left by every tensor-factor permutation.**

For `ψ` pure on `ℂ^D`, `U_τ · ψ^{⊗n} = ψ^{⊗n}`.  This is strictly stronger than permutation
*invariance* `U_τ ρ U_τ† = ρ` (which holds for every `ρ`, `tensorPow_isPermutationInvariant`) and
is what places `ψ^{⊗n}` inside — not merely commuting with — the symmetric subspace: writing
`ψ_{ab} = v_a \overline{v_b}`, precomposing the row multi-index with `τ` permutes the factors of
`∏ₖ v_{f(k)}` and leaves the product unchanged. -/
lemma permRep_mul_tensorPowGen_of_isPure {D n : ℕ} [NeZero D] [NeZero (D ^ n)]
    (ψ : DensityOp D) (hψ : ψ.IsPure) (τ : Equiv.Perm (Fin n)) :
    permutationRepresentation D n τ * (ψ.tensorPowGen n).toOp = (ψ.tensorPowGen n).toOp := by
  set e := @finFunctionFinEquiv D n with he
  set M := (ψ.tensorPowGen n).toOp with hM
  set v := ψ.pureKetOf hψ with hv
  -- Entrywise: the row multi-index may be permuted freely inside a pure IID power.
  have key : ∀ f g : Fin n → Fin D, M (e (f ∘ ⇑τ)) (e g) = M (e f) (e g) := by
    intro f g
    rw [hM, tensorPowGen_toOp_eq_prod ψ (f ∘ ⇑τ) g, tensorPowGen_toOp_eq_prod ψ f g]
    have hent : ∀ a b : Fin D, ψ.toOp a b = v.vec a * star (v.vec b) := by
      intro a b; simpa [hv] using ψ.pureKetOf_entry hψ a b
    simp only [hent, Function.comp_apply, Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_equiv (τ : Fin n ≃ Fin n) (by simp) (by intro k _; simp)
  ext i j
  set i' := e (e.symm i ∘ ⇑τ) with hi'_def
  have hi'_inv : e.symm i = e.symm i' ∘ ⇑τ.symm := by
    rw [hi'_def, Equiv.symm_apply_apply]; funext x; simp
  -- The permutation matrix collapses the row sum to the single index `i'`.
  have hUM : (permutationRepresentation D n τ * M) i j = M i' j := by
    simp only [Matrix.mul_apply, permutationRepresentation, Matrix.of_apply]
    rw [Finset.sum_eq_single i']
    · rw [if_pos hi'_inv, one_mul]
    · intro k _ hk
      rw [if_neg fun h => hk (e.symm.injective (by
        rw [hi'_inv] at h
        exact funext fun x => by
          have hx := congr_fun h (τ x); simp only [Function.comp_apply] at hx
          simpa using hx.symm))]
      ring
    · intro h; exact absurd (Finset.mem_univ i') h
  rw [hUM, hi'_def]
  calc M (e (e.symm i ∘ ⇑τ)) j
      = M (e (e.symm i ∘ ⇑τ)) (e (e.symm j)) := by rw [e.apply_symm_apply]
    _ = M (e (e.symm i)) (e (e.symm j)) := key _ _
    _ = M i j := by rw [e.apply_symm_apply, e.apply_symm_apply]

/-- **A pure IID power is fixed on the right by every tensor-factor permutation.**

The conjugate-transpose of `permRep_mul_tensorPowGen_of_isPure` at `τ⁻¹`, using
`U_{τ⁻¹} = U_τ†` and hermiticity of a density operator. -/
lemma tensorPowGen_mul_permRep_of_isPure {D n : ℕ} [NeZero D] [NeZero (D ^ n)]
    (ψ : DensityOp D) (hψ : ψ.IsPure) (τ : Equiv.Perm (Fin n)) :
    (ψ.tensorPowGen n).toOp * permutationRepresentation D n τ = (ψ.tensorPowGen n).toOp := by
  have hherm : (ψ.tensorPowGen n).toOp.IsHermitian :=
    (posSemidefOp_implies_mathlib (ψ.tensorPowGen n).toPosSemidefOp).isHermitian
  have h := congrArg Matrix.conjTranspose (permRep_mul_tensorPowGen_of_isPure ψ hψ τ⁻¹)
  rw [Matrix.conjTranspose_mul, hherm, permutationRepresentation_inv,
    Matrix.conjTranspose_conjTranspose] at h
  exact h

/-! ## The interleaved pure IID block sits in the paired symmetric subspace -/

private lemma reindex_interleaving_mul {d n : ℕ} [NeZero d] (A B : Op (d ^ n * d ^ n)) :
    Matrix.reindex (interleavingEquiv d n) (interleavingEquiv d n) (A * B) =
      Matrix.reindex (interleavingEquiv d n) (interleavingEquiv d n) A *
        Matrix.reindex (interleavingEquiv d n) (interleavingEquiv d n) B := by
  have h := Matrix.reindexAlgEquiv_mul ℂ ℂ (interleavingEquiv d n) A B
  simp only [Matrix.reindexAlgEquiv_apply] at h
  exact h

private lemma reindex_interleaving_pairedTensorPow {d n : ℕ} [NeZero d] [NeZero (d * d)]
    (ψ : DensityOp (d * d)) :
    Matrix.reindex (interleavingEquiv d n) (interleavingEquiv d n)
        (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp =
      (ψ.tensorPowGen n).toOp := by
  have hX : (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp =
      Matrix.reindex (interleavingEquiv d n).symm (interleavingEquiv d n).symm
        (ψ.tensorPowGen n).toOp := rfl
  rw [hX]
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- **The interleaved pure IID block is supported on the paired symmetric subspace.**

`P · X · P = X` for `P = symmetricProjectorPaired d n` and `X` the interleaved `n`-fold power of a
pure `ψ` on `ℂ^d ⊗ ℂ^d`.  Under the interleaving equivalence the paired action `U_τ ⊗ U_τ` becomes
the ordinary permutation representation on `(ℂ^{d²})^{⊗n}`
(`interleavingEquiv_conjugates_perm`), where the pure IID power is fixed on both sides. -/
lemma symmetricProjectorPaired_sandwich_pairedTensorPow {d n : ℕ}
    [NeZero d] [NeZero n] [NeZero (d * d)]
    (ψ : DensityOp (d * d)) (hψ : ψ.IsPure) :
    symmetricProjectorPaired d n *
        (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp *
        symmetricProjectorPaired d n =
      (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp := by
  haveI : NeZero ((d * d) ^ n) := ⟨pow_ne_zero n (NeZero.ne (d * d))⟩
  set X := (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp with hX
  set e := interleavingEquiv d n with he
  have hinj : Function.Injective
      ((Matrix.reindex e e : Op (d ^ n * d ^ n) ≃ Op ((d * d) ^ n))) := Equiv.injective _
  have hXre : Matrix.reindex e e X = (ψ.tensorPowGen n).toOp :=
    reindex_interleaving_pairedTensorPow ψ
  have hleft : symmetricProjectorPaired d n * X = X := by
    apply symmetricProjectorPaired_mul_eq_of_perm_left_invariant
    intro τ
    apply hinj
    rw [reindex_interleaving_mul, hXre, interleavingEquiv_conjugates_perm τ]
    exact permRep_mul_tensorPowGen_of_isPure ψ hψ τ
  have hright : X * symmetricProjectorPaired d n = X := by
    apply mul_symmetricProjectorPaired_eq_of_perm_right_invariant
    intro τ
    apply hinj
    rw [reindex_interleaving_mul, hXre, interleavingEquiv_conjugates_perm τ]
    exact tensorPowGen_mul_permRep_of_isPure ψ hψ τ
  rw [hleft, hright]

/-! ## The paired Löwner domination at the constant `g` -/

/-- `g • pairedDeFinettiState d n = symmetricProjectorPaired d n`: the paired reference is the
normalized paired symmetric projector and its normalization is exactly `g`. -/
lemma choose_smul_pairedDeFinettiState_eq_symmetricProjectorPaired
    (d n : ℕ) [NeZero d] [NeZero n] :
    (↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) : ℂ) • (pairedDeFinettiState d n).toOp =
      symmetricProjectorPaired d n := by
  have htoOp : (pairedDeFinettiState d n).toOp =
      (1 / (symmetricProjectorPaired d n).trace) • symmetricProjectorPaired d n := by
    rw [pairedDeFinettiState_eq_of_neZero]; rfl
  rw [htoOp, smul_smul, symmetricProjectorPaired_trace_eq d n]
  have hC : (↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) : ℂ) ≠ 0 := by
    exact_mod_cast (ckr_paired_dim_choose_pos d n).ne'
  rw [mul_one_div_cancel hC, one_smul]

/-- **The paired CKR/Renner de Finetti operator-order domination at the constant `g`.**

For every **pure** state `ψ` on `ℂ^d ⊗ ℂ^d`, the interleaved `n`-fold tensor power of `ψ` on the
paired register `(ℂ^d)^{⊗n} ⊗ (ℂ^d)^{⊗n}` is Löwner-dominated by `g` times the paired de Finetti
reference, with `g = C(n + d² − 1, d² − 1) = dim Sym^n(ℂ^{d²})`:

`ψ^{⊗n}(interleaved) ⪯ g · pairedDeFinettiState d n`.

This is the joint-register companion of the marginal form
`ckrDeFinettiState_opGe_inv_choose_smul_tensorPow`, at the **same** constant `g` — moving from the
signal marginal to the paired register costs nothing, and `g` is exactly optimal here (the paired
reference is `(1/g)·P` with `P` a projector, and the pure block is a rank-one projector inside
`range P`, so the top direction saturates).

The unpaired marginal form is the partial trace of this one: `Tr_B P = g · ckrDeFinettiState` and
partial trace is PSD-monotone.

References: Christandl–König–Renner 2009 (arXiv:0809.3019) `\label{lem:extractpart}`
(main.tex:319–:328); Renner 2005
(arXiv:quant-ph/0512258v2) §5.5 `lem:SymPOVM`. -/
theorem pairedDeFinettiState_opGe_inv_choose_smul_pairedTensorPow
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d * d)]
    (ψ : DensityOp (d * d)) (hψ : ψ.IsPure) :
    opLe (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp
      ((↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) : ℂ) • (pairedDeFinettiState d n).toOp) := by
  set X := (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n))
  have hsub : (symmetricProjectorPaired d n - X.toOp).PosSemidef :=
    symmetricProjectorPaired_sub_psd_of_support d n X.toOp
      (posSemidefOp_implies_mathlib X.toPosSemidefOp)
      (by rw [X.trace_one, Complex.one_re])
      (symmetricProjectorPaired_sandwich_pairedTensorPow ψ hψ)
  rw [choose_smul_pairedDeFinettiState_eq_symmetricProjectorPaired d n]
  exact opLe_of_posSemidef_sub hsub

/-- **The `ψ`-independent-reference form: a completely positive map preserves the constant `g`.**

Pushing both sides of `pairedDeFinettiState_opGe_inv_choose_smul_pairedTensorPow` through the *same*
completely positive linear map `Φ` on the paired register keeps the domination constant at `g`:

`Φ(ψ^{⊗n}(interleaved)) ⪯ g · Φ(pairedDeFinettiState d n)`.

This is the resolved-reference move used by the de Finetti assembler: instead of scoring the
post-measurement block against a product reference on the classical register (which would pay the
full classical-register dimension), one scores it against the image of the *same* map applied to the
de Finetti state.  `Φ` is only required to be completely positive and linear — measure-and-record,
conditioning on a classical announcement, sifting, and PE filtering are all of this form. -/
theorem cp_pairedTensorPow_opLe_choose_smul_pairedDeFinettiState
    {d n m : ℕ} [NeZero d] [NeZero n] [NeZero (d * d)] [NeZero m]
    (Φ : Op (d ^ n * d ^ n) →ₗ[ℂ] Op m) (hΦ : IsCompletelyPositive ⇑Φ)
    (ψ : DensityOp (d * d)) (hψ : ψ.IsPure) :
    opLe (Φ (densityOp_reindex (interleavingEquiv d n).symm (ψ.tensorPowGen n)).toOp)
      ((↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) : ℂ) •
        Φ (pairedDeFinettiState d n).toOp) := by
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  haveI : NeZero (d ^ n * d ^ n) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have h := cp_linear_preserves_opLe Φ hΦ
    (pairedDeFinettiState_opGe_inv_choose_smul_pairedTensorPow d n ψ hψ)
  rwa [map_smul] at h

end Quantum.Channels

end
