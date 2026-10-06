import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Order

/-!
# CKR Paired Reference States — operator-order (Löwner) de Finetti infrastructure

The proved paired CKR bounds in `Reference/Paired.lean` are of two kinds:

* `partial_trace_paired_symmetric_bound` — a Löwner domination of the
  *signal-register marginal* `partialTraceB ρ'` by `polyDim · ckrDeFinettiState`
  (no reference register), and
* `ckr_psd_bound_paired_support` — a *trace-norm* domination of the joint
  `mapTensorId Δ ρ'` by `polyDim · ‖mapTensorId Δ τ‖₁`.

Neither is a *joint operator-order* (Löwner) domination of `mapTensorId Δ ρ'`.
This file supplies the covariance-free, completely-positive-monotone reductions
that the deep operator-order layer consumes:

* `mapTensorId_opLe_symmetricProjectorPaired` — the completely-positive-monotone
  lift of `ρ' ⪯ P` (the paired symmetric projector) through `mapTensorId Δ`,
  giving `mapTensorId Δ ρ' ⪯ mapTensorId Δ P`.  This is the trivial half of the
  operator-order CKR content (it loses the feasibility scale, so it is not by itself the
  de Finetti bound).
* `mapTensorId_opLe_card_smul_one_of_marginalNorm` — the generic structural
  reference-dimension (constant `d ^ n`) operator-norm bound, with no paired support and no
  covariance.

The genuinely deep operator-order de Finetti improvement (the symmetric-subspace top-eigenvalue
concentration replacing the generic `d ^ n` factor by `polyDim / d ^ n`;
Christandl–König–Renner 2009 `lem:extractpart`, Harrow §3) is **not** in this file: it is not
derivable from `ρ' ⪯ P`, from the generic `d ^ n` card route, or from the trace-norm CKR bound
`ckr_psd_bound_paired_support`.

The genuine `lem:extractpart` **operator core** takes the honest Löwner form `(1/c)·P ⪯ M`
(PSD difference `M − (1/c)·P`): that one PSD inequality encodes *both* halves of the
spike-decomposition mechanism — the support-containment `range P ⊆ range M` (without which the
Löwner domination fails on a `ker M` direction) and the uniform symmetric-subspace eigenvalue
floor `M|_{range P} ⪰ (1/c)·P` realized by the maximally-entangled purification of CKR
`lem:extractpart`.  At this maximally-general level the inequality is *false* for arbitrary
`P`, `M`, so the deep fact is stated with the de Finetti structure in scope at its BB84
instantiation; this file supplies only the rescaling reduction
`opLe_projector_smul_of_invFloor` converting it to the projector-domination form `P ⪯ c·M`.

## Main statements
- `mapTensorId_opLe_symmetricProjectorPaired`: CP-monotone lift of `ρ' ⪯ P`.
- `mapTensorId_opLe_card_smul_one_of_marginalNorm`: generic `d ^ n` card route.
- `opLe_projector_smul_of_invFloor`: the rescaling `(1/c)·P ⪯ M ⟹ P ⪯ c·M`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- **Completely-positive-monotone lift of paired-symmetric support.**

For any density operator `ρ'` on `(d^n) ⊗ (d^n)` supported on the paired
symmetric subspace (PSD, subnormalized, `P ρ' P = ρ'`) and any completely
positive linear map `Δ : Op (d^n) → Op dimOut`, applying `Δ` to the first tensor
factor (`mapTensorId Δ`, identity on the reference register) is monotone in the
Löwner order: from `ρ' ⪯ P` (the paired symmetric projector dominates every
subnormalized PSD operator it supports, `symmetricProjectorPaired_sub_psd_of_support`)
we get `mapTensorId Δ ρ' ⪯ mapTensorId Δ P`.

This is the operator-order companion of the marginal bound
`partial_trace_paired_symmetric_bound`.  It is the easy half of the operator-order
CKR content: it bounds the lifted operator by the *projector* image, which carries
the trivial scale `1` (from `tr ρ' ≤ 1`), not the feasibility scale of the
signal-register marginal.  The feasibility scale enters only through the deep
covariant de Finetti bound. -/
lemma mapTensorId_opLe_symmetricProjectorPaired {d n dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ_cp : IsCompletelyPositive ⇑Δ)
    (ρ' : Op (d ^ n * d ^ n))
    (hρ'_psd : ρ'.PosSemidef)
    (hρ'_trace : ρ'.trace.re ≤ 1)
    (hρ'_support : symmetricProjectorPaired d n * ρ' * symmetricProjectorPaired d n = ρ') :
    opLe (mapTensorId Δ ρ') (mapTensorId Δ (symmetricProjectorPaired d n)) := by
  have h_sub : opLe ρ' (symmetricProjectorPaired d n) :=
    opLe_of_posSemidef_sub
      (symmetricProjectorPaired_sub_psd_of_support d n ρ' hρ'_psd hρ'_trace hρ'_support)
  exact mapTensorId_preserves_opLe Δ hΔ_cp h_sub

/-- **Generic structural card-route operator-norm bound (constant `d ^ n`).**

For any completely positive map `Δ : Op (d^n) → Op dimOut` and any PSD subnormalized
substate `ρ'` on `(d^n) ⊗ (d^n)`, with a scalar operator-norm bound on the lifted
`dimOut`-marginal `Δ (partialTraceB ρ') ⪯ c · 1`, the lifted block
`mapTensorId Δ ρ'` is operator-norm dominated by the *same* scalar `c` improved only
by the generic reference-dimension penalty `d ^ n`:

  `mapTensorId Δ ρ' ⪯ (d ^ n · c) · 1`.

Proved from the generic Cauchy/pinching bound
`opLe_le_card_smul_partialTraceB_tensor_one`
(`A ⪯ dim_R · (partialTraceB A ⊗ 1)`), the partial-trace identity
`partialTraceB (mapTensorId Δ ρ') = Δ (partialTraceB ρ')`, and the marginal datum.
It uses *no* paired-symmetric support and *no* permutation covariance: it is the
reference-dimension penalty that holds for every PSD substate.

The CKR de Finetti improvement replaces the reference-dimension penalty `d ^ n` of this card
route by the polynomial `polyDim / d^n` order, a gain of `polyDim / d^{2n}`; that improvement
is the genuinely deep content and is supplied on the live keystone route through the
spike-decomposition layer, not in this file.  Note the *anisotropic* operator-norm form
`mapTensorId Δ ρ' ⪯ (polyDim / d^n) · (Δ (partialTraceB ρ') ⊗ 1)` is too strong — the
anisotropic operator-norm form fails (a paired-symmetric witness gives ratio `≈ 1.20 > 1`). -/
lemma mapTensorId_opLe_card_smul_one_of_marginalNorm {d n dimOut : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ_cp : IsCompletelyPositive ⇑Δ)
    (ρ' : Op (d ^ n * d ^ n))
    (hρ'_psd : ρ'.PosSemidef)
    (c : ℝ)
    (hMargNorm : opLe (Δ (partialTraceB ρ'))
      (Complex.ofReal c • (1 : Op dimOut))) :
    opLe (mapTensorId Δ ρ')
      ((Complex.ofReal (((d ^ n : ℕ) : ℝ) * c)) •
        (1 : Op (dimOut * d ^ n))) := by
  have : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  -- The lifted block is PSD; apply the generic card bound.
  have hcp : IsCompletelyPositive
      (⇑(mapTensorIdLinear (k := d ^ n) Δ)) := by
    simpa [mapTensorIdLinear] using
      mapTensorId_isCompletelyPositive (k := d ^ n) Δ hΔ_cp
  have hA_psd : (mapTensorId Δ ρ').PosSemidef := by
    simpa [mapTensorIdLinear] using
      cp_linear_preserves_posSemidef (mapTensorIdLinear (k := d ^ n) Δ) hcp ρ' hρ'_psd
  have hcard := Quantum.Operators.opLe_le_card_smul_partialTraceB_tensor_one hA_psd
  rw [partialTraceB_mapTensorId] at hcard
  -- The card scalar `↑↑(d^n)` agrees with `Complex.ofReal ↑(d^n)`; rewrite the bound.
  have hcard' :
      opLe (mapTensorId Δ ρ')
        (Complex.ofReal ((d ^ n : ℕ) : ℝ) •
          Quantum.TensorProducts.Op.tensor (Δ (partialTraceB ρ')) (1 : Op (d ^ n))) := by
    have hcardcast : Complex.ofReal ((d ^ n : ℕ) : ℝ) = ((d ^ n : ℕ) : ℂ) := by
      push_cast; ring
    rw [hcardcast]; exact hcard
  -- Tensor the marginal bound on the right by `1_R` and identify with `c • 1`.
  have hMargT :
      opLe (Quantum.TensorProducts.Op.tensor (Δ (partialTraceB ρ')) (1 : Op (d ^ n)))
        (Complex.ofReal c • (1 : Op (dimOut * d ^ n))) := by
    have h := opLe_tensor_right_one (dR := d ^ n) hMargNorm
    rwa [Quantum.TensorProducts.Op.tensor_smul_left,
      Quantum.TensorProducts.Op.tensor_one] at h
  -- Scale the marginal bound by `d ^ n ≥ 0` (inline) and chain.
  have hdn_nonneg : (0 : ℝ) ≤ ((d ^ n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hscaled :
      opLe (Complex.ofReal ((d ^ n : ℕ) : ℝ) •
            Quantum.TensorProducts.Op.tensor (Δ (partialTraceB ρ')) (1 : Op (d ^ n)))
        ((Complex.ofReal (((d ^ n : ℕ) : ℝ) * c)) •
          (1 : Op (dimOut * d ^ n))) := by
    intro v
    simp only [Quantum.Operators.quadraticForm_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hstep := mul_le_mul_of_nonneg_left (hMargT v) hdn_nonneg
    simp only [Quantum.Operators.quadraticForm_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hstep
    calc ((d ^ n : ℕ) : ℝ) *
            (quadraticForm
              (Quantum.TensorProducts.Op.tensor (Δ (partialTraceB ρ'))
                (1 : Op (d ^ n))) v).re
          ≤ ((d ^ n : ℕ) : ℝ) *
              (c * (quadraticForm (1 : Op (dimOut * d ^ n)) v).re) := hstep
      _ = (((d ^ n : ℕ) : ℝ) * c) * (quadraticForm (1 : Op (dimOut * d ^ n)) v).re := by
            ring
  exact fun v => le_trans (hcard' v) (hscaled v)

/-! ## The `lem:extractpart` rescaling reduction

The genuinely-deep operator-order de Finetti content (Christandl–König–Renner 2009
`lem:extractpart`, arXiv:0809.3019, `main.tex:314–360`) takes the honest Löwner form
`(1/c)·P ⪯ M`: the *normalized* projector `(1/c)·P` (`P` the support projector of the
combined symmetric component, `c = g_{n,d}` the symmetric-subspace dimension) is dominated by
the de Finetti correlated marginal `M`.  That single PSD inequality `M − (1/c)·P ⪰ 0`
carries *both* the support-containment `range P ⊆ range M` and the uniform symmetric-subspace
eigenvalue floor `M|_{range P} ⪰ (1/c)·P` (the CKR maximally-entangled purification realizing
the uniform `1/c` eigenvalue, `|Ψ⟩ = g^{-1/2} Σ_i |ν_i⟩⊗|ν_i⟩` over an eigenbasis).

This file supplies only the **rescaling reduction** `opLe_projector_smul_of_invFloor`,
which converts that floor to the projector-domination form `P ⪯ c·M` the downstream feasibility
step consumes.  The deep PSD-difference fact itself cannot be a theorem at this maximally
general level — for arbitrary `P`, `M` the inequality is *false* (it requires the de Finetti
symmetric-subspace structure relating `P` to `M`) — so it is stated, with that structure in
scope, at its BB84 instantiation against the symmetric-subspace group-average projector
`P = R.groupAverageProjector`. -/

/-- **Rescaling the `lem:extractpart` floor to projector-domination form.**

From the normalized-projector floor `(1/c)·P ⪯ M` (`hFloor`) and `c > 0`, scaling both sides
by `c` and cancelling `c·(1/c) = 1` gives the projector domination `P ⪯ c·M`.  The only content
is the scalar arithmetic on the Löwner order.  This is the covariance-free
reduction the symmetric → correlated feasibility transfer consumes: the deep content lives
entirely in `hFloor`. -/
lemma opLe_projector_smul_of_invFloor {N : ℕ} (P M : Op N) (c : ℝ) (hc_pos : 0 < c)
    (hFloor : opLe (Complex.ofReal (1 / c) • P) M) :
    opLe P (Complex.ofReal c • M) := by
  intro v
  have hscaled := mul_le_mul_of_nonneg_left (hFloor v) hc_pos.le
  rw [Quantum.Operators.quadraticForm_smul, Complex.mul_re] at hscaled
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hscaled
  rw [show c * ((1 / c) * (Quantum.Operators.quadraticForm P v).re)
        = (Quantum.Operators.quadraticForm P v).re by field_simp] at hscaled
  rw [Quantum.Operators.quadraticForm_smul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact hscaled

/-- **The CKR/Renner de Finetti operator-order domination (`lem:SymPOVM`).**

For every product (IID) density operator `σ` on `ℂ^d`, the `n`-fold tensor power `σ^{⊗n}`
is Löwner-dominated by `g` times the CKR de Finetti state, with
`g = C(n + d² − 1, d² − 1) = dim Sym^n(ℂ^{d²})` the paired symmetric-subspace dimension:

`σ^{⊗n} ≼ g · (ckrDeFinettiState d n)`,    equivalently    `ckrDeFinettiState d n ≽ g⁻¹·σ^{⊗n}`.

This is the genuinely deep CKR/Renner symmetric-subspace fact: the de Finetti state — the
average over the symmetric subspace of all `σ^{⊗n}` — dominates each individual IID product
state by the polynomial factor `g`, **not** by the ambient `d^{2n}` dimension.  It is the
operator content of Renner `lem:SymPOVM` / CKR `lem:extractpart`: `σ^{⊗n}` is supported on
the symmetric subspace `Sym^n(ℂ^d)`, on which the de Finetti state has its eigenvalues
floored at `g⁻¹` times the symmetric identity (the maximally-entangled-purification floor of
CKR main.tex:268–:401 (\emph{Main Result}: Theorem `\label{thm:main}` :291–:301, Lemma
`\label{lem:extractpart}` :319–:328)).

**Quantitatively (Renner `lem:SymPOVM`):** at `d = 4`, the domination holds with
`g = C(n+15,15)` (the symmetric-subspace dimension), which is `136` at `n = 2`.
The embedded-vs-ambient register-extension penalty it funds is
`2·log₂ g = O(log n)` — **NOT** the ambient `2·log₂(d^{2n}) = 4n` full-max-mixed cost.  This is
the single irreducible CKR/Renner core that the Nahar et al. B17 register extension consumes;
it is the deep PSD-difference fact that this file records as *not* derivable from `ρ' ⪯ P`,
the generic `d^n`-card route, or the trace-norm CKR bound (it requires the uniform
symmetric-subspace eigenvalue floor of `lem:extractpart`).

It feeds the generic register-extension host
`InfoTheory.SmoothMinEntropy.smoothMinEntropy_ge_of_smul_opLe` at `c = g⁻¹` (the `hdom`
hypothesis, with the larger reference `σ' = ckrDeFinettiState` and the rescaled product
reference `c · σ^{⊗n}`), discharging the `−2·log₂ g` Nahar et al. B17 penalty against the faithful
de
Finetti reference rather than the `4ⁿ` full-max-mixed reference.

References: Renner 2005 (arXiv:quant-ph/0512258v2) §5.5, `lem:SymPOVM`; Christandl–König–Renner
2009 (arXiv:0809.3019) `\label{lem:extractpart}` (main.tex:319–:328); Nahar, Tupkary, Zhao,
Lütkenhaus, Tan 2024 (arXiv:2403.11851) Theorem 3,
`\label{eq:splittingoffV}` (main.tex:1393–:1396). -/
theorem ckrDeFinettiState_opGe_inv_choose_smul_tensorPow
    (d n : ℕ) [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (σ : DensityOp d) :
    opLe (σ.tensorPowGen n).toOp
      ((↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) : ℂ) • (ckrDeFinettiState d n).toOp) := by
  -- CKR `lem:extractpart` purification argument.  `σ^{⊗n}` is permutation-invariant, so it
  -- has a *pure* paired-symmetric purification `Ψ` on `(d^n) ⊗ (d^n)` with
  -- `Tr_B Ψ = σ^{⊗n}` and `P · Ψ · P = Ψ` (`P` = `symmetricProjectorPaired d n`).  Since `Ψ` is
  -- subnormalized (trace 1) and supported on the paired symmetric subspace, `P − Ψ ⪰ 0`, hence
  -- (partial trace is PSD-monotone) `Tr_B P − Tr_B Ψ = g·ckr − σ^{⊗n} ⪰ 0`, i.e. the domination.
  obtain ⟨Ψ, _hΨ_pure, _hΨ_paired, hΨ_support, hΨ_marginal⟩ :=
    InfoTheory.DeFinetti.symmetric_purification_with_pure
      (σ.tensorPowGen n) (Quantum.Symmetry.tensorPow_isPermutationInvariant σ)
  -- `Ψ ⪯ P` from PSD + subnormalization + paired-symmetric support.
  have h_sub_psd :
      (symmetricProjectorPaired d n - Ψ.toOp).PosSemidef :=
    symmetricProjectorPaired_sub_psd_of_support d n Ψ.toOp
      (posSemidefOp_implies_mathlib Ψ.toPosSemidefOp)
      (by rw [Ψ.trace_one, Complex.one_re])
      hΨ_support
  -- Partial trace is PSD-monotone: `Tr_B P − Tr_B Ψ ⪰ 0`.
  have h_ptrace_psd :=
    partialTraceB_psd_mono (symmetricProjectorPaired d n) Ψ.toOp h_sub_psd
  -- Identify the two partial traces: `Tr_B P = g·ckr` and `Tr_B Ψ = σ^{⊗n}`.
  rw [hΨ_marginal,
    ← choose_smul_ckrDeFinettiState_eq_partialTraceB_symmetricProjectorPaired d n] at h_ptrace_psd
  exact opLe_of_posSemidef_sub h_ptrace_psd

end Quantum.Channels

end -- noncomputable section
