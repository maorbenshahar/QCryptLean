import QCryptLean.QKD.BB84.Engine.Postselection.RegisterTrick
import QCryptLean.QKD.BB84.Engine.InnerBudget.BellInnerBudget
import QCryptLean.Quantum.Channels.CPTP.DiamondNormAncilla
import QCryptLean.Quantum.Metrics.KitaevWatrous

/-!
# The channel-agnostic Bell-tightened CKR postselection engine

The channel-agnostic engine behind the exponent-`3` Bell-tightened CKR postselection reduction,
stated for any linear map `Δ : Op (4^n) →ₗ[ℂ] Op dimOut` that is permutation covariant,
conj-transpose preserving (diamond lift only) and stabilized Bell-twirl trace-norm invariant.
`BellReductionGeneral.lean` applies this engine to the agree block and adds the direct
verification bound. It is the Bell analogue of `ckr_security_reduction_exact`.

## Main results

* `bb84_bellSym_ckr_psd_bound_of_bellTwirl_invariant` — the per-operator PSD bound
  `‖(Δ ⊗ id)(W)‖₁ ≤ C(n+3,3) · ckrTensorTraceNorm(Δ, τ_Bell)` for PSD `W` with `Tr W ≤ 1`.
* `diamondNorm_le_bellSymDim_mul_ckrTraceNorm_of_bellTwirl_invariant` — its Kitaev–Watrous lift to
  the diamond norm: `‖Δ‖_◇ ≤ C(n+3,3) · ckrTensorTraceNorm(Δ, τ_Bell)`.

The error-correction scheme feeding a channel `Δ` that satisfies the Bell-twirl-invariance
hypothesis must be translation equivariant: `ECScheme.IsTranslationEquivariant` clause (i) relabels
the announced-syndrome register, clause (ii) makes the reconciled string, the verification tag and
the accept flag covariant. This is a condition on the honest parties' announced-syndrome format — a
linear code with coset decoding, up to a relabelling of the syndrome alphabet.

## Which Nahar et al. statement licenses `x = 4`

The de Finetti dimension for a symmetric reference is cited here from
arXiv:2403.11851, `main.tex:354` `\label{lem:groupPurification}`, which is stated for a
**general compact `G`** and gives a purification on `Sym(⨁ᵢ ℂ^{mᵢ} ⊗ ℂ^{mᵢ})`, i.e. `x = ∑ᵢ mᵢ²`
(IID-`G`-invariance is defined at `main.tex:345`).

It is **not** cited from `main.tex:362` `\label{cor:symmetryDeFinetti}`, nor from its lift
`main.tex:521` `\label{cor:liftToCoherentSymmetries}`: both are stated only for a **product** group
`G = G_A × G_B`, at `x = ∑_{i,j} (mᵢ^A)² (mⱼ^B)²`, and the group used here,
`bb84BellSinglePairTwirlGroup = ![I⊗I, X⊗X, Y⊗Y, Z⊗Z]`, is the bilateral `ℤ₂×ℤ₂`, which is not of
that form.  The value is unaffected — the four Bell operators give four one-dimensional irreps on
`ℂ⁴`, so `∑ᵢ mᵢ² = 4` and the exponent is `x − 1 = 3` — only the citation.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B,
`main.tex:481` `\label{thm:maintheorem}`, `main.tex:354` `\label{lem:groupPurification}`;
Christandl–König–Renner (2009), `arXiv:0809.3019`,
`main.tex:268`–`:401` (\emph{Main Result}: the Post-Selection Theorem `\label{thm:main}` :291–:301,
the substate-extraction Lemma `\label{lem:extractpart}` :319–:328) and `main.tex:447`–`:448` for the
un-halved `ε`-security convention; Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics Math.RepresentationTheory Math.ClassicalEntropy
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace QKD.BB84.Engine

open QKD.BB84.Model.bb84

/-! ## The channel-agnostic Bell-tightened per-operator PSD bound -/

/-- **The Bell-tightened CKR PSD per-operator bound, for any Bell-twirl trace-norm invariant `Δ`.**

For a linear map `Δ : Op (4^n) →ₗ[ℂ] Op dimOut` that is permutation covariant and whose stabilized
trace norm is invariant under the IID bilateral Bell twirl at every ancilla width, and any PSD
`W₀` on `(ℂ⁴)^{⊗n} ⊗ (ℂ⁴)^{⊗n}` with `Tr W₀ ≤ 1`,

`‖(Δ ⊗ id)(W₀)‖₁ ≤ C(n+3,3) · ckrTensorTraceNorm(Δ, τ_Bell)`.

The Bell analogue of `ckr_security_reduction_exact`, and the engine behind the general-`m`
agree-block lift in `BellReductionGeneral.lean`: the combined
extension `ρ̃ = bellRegExt (blockDiagExt W₀)` has the same
`Δ`-trace-norm as `W₀` — the permutation symmetrization by `blockDiagExt_traceNorm_mapTensorId` at
`hΔ.covariance`, the Bell symmetrization by
`bellRegExt_traceNorm_mapTensorId_referee_of_bellTwirl_invariant` at `hinv`, consumed at the single
width `dimR := 4^n * Fintype.card (Equiv.Perm (Fin n))` — and its `(ℂ⁴)^{⊗n}` marginal is the Bell
twirl of the perm-symmetrized marginal, hence permutation invariant (`bellTwirl_perm_conj`) and
jointly Bell-diagonal (`bellTwirl_isIIDBellDiagonal`).  The Bell de Finetti domination
`bellSym_subnormalized_marginal_dominated` bounds that marginal by `C(n+3,3) · τ_Bell`, and
substate extraction (`traceNorm_mapTensorId_substate_bound`) converts the marginal domination into
the trace-norm bound.

Conj-transpose preservation of `Δ` is **not** a hypothesis here — neither instance uses it at this
level; it enters one level up, in the Kitaev–Watrous diamond-norm lift.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, `main.tex:481`
`\label{thm:maintheorem}` and `main.tex:354` `\label{lem:groupPurification}` at `x = ∑ᵢ mᵢ² = 4`
(the joint Bell `ℤ₂×ℤ₂` symmetry); Christandl–König–Renner (2009), `arXiv:0809.3019`,
`main.tex:268`–`:401`; Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5. -/
theorem bb84_bellSym_ckr_psd_bound_of_bellTwirl_invariant {n dimOut : ℕ} [NeZero n]
    [NeZero (4 ^ n)] [NeZero dimOut] (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ : PermutationCovariant Δ)
    (hinv : ∀ (dimR : ℕ) [NeZero dimR] (g : Fin n → Fin 4) (M : Op (4 ^ n * dimR)),
      traceNorm (mapTensorId (k := dimR) Δ
          (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR) * M *
            (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR))ᴴ)) =
        traceNorm (mapTensorId (k := dimR) Δ M))
    (W0 : Op (4 ^ n * 4 ^ n)) (hW0_psd : W0.PosSemidef) (hW0_trace : W0.trace.re ≤ 1) :
    traceNorm (mapTensorId Δ W0) ≤
      (Nat.choose (n + 3) 3 : ℝ) *
        ckrTensorTraceNorm Δ (bb84BellCKRDeFinettiPurification n) := by
  have hkNZ : NeZero (Fintype.card (Equiv.Perm (Fin n))) :=
    ⟨by simp [Fintype.card_perm, Fintype.card_fin, Nat.factorial_ne_zero]⟩
  have hdimR_NZ : NeZero (4 ^ n * Fintype.card (Equiv.Perm (Fin n))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have : NeZero ((4 ^ n * Fintype.card (Equiv.Perm (Fin n))) * 4 ^ n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hcov := hΔ.covariance
  -- the combined symmetrization extension `ρ̃ = bellRegExt (blockDiagExt W₀)`
  set bd := Quantum.Channels.blockDiagExt W0 with hbd
  set ρt := bellRegExt bd with hρt
  have hbd_psd : bd.PosSemidef := Quantum.Channels.blockDiagExt_posSemidef W0 hW0_psd
  have hρt_psd : ρt.PosSemidef := bellRegExt_posSemidef bd hbd_psd
  -- both extensions preserve `‖(Δ ⊗ id)·‖₁` exactly
  have htn : traceNorm (mapTensorId Δ ρt) = traceNorm (mapTensorId Δ W0) := by
    rw [hρt,
      bellRegExt_traceNorm_mapTensorId_referee_of_bellTwirl_invariant Δ
        (fun g M => hinv (4 ^ n * Fintype.card (Equiv.Perm (Fin n))) g M) bd,
      hbd, Quantum.Channels.blockDiagExt_traceNorm_mapTensorId _ hcov W0]
  -- the combined marginal `Y = bb84BellTwirl n (sym marginal)`
  set Ymarg := partialTraceB ρt with hY
  have hY_eq_twirl : Ymarg = bb84BellTwirl n (partialTraceB bd) := bellRegExt_partialTraceB bd
  have hY_psd : Ymarg.PosSemidef := partialTraceB_posSemidef_mathlib _ hρt_psd
  have hY_trace : Ymarg.trace.re ≤ 1 := by
    rw [hY_eq_twirl, bb84BellTwirl_trace, blockDiagExt_marginal_trace]; exact hW0_trace
  have hY_bell : IsIIDBellDiagonal Ymarg := by
    rw [hY_eq_twirl]; exact bellTwirl_isIIDBellDiagonal n (partialTraceB bd)
  have hY_perm : ∀ σ : Equiv.Perm (Fin n),
      permutationRepresentation 4 n σ * Ymarg = Ymarg * permutationRepresentation 4 n σ := by
    intro σ
    apply perm_commute_of_conjInvariant n σ Ymarg
    rw [hY_eq_twirl, ← bellTwirl_perm_conj n σ (partialTraceB bd),
      blockDiagExt_marginal_permConjInvariant n W0 σ]
  -- Bell de Finetti domination on the marginal
  have hdom := bellSym_subnormalized_marginal_dominated n Ymarg hY_psd hY_trace hY_perm hY_bell
  have hmarg_bridge :
      (bb84BellCKRDeFinettiPurification n).partialTraceB.toOp = (bb84BellDeFinettiState n).toOp :=
          by
    rw [(bb84BellCKRDeFinettiPurification_isPurification n).marginal, bb84BellDeFinettiState_toOp]
    rfl
  have hdom' :
      (((Nat.choose (n + 3) 3 : ℝ) : ℂ) •
          (bb84BellCKRDeFinettiPurification n).partialTraceB.toOp - partialTraceB ρt).PosSemidef :=
              by
    rw [hmarg_bridge,
      show ((Nat.choose (n + 3) 3 : ℝ) : ℂ) = (Nat.choose (n + 3) 3 : ℂ) by push_cast; ring]
    exact hdom
  -- substate extraction → the trace-norm bound
  have hC_pos : (0 : ℝ) < (Nat.choose (n + 3) 3 : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hsub := traceNorm_mapTensorId_substate_bound Δ ρt hρt_psd
    (bb84BellCKRDeFinettiPurification n)
    (bb84BellCKRDeFinettiPurification_isPurification n).isPure
    (Nat.choose (n + 3) 3 : ℝ) hC_pos hdom'
  rw [htn] at hsub
  exact hsub

/-! ## The channel-agnostic Bell-tightened diamond-norm reduction -/

/-- **The Bell-tightened CKR diamond-norm bound, for any Bell-twirl trace-norm invariant `Δ`.**

`‖Δ‖_◇ ≤ C(n+3,3) · ckrTensorTraceNorm(Δ, τ_Bell)`.  The channel-agnostic engine behind the
general-`m` agree-block lift in `BellReductionGeneral.lean`:
the PSD per-operator bound `bb84_bellSym_ckr_psd_bound_of_bellTwirl_invariant` is lifted to all
`‖X‖₁ ≤ 1` by the Kitaev–Watrous square-ancilla reduction (`kw_nonhermitian_reduction`, at
`hΔ_conj`), and the diamond norm is the supremum over such `X`.

The Bell analogue of `ckr_security_reduction_exact` at the exponent-`3` de Finetti constant.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, `main.tex:481`
`\label{thm:maintheorem}` and `main.tex:354` `\label{lem:groupPurification}` at `x = ∑ᵢ mᵢ² = 4`;
Christandl–König–Renner (2009), `arXiv:0809.3019`, `main.tex:268`–`:401`; Renner (2005),
`arXiv:quant-ph/0512258v2`, §6.5. -/
theorem diamondNorm_le_bellSymDim_mul_ckrTraceNorm_of_bellTwirl_invariant {n dimOut : ℕ}
    [NeZero n] [NeZero (4 ^ n)] [NeZero dimOut] (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ : PermutationCovariant Δ)
    (hΔ_conj : ∀ M : Op (4 ^ n), Δ M.conjTranspose = (Δ M).conjTranspose)
    (hinv : ∀ (dimR : ℕ) [NeZero dimR] (g : Fin n → Fin 4) (M : Op (4 ^ n * dimR)),
      traceNorm (mapTensorId (k := dimR) Δ
          (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR) * M *
            (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR))ᴴ)) =
        traceNorm (mapTensorId (k := dimR) Δ M)) :
    diamondNorm Δ ≤
      (Nat.choose (n + 3) 3 : ℝ) *
        ckrTensorTraceNorm Δ (bb84BellCKRDeFinettiPurification n) := by
  set B : ℝ :=
    (Nat.choose (n + 3) 3 : ℝ) * ckrTensorTraceNorm Δ (bb84BellCKRDeFinettiPurification n) with hB
  have hB_nn : (0 : ℝ) ≤ B :=
    mul_nonneg (by positivity) (ckrTensorTraceNorm_nonneg _ _)
  have hPSD : ∀ (ρ : Op (4 ^ n * 4 ^ n)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Δ ρ) ≤ B := by
    intro ρ hρ_psd hρ_trace
    exact bb84_bellSym_ckr_psd_bound_of_bellTwirl_invariant Δ hΔ hinv ρ hρ_psd hρ_trace
  unfold diamondNorm
  apply csSup_le
  · exact ⟨0, 0, by rw [traceNorm_zero]; exact zero_le_one,
      by rw [mapTensorId_zero, traceNorm_zero]⟩
  · rintro t ⟨W1, hW1_norm, rfl⟩
    exact Quantum.Metrics.KitaevWatrous.kw_nonhermitian_reduction Δ B hB_nn hΔ_conj hPSD W1 hW1_norm

end QKD.BB84.Engine

end -- noncomputable section
