import QCryptLean.QKD.BB84.Engine.Postselection.PEAnnounceRelabel

/-!
# Bell-twirl covariance of the retained-Eve pre-channel, and the generic register trick

The pre-channel-level covariance hypothesis that the Bell-twirl trace-norm invariance of the
genuine-LOCC symmetrized channels (`RegisterTrickGeneral.lean`) needs, and the generic (channel-
independent) register-trick lemma it is combined with.

`bb84SymRealChannel` / `bb84SymIdealChannel` carry the unit register embedding
`bb84UnitRegisterEmbed n` in their pre-channel slot.  Bell-twirl invariance is **not available**
for an arbitrary retained-Eve pre-channel `pre : Op (4ⁿ) →ₗ Op (4ⁿ · eveDim)`: the twirl reaches the
sift only through that slot (`bb84SiftedConjAfterPre` is `bb84SiftedConjChannel ∘ₗ pre`), and
`IsCPTP ⇑pre` says nothing about `pre` on twirled inputs. `IsBellTwirlCovariantPre` is the explicit
hypothesis that closes this gap; the unit register embedding satisfies it
(`bb84UnitRegisterEmbed_isBellTwirlCovariantPre`).

**The hypothesis is not a formality.**  It is a genuine restriction on `pre` at every `eveDim`,
`eveDim = 1` included — the linear map `A ↦ Op.castDim _ (W * A * Wᴴ)` at `W = 1_A ⊗ H_B` on one
round violates it, because `hadamardPair_conj_bellTwirl` carries `X⊗X` to `X⊗Z`, outside the
bilateral group `bb84BellSinglePairTwirlGroup = ![I⊗I, X⊗X, Y⊗Y, Z⊗Z]`.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B, the
Postselection Theorem `\label{thm:maintheorem}` (`main.tex:481`–`:491`) and its appendix proof
(`main.tex:1331`–`:1421`); Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5;
Christandl–König–Renner (2009), `arXiv:0809.3019`, `main.tex:268`–`:401` (Main Result: the
Post-Selection Theorem `\label{thm:main}` :291–:301, the substate-extraction Lemma
`\label{lem:extractpart}` :319–:328).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

open QKD.BB84.Model.bb84
open QKD.BB84.Model

/-! ## The pre-channel layer -/

/-- **Bell-twirl covariance of a retained-Eve pre-channel.**  The map `pre` transports the input
bilateral-Pauli twirl `U_h` to `U_h ⊗ 1_E` on its output:
`pre (U_h · ρ · U_h†) = (U_h ⊗ 1_E) · pre ρ · (U_h ⊗ 1_E)†`.

Indexed by a bare retained-Eve dimension and an opaque pre-channel rather than by an attack
object, exactly as `IsPermutationCovariantUpToEveRelabelPre` (`UnitRegisterEmbed.lean`) is.

**Nothing supplies this for free**, and the Bell-twirl trace-norm invariance genuinely needs
it: the twirl reaches the sift only through the pre-channel slot, and `IsCPTP ⇑pre` constrains
`pre` on no twirled input.  The unit register embedding satisfies it
(`bb84UnitRegisterEmbed_isBellTwirlCovariantPre`), which is the slot `bb84SymRealChannel` /
`bb84SymIdealChannel` live at.

**The predicate is a real restriction at every `eveDim`, `eveDim = 1` included.**  At `n = 1`,
`eveDim = 1` the linear map `A ↦ W · A · Wᴴ` at `W = 1_A ⊗ H_B` violates it: `(1⊗H)(X⊗X)(1⊗H)ᴴ =
X⊗Z`, which is outside the bilateral group `bb84BellSinglePairTwirlGroup = ![I⊗I, X⊗X, Y⊗Y, Z⊗Z]`,
so the two sides need not agree.  A **one-sided Pauli** `W` does *not*
refute it — `W = X⊗I`, `Z⊗I` and the bilateral `X⊗X` all give deviation `0`, because the two
anticommutation signs cancel in the bilateral product.

No `¬IsBellTwirlCovariantPre` statement is compiled from this counterexample in this file. -/
def IsBellTwirlCovariantPre {n : ℕ} [NeZero (4 ^ n)] {eveDim : ℕ}
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) : Prop :=
  ∀ (h : Fin n → Fin 4) (ρ : Op (4 ^ n)),
    pre (bellTwirlUnitary n h * ρ * (bellTwirlUnitary n h)ᴴ) =
      Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) *
        pre ρ *
        (Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim))ᴴ

/-- **The unit register embedding is Bell-twirl covariant**: `A ↦ A ⊗ 1₁` commutes with
signal-round conjugation because nothing acts on the one-dimensional side register.

Stated on the bare pre-channel `bb84UnitRegisterEmbed n` and proved from
`bb84UnitRegisterEmbed_apply` alone, so no attack object appears in its statement or in its
proof. -/
theorem bb84UnitRegisterEmbed_isBellTwirlCovariantPre (n : ℕ) [NeZero (4 ^ n)] :
    IsBellTwirlCovariantPre (bb84UnitRegisterEmbed n) := by
  intro h ρ
  rw [bb84UnitRegisterEmbed_apply, bb84UnitRegisterEmbed_apply,
    Op.tensor_conjTranspose, Op.tensor_mul, Op.tensor_mul, Matrix.conjTranspose_one,
    Matrix.mul_one, Matrix.mul_one]

/-!
## The generic register trick

`bellRegExt` (`RegisterTrickReferee.lean`) is channel-independent, so only the trace-norm
preservation has to be redone.  It is stated here **generically** in the map `Δ`, with the
Bell-twirl trace-norm invariance as an explicit hypothesis: that is the only property of `Δ` the
argument uses, so every channel difference satisfying it is an instance.  The block decomposition
it needs is already generic-in-`Δ` and public in `RegisterTrickReferee.lean` (`bellRegBlock`,
`bellRegReindexOut`, `bellRegExt_traceNorm_as_sum`), so it is cited directly below instead of being
repeated.
-/

/-- **The Bell register extension preserves `‖(Δ ⊗ id)·‖₁` exactly, for any Bell-twirl trace-norm
invariant `Δ`.**

The orthogonal `|g⟩` blocks add, each block is invariant by `hinv`, and the `4^n` equal terms with
weight `1/4^n` collapse to the un-extended norm.  The conclusion is an equality, not an
inequality: no convexity loss. -/
theorem bellRegExt_traceNorm_mapTensorId_referee_of_bellTwirl_invariant {n dimR dimOut : ℕ}
    [NeZero (4 ^ n)]
    [NeZero dimR] [NeZero dimOut] (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (hinv : ∀ (g : Fin n → Fin 4) (M : Op (4 ^ n * dimR)),
      traceNorm (mapTensorId (k := dimR) Δ
          (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR) * M *
            (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR))ᴴ)) =
        traceNorm (mapTensorId (k := dimR) Δ M))
    (ρ : Op (4 ^ n * dimR)) :
    traceNorm (mapTensorId (k := dimR * 4 ^ n) Δ (bellRegExt ρ)) =
      traceNorm (mapTensorId (k := dimR) Δ ρ) := by
  rw [bellRegExt_traceNorm_as_sum Δ ρ]
  rw [Finset.sum_congr rfl (fun ν _ => by rw [hinv ((@finFunctionFinEquiv 4 n).symm ν) ρ])]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnorm : ‖(1 : ℂ) / (4 ^ n : ℂ)‖ = 1 / (4 ^ n : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_pow, Complex.norm_ofNat]
  rw [hnorm]
  rw [show ((4 ^ n : ℕ) : ℝ) = (4 : ℝ) ^ n by push_cast; ring]
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

end QKD.BB84.Engine

end
