import QCryptLean.InfoTheory.SmoothMinEntropy.Extension.ExtensionPenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.SmoothSuperadditivity

/-!
# Constant CQ state and same-radius right-register contraction

The one-block constant CQ state `CQState.const σ` carrying a fixed density
operator, and the same-radius CQ purified-distance contraction under tensoring
both states with the same fixed right register (Tomamichel 2016, eq. 3.41).

General quantum-information mathematics: these
statements are stated over generic `CQState`/`DensityOp` objects, with no BB84 or
QKD-protocol content.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The one-block constant CQ state carrying a fixed density operator `σ` on a
singleton classical register.

`CQState.const σ : CQState Unit n` has its (unique) block equal to
`σ.toSubDensityOp`, so its total weight is `tr σ = 1`.  This is the right-register
factor in the product-center geometry: tensoring it on the right of an arbitrary CQ
state appends the fixed register `σ` to every block. -/
def CQState.const {n : ℕ} (σ : DensityOp n) : CQState Unit n where
  stateMap := fun _ => DensityOp.toSubDensityOp σ
  weight_le_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul,
      toSubDensityOp_trace]

/-- **Same-radius right-register contraction (Tomamichel 2016, eq. 3.41).**

Tensoring both CQ states with the SAME fixed right register `σR` (a normalized
density operator, `tr σR = 1`) does not increase — and here, since the right factor
is identical on both sides, preserves at the level of the bound — the CQ purified
distance, at the SAME smoothing radius:
`P(ρE ⊗ const σR, σE ⊗ const σR) ≤ P(ρE, σE)`.

This is the geometric backbone of the smooth CKR ball lift in the special
product-center case (Nahar et al. 2024, Eqs. B16-B17): the `ε`-ball on the marginal `E`
register transports to an `ε`-ball on the joint `E ⊗ R` register when the extension
is the product lift `ρ ⊗ σR`.  The general entangled-center case has no
statement in this package.

Proof: by CQ-tensor purified-distance subadditivity
(`InfoTheory.SmoothMinEntropy.CQState.tensor_purifiedDistance_subadditive`, Tomamichel 2016 eq.
3.41) and
`P(const σR, const σR) = 0` (`CQState.purifiedDistance_self_zero`). -/
theorem CQState.purifiedDistance_tensorRight_contract_sameRadius
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {dE dR : ℕ} [NeZero dE] [NeZero dR]
    (ρE σE : CQState X dE) (σR : DensityOp dR) :
    CQState.purifiedDistance (ρE.tensor (CQState.const σR))
        (σE.tensor (CQState.const σR)) ≤
      CQState.purifiedDistance ρE σE := by
  haveI : NeZero (dE * dR) := ⟨Nat.mul_ne_zero (NeZero.ne dE) (NeZero.ne dR)⟩
  have hsub :
      CQState.purifiedDistance (ρE.tensor (CQState.const σR))
          (σE.tensor (CQState.const σR)) ≤
        CQState.purifiedDistance ρE σE +
          CQState.purifiedDistance (CQState.const σR) (CQState.const σR) :=
    InfoTheory.SmoothMinEntropy.CQState.tensor_purifiedDistance_subadditive ρE σE
      (CQState.const σR) (CQState.const σR)
  rwa [CQState.purifiedDistance_self_zero, add_zero] at hsub

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
