import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.InfoTheory.DistanceBounds.Basic

/-!
# Composable Security (Renner 2005 form)

`IsComposableSecure` encodes Renner's composable security definition
(Renner 2005, PhD thesis, Def. 6.1.1): a joint key-Eve density operator
`ρ_KE` is `ε`-composable-secure if

    ½ · ‖ρ_KE − π_K ⊗ ρ_E‖₁ ≤ ε

where `π_K` is the maximally mixed state on the key register and `ρ_E`
is Eve's marginal. The factor of ½ follows the convention of
`Quantum.Metrics.traceDistance := ½ · traceNorm`, which matches
Renner–Koenig (arXiv:quant-ph/0403133, Def. 1 and Thm. 4.1). Renner's
thesis uses the full L1 norm `‖ρ_AB − ρ_U ⊗ ρ_B‖₁` (Def. 5.2.1); our
bound is consistent with Renner Cor. 5.6.1 under that rescaling.

This file is scoped to the density-operator-level security definition:
the predicate `IsComposableSecure` and two elementary lemmas about it
(`zero_iff`, `mono`). The full BB84 composable-security reduction is
assembled elsewhere in this library.

## References
- Renner (2005) PhD thesis, arXiv:quant-ph/0512258, Def. 6.1.1
- Renner–Koenig (2005), arXiv:quant-ph/0403133
-/

open Quantum.Operators Quantum.Metrics
open scoped Matrix

noncomputable section

namespace InfoTheory.Security

/-- **Renner composable security** (Renner 2005, Def. 6.1.1).

    A joint key-Eve density operator `ρ_KE` on `keyDim * eveDim` is
    `ε`-composable-secure if its trace distance to the ideal key-Eve state
    `π_K ⊗ ρ_E` is at most `ε`, where `π_K` is the maximally mixed state
    on the key register and `ρ_E` is the Eve marginal.

    This is the standard composable security definition used throughout
    modern QKD analysis. It captures the universally composable notion:
    the key is indistinguishable from uniformly random and independent of
    Eve's side information up to ε in trace distance. -/
def IsComposableSecure {keyDim eveDim : ℕ} [NeZero keyDim] [NeZero eveDim]
    (ρ_KE : DensityOp (keyDim * eveDim)) (ρ_E : DensityOp eveDim) (ε : ℝ) : Prop :=
  traceDistance ρ_KE.toOp
    ((DensityOp.maxMixed keyDim).tensor ρ_E).toOp ≤ ε

/-- Composable security with ε = 0 means the real key-Eve state equals the
    ideal one: the key is exactly uniform and exactly independent of Eve. -/
lemma IsComposableSecure.zero_iff {keyDim eveDim : ℕ}
    [NeZero keyDim] [NeZero eveDim]
    (ρ_KE : DensityOp (keyDim * eveDim)) (ρ_E : DensityOp eveDim) :
    IsComposableSecure ρ_KE ρ_E 0 ↔
      ρ_KE = (DensityOp.maxMixed keyDim).tensor ρ_E := by
  unfold IsComposableSecure
  constructor
  · intro h
    have h_nonneg : 0 ≤ traceDistance ρ_KE.toOp
        ((DensityOp.maxMixed keyDim).tensor ρ_E).toOp :=
      traceDistance_nonneg _ _
    have h_eq : traceDistance ρ_KE.toOp
        ((DensityOp.maxMixed keyDim).tensor ρ_E).toOp = 0 :=
      le_antisymm h h_nonneg
    exact (traceDistance_eq_zero_iff _ _).mp h_eq
  · intro h
    exact le_of_eq ((traceDistance_eq_zero_iff ρ_KE _).mpr h)

/-- Composable security is monotone in ε. -/
lemma IsComposableSecure.mono {keyDim eveDim : ℕ}
    [NeZero keyDim] [NeZero eveDim]
    {ρ_KE : DensityOp (keyDim * eveDim)} {ρ_E : DensityOp eveDim} {ε ε' : ℝ}
    (h : IsComposableSecure ρ_KE ρ_E ε) (hle : ε ≤ ε') :
    IsComposableSecure ρ_KE ρ_E ε' :=
  le_trans h hle

/-- **Abort-aware (weighted) composable security.**

    The accept-branch key–Eve state `ρ_KE` is `(p_acc, ε)`-abort-aware-composable-secure if its
    trace distance to the ideal key-Eve state `π_K ⊗ ρ_E`, **weighted by the acceptance probability
    `p_acc`**, is at most `ε`:

      `p_acc · ½‖ρ_KE − π_K ⊗ ρ_E‖₁ ≤ ε` .

    This is the composable figure of merit for a protocol with an abort event: the secrecy defect
    only matters on the accepted branch, so it is charged at weight `p_acc = Pr[accept]`. Setting
    `p_acc = 1` recovers `IsComposableSecure` (`IsAbortAwareComposableSecure_of_composable`). It is
    the shape that lets a large per-branch smoothing radius `ε_smooth = ε₀/√p_acc` cancel against
    the `p_acc` weight: `p_acc · (a + b/√p_acc) = p_acc·a + √p_acc·b`. -/
def IsAbortAwareComposableSecure {keyDim eveDim : ℕ} [NeZero keyDim] [NeZero eveDim]
    (ρ_KE : DensityOp (keyDim * eveDim)) (ρ_E : DensityOp eveDim) (p_acc ε : ℝ) : Prop :=
  p_acc * traceDistance ρ_KE.toOp
    ((DensityOp.maxMixed keyDim).tensor ρ_E).toOp ≤ ε

/-- Ordinary composable security at budget `ε` is abort-aware composable security at acceptance
    weight `p_acc = 1` and the same budget: the acceptance weight drops out and the two notions
    coincide. -/
lemma IsAbortAwareComposableSecure_of_composable {keyDim eveDim : ℕ}
    [NeZero keyDim] [NeZero eveDim]
    {ρ_KE : DensityOp (keyDim * eveDim)} {ρ_E : DensityOp eveDim} {ε : ℝ}
    (h : IsComposableSecure ρ_KE ρ_E ε) :
    IsAbortAwareComposableSecure ρ_KE ρ_E 1 ε := by
  unfold IsAbortAwareComposableSecure
  rw [one_mul]
  exact h

/-- If the acceptance probability is itself below the budget, `p_acc ≤ ε`, then abort-aware
    composable security holds unconditionally at that budget: the weighted trace distance is at most
    `p_acc · 1 = p_acc ≤ ε`, since trace distance between density operators never exceeds `1`
    (`traceDistance_le_one`). This is the trivial floor of the abort-aware bound (a rarely-accepting
    protocol is secure regardless of the branch state). -/
lemma IsAbortAwareComposableSecure_of_pacc_le {keyDim eveDim : ℕ}
    [NeZero keyDim] [NeZero eveDim]
    {ρ_KE : DensityOp (keyDim * eveDim)} {ρ_E : DensityOp eveDim} {p_acc ε : ℝ}
    (hp_acc : 0 ≤ p_acc) (h : p_acc ≤ ε) :
    IsAbortAwareComposableSecure ρ_KE ρ_E p_acc ε := by
  unfold IsAbortAwareComposableSecure
  calc p_acc * traceDistance ρ_KE.toOp ((DensityOp.maxMixed keyDim).tensor ρ_E).toOp
      ≤ p_acc * 1 :=
        mul_le_mul_of_nonneg_left (traceDistance_le_one _ _) hp_acc
    _ = p_acc := mul_one p_acc
    _ ≤ ε := h

end InfoTheory.Security

end
