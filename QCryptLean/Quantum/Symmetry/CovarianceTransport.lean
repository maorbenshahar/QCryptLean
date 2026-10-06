import QCryptLean.Quantum.Symmetry.Covariance
import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.Channels.CPTP.PureStateExtension
import QCryptLean.Quantum.TensorProducts.Basic

/-!
# Transport of `PermutationCovariant` along a fixed dimension cast

The register-generic cast-transport primitive: `permutationCovariant_castDimLinear_comp`, stated
directly on `PermutationCovariant`.
-/

open Quantum.Operators Quantum.Channels
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Symmetry

/-- **A cast along a fixed output relabeling transports `PermutationCovariant`.** If `Δ` is
    permutation covariant with a `π`-family of CPTP corrections `K_π`, then so is
    `(Op.castDimLinear h).comp Δ`, with corrections `X ↦ Op.castDim h (K_π (Op.castDim h.symm X))`.
-/
theorem permutationCovariant_castDimLinear_comp {d n m m' : ℕ} [NeZero d] [NeZero n]
    [NeZero m] [NeZero m'] (h : m = m') {Δ : Op (d ^ n) →ₗ[ℂ] Op m}
    (hΔ : PermutationCovariant Δ) :
    PermutationCovariant ((Op.castDimLinear h).comp Δ) := by
  refine ⟨fun π => ?_⟩
  obtain ⟨K, hK, hInt⟩ := hΔ.covariance π
  refine ⟨fun opv => Op.castDim h (K (Op.castDim h.symm opv)), ?_, ?_⟩
  · have hcomp := cptp_comp (⇑(Op.castDimLinear h))
      (fun opv : Op m' => K (Op.castDim h.symm opv))
      (castDimLinear_isCPTP h)
      (cptp_comp K (⇑(Op.castDimLinear h.symm)) hK (castDimLinear_isCPTP h.symm))
    simpa [Function.comp, Op.castDimLinear] using hcomp
  · intro ρ
    simp only [LinearMap.comp_apply, Op.castDimLinear, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hInt ρ]
    subst h; rfl

end Quantum.Symmetry

end
