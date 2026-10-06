import QCryptLean.Quantum.Symmetry.BellDickeCore

/-!
# Bell de Finetti — the Bell joint de Finetti Haar-integral representation

Part of the Bell reference/floor construction (with `BellPairedDeFinetti.lean`,
`BellDickeCore.lean`): the Bell joint de Finetti mixture as the `W`-pushed IID Haar integral.
Protocol-independent (no BB84 or QKD-protocol object beyond the pure scalar dimension
`bb84PolyDimTight`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Engine

noncomputable section

namespace Quantum.Symmetry

/-! ## The Bell joint de Finetti state as the `W`-pushed IID Haar integral

(Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 `arXiv:2403.11851` Lemma 2, `x = 4`, joint Bell
`ℤ₂×ℤ₂` symmetry.) -/

section BellJointHaarIntegral

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-- **The Haar moment of the `n`-fold tensor power** — the Bochner integral, over Haar-random
single-pair pure states `φ : DensityOp 4`, of the bare tensor power `φ^{⊗n}` equals the symmetric
de Finetti state `deFinettiState 4 n`.  (`∫ φ^{⊗n} ∂Haar = deFinettiState 4 n`, entrywise via
`deFinettiState_eq_haar_integral` + `matrix_integral_entry` + `integralTensorPower_toOp_apply`.)
Named extraction of the inline `hdf` step of `bb84BellPairedDeFinettiState_eq_haar_integral`. -/
theorem bb84_haarMoment_tensorPow (n : ℕ) [NeZero n] [NeZero (4 ^ n)] :
    (∫ φ : DensityOp 4, (φ.tensorPowGen n).toOp ∂(deFinetti_haarMeasure 4).measure)
      = (deFinettiState 4 n).toOp := by
  rw [deFinettiState_eq_haar_integral 4 n, integralTensorPower_toOp_eq_integral]

/-- **The Bell joint de Finetti mixture as the `W`-pushed IID Haar integral**
(Nahar et al. 2024 `arXiv:2403.11851` Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry).

The type-coherent finite-sum joint state `bb84BellPairedDeFinettiState n` equals the Bochner
integral, over Haar-random single-pair pure states `φ : DensityOp 4`, of the interleaved tensor
power of the Bell-doubled state `bellWembed φ = W·φ·Wᴴ` (`W = bellDoublingIsometry`).  This is the
IID-integral reconstruction the de Finetti post-filter floor host
(`smoothMinEntropy_subMixture_ge_inf_component`, its `hf_lin` input) reads: the type
components of the finite sum are coherent, but the state equals the genuine IID integral after
folding the fixed Bell-doubling isometry `W = (Vᴴ⊗Vᴴ)·COPY·V` into the integrand.  Mirror at `d = 4`
(with `W`-conjugation) of `pairedDeFinettiState_eq_haar_integral_paired`.

The proof reduces — via the tensor
functoriality `((bellWembed φ).tensorPowGen n).toOp = W^{⊗n}·(φ.tensorPowGen n).toOp·(W^{⊗n})ᴴ`, the
entry-wise `ContinuousLinearMap.integral_comp_comm`, and `deFinettiState_eq_haar_integral 4 n` — to
the exact finite operator identity `bb84BellPairedDeFinettiState_eq_Wconj_symProj`:
`bb84BellPairedDeFinettiStateOp n = rdx(W^{⊗n}·(C(n+3,3)⁻¹•symmetricProjector 4 n)·(W^{⊗n})ᴴ)`. That
identity requires the parametric-in-`n` Dicke decomposition `symmetricProjector 4 n = ∑_T
|D_T⟩⟨D_T|/mult_T` with `τ_T = (C(n+3,3)·mult_T)⁻¹`, plus the rectangular `n`-fold Kronecker power
`bellDoublingIsometryPow` of `bellDoublingIsometry` (a rectangular `tensorFamily`) and its
functoriality, all in `BellDickeCore.lean`.  The marginal-only route via
`bb84BellPairedDeFinettiState_partialTraceB` cannot close this: `partialTraceB(W^{⊗n}·a·(W^{⊗n})ᴴ)`
recovers only the Bell-diagonal of `a`, so the `A`-marginal `τ_Bell` underdetermines the joint
operator.

This identity is upstream of the Bell inner-budget floor construction; the standard (non-Bell)
reference route pays the full `(n+1)^15` prefactor and never reaches the Bell reference. -/
theorem bb84BellPairedDeFinettiState_eq_haar_integral {n : ℕ} [NeZero n] [NeZero (4 ^ n)] :
    (bb84BellPairedDeFinettiState n).toOp =
      ∫ φ : DensityOp 4,
        (densityOp_reindex (interleavingEquiv 4 n).symm
          ((bellWembed φ).tensorPowGen n)).toOp
        ∂(deFinetti_haarMeasure 4).measure := by
  have : MeasureTheory.IsProbabilityMeasure (deFinetti_haarMeasure 4).measure :=
    (deFinetti_haarMeasure 4).isProbability
  -- The fixed ℂ-linear `W`-conjugation-then-reindex map pulled out of the Bochner integral.
  let L : Op (4 ^ n) →L[ℂ] Op (4 ^ n * 4 ^ n) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M =>
          Matrix.reindex (interleavingEquiv 4 n).symm (interleavingEquiv 4 n).symm
            (bellDoublingIsometryPow n * M * (bellDoublingIsometryPow n)ᴴ)
        map_add' := by
          intro M N
          ext i j
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
            Matrix.add_apply]
        map_smul' := by
          intro c M
          ext i j
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.reindex_apply,
            Matrix.submatrix_apply, Matrix.smul_apply, RingHom.id_apply] }
  -- Matrix-valued integrability of the bare tensor power against the Haar de Finetti measure.
  have htint : MeasureTheory.Integrable
      (fun φ : DensityOp 4 => (φ.tensorPowGen n).toOp) (deFinetti_haarMeasure 4).measure :=
    continuous_tensorPowGen_toOp.integrable_of_compactSpace
  -- The integrand is `L` applied to the bare tensor power (tensor functoriality of `Wembed`).
  have hintegrand : ∀ φ : DensityOp 4,
      (densityOp_reindex (interleavingEquiv 4 n).symm
          ((bellWembed φ).tensorPowGen n)).toOp = L ((φ.tensorPowGen n).toOp) := by
    intro φ
    change Matrix.reindex (interleavingEquiv 4 n).symm (interleavingEquiv 4 n).symm
        ((bellWembed φ).tensorPowGen n).toOp = _
    rw [bellWembed_tensorPow_eq_Wconj]
    rfl
  -- The bare Haar integral of the tensor power is the symmetric de Finetti state.
  have hdf : (∫ φ : DensityOp 4, (φ.tensorPowGen n).toOp ∂(deFinetti_haarMeasure 4).measure)
      = (deFinettiState 4 n).toOp := bb84_haarMoment_tensorPow n
  -- `deFinettiState 4 n = C(n+3,3)⁻¹ • symProj`.
  have hdef : (deFinettiState 4 n).toOp
      = (bb84PolyDimTight n : ℂ)⁻¹ • symmetricProjector 4 n := by
    have h0 : (deFinettiState 4 n).toOp
        = (1 / (symmetricProjector 4 n).trace) • symmetricProjector 4 n := rfl
    rw [h0, symmetricProjector_four_trace, one_div, bb84PolyDimTight]
  calc (bb84BellPairedDeFinettiState n).toOp
         = Matrix.reindex (interleavingEquiv 4 n).symm (interleavingEquiv 4 n).symm
          (bellDoublingIsometryPow n * ((bb84PolyDimTight n : ℂ)⁻¹ • symmetricProjector 4 n)
            * (bellDoublingIsometryPow n)ᴴ) := bb84BellPairedDeFinettiState_eq_Wconj_symProj n
    _ = L ((deFinettiState 4 n).toOp) := by rw [hdef]; rfl
    _ = L (∫ φ : DensityOp 4, (φ.tensorPowGen n).toOp ∂(deFinetti_haarMeasure 4).measure) := by
        rw [hdf]
    _ = ∫ φ : DensityOp 4, L ((φ.tensorPowGen n).toOp) ∂(deFinetti_haarMeasure 4).measure :=
        (L.integral_comp_comm htint).symm
    _ = ∫ φ : DensityOp 4,
          (densityOp_reindex (interleavingEquiv 4 n).symm
            ((bellWembed φ).tensorPowGen n)).toOp ∂(deFinetti_haarMeasure 4).measure := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun φ => ?_))
        exact (hintegrand φ).symm

/-! ## The Bell integral-representation clones of the CKR post-filter floor inputs

(Nahar et al. 2024 `arXiv:2403.11851` Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry.)  The
per-σ-family block continuity / integrability lemmas built on this Haar-integral representation are
protocol-specific and stay in the engine (`QKD/BB84/Engine/EntropyFloor/BellFloorChain.lean`). -/

end BellJointHaarIntegral

end Quantum.Symmetry

end -- noncomputable section
