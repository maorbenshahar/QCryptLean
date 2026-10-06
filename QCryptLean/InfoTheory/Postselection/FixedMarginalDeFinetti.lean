import QCryptLean.Quantum.Operators.MatrixIntegral
import QCryptLean.Quantum.TensorProducts.Rpow
import QCryptLean.Quantum.TensorProducts.ReferenceTransport
import QCryptLean.InfoTheory.Postselection.Mixture
import QCryptLean.InfoTheory.DeFinetti.DeFinettiPrefactor
import QCryptLean.InfoTheory.Postselection.SchurWeylTwirl
import QCryptLean.InfoTheory.Postselection.SchurWeylTwirlProjection
import QCryptLean.InfoTheory.Postselection.PairedBlockedTransport
import QCryptLean.InfoTheory.Postselection.PairedBlockedOperators
import QCryptLean.InfoTheory.Postselection.FixedMarginalHaarMeasure
import QCryptLean.InfoTheory.DeFinetti.Theorem.UnequalInterleaving
import QCryptLean.Quantum.Operators.OpGeoMean

/-!
# The fixed-marginal de Finetti operator inequality

`roundwiseAliceMarginal` expresses the Alice marginal after regrouping the round indices.
`fixedMarginalMeasure_twirl_identity` identifies the fixed-marginal twirl reference.
`deFinetti_fixedMarginal_purified_op_le` proves the purified operator bound, and
`deFinetti_fixedMarginal_op_le` obtains the mixed-state inequality by partial trace.

The bound keeps Alice's marginal equal to `σA.tensorPowGen n`, with the explicit full-rank
assumption `σA.toOp.PosDef`. It uses Schur–Weyl flattening and a symmetric purification.
The resulting measure is the reference for
`permInvariant_postselection_security_of_referenceBound`.

References: Nahar et al., arXiv:2403.11851, `cor:generalMixedDeFinetti` (main.tex:263–268),
Theorem 1 and Appendix A; the full-rank specialization corresponds to the WLOG step at
main.tex:1097. Symmetric purification follows Renner, quant-ph/0512258, Lemma 4.2.2.
-/

open Equiv

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry
open InfoTheory.DeFinetti MeasureTheory Math.HaarMeasure
open scoped ComplexOrder MatrixOrder Matrix

noncomputable section

namespace InfoTheory.Postselection

/-- **Round-wise Alice marginal** `Tr_{Bⁿ}(ρ)` of a state `ρ` on the round-grouped
    register `(dA·dB)^n`.

    Regroups `ρ` from the interleaved layout `(dA·dB)^n` to the grouped layout
    `dA^n · dB^n` via `roundGroupEquiv`, then traces out the `B^n` block with
    `DensityOp.partialTraceB`. The result is a `DensityOp (dA^n)`.

    This traces out **every** `Bᵢ` round (Nahar et al.'s `Tr_{Bⁿ}ρ`), which is *not* the
    plain `DensityOp.partialTraceB ρ` splitting `(dA·dB)^n` as `(dA·dB)^{n−1}⊗(dA·dB)`. -/
def roundwiseAliceMarginal {dA dB n : ℕ} (ρ : DensityOp ((dA * dB) ^ n)) :
    DensityOp (dA ^ n) :=
  DensityOp.partialTraceB (densityOp_reindex (roundGroupEquiv dA dB n) ρ)

/-- `dA ≤ dA·dB²`, the load-bearing dimension inequality `dA ≤ dR` for the Nahar et al.
    purifying register `dR = dA·dB²`. -/
private lemma dA_le_dA_mul_dBsq (dA dB : ℕ) [NeZero dB] : dA ≤ dA * dB ^ 2 := by
  have h1 : 1 ≤ dB ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (NeZero.ne dB))
  calc dA = dA * 1 := (mul_one dA).symm
    _ ≤ dA * dB ^ 2 := by gcongr

/-- **Nahar et al.'s fixed-marginal de Finetti reference** in closed operator form
    (Nahar et al. Thm 1 proof line 1644):

    `τ_ABE := (σ̂A^{⊗n} ⊗ id_{Rⁿ})^{1/2} · Tₙ · (σ̂A^{⊗n} ⊗ id_{Rⁿ})^{1/2}`

    on the blocked register `Aⁿ ⊗ Rⁿ` (`dR = dA·dB²`), where `Tₙ` is the Schur–Weyl
    Haar twirl (`maxEntangledUnitaryTwirl`) and the square root is the CFC square root.
    This is an explicit construction (no `Classical.choose`, no `sorry`): the reference
    de Finetti state before tracing out the purifying register `Eⁿ`. -/
def fixedMarginalTwirlReference (dA dB n : ℕ) [NeZero dA] [NeZero dB] [NeZero n]
    (σA : DensityOp dA) : Op (dA ^ n * (dA * dB ^ 2) ^ n) :=
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  let S := CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))
  S * maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB) * S

-- Frobenius (Hilbert–Schmidt) normed structure on matrices, matching `SchurWeylTwirl.lean`'s
-- local instances, so the Bochner integral `∫ … ∂(haarProbUnitary dR)` machinery (`twirlMap`,
-- `Integrable`, `ContinuousLinearMap.integral_comp_comm`) is well-typed here too.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-! ### Marginal computation `Tr_{Rⁿ}[Tₙ] = id_{Aⁿ}` and the `σ̂A^{1/2} ⊗ id` distribution

Facts needed for `fixedMarginalMeasure_twirl_identity`'s operator identity. The tensor-power
laws are `Quantum.TensorProducts.Op.tensorPow`'s; the twirl-kernel continuity and integrability
are `twirlKernel_continuous` and `twirlIntegrand_integrable` (`SchurWeylTwirlProjection.lean`).
The `1 ⊗ V` sandwich invariance of `partialTraceB` is
`Quantum.TensorProducts.partialTraceB_one_tensor_sandwich_of_mul_eq_one`
(`Quantum/TensorProducts/ReferenceTransport.lean`). -/

private lemma fmPartialTraceB_kraus_conj_eq_self (dA dR n : ℕ) [NeZero dR]
    (T : Op (dA ^ n * dR ^ n)) (U : Matrix.unitaryGroup (Fin dR) ℂ) :
    partialTraceB (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n) * T *
      (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))ᴴ) = partialTraceB T := by
  rw [Op.tensor_conjTranspose, Matrix.conjTranspose_one]
  exact partialTraceB_one_tensor_sandwich_of_mul_eq_one _ _
    (Op.conjTranspose_tensorPow_mul_self ((Matrix.mem_unitaryGroup_iff').mp U.2) n) T

/-- `partialTraceB` is invariant under `twirlMap` (tracing out `Rⁿ` commutes with the Haar
twirl, since tracing `Rⁿ` is invariant under any unitary conjugation of `Rⁿ`, and the Haar
probability measure has total mass `1`). -/
private lemma fmPartialTraceB_twirlMap_eq (dA dR n : ℕ) [NeZero dR]
    (T : Op (dA ^ n * dR ^ n)) :
    partialTraceB (twirlMap dA dR n T) = partialTraceB T := by
  haveI : MeasureTheory.IsProbabilityMeasure (haarProbUnitary dR) :=
    haarProbUnitary_isProbability dR
  rw [twirlMap, partialTraceB_integral _ (twirlIntegrand_integrable dA dR n T)]
  simp_rw [fmPartialTraceB_kraus_conj_eq_self]
  simp

/-- **`Tr_{Rⁿ}[Tₙ] = id_{Aⁿ}`.** The Haar twirl of the maximally entangled projector has
trivial `Rⁿ`-marginal: `Tₙ = twirlMap Θₙ`, `partialTraceB` is `twirlMap`-invariant
(`fmPartialTraceB_twirlMap_eq`), and `Tr_{Rⁿ}[Θₙ] = id_{Aⁿ}`
(`maxEntangledProjectorPaired_partialTraceB_eq_one`). -/
private lemma fmPartialTraceB_maxEntangledUnitaryTwirl_eq_one (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    partialTraceB (maxEntangledUnitaryTwirl dA dR n hdim) = (1 : Op (dA ^ n)) := by
    rw [twirlMap_maxEntangledProjectorPaired dA dR n hdim, fmPartialTraceB_twirlMap_eq,
    maxEntangledProjectorPaired_partialTraceB_eq_one]

/-- **The fixed-marginal identity, proven with a trivial witness measure** (cf. Nahar et al. Thm 1
    proof lines 1628–1645, which additionally identifies `μ` with the pushforward of the Haar
    measure on `U(dR)` — see the "What this lemma does NOT establish" note below).

    Proves two logically decoupled conjuncts:
    - an operator identity that does not mention `μ` at all,

      `Tr_{Rⁿ}[(σ̂A^{⊗n}⊗id)^{1/2} Tₙ (σ̂A^{⊗n}⊗id)^{1/2}] = σ̂A^{⊗n}`,

      the operator form of the "extensions `σ_AB` of `σ̂A`" condition (the marginal is
      fixed because `Tr_{Rⁿ} Tₙ = id_{Aⁿ}`, `|θ⟩` being maximally entangled on the
      `dA`-diagonal, so the `σ̂A^{1/2}`-conjugation restores `σ̂A^{⊗n}`); it holds for every density
      operator `σ̂A` — full rank is not needed, since `(σ̂A^{⊗n}⊗id)^{1/2}` enters only through
      `√P·√P = P`;
    - the existential `∃ μ, IsFixedMarginalMeasure σA μ`, witnessed here **trivially** by the Dirac
      measure at the product extension `σ̂A ⊗ I/dB` — not by Nahar et al.'s intended construction.

    **What this lemma does NOT establish.** Nahar et al.'s own reference measure `μ` is the
    pushforward of the Haar measure on `U(dR)` (`dR = dA·dB²`) under `U ↦ Tr_E |ϕ_U⟩⟨ϕ_U|`,
    `|ϕ_U⟩ = (σ̂A^{1/2} ⊗ U)|θ⟩`; that is the measure `fixedMarginalHaarMeasure` constructs, and
    `fmTwirlReference_reindex_partialTraceB_eq` below is the stronger fact relating *it* to the
    de Finetti mixture. This lemma's `∃ μ` conjunct is satisfied without needing that construction,
    since the operator identity above holds independently of which fixed-marginal `μ` is supplied —
    it is not a claim that the Dirac witness recovers Nahar et al.'s Haar-pushforward measure. -/
theorem fixedMarginalMeasure_twirl_identity {dA dB n : ℕ}
    [NeZero dA] [NeZero dB] [NeZero n]
    (σA : DensityOp dA) :
    ∃ μ : DensityMeasure (dA * dB), IsFixedMarginalMeasure σA μ ∧
      partialTraceB (fixedMarginalTwirlReference dA dB n σA) = (σA.tensorPowGen n).toOp := by
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  -- The two conjuncts are logically decoupled: the operator identity below never mentions
  -- `μ`, so any `μ` satisfying `IsFixedMarginalMeasure σA μ` discharges the first conjunct.
  -- The trivial witness: the Dirac measure at the product extension `σA ⊗ (maxMixed dB)`.
  refine ⟨⟨MeasureTheory.Measure.dirac (σA.tensor (DensityOp.maxMixed dB)), inferInstance⟩,
    ?_, ?_⟩
  · -- `IsFixedMarginalMeasure σA μ`
    have hmarg : DensityOp.partialTraceB (σA.tensor (DensityOp.maxMixed dB)) = σA :=
      DensityOp.ext (partialTraceB_tensor σA (DensityOp.maxMixed dB))
    haveI hT2 : T2Space (DensityOp dA) :=
      Topology.IsEmbedding.t2Space ⟨⟨rfl⟩, fun _ _ h => DensityOp.ext h⟩
    have hp : MeasurableSet
        (DensityOp.partialTraceB ⁻¹' ({σA} : Set (DensityOp dA)) : Set (DensityOp (dA * dB))) :=
      partialTraceB_measurable_general (measurableSet_singleton σA)
    exact (MeasureTheory.ae_dirac_iff hp).mpr hmarg
  · -- the operator identity `Tr_{Rⁿ}[fixedMarginalTwirlReference] = σ̂A^{⊗n}`
    unfold fixedMarginalTwirlReference
    set P : Op (dA ^ n) := (σA.tensorPowGen n).toOp with hP_def
    have hP_psd : P.PosSemidef := posSemidefOp_implies_mathlib (σA.tensorPowGen n).toPosSemidefOp
    have hS : CFC.sqrt (Op.tensor P (1 : Op ((dA * dB ^ 2) ^ n))) =
        Op.tensor (CFC.sqrt P) (1 : Op ((dA * dB ^ 2) ^ n)) :=
      Op.tensorRightOne_sqrt P hP_psd
    rw [hS,
      show Op.tensor (CFC.sqrt P) (1 : Op ((dA * dB ^ 2) ^ n)) *
          maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB) *
          Op.tensor (CFC.sqrt P) (1 : Op ((dA * dB ^ 2) ^ n)) =
        Op.tensor (CFC.sqrt P) (1 : Op ((dA * dB ^ 2) ^ n)) *
          maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB) *
          Op.tensor (CFC.sqrt P) (1 : Op ((dA * dB ^ 2) ^ n))
        from rfl,
      partialTraceB_sandwich_tensor_one (CFC.sqrt P) (CFC.sqrt P)
        (maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)),
      fmPartialTraceB_maxEntangledUnitaryTwirl_eq_one dA (dA * dB ^ 2) n
        (dA_le_dA_mul_dBsq dA dB),
      Matrix.mul_one, CFC.sqrt_mul_sqrt_self P (Matrix.nonneg_iff_posSemidef.mpr hP_psd)]

/-! ### condB (Stage 1): `Tr_{Eⁿ}[τ] = ∫ σ_AB(U)^{⊗n} dHaar`

The per-`U` marginal identity, with orientations pinned. -/

/-- `CFC.sqrt` distributes over `⊗` for PSD arguments (generalizing `Op.tensorRightOne_sqrt`). -/
private lemma fmCfcSqrt_tensor {n m : ℕ} (A : Op n) (B : Op m)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (Op.tensor A B) = Op.tensor (CFC.sqrt A) (CFC.sqrt B) := by
  -- Uniqueness of the PSD square root: `√A ⊗ √B ⪰ 0` squares to `A ⊗ B`.
  refine CFC.sqrt_unique ?_ (Matrix.nonneg_iff_posSemidef.mpr
    (Quantum.TensorProducts.Op.tensor_posSemidef_mathlib
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))))
  rw [Op.tensor_mul, CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA),
    CFC.sqrt_mul_sqrt_self B (Matrix.nonneg_iff_posSemidef.mpr hB)]

/-- `CFC.sqrt` commutes with a numeric dimension cast. -/
private lemma fmCfcSqrt_castDim {n m : ℕ} (h : n = m) (A : Op n) :
    CFC.sqrt (Op.castDim h A) = Op.castDim h (CFC.sqrt A) := by
  subst h; rfl

/-- **SQRTPOW.** `CFC.sqrt (σA^{⊗n}).toOp = (√σA)^{⊗n}`. -/
private lemma fmCfcSqrt_tensorPowGen {dA : ℕ} [NeZero dA]
    (σA : DensityOp dA) (n : ℕ) :
    CFC.sqrt (σA.tensorPowGen n).toOp = Op.tensorPow (CFC.sqrt σA.toOp) n := by
  have hσ_psd : σA.toOp.PosSemidef := posSemidefOp_implies_mathlib σA.toPosSemidefOp
  rw [DensityOp.tensorPowGen_toOp]
  induction n with
  | zero => simpa only [Op.tensorPow_zero] using CFC.sqrt_one
  | succ k ih =>
      rw [Op.tensorPow_succ, Op.tensorPow_succ, fmCfcSqrt_castDim,
        fmCfcSqrt_tensor σA.toOp _ hσ_psd (hσ_psd.tensorPow k), ih]

/-! The relabelling composition and round-trip laws used below are `Matrix.reindex_trans_apply`,
`Matrix.reindex_symm_reindex` and `Matrix.reindex_reindex_symm` in the Quantum.Matrix.Reindex
module. -/

private lemma fmTheta1_cond_iff {dA dR : ℕ} [NeZero dA] [NeZero dR] (hdim : dA ≤ dR)
    (p : Fin (dA * dR)) :
    ((finProdFinEquiv.symm (Fin.cast (by rw [pow_one, pow_one] : dA * dR = dA ^ 1 * dR ^ 1) p)).2 =
        finFunctionFinEquiv fun j => Fin.castLE hdim
          (finFunctionFinEquiv.symm
            (finProdFinEquiv.symm
              (Fin.cast (by rw [pow_one, pow_one] : dA * dR = dA ^ 1 * dR ^ 1) p)).1 j))
      ↔ (finProdFinEquiv.symm p).2 = Fin.castLE hdim (finProdFinEquiv.symm p).1 := by
  rw [Fin.ext_iff, Fin.ext_iff]
  simp only [finProdFinEquiv, Equiv.coe_fn_symm_mk, Fin.coe_modNat, Fin.coe_divNat, Fin.val_cast,
    Fin.val_castLE, finFunctionFinEquiv_apply_val, finFunctionFinEquiv_symm_apply_val,
    Fin.sum_univ_one, Fin.val_zero, pow_zero, pow_one, Nat.div_one, mul_one]
  have hlt : (p : ℕ) / dR < dA := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm dR dA]; exact p.isLt)
  rw [Nat.mod_eq_of_lt hlt]

/-- **Θ₁' entry formula.** The `n = 1` maximally entangled projector, cast to `Op (dA*dR)`,
    is the rank-one paired-diagonal indicator in `finProdFinEquiv` coordinates. -/
private lemma fmTheta1_apply {dA dR : ℕ} [NeZero dA] [NeZero dR] (hdim : dA ≤ dR)
    (p q : Fin (dA * dR)) :
    (Op.castDim (by rw [pow_one, pow_one] : dA ^ 1 * dR ^ 1 = dA * dR)
        (maxEntangledProjectorPaired dA dR 1 hdim)) p q
      = (if (finProdFinEquiv.symm p).2 = Fin.castLE hdim (finProdFinEquiv.symm p).1
            then (1 : ℂ) else 0)
        * (starRingEnd ℂ) (if (finProdFinEquiv.symm q).2 = Fin.castLE hdim (finProdFinEquiv.symm
            q).1
            then 1 else 0) := by
  rw [Op.castDim_apply]
  simp only [maxEntangledProjectorPaired, Matrix.of_apply]
  rw [if_congr (fmTheta1_cond_iff hdim p) rfl rfl, if_congr (fmTheta1_cond_iff hdim q) rfl rfl]

/-- **THPOW.** `Θₙ` is the interleave-transport of `Θ₁'^{⊗n}` (orientation
    pinned to the `ie.symm` side). -/
private lemma fmMaxEntangledProjectorPaired_eq_reindex_tensorPow {dA dR n : ℕ}
    [NeZero dA] [NeZero dR] (hdim : dA ≤ dR) :
    maxEntangledProjectorPaired dA dR n hdim
      = Matrix.reindex (interleavingEquivGen dA dR n).symm (interleavingEquivGen dA dR n).symm
          (Op.tensorPow (Op.castDim (by rw [pow_one, pow_one] : dA ^ 1 * dR ^ 1 = dA * dR)
            (maxEntangledProjectorPaired dA dR 1 hdim)) n) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Op.tensorPow_apply]
  simp_rw [fmTheta1_apply]
  rw [Finset.prod_mul_distrib, ← map_prod]
  -- reduce the two factors to the blocked emb-indicators
  have key : ∀ x : Fin (dA ^ n * dR ^ n),
      (∏ k : Fin n, (if (finProdFinEquiv.symm
              ((@finFunctionFinEquiv (dA * dR) n).symm
                (interleavingEquivGen dA dR n x) k)).2 =
            Fin.castLE hdim (finProdFinEquiv.symm
              ((@finFunctionFinEquiv (dA * dR) n).symm
                (interleavingEquivGen dA dR n x) k)).1 then (1 : ℂ) else 0))
        = (if (finProdFinEquiv.symm x).2 =
              finFunctionFinEquiv (fun j => Fin.castLE hdim
                (finFunctionFinEquiv.symm (finProdFinEquiv.symm x).1 j)) then (1 : ℂ) else 0) := by
    intro x
    simp_rw [← interleavingEquivGen_digit_fst (dA := dA) (dR := dR) (n := n)
        (interleavingEquivGen dA dR n x),
      ← interleavingEquivGen_digit_snd (dA := dA) (dR := dR) (n := n)
        (interleavingEquivGen dA dR n x),
      Equiv.symm_apply_apply]
    rw [Finset.prod_boole]
    congr 1
    apply propext
    simp only [Finset.mem_univ, forall_true_left]
    constructor
    · intro h
      apply finFunctionFinEquiv.symm.injective
      funext k
      rw [Equiv.symm_apply_apply]
      exact h k
    · intro h k
      have h2 := congrArg finFunctionFinEquiv.symm h
      rw [Equiv.symm_apply_apply] at h2
      exact congrFun h2 k
  rw [key i, key j]
  simp only [maxEntangledProjectorPaired, Matrix.of_apply]

/-- **REG.** The `.symm` form of REG: the blocked tensor product is the interleave-transport
    of the interleaved single-round tensor power (constant case of
    `tensorFamily_tensor_interleaving`). -/
private lemma fmReg_symm {dA dR n : ℕ} [NeZero dA] [NeZero dR] (V : Op dA) (W : Op dR) :
    Op.tensor (Op.tensorPow V n) (Op.tensorPow W n)
      = Matrix.reindex (interleavingEquivGen dA dR n).symm (interleavingEquivGen dA dR n).symm
          (Op.tensorPow (Op.tensor V W) n) := by
  simpa only [Op.tensorPow_eq_tensorFamily] using
    (tensorFamily_tensor_interleaving (n := n) (fun _ => V) (fun _ => W)).symm

/-- `reindex e.symm e.symm` is multiplicative (via `reindexAlgEquiv`). -/
private lemma fmReindex_symm_mul {N M : ℕ} (e : Fin N ≃ Fin M) (A B : Op N) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B := by
  have := Matrix.reindexAlgEquiv_mul ℂ ℂ e A B
  simpa only [Matrix.reindexAlgEquiv_apply] using this

/-- **PERU.** The per-`U` marginal identity: tracing out `Eⁿ` from the
    interleave-transport of the twirl integrand gives `σ_AB(U)^{⊗n}`. -/
private lemma perU_marginal_traceE_eq (dA dB n : ℕ) [NeZero dA] [NeZero dB] [NeZero n]
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ) :
    partialTraceB (Matrix.reindex (pairedToBlockedEquiv dA dB n).symm
        (pairedToBlockedEquiv dA dB n).symm
        (CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))
          * (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op (dA * dB ^ 2)) n)
              * maxEntangledProjectorPaired dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
              * (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op (dA * dB ^ 2)) n))ᴴ)
          * CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))))
      = ((fixedMarginalSingleRoundState σA hσA U).tensorPowGen n).toOp := by
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  set ie := interleavingEquivGen dA (dA * dB ^ 2) n with hie
  set S := CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n))) with hSdef
  set MU : Op (dA * (dA * dB ^ 2)) := Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) with hMU
  set Θ₁ : Op (dA * (dA * dB ^ 2)) := Op.castDim (by rw [pow_one, pow_one])
    (maxEntangledProjectorPaired dA (dA * dB ^ 2) 1 (dA_le_dA_mul_dBsq dA dB)) with hΘ₁
  set KU : Op (dA ^ n * (dA * dB ^ 2) ^ n) :=
    Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op (dA * dB ^ 2)) n) with hKU
  have hP_psd : (σA.tensorPowGen n).toOp.PosSemidef :=
    posSemidefOp_implies_mathlib (σA.tensorPowGen n).toPosSemidefOp
  have hS : S = Op.tensor (Op.tensorPow (CFC.sqrt σA.toOp) n) (1 : Op ((dA * dB ^ 2) ^ n)) := by
    rw [hSdef, Op.tensorRightOne_sqrt _ hP_psd, fmCfcSqrt_tensorPowGen]
  have hS_herm : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  -- A_U := S * K U in interleave-transport form (REG.symm)
  have hAU : S * KU = Matrix.reindex ie.symm ie.symm (Op.tensorPow MU n) := by
    rw [hS, hKU, Op.tensor_mul, Matrix.mul_one, Matrix.one_mul, hMU, hie, fmReg_symm]
  -- Θₙ in interleave-transport form (THPOW)
  have hΘn : maxEntangledProjectorPaired dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
      = Matrix.reindex ie.symm ie.symm (Op.tensorPow Θ₁ n) := by
    rw [hΘ₁, hie]
    exact fmMaxEntangledProjectorPaired_eq_reindex_tensorPow (dA_le_dA_mul_dBsq dA dB)
  -- the sandwich collapses to a single reindexed tensor power
  have hsandwich : S * (KU * maxEntangledProjectorPaired dA (dA * dB ^ 2) n
        (dA_le_dA_mul_dBsq dA dB) * KUᴴ) * S
      = Matrix.reindex ie.symm ie.symm (Op.tensorPow (MU * Θ₁ * MUᴴ) n) := by
    have e1 : S * (KU * maxEntangledProjectorPaired dA (dA * dB ^ 2) n
          (dA_le_dA_mul_dBsq dA dB) * KUᴴ) * S
        = (S * KU) * maxEntangledProjectorPaired dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
          * (S * KU)ᴴ := by
      rw [Matrix.conjTranspose_mul, hS_herm]
      simp only [Matrix.mul_assoc]
    rw [e1, hAU, hΘn, Matrix.conjTranspose_reindex, Op.conjTranspose_tensorPow,
      ← fmReindex_symm_mul, ← fmReindex_symm_mul, ← Op.mul_tensorPow, ← Op.mul_tensorPow]
  rw [hsandwich]
  -- M_U Θ₁ M_Uᴴ = |ϕ_U⟩⟨ϕ_U| (fixedMarginalPureState_toOp)
  have hpure : MU * Θ₁ * MUᴴ = (fixedMarginalPureState σA hσA U).toOp := by
    rw [hMU, hΘ₁, fixedMarginalPureState_toOp]
  rw [hpure]
  -- ptb.symm decomposition into three reindex layers, then collapse and trace (II.4/II.5)
  have hpb : (dA * dB) * (dA * dB) = dA * (dA * dB ^ 2) := by ring
  have hptb_symm : (pairedToBlockedEquiv dA dB n).symm
      = (interleavingEquivGen dA (dA * dB ^ 2) n).trans
          ((finCongr (congrArg (· ^ n) hpb)).symm.trans
            (interleavingEquivGen (dA * dB) (dA * dB) n).symm) := by
    rw [show pairedToBlockedEquiv dA dB n
        = (interleavingEquivGen (dA * dB) (dA * dB) n).trans
            ((finCongr (congrArg (· ^ n) hpb)).trans
              (interleavingEquivGen dA (dA * dB ^ 2) n).symm) from rfl]
    apply Equiv.ext
    intro x
    simp only [Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm]
  have hfc : ∀ X : Op (dA * (dA * dB ^ 2)),
      Matrix.reindex (finCongr (congrArg (· ^ n) hpb)).symm (finCongr (congrArg (· ^ n) hpb)).symm
          (Op.tensorPow X n) =
        Op.tensorPow (Matrix.reindex (finCongr hpb).symm (finCongr hpb).symm X) n := fun X => by
    simpa only [finCongr_symm] using Op.reindex_finCongr_tensorPow hpb.symm X
  rw [hptb_symm, ← hie, Matrix.reindex_trans_apply, Matrix.reindex_trans_apply,
    Matrix.reindex_reindex_symm, hfc]
  -- the inner operator is now `ψ.toOp` on the paired register (dA·dB)·(dA·dB)
  set ψ := densityOp_reindex (assocEquiv dA dB) (fixedMarginalPureState σA hσA U) with hψ
  have hφeq : Matrix.reindex (finCongr hpb).symm (finCongr hpb).symm
        (fixedMarginalPureState σA hσA U).toOp = ψ.toOp := by
    rw [hψ]
    rfl
  rw [hφeq, ← DensityOp.tensorPowGen_toOp]
  -- II.5: partial trace of the interleaved tensor power (tensorPowerProductEquiv rfl-bridge)
  rw [show (interleavingEquivGen (dA * dB) (dA * dB) n).symm
      = (tensorPowerProductEquiv (dA * dB) (dA * dB) n).symm from rfl]
  have hpt := partialTraceB_tensorPow_reindex (d := dA * dB) (e := dA * dB) (n := n) ψ
  change (densityOp_reindex (tensorPowerProductEquiv (dA * dB) (dA * dB) n).symm
      (ψ.tensorPowGen n)).partialTraceB.toOp = _
  rw [hpt, hψ]
  rfl

/-- `densityOp_reindex e` is continuous (inline re-derivation). -/
private lemma fmDensityOpReindex_continuous {a b : ℕ} (e : Fin a ≃ Fin b) :
    Continuous (densityOp_reindex e : DensityOp a → DensityOp b) := by
  rw [continuous_induced_rng]
  apply continuous_pi; intro i; apply continuous_pi; intro j
  have h_eq : (fun ρ : DensityOp a =>
      ((fun σ : DensityOp b => σ.toOp) ∘ densityOp_reindex e) ρ i j) =
      (fun ρ : DensityOp a => ρ.toOp (e.symm i) (e.symm j)) := by
    ext ρ
    simp only [Function.comp, densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [h_eq]
  exact (continuous_apply (e.symm j)).comp ((continuous_apply (e.symm i)).comp
    continuous_induced_dom)

/-- `fixedMarginalPureState σA hσA` is continuous in `U` (via `fixedMarginalPureState_toOp`). -/
private lemma fmPureState_continuous {dA dB : ℕ} [NeZero dA] [NeZero dB]
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef) :
    Continuous (fixedMarginalPureState σA hσA :
      Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ → DensityOp (dA * (dA * dB ^ 2))) := by
  rw [continuous_induced_rng]
  have hfun : ((fun ρ : DensityOp (dA * (dA * dB ^ 2)) => ρ.toOp) ∘
        (fixedMarginalPureState σA hσA))
      = fun U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ =>
          Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2))
            * Op.castDim (by rw [pow_one, pow_one])
              (maxEntangledProjectorPaired dA (dA * dB ^ 2) 1 (dA_le_dA_mul_dBsq dA dB))
            * (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)))ᴴ := by
    ext U
    exact congrFun₂ (fixedMarginalPureState_toOp σA hσA U) _ _
  rw [hfun]
  have hU : Continuous (fun U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ =>
      (U : Op (dA * dB ^ 2))) := continuous_subtype_val
  have htens : Continuous (fun U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ =>
      Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2))) :=
    Op.continuous_tensor.comp (continuous_const.prodMk hU)
  exact (htens.matrix_mul continuous_const).matrix_mul htens.matrix_conjTranspose

/-- `fixedMarginalSingleRoundState σA hσA` is measurable in `U`. -/
private lemma fmSingleRound_measurable {dA dB : ℕ} [NeZero dA] [NeZero dB]
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef) :
    Measurable (fixedMarginalSingleRoundState σA hσA :
      Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ → DensityOp (dA * dB)) :=
  (partialTraceB_continuous_general.comp
    ((fmDensityOpReindex_continuous (assocEquiv dA dB)).comp
      (fmPureState_continuous σA hσA))).measurable

/-- `U ↦ ((fixedMarginalSingleRoundState σA hσA U).tensorPowGen n).toOp` is continuous. -/
private lemma fmSingleRound_tensorPow_continuous {dA dB n : ℕ} [NeZero dA] [NeZero dB]
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef) :
    Continuous (fun U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ =>
      ((fixedMarginalSingleRoundState σA hσA U).tensorPowGen n).toOp) :=
  (InfoTheory.DeFinetti.continuous_tensorPowGen_toOp (d := dA * dB) (n := n)).comp
    (partialTraceB_continuous_general.comp
      ((fmDensityOpReindex_continuous (assocEquiv dA dB)).comp
        (fmPureState_continuous σA hσA)))

/-- **condB (Stage 1).** `Tr_{Eⁿ}[τ] = ∫ σ_AB(U)^{⊗n} dHaar`, the Nahar et al. Thm 1 marginal
identity
    (App. A, L1628–1645): the `Eⁿ`-marginal of the (paired-transported) fixed-marginal twirl
    reference is the de Finetti mixture at the Haar-pushforward measure `μ`. -/
theorem fmTwirlReference_reindex_partialTraceB_eq {dA dB n : ℕ}
    [NeZero dA] [NeZero dB] [NeZero n]
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef) :
    partialTraceB
        (Matrix.reindex (pairedToBlockedEquiv dA dB n).symm
          (pairedToBlockedEquiv dA dB n).symm
          (fixedMarginalTwirlReference dA dB n σA)) =
      (deFinettiMixtureFixedMarginal dA dB n (fixedMarginalHaarMeasure σA hσA)).toOp := by
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  haveI hprob : MeasureTheory.IsProbabilityMeasure (haarProbUnitary (dA * dB ^ 2)) :=
    haarProbUnitary_isProbability (dA * dB ^ 2)
  set S := CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n))) with hSdef
  set ptb := pairedToBlockedEquiv dA dB n with hptbdef
  -- Φ: the ℝ-linear "conjugate-by-S, reindex to paired, trace out Eⁿ" map, a continuous LM.
  let Φlin : Op (dA ^ n * (dA * dB ^ 2) ^ n) →ₗ[ℝ] Op ((dA * dB) ^ n) :=
    { toFun := fun M => partialTraceB (Matrix.reindex ptb.symm ptb.symm (S * M * S))
      map_add' := by
        intro x y
        rw [show S * (x + y) * S = S * x * S + S * y * S from by
            rw [Matrix.mul_add, Matrix.add_mul]]
        rw [show Matrix.reindex ptb.symm ptb.symm (S * x * S + S * y * S)
            = Matrix.reindex ptb.symm ptb.symm (S * x * S)
              + Matrix.reindex ptb.symm ptb.symm (S * y * S) by
            simp only [Matrix.reindex_apply, Matrix.submatrix_add, Pi.add_apply]]
        exact partialTraceB_add _ _
      map_smul' := by
        intro r M
        rw [show S * (r • M) * S = r • (S * M * S) from by
            rw [mul_smul_comm, smul_mul_assoc]]
        rw [show Matrix.reindex ptb.symm ptb.symm (r • (S * M * S))
            = r • Matrix.reindex ptb.symm ptb.symm (S * M * S) by
            simp only [Matrix.reindex_apply, Matrix.submatrix_smul, Pi.smul_apply]]
        simpa using partialTraceB_smul (r : ℂ) (Matrix.reindex ptb.symm ptb.symm (S * M * S)) }
  -- twirl integrand integrability
  have hInt : MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ =>
        (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op (dA * dB ^ 2)) n))
          * maxEntangledProjectorPaired dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
          * (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op (dA * dB ^ 2)) n))ᴴ)
      (haarProbUnitary (dA * dB ^ 2)) :=
    twirlIntegrand_integrable dA (dA * dB ^ 2) n
      (maxEntangledProjectorPaired dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB))
  have hcomm := Φlin.toContinuousLinearMap.integral_comp_comm hInt
  -- LHS: Φ applied to the twirl reference; RHS: integral of PERU integrands
  have hLHS : partialTraceB (Matrix.reindex ptb.symm ptb.symm (fixedMarginalTwirlReference dA dB n
      σA))
      = ∫ U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ,
          ((fixedMarginalSingleRoundState σA hσA U).tensorPowGen n).toOp
          ∂(haarProbUnitary (dA * dB ^ 2)) := by
    have hlhs_eq : Φlin.toContinuousLinearMap
        (∫ U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ,
          (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op (dA * dB ^ 2)) n))
            * maxEntangledProjectorPaired dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
            * (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op (dA * dB ^ 2)) n))ᴴ
          ∂(haarProbUnitary (dA * dB ^ 2)))
        = partialTraceB (Matrix.reindex ptb.symm ptb.symm (fixedMarginalTwirlReference dA dB n σA))
            := by
      change partialTraceB (Matrix.reindex ptb.symm ptb.symm (S * _ * S)) = _
      rfl
    rw [← hlhs_eq]
    refine hcomm.symm.trans ?_
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun U => ?_))
    change partialTraceB (Matrix.reindex ptb.symm ptb.symm (S * _ * S)) = _
    exact perU_marginal_traceE_eq dA dB n σA hσA U
  rw [hLHS]
  -- pushforward: the Haar integral of σ_AB(U)^{⊗n} is the de Finetti mixture at μ
  have hFint : MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ =>
        ((fixedMarginalSingleRoundState σA hσA U).tensorPowGen n).toOp)
      (haarProbUnitary (dA * dB ^ 2)) :=
    (fmSingleRound_tensorPow_continuous σA hσA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  symm
  ext i j
  rw [show deFinettiMixtureFixedMarginal dA dB n (fixedMarginalHaarMeasure σA hσA)
        = InfoTheory.DeFinetti.integralTensorPower n (fixedMarginalHaarMeasure σA hσA) from rfl,
    InfoTheory.DeFinetti.PureState.integralTensorPower_toOp_apply,
    show (fixedMarginalHaarMeasure σA hσA).measure
      = MeasureTheory.Measure.map (fixedMarginalSingleRoundState σA hσA)
        (haarProbUnitary (dA * dB ^ 2)) from rfl,
    MeasureTheory.integral_map (fmSingleRound_measurable σA hσA).aemeasurable
      (InfoTheory.DeFinetti.integrable_tensorPow_entry n i j
        (fixedMarginalHaarMeasure σA hσA)).aestronglyMeasurable,
    Quantum.Operators.matrix_integral_entry _ hFint i j]

/-! ### Part A helpers: CFC commutation, inverse-conjugator
    commutation, and support conjugation -/

/-- Commutation transfers to a two-sided inverse: if `a` commutes with `c` and
    `b` is a two-sided inverse of `a`, then `b` commutes with `c`. -/
private lemma fmCommute_of_inv {N : ℕ} {a b c : Op N}
    (hac : a * c = c * a) (h1 : a * b = 1) (h2 : b * a = 1) :
    b * c = c * b := by
  calc b * c = b * c * (a * b) := by rw [h1, mul_one]
    _ = b * (c * a) * b := by rw [← mul_assoc, mul_assoc b c a]
    _ = b * (a * c) * b := by rw [← hac]
    _ = c * b := by rw [← mul_assoc b a c, h2, one_mul]

/-- Conjugation by a `P`-commuting operator preserves `P`-support. -/
private lemma fmSupport_conj {N : ℕ} {P X C : Op N}
    (hX : P * X * P = X) (hC : C * P = P * C) (hCH : Cᴴ * P = P * Cᴴ) :
    P * (C * X * Cᴴ) * P = C * X * Cᴴ := by
  calc P * (C * X * Cᴴ) * P
      = (P * C) * (X * (Cᴴ * P)) := by simp only [mul_assoc]
    _ = (C * P) * (X * (P * Cᴴ)) := by rw [← hC, hCH]
    _ = C * (P * X * P) * Cᴴ := by simp only [mul_assoc]
    _ = C * X * Cᴴ := by rw [hX]

/-- **Nahar et al. Theorem 1 (purified fixed-marginal de Finetti) + Corollary 1.1 reference**,
    on the paired register `(dA·dB)ⁿ ⊗ (dA·dB)ⁿ`.

    For a state `Ψ` supported on the paired symmetric subspace (`hΨ_supp`) whose
    `Bⁿ`-marginal is a state `ρ` with round-wise Alice marginal `σ̂A^{⊗n}` (`hΨ_marg`,
    `hmarg`) — for example the pure symmetric purification of a permutation-invariant `ρ`
    produced by `symmetric_purification_with_pure`; neither purity of `Ψ` nor permutation
    invariance of `ρ` is used — there is a fixed-marginal measure `μ` and a PSD reference
    `τ_ABE` (Nahar et al.'s
    `∫|ϕ_U⟩⟨ϕ_U|^{⊗n} dU`, regrouped) whose reference-register marginal is the de Finetti
    mixture `τ = ∫ σ_AB^{⊗n} dμ`, dominating `Ψ` at the exact de Finetti prefactor:

    `g_{n, dA²dB²} · τ_ABE − Ψ  ⪰  0`.

    **Proven** (Nahar et al. Thm 1 proof, App. A L1618–1673).
    The witness reference is the paired-transported `fixedMarginalTwirlReference`
    `τ_ABE = S·Tₙ·S` (`S = √(σ̂A^{⊗n}⊗1)`), whose `Eⁿ`-marginal is the de Finetti mixture
    at the Haar-pushforward measure (`fmTwirlReference_reindex_partialTraceB_eq`, condB).
    The domination conjunct is discharged on the **blocked** register `Aⁿ⊗Rⁿ`
    (`dR = dA·dB²`): transport `Ψ` across `pairedToBlockedEquiv`
    (`pairedToBlockedEquiv_transports_support`), undo the `σ̂A^{1/2}`-conjugation
    (`Matrix.PosDef.inverseSqrt` suite) and the SP1 Schur–Weyl `κₙ^{1/2}`-flattening
    (`exists_flatten_maxEntangledUnitaryTwirl`, Nahar et al. Lemma 10, sorry-free), evaluate the
    flattened trace `Tr(ρ̂) = Tr(κ⁻¹) = Tr(P_Sym) = g` via the blocked-Alice-marginal
    bridge `pairedToBlockedEquiv_partialTraceB_eq_roundGroup` (D1,
    `PairedBlockedTransport.lean`) together with `hΨ_marg`/`hmarg`, bound the flattened
    state by `symmetricProjectorPairedGen_sub_psd_of_support` at trace `g`, and
    conjugate/reindex back (`Matrix.PosSemidef.reindex`). -/
theorem deFinetti_fixedMarginal_purified_op_le {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (ρ : DensityOp ((dA * dB) ^ n))
    (hmarg : roundwiseAliceMarginal ρ = σA.tensorPowGen n)
    (Ψ : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n))
    (hΨ_supp : symmetricProjectorPaired (dA * dB) n * Ψ.toOp *
      symmetricProjectorPaired (dA * dB) n = Ψ.toOp)
    (hΨ_marg : partialTraceB Ψ.toOp = ρ.toOp) :
    ∃ μ : DensityMeasure (dA * dB), IsFixedMarginalMeasure σA μ ∧
      ∃ τ_ABE : Op ((dA * dB) ^ n * (dA * dB) ^ n), τ_ABE.PosSemidef ∧
        partialTraceB τ_ABE = (deFinettiMixtureFixedMarginal dA dB n μ).toOp ∧
        (((deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℂ) • τ_ABE) - Ψ.toOp).PosSemidef := by
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  haveI hprob : MeasureTheory.IsProbabilityMeasure (haarProbUnitary (dA * dB ^ 2)) :=
    haarProbUnitary_isProbability (dA * dB ^ 2)
  -- The witness reference `τ_ABE` is PSD: `maxEntangledUnitaryTwirl` is a Haar integral of the PSD
  -- conjugates `K U · Θₙ · K Uᴴ`, and `S · (·) · S` (with `S = √(σ̂A^{⊗n}⊗id)` Hermitian) preserves
  -- PSD.
  have hT_psd : (maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)).PosSemidef
      := by
    rw [twirlMap_maxEntangledProjectorPaired]
    refine InfoTheory.DeFinetti.PureState.bochner_integral_posSemidef _
      (twirlIntegrand_integrable dA (dA * dB ^ 2) n
        (maxEntangledProjectorPaired dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB))) (fun U => ?_)
    exact (maxEntangledProjectorPaired_posSemidef dA (dA * dB ^ 2) n
      (dA_le_dA_mul_dBsq dA dB)).mul_mul_conjTranspose_same _
  have hSherm : (CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n))))ᴴ
      = CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n))) :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  have hFTR_psd : (fixedMarginalTwirlReference dA dB n σA).PosSemidef := by
    change (CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))
        * maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
        * CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))).PosSemidef
    rw [show CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))
          * maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
          * CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))
        = CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))
          * maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
          * (CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n))))ᴴ from by
        rw [hSherm]]
    exact hT_psd.mul_mul_conjTranspose_same _
  refine ⟨fixedMarginalHaarMeasure σA hσA, fixedMarginalHaarMeasure_isFixedMarginal σA hσA,
    Matrix.reindex (pairedToBlockedEquiv dA dB n).symm (pairedToBlockedEquiv dA dB n).symm
      (fixedMarginalTwirlReference dA dB n σA),
    hFTR_psd.reindex (pairedToBlockedEquiv dA dB n).symm,
    fmTwirlReference_reindex_partialTraceB_eq σA hσA, ?_⟩
  -- The exact de Finetti domination `g • τ_ABE − Ψ ⪰ 0`:
  -- transport `Ψ` to the blocked register, undo the `σ̂A^{1/2}`- and SP1 `κ^{1/2}`-conjugations,
  -- bound the flattened state by `P_Sym` at trace `g` (the D1 marginal supplies `Tr(ρ̂) = g`),
  -- and conjugate/reindex back.
  haveI : NeZero (dA ^ n) := ⟨pow_ne_zero n (NeZero.ne dA)⟩
  -- SP1: the Schur–Weyl flattening κ of the Haar twirl
  obtain ⟨κ, hκ_psd, hκ_unit, hκ_comm, hT_eq⟩ :=
    exists_flatten_maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
  have hκ_pd : κ.PosDef := (Matrix.PosSemidef.posDef_iff_isUnit hκ_psd).mpr hκ_unit
  set P : Op (dA ^ n * (dA * dB ^ 2) ^ n) := symmetricProjectorPairedGen dA (dA * dB ^ 2) n
    with hP_def
  -- the full-rank Alice tensor power
  set PA : Op (dA ^ n) := (σA.tensorPowGen n).toOp with hPA_def
  have hPA_pd : PA.PosDef := by rw [hPA_def, DensityOp.tensorPowGen_toOp]; exact hσA.tensorPow n
  have hPA_psd : PA.PosSemidef := hPA_pd.posSemidef
  -- conjugators: S = √PA ⊗ 1, W = √κ ⊗ 1 and their inverses
  set S : Op (dA ^ n * (dA * dB ^ 2) ^ n) :=
    Op.tensor (CFC.sqrt PA) (1 : Op ((dA * dB ^ 2) ^ n)) with hS_def
  set Si : Op (dA ^ n * (dA * dB ^ 2) ^ n) :=
    Op.tensor hPA_pd.inverseSqrt (1 : Op ((dA * dB ^ 2) ^ n)) with hSi_def
  set W : Op (dA ^ n * (dA * dB ^ 2) ^ n) :=
    Op.tensor (CFC.sqrt κ) (1 : Op ((dA * dB ^ 2) ^ n)) with hW_def
  set Wi : Op (dA ^ n * (dA * dB ^ 2) ^ n) :=
    Op.tensor hκ_pd.inverseSqrt (1 : Op ((dA * dB ^ 2) ^ n)) with hWi_def
  -- two-sided inverse identities
  have hSSi : S * Si = 1 := by
    rw [hS_def, hSi_def, Op.tensor_mul, hPA_pd.sqrt_mul_inverseSqrt, Matrix.one_mul,
      Op.tensor_one]
  have hSiS : Si * S = 1 := by
    rw [hSi_def, hS_def, Op.tensor_mul, hPA_pd.inverseSqrt_mul_sqrt, Matrix.one_mul,
      Op.tensor_one]
  have hWWi : W * Wi = 1 := by
    rw [hW_def, hWi_def, Op.tensor_mul, hκ_pd.sqrt_mul_inverseSqrt, Matrix.one_mul,
      Op.tensor_one]
  have hWiW : Wi * W = 1 := by
    rw [hWi_def, hW_def, Op.tensor_mul, hκ_pd.inverseSqrt_mul_sqrt, Matrix.one_mul,
      Op.tensor_one]
  have hWW : W * W = Op.tensor κ (1 : Op ((dA * dB ^ 2) ^ n)) := by
    rw [hW_def, Op.tensor_mul, CFC.sqrt_mul_sqrt_self κ (Matrix.nonneg_iff_posSemidef.mpr hκ_psd),
      Matrix.one_mul]
  -- Hermitian facts
  have hsA_herm : (CFC.sqrt PA)ᴴ = CFC.sqrt PA :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg PA)).isHermitian
  have hsκ_herm : (CFC.sqrt κ)ᴴ = CFC.sqrt κ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg κ)).isHermitian
  have hS_herm : Sᴴ = S := by
    rw [hS_def, Op.tensor_conjTranspose, hsA_herm, Matrix.conjTranspose_one]
  have hSi_herm : Siᴴ = Si := by
    rw [hSi_def, Op.tensor_conjTranspose, hPA_pd.inverseSqrt_isHermitian.eq,
      Matrix.conjTranspose_one]
  have hW_herm : Wᴴ = W := by
    rw [hW_def, Op.tensor_conjTranspose, hsκ_herm, Matrix.conjTranspose_one]
  have hWi_herm : Wiᴴ = Wi := by
    rw [hWi_def, Op.tensor_conjTranspose, hκ_pd.inverseSqrt_isHermitian.eq,
      Matrix.conjTranspose_one]
  -- A-4 prerequisites: all four conjugators commute with P_Sym
  have hPA_perm : ∀ σ : Equiv.Perm (Fin n),
      Math.RepresentationTheory.permutationRepresentation dA n σ * PA
        = PA * Math.RepresentationTheory.permutationRepresentation dA n σ :=
    (isPermutationInvariant_iff_commutes (σA.tensorPowGen n)).mp
      (tensorPow_isPermutationInvariant σA)
  have hPA1_comm : Op.tensor PA (1 : Op ((dA * dB ^ 2) ^ n)) * P
      = P * Op.tensor PA (1 : Op ((dA * dB ^ 2) ^ n)) := by
    rw [hP_def]
    exact tensor_one_commute_symmetricProjectorPairedGen PA hPA_perm
  have hS_comm : S * P = P * S := by
    rw [hS_def, ← Op.tensorRightOne_sqrt PA hPA_psd]
    exact sqrt_commute hPA1_comm
  have hSi_comm : Si * P = P * Si := fmCommute_of_inv hS_comm hSSi hSiS
  have hκ1_comm : Op.tensor κ (1 : Op ((dA * dB ^ 2) ^ n)) * P
      = P * Op.tensor κ (1 : Op ((dA * dB ^ 2) ^ n)) := hκ_comm
  have hW_comm : W * P = P * W := by
    rw [hW_def, ← Op.tensorRightOne_sqrt κ hκ_psd]
    exact sqrt_commute hκ1_comm
  have hWi_comm : Wi * P = P * Wi := fmCommute_of_inv hW_comm hWWi hWiW
  -- transported Ψ facts (blocked register)
  set e := pairedToBlockedEquiv dA dB n with he_def
  set Ψb : Op (dA ^ n * (dA * dB ^ 2) ^ n) := Matrix.reindex e e Ψ.toOp with hΨb_def
  have hΨb_psd : Ψb.PosSemidef :=
    (posSemidefOp_implies_mathlib Ψ.toPosSemidefOp).reindex e
  have hΨb_supp : P * Ψb * P = Ψb := by
    rw [hP_def, hΨb_def, he_def]
    exact pairedToBlockedEquiv_transports_support dA dB n Ψ.toOp hΨ_supp
  -- the D1 marginal: Tr_{Rⁿ}(Ψb) = σ̂A^{⊗n}
  have hΨb_marg : partialTraceB Ψb = PA := by
    rw [hΨb_def, he_def, pairedToBlockedEquiv_partialTraceB_eq_roundGroup dA dB n Ψ.toOp,
      hΨ_marg, hPA_def]
    exact congrArg (fun τ : DensityOp (dA ^ n) => τ.toOp) hmarg
  -- A-1/A-2: the fully flattened state ρ̂ = W⁻¹ S⁻¹ Ψb S⁻¹ W⁻¹
  set ρtil : Op (dA ^ n * (dA * dB ^ 2) ^ n) := Si * Ψb * Si with hρtil_def
  set ρhat : Op (dA ^ n * (dA * dB ^ 2) ^ n) := Wi * ρtil * Wi with hρhat_def
  have hρtil_psd : ρtil.PosSemidef := by
    have h := hΨb_psd.mul_mul_conjTranspose_same Si
    rwa [hSi_herm] at h
  have hρhat_psd : ρhat.PosSemidef := by
    have h := hρtil_psd.mul_mul_conjTranspose_same Wi
    rwa [hWi_herm] at h
  have hρtil_supp : P * ρtil * P = ρtil := by
    rw [hρtil_def, show Si * Ψb * Si = Si * Ψb * Siᴴ from by rw [hSi_herm]]
    exact fmSupport_conj hΨb_supp hSi_comm (by rw [hSi_herm]; exact hSi_comm)
  have hρhat_supp : P * ρhat * P = ρhat := by
    rw [hρhat_def, show Wi * ρtil * Wi = Wi * ρtil * Wiᴴ from by rw [hWi_herm]]
    exact fmSupport_conj hρtil_supp hWi_comm (by rw [hWi_herm]; exact hWi_comm)
  -- A-3: Tr(ρ̂) = Tr(κ⁻¹) = Tr(P_Sym) = g, via the D1 marginal
  have harg : dA * (dA * dB ^ 2) = dA ^ 2 * dB ^ 2 := by ring
  have hκinv : κ⁻¹ = partialTraceB P := by
    have h1 : partialTraceB (maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n
        (dA_le_dA_mul_dBsq dA dB)) = (1 : Op (dA ^ n)) :=
      fmPartialTraceB_maxEntangledUnitaryTwirl_eq_one dA (dA * dB ^ 2) n
        (dA_le_dA_mul_dBsq dA dB)
    rw [hT_eq,
      show Op.tensor κ (1 : Op ((dA * dB ^ 2) ^ n)) * P
          = Op.tensor κ (1 : Op ((dA * dB ^ 2) ^ n)) * P
            * Op.tensor (1 : Op (dA ^ n)) (1 : Op ((dA * dB ^ 2) ^ n)) from by
        rw [Op.tensor_one, mul_one],
      partialTraceB_sandwich_tensor_one, mul_one] at h1
    exact Matrix.inv_eq_right_inv h1
  have hρhat_trace : ρhat.trace = (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℂ) := by
    have hcollapse : ρhat
        = Op.tensor (hκ_pd.inverseSqrt * hPA_pd.inverseSqrt) (1 : Op ((dA * dB ^ 2) ^ n)) * Ψb
          * Op.tensor (hPA_pd.inverseSqrt * hκ_pd.inverseSqrt) (1 : Op ((dA * dB ^ 2) ^ n)) := by
      rw [hρhat_def, hρtil_def]
      calc Wi * (Si * Ψb * Si) * Wi
          = (Wi * Si) * Ψb * (Si * Wi) := by simp only [mul_assoc]
        _ = _ := by rw [hWi_def, hSi_def, Op.tensor_mul, Op.tensor_mul, Matrix.one_mul]
    rw [hcollapse, ← trace_partialTraceB, partialTraceB_sandwich_tensor_one, hΨb_marg]
    have hmid : hκ_pd.inverseSqrt * hPA_pd.inverseSqrt * PA
          * (hPA_pd.inverseSqrt * hκ_pd.inverseSqrt)
        = hκ_pd.inverseSqrt * hκ_pd.inverseSqrt := by
      calc hκ_pd.inverseSqrt * hPA_pd.inverseSqrt * PA
            * (hPA_pd.inverseSqrt * hκ_pd.inverseSqrt)
          = hκ_pd.inverseSqrt * (hPA_pd.inverseSqrt * PA * hPA_pd.inverseSqrt)
              * hκ_pd.inverseSqrt := by simp only [mul_assoc]
        _ = hκ_pd.inverseSqrt * 1 * hκ_pd.inverseSqrt := by
            rw [hPA_pd.inverseSqrt_sandwich_eq_one]
        _ = hκ_pd.inverseSqrt * hκ_pd.inverseSqrt := by rw [mul_one]
    rw [hmid, hκ_pd.inverseSqrt_sq, hκinv, trace_partialTraceB, hP_def,
      symmetricProjectorPairedGen_trace_eq, harg, deFinettiPrefactor]
  -- the support bound at trace g: P_Sym − g⁻¹·ρ̂ ⪰ 0, hence g·P_Sym − ρ̂ ⪰ 0
  set g : ℕ := deFinettiPrefactor (dA ^ 2 * dB ^ 2) n with hg_def
  have hg_pos : 0 < g := by
    rw [hg_def]
    exact Nat.choose_pos (by omega)
  have hgC_ne : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg_pos.ne'
  have hdom0 : (P - ((g : ℂ))⁻¹ • ρhat).PosSemidef := by
    rw [hP_def]
    refine symmetricProjectorPairedGen_sub_psd_of_support dA (dA * dB ^ 2) n _
      (hρhat_psd.smul (by positivity)) ?_ ?_
    · rw [Matrix.trace_smul, hρhat_trace, smul_eq_mul, inv_mul_cancel₀ hgC_ne]
      norm_num
    · rw [Matrix.mul_smul, Matrix.smul_mul, ← hP_def, hρhat_supp]
  have hdom1 : (((g : ℂ)) • P - ρhat).PosSemidef := by
    have h := hdom0.smul (show (0 : ℂ) ≤ ((g : ℕ) : ℂ) by positivity)
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hgC_ne, one_smul] at h
    exact h
  -- A-2 back: conjugate by W to restore the Haar twirl Tₙ = W·P_Sym·W
  have hWPW : W * P * W = maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n
      (dA_le_dA_mul_dBsq dA dB) := by
    rw [hT_eq]
    calc W * P * W = W * (P * W) := by rw [mul_assoc]
      _ = W * (W * P) := by rw [← hW_comm]
      _ = W * W * P := by rw [← mul_assoc]
      _ = Op.tensor κ (1 : Op ((dA * dB ^ 2) ^ n)) * P := by rw [hWW]
  have hdom2 : (((g : ℂ)) • maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n
      (dA_le_dA_mul_dBsq dA dB) - ρtil).PosSemidef := by
    have h := hdom1.mul_mul_conjTranspose_same W
    rw [hW_herm] at h
    have hexp : W * (((g : ℂ)) • P - ρhat) * W
        = ((g : ℂ)) • (W * P * W) - W * ρhat * W := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    have hWρW : W * ρhat * W = ρtil := by
      rw [hρhat_def]
      calc W * (Wi * ρtil * Wi) * W
          = (W * Wi) * ρtil * (Wi * W) := by simp only [mul_assoc]
        _ = ρtil := by rw [hWWi, hWiW, Matrix.one_mul, mul_one]
    rw [hexp, hWPW, hWρW] at h
    exact h
  -- A-1 back: conjugate by S to restore the fixed-marginal reference
  have hSTS : S * maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB) * S
      = fixedMarginalTwirlReference dA dB n σA := by
    change _ = CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))
        * maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n (dA_le_dA_mul_dBsq dA dB)
        * CFC.sqrt (Op.tensor (σA.tensorPowGen n).toOp (1 : Op ((dA * dB ^ 2) ^ n)))
    rw [← hPA_def, Op.tensorRightOne_sqrt PA hPA_psd, ← hS_def]
  have hdom3 : (((g : ℂ)) • fixedMarginalTwirlReference dA dB n σA - Ψb).PosSemidef := by
    have h := hdom2.mul_mul_conjTranspose_same S
    rw [hS_herm] at h
    have hexp : S * (((g : ℂ)) • maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n
          (dA_le_dA_mul_dBsq dA dB) - ρtil) * S
        = ((g : ℂ)) • (S * maxEntangledUnitaryTwirl dA (dA * dB ^ 2) n
            (dA_le_dA_mul_dBsq dA dB) * S) - S * ρtil * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    have hSρS : S * ρtil * S = Ψb := by
      rw [hρtil_def]
      calc S * (Si * Ψb * Si) * S
          = (S * Si) * Ψb * (Si * S) := by simp only [mul_assoc]
        _ = Ψb := by rw [hSSi, hSiS, Matrix.one_mul, mul_one]
    rw [hexp, hSTS, hSρS] at h
    exact h
  -- transport the domination back across the paired↔blocked register equivalence
  have hswap : Matrix.reindex e.symm e.symm
        (((g : ℂ)) • fixedMarginalTwirlReference dA dB n σA - Ψb)
      = ((g : ℂ)) • Matrix.reindex e.symm e.symm (fixedMarginalTwirlReference dA dB n σA)
        - Ψ.toOp := by
    rw [hΨb_def]
    ext a b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.smul_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hfinal := hdom3.reindex e.symm
  rw [hswap] at hfinal
  exact hfinal

/-- **Nahar et al. Corollary 1.1 (main.tex:265–:267 (unlabeled; inside
`\label{cor:generalMixedDeFinetti}` :263–:268, Corollary 1.1)) — fixed-marginal de Finetti operator
inequality.**

    Let `dA, dB, n ≥ 1`, `d := dA·dB`, `x := dA²dB² = d²`, and
    `g := deFinettiPrefactor x n = C(n+x−1, x−1) = dim Sym^n(ℂ^x)`. Let
    `σA : DensityOp dA` be **full rank** (`hσA : σA.toOp.PosDef`; QKD's `σ̂A` is
    full-rank, Nahar et al.'s faithful specialization). Let
    `ρ : DensityOp (d^n)` be **permutation-invariant** (`hperm`) with **round-wise
    Alice marginal `σA^{⊗n}`** (`hmarg`: `Tr_{Bⁿ}ρ = σA^{⊗n}`).

    Then there exists a **fixed-marginal measure** `μ` (`IsFixedMarginalMeasure σA μ`,
    supported on extensions `σ_AB` of `σ̂A`) such that

    `g • (deFinettiMixtureFixedMarginal dA dB n μ) − ρ ⪰ 0`.

    The measure `μ` is Nahar et al.'s Haar pushforward on `U(dR)` (`ρ`-independent),
    supplied by the conclusion's `∃`.

    **The fixed-marginal hypothesis `hmarg` is load-bearing**: without
    it only the universal `I/dA`-marginal CKR bound holds, and the reference state
    would not chain to `permInvariant_postselection_security_of_referenceBound`'s
    `deFinettiMixtureFixedMarginal`.

    **Proven**: symmetrically purify `ρ` with
    `symmetric_purification_with_pure` (SP2 = Renner 4.2.2, proven), apply the purified
    fixed-marginal domination `deFinetti_fixedMarginal_purified_op_le` (Part A / Nahar et al.
    Theorem 1),
    then trace out the purifying register `Eⁿ` via `partialTraceB_psd_mono`. The deepest
    upstream lemma is `deFinetti_fixedMarginal_purified_op_le`, whose key ingredient
    is SP1 = `exists_flatten_maxEntangledUnitaryTwirl` (Nahar et al. Lemma 10 / Schur–Weyl κₙ,
    formalized in `SchurWeylFlatten.lean`, absent from Mathlib). -/
theorem deFinetti_fixedMarginal_op_le {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (ρ : DensityOp ((dA * dB) ^ n))
    (hperm : IsPermutationInvariant ρ)
    (hmarg : roundwiseAliceMarginal ρ = σA.tensorPowGen n) :
    ∃ μ : DensityMeasure (dA * dB), IsFixedMarginalMeasure σA μ ∧
      (((deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℂ) •
          (deFinettiMixtureFixedMarginal dA dB n μ).toOp) - ρ.toOp).PosSemidef := by
  haveI : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  haveI : NeZero ((dA * dB) ^ n) :=
    ⟨pow_ne_zero n (Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB))⟩
  -- Part B: symmetrically purify `ρ` (SP2 = Renner 4.2.2, proven), apply the purified
  -- fixed-marginal domination (Part A / Nahar et al. Theorem 1), then trace out the purifying
  -- register `Eⁿ` (partial-trace PSD-monotonicity).
  obtain ⟨Ψ, _hΨ_pure, _hΨ_paired, hΨ_supp, hΨ_marg⟩ :=
    symmetric_purification_with_pure ρ hperm
  obtain ⟨μ, hμ_marg, τ_ABE, _hτ_psd, hτ_ptb, hτ_op⟩ :=
    deFinetti_fixedMarginal_purified_op_le σA hσA ρ hmarg Ψ hΨ_supp hΨ_marg
  refine ⟨μ, hμ_marg, ?_⟩
  have hmono := Quantum.Channels.partialTraceB_psd_mono
    ((deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℂ) • τ_ABE) Ψ.toOp hτ_op
  rwa [partialTraceB_smul, hτ_ptb, hΨ_marg] at hmono

end InfoTheory.Postselection

end
