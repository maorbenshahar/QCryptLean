import QCryptLean.InfoTheory.Postselection.SchurWeylKappa
import QCryptLean.InfoTheory.Postselection.Mixture

/-!
# QKD postselection — the fixed-marginal Haar-pushforward measure `σ(U)`

Standalone measure-theoretic layer for Nahar, Tupkary, Zhao, Lütkenhaus, Tan's
construction (arXiv:2403.11851, App. A, lines 1628–1645) of a *fixed-marginal*
measure on single-round joint states `AB`: purify
`σ̂A` with a Haar-random unitary `U` on the reference register `R = B⊗E`
(`dR = dA·dB²`), trace out `E`, and push the normalized Haar measure on `U(dR)` forward
along this map.

This is the standalone measure layer only: it constructs the measure and proves it is
fixed-marginal (`IsFixedMarginalMeasure`). It does **not** discharge the `condB`/Part A
obligations of `FixedMarginalDeFinetti.lean`; those are consumed by later work.

## Main definitions
- `InfoTheory.Postselection.fixedMarginalPureState` : the purification
  `|ϕ_U⟩ = (σ̂A^{1/2}⊗U)|θ⟩` of `σ̂A` on `A⊗R`, `R = B⊗E`.
- `InfoTheory.Postselection.fixedMarginalSingleRoundState` : its `AB`-marginal `Tr_E|ϕ_U⟩⟨ϕ_U|`.
- `InfoTheory.Postselection.fixedMarginalHaarMeasure` : the Haar pushforward of
  `fixedMarginalSingleRoundState` along the normalized Haar measure on `U(dR)`.

## Main statements
- `InfoTheory.Postselection.fixedMarginalHaarMeasure_isFixedMarginal` : the pushforward measure is
  fixed-marginal at `σ̂A` (in fact the underlying identity `Tr_B[fixedMarginalSingleRoundState
  σA hσA U] = σA` holds for *every* `U`, not merely almost every).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open InfoTheory.DeFinetti MeasureTheory Math.HaarMeasure
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.Postselection

variable {dA dB : ℕ} [NeZero dA] [NeZero dB]

/-! ## The dimension bookkeeping: `R = B ⊗ E`, `dR = dA·dB² = dB·(dA·dB)` -/

/-- `dA ≤ dA·dB²`, the load-bearing dimension inequality for the paired maximally-entangled
    vector `θ` (re-derivation of `FixedMarginalDeFinetti.lean`'s private
    `dA_le_dA_mul_dBsq`, not accessible here). -/
private lemma fmDimLe (dA dB : ℕ) [NeZero dB] : dA ≤ dA * dB ^ 2 := by
  have h1 : 1 ≤ dB ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (NeZero.ne dB))
  calc dA = dA * 1 := (mul_one dA).symm
    _ ≤ dA * dB ^ 2 := by gcongr

/-! ## The maximally entangled vector `|θ⟩` on `A ⊗ R` -/

/-- **The maximally entangled vector `|θ⟩` on `A ⊗ R`**, `dR = dA·dB²`
    (Nahar et al. App. A, `|θ⟩ = Σ_{i<dA}|i⟩|i⟩`, factor-wise `dA`-diagonal embedding into `R`).

    Index-wise identical (up to the `n = 1`/`pow_one` identification) to the `Θ` built
    inside `maxEntangledProjectorPaired dA (dA·dB²) 1 (fmDimLe dA dB)`. -/
private def fmTheta (dA dB : ℕ) [NeZero dA] [NeZero dB] : Ket (dA * (dA * dB ^ 2)) :=
  ⟨fun i => if (finProdFinEquiv.symm i).2 =
      Fin.castLE (fmDimLe dA dB) (finProdFinEquiv.symm i).1 then (1 : ℂ) else 0⟩

/-- **`Tr_R[|θ⟩⟨θ|] = id_A`.** The direct analogue, for `fmTheta`, of
    `maxEntangledProjectorPaired_partialTraceB_eq_one` at `n = 1`: the surviving diagonal
    terms of the trace are exactly the `(a,a)` entries, since `r ↦ (a,r)` supported on
    `|θ⟩⟨θ|` (i.e. `r = castLE a`) is injective in `a`. -/
private lemma fmTheta_partialTraceB_eq_one (dA dB : ℕ) [NeZero dA] [NeZero dB] :
    partialTraceB ((fmTheta dA dB) * (fmTheta dA dB).dag) = (1 : Op dA) := by
  ext i j
  simp only [partialTraceB, Matrix.of_apply, Matrix.one_apply, ket_mul_bra_apply, Ket.dag_vec,
    fmTheta, Equiv.symm_apply_apply, starRingEnd_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single (Fin.castLE (fmDimLe dA dB) i)]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro k _
    have hne : Fin.castLE (fmDimLe dA dB) i ≠ Fin.castLE (fmDimLe dA dB) j :=
      fun h => hij (Fin.castLE_injective _ h)
    by_cases hk : k = Fin.castLE (fmDimLe dA dB) i
    · subst hk; simp [hne]
    · simp [hk]

/-! ## Generic bra-ket / trace / partial-trace algebra used to build the purification -/

/-- `(A|ψ⟩)† = ⟨ψ|Aᴴ` for a general (not necessarily Hermitian) operator `A`. -/
private lemma fmDagOpMul {n : ℕ} (A : Op n) (ψ : Ket n) : (A * ψ).dag = ψ.dag * Aᴴ := by
  ext j
  simp only [Ket.dag_vec, bra_mul_op_vec, op_mul_ket_vec, Matrix.mulVec, dotProduct,
    map_sum, map_mul]
  congr 1; ext i
  change star (A j i) * star (ψ.vec i) = star (ψ.vec i) * Aᴴ i j
  rw [Matrix.conjTranspose_apply]
  ring

/-- `B * (A * ψ) = (B * A) * ψ` (associativity of operator action on kets). -/
private lemma fmOpMulOpMulKet {n : ℕ} (B A : Op n) (ψ : Ket n) :
    B * (A * ψ) = (B * A) * ψ := by
  ext i
  simp only [op_mul_ket_vec, Matrix.mulVec_mulVec]

/-- `Tr[(P⊗1)·M] = Tr[P·Tr_B(M)]`, the trace-of-tensor-sandwich identity used to reduce
    `⟨θ|(P⊗1)|θ⟩` to `Tr(P·Tr_R|θ⟩⟨θ|)`. -/
private lemma fmTrace_tensor_one_eq (n m : ℕ) (P : Op n) (M : Op (n * m)) :
    Matrix.trace (Op.tensor P (1 : Op m) * M) = Matrix.trace (P * partialTraceB M) := by
  have h := partialTraceB_sandwich_tensor_one P (1 : Op n) M
  rw [Op.tensor_one, Matrix.mul_one, Matrix.mul_one] at h
  calc Matrix.trace (Op.tensor P (1 : Op m) * M)
      = Matrix.trace (partialTraceB (Op.tensor P (1 : Op m) * M)) :=
        (trace_partialTraceB _).symm
    _ = Matrix.trace (P * partialTraceB M) := by rw [h]

/-- **`⟨θ|(σ̂A⊗1)|θ⟩ = 1`.** The key normalization scalar: sandwiching the fixed marginal
    `σ̂A` (tensored with the identity on `R`) between `θ` reduces, via
    `fmTrace_tensor_one_eq` and `fmTheta_partialTraceB_eq_one`, to `Tr(σ̂A) = 1`. -/
private lemma fmTheta_dag_tensor_one_mul_theta (σA : DensityOp dA) :
    (fmTheta dA dB).dag * (Op.tensor σA.toOp (1 : Op (dA * dB ^ 2))) * (fmTheta dA dB) = 1 := by
  have hmul := trace_ketbra_mul (fmTheta dA dB) (Op.tensor σA.toOp (1 : Op (dA * dB ^ 2)))
  rw [Matrix.trace_mul_comm] at hmul
  rw [← hmul, fmTrace_tensor_one_eq, fmTheta_partialTraceB_eq_one, Matrix.mul_one]
  exact σA.trace_one

/-! ## Definition 1: the purification `|ϕ_U⟩⟨ϕ_U|` -/

/-- The `Uᴴ * U = 1` fact for `U : unitaryGroup`, in `Op` form. -/
private lemma fmUnitary_conjTranspose_mul_self {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) : (U : Op d)ᴴ * (U : Op d) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact (Matrix.mem_unitaryGroup_iff').mp U.2

/-- **`|ϕ_U⟩ = (σ̂A^{1/2}⊗U)|θ⟩` is normalized.** -/
private lemma fmPureState_normalized (σA : DensityOp dA)
    (U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ) :
    (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) * fmTheta dA dB).dag *
      (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) * fmTheta dA dB) = 1 := by
  set S := CFC.sqrt σA.toOp with hS_def
  set A : Op (dA * (dA * dB ^ 2)) := Op.tensor S (U : Op (dA * dB ^ 2)) with hA_def
  have hS_herm : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σA.toOp)).isHermitian
  have hS_sq : S * S = σA.toOp :=
    CFC.sqrt_mul_sqrt_self σA.toOp
      (Matrix.nonneg_iff_posSemidef.mpr (posSemidefOp_implies_mathlib σA.toPosSemidefOp))
  have hAH_A : Aᴴ * A = Op.tensor σA.toOp (1 : Op (dA * dB ^ 2)) := by
    rw [hA_def, Op.tensor_conjTranspose, Op.tensor_mul, hS_herm, hS_sq,
      fmUnitary_conjTranspose_mul_self]
  calc (A * fmTheta dA dB).dag * (A * fmTheta dA dB)
      = ((fmTheta dA dB).dag * Aᴴ) * (A * fmTheta dA dB) := by rw [fmDagOpMul]
    _ = (fmTheta dA dB).dag * (Aᴴ * (A * fmTheta dA dB)) := by rw [braop_mul_ket]
    _ = (fmTheta dA dB).dag * ((Aᴴ * A) * fmTheta dA dB) := by rw [fmOpMulOpMulKet]
    _ = (fmTheta dA dB).dag * (Op.tensor σA.toOp (1 : Op (dA * dB ^ 2)) * fmTheta dA dB) := by
        rw [hAH_A]
    _ = 1 := by rw [← braop_mul_ket]; exact fmTheta_dag_tensor_one_mul_theta σA

/-- **Nahar et al.'s purification `|ϕ_U⟩⟨ϕ_U| = (σ̂A^{1/2}⊗U)|θ⟩⟨θ|(σ̂A^{1/2}⊗U)†`** (App. A,
    lines 1628–1645), on `A ⊗ R`, `R = B⊗E`, `dR = dA·dB²`. -/
def fixedMarginalPureState (σA : DensityOp dA) (_hσA : σA.toOp.PosDef)
    (U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ) : DensityOp (dA * (dA * dB ^ 2)) :=
  DensityOp.fromPure
    (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) * fmTheta dA dB)
    (fmPureState_normalized σA U)

/-! ## Definition 2: the single-round `AB` state `Tr_E|ϕ_U⟩⟨ϕ_U|`, via `A⊗(B⊗E) ≃ (A⊗B)⊗E` -/

/-- **The `A⊗(B⊗E) ≃ (A⊗B)⊗E` regrouping equivalence**, `dR = dA·dB² = dB·(dA·dB)`
    (`E`-dim `dA·dB`), realized as a bare `Nat`-value cast (a genuine re-association, not a
    reordering of interleaved digits: `finProdFinEquiv_assoc_cast` confirms the "genuine"
    structural regrouping of a plain tensor re-association coincides exactly with the
    `Fin`-value cast). -/
def assocEquiv (dA dB : ℕ) :
    Fin (dA * (dA * dB ^ 2)) ≃ Fin ((dA * dB) * (dA * dB)) :=
  finCongr (by ring)

/-- Reindexing along `finCongr h` is the raw `▸`-cast (generic form, abstract `n m`). -/
private lemma fmReindex_finCongr_eq_cast {n m : ℕ} (h : n = m) (M : Op n) :
    Matrix.reindex (finCongr h) (finCongr h) M = h ▸ M := by
  subst h; simp

/-- Cast composition for `▸`: `(p.trans q) ▸ M = q ▸ (p ▸ M)`. -/
private lemma fmEqRec_trans {n m k : ℕ} (p : n = m) (q : m = k) (M : Op n) :
    (p.trans q) ▸ M = q ▸ (p ▸ M) := by
  cases p; cases q; rfl

/-- Cast cancellation for `▸`: `h ▸ (h.symm ▸ M) = M`. -/
private lemma fmEqRec_symm_cancel {n m : ℕ} (h : n = m) (M : Op m) :
    h ▸ (h.symm ▸ M) = M := by
  cases h; rfl

/-- Casting only the (numerically-relabeled) traced-out factor does not change
    `partialTraceB` (generic form, abstract `n m₁ m₂`). -/
private lemma fmPartialTraceB_cast_snd {n m1 m2 : ℕ} (h : m1 = m2) (M : Op (n * m1)) :
    partialTraceB ((congrArg (n * ·) h) ▸ M : Op (n * m2)) = partialTraceB M := by
  cases h; rfl

/-- **The `assocEquiv` bridging identity.** Tracing out `E` then `B` from the `assocEquiv`-
    reindexed state agrees with tracing out the whole `R`-register directly: composing the
    `Nat`-value cast underlying `assocEquiv` with the
    `partialTraceB_partialTraceB_eq_assoc` (`a = dA, b = dB, c = dA·dB`) and cancelling the
    inner `dA·dB² = dB·(dA·dB)` relabeling (`fmPartialTraceB_cast_snd`). -/
private lemma fmAssoc_partialTraceB_partialTraceB {dA dB : ℕ}
    (M : Op (dA * (dA * dB ^ 2))) :
    partialTraceB (partialTraceB
        (Matrix.reindex (assocEquiv dA dB) (assocEquiv dA dB) M)) = partialTraceB M := by
  have hInner : dA * dB ^ 2 = dB * (dA * dB) := by ring
  rw [show assocEquiv dA dB = finCongr ((congrArg (dA * ·) hInner).trans
      (Nat.mul_assoc dA dB (dA * dB)).symm) from rfl,
    fmReindex_finCongr_eq_cast,
    fmEqRec_trans (congrArg (dA * ·) hInner) (Nat.mul_assoc dA dB (dA * dB)).symm,
    partialTraceB_partialTraceB_eq_assoc,
    fmEqRec_symm_cancel (Nat.mul_assoc dA dB (dA * dB)), fmPartialTraceB_cast_snd hInner]

/-- **`fixedMarginalSingleRoundState`: the single-round `AB` state `Tr_E|ϕ_U⟩⟨ϕ_U|`.**
    Regroups `A⊗(B⊗E)` to `(A⊗B)⊗E` via `assocEquiv`, then traces out the trailing `E`
    factor, landing on the `AB`-register (dimension `dA·dB`) matching
    `IsFixedMarginalMeasure`'s convention. -/
def fixedMarginalSingleRoundState (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ) : DensityOp (dA * dB) :=
  DensityOp.partialTraceB (densityOp_reindex (assocEquiv dA dB) (fixedMarginalPureState σA hσA U))

/-! ## Definition 3: the Haar-pushforward measure -/

/-- `densityOp_reindex` is continuous (entrywise a coordinate projection of the input). -/
private lemma fmDensityOpReindex_continuous {n m : ℕ} (e : Fin n ≃ Fin m) :
    Continuous (densityOp_reindex e : DensityOp n → DensityOp m) := by
  rw [continuous_induced_rng]
  apply continuous_pi; intro i; apply continuous_pi; intro j
  have h_eq : (fun ρ : DensityOp n =>
      ((fun σ : DensityOp m => σ.toOp) ∘ densityOp_reindex e) ρ i j) =
      (fun ρ : DensityOp n => ρ.toOp (e.symm i) (e.symm j)) := by
    ext ρ
    simp only [Function.comp, densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [h_eq]
  exact (continuous_apply (e.symm j)).comp ((continuous_apply (e.symm i)).comp
    continuous_induced_dom)

/-- `fixedMarginalPureState σA hσA` is continuous in `U` (entrywise a product of the
    `(σ̂A^{1/2}⊗U)|θ⟩` coordinate, continuous in `U`'s matrix entries). -/
private lemma fixedMarginalPureState_continuous (σA : DensityOp dA) (hσA : σA.toOp.PosDef) :
    Continuous (fixedMarginalPureState σA hσA :
      Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ → DensityOp (dA * (dA * dB ^ 2))) := by
  rw [continuous_induced_rng]
  apply continuous_pi; intro i; apply continuous_pi; intro j
  have hveccont : Continuous (fun U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ =>
      (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) * fmTheta dA dB).vec) := by
    have h1 : Continuous (fun U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ =>
        Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2))) :=
      Op.continuous_tensor.comp (continuous_const.prodMk continuous_subtype_val)
    have h2 : Continuous (fun p : Op (dA * (dA * dB ^ 2)) =>
        (p * fmTheta dA dB).vec) := by
      apply continuous_pi; intro k
      simp only [op_mul_ket_vec, Matrix.mulVec, dotProduct]
      exact continuous_finsetSum _ (fun l _ =>
        Continuous.mul
          (show Continuous (fun a : Op (dA * (dA * dB ^ 2)) => a k l) from
            (continuous_apply l).comp (continuous_apply k))
          continuous_const)
    exact h2.comp h1
  have h_entry : ∀ U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ,
      ((fun ρ : DensityOp (dA * (dA * dB ^ 2)) => ρ.toOp) ∘ fixedMarginalPureState σA hσA) U i j =
      (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) * fmTheta dA dB).vec i *
        star ((Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) * fmTheta dA dB).vec j) := by
    intro U
    simp only [Function.comp, fixedMarginalPureState, DensityOp.fromPure, ket_mul_bra_apply,
      Ket.dag_vec, starRingEnd_apply]
  simp_rw [show (fun U => ((fun ρ : DensityOp (dA * (dA * dB ^ 2)) => ρ.toOp) ∘
      fixedMarginalPureState σA hσA) U i j) =
      (fun U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ =>
        (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) * fmTheta dA dB).vec i *
          star ((Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) *
            fmTheta dA dB).vec j)) from funext h_entry]
  exact ((continuous_apply i).comp hveccont).mul
    (continuous_star.comp ((continuous_apply j).comp hveccont))

/-- **`fixedMarginalSingleRoundState σA hσA` is continuous in `U`**, hence measurable. -/
private lemma fixedMarginalSingleRoundState_continuous
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef) :
    Continuous (fixedMarginalSingleRoundState σA hσA :
      Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ → DensityOp (dA * dB)) :=
  partialTraceB_continuous_general.comp
    ((fmDensityOpReindex_continuous (assocEquiv dA dB)).comp
      (fixedMarginalPureState_continuous σA hσA))

private lemma fixedMarginalSingleRoundState_measurable
    (σA : DensityOp dA) (hσA : σA.toOp.PosDef) :
    Measurable (fixedMarginalSingleRoundState σA hσA :
      Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ → DensityOp (dA * dB)) :=
  (fixedMarginalSingleRoundState_continuous σA hσA).measurable

/-- **`fixedMarginalHaarMeasure`: the Haar-pushforward measure on single-round `AB`
    states.** Pushforward of the normalized Haar probability measure on `U(dA·dB²)` along
    `fixedMarginalSingleRoundState σA hσA`. -/
def fixedMarginalHaarMeasure (σA : DensityOp dA) (hσA : σA.toOp.PosDef) :
    DensityMeasure (dA * dB) :=
  haveI : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  { measure := Measure.map (fixedMarginalSingleRoundState σA hσA) (haarProbUnitary (dA * dB ^ 2))
    isProbability := by
      constructor
      rw [Measure.map_apply (fixedMarginalSingleRoundState_measurable σA hσA)
        MeasurableSet.univ]
      simp only [Set.preimage_univ]
      exact (haarProbUnitary_isProbability (dA * dB ^ 2)).measure_univ }

/-! ## Definition 4: the fixed-marginal identity -/

/-- **The pointwise marginal identity**: `Tr_B[fixedMarginalSingleRoundState σA hσA U] = σA`
    for *every* `U` (Nahar et al. App. A: "every element of `PuriR(σ̂A)` has `Tr_R = σ̂A`"). -/
private lemma fixedMarginalSingleRoundState_partialTraceB_eq (σA : DensityOp dA)
    (hσA : σA.toOp.PosDef) (U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ) :
    DensityOp.partialTraceB (fixedMarginalSingleRoundState σA hσA U) = σA := by
  have : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  apply DensityOp.ext
  change partialTraceB (partialTraceB
      (Matrix.reindex (assocEquiv dA dB) (assocEquiv dA dB)
        (fixedMarginalPureState σA hσA U).toOp)) = σA.toOp
  rw [fmAssoc_partialTraceB_partialTraceB]
  set S := CFC.sqrt σA.toOp with hS_def
  set A : Op (dA * (dA * dB ^ 2)) := Op.tensor S (U : Op (dA * dB ^ 2)) with hA_def
  change partialTraceB ((A * fmTheta dA dB) * (A * fmTheta dA dB).dag) = σA.toOp
  have hS_herm : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σA.toOp)).isHermitian
  have hS_sq : S * S = σA.toOp :=
    CFC.sqrt_mul_sqrt_self σA.toOp
      (Matrix.nonneg_iff_posSemidef.mpr (posSemidefOp_implies_mathlib σA.toPosSemidefOp))
  have hU2 : (U : Op (dA * dB ^ 2))ᴴ * (U : Op (dA * dB ^ 2)) = 1 :=
    fmUnitary_conjTranspose_mul_self U
  have hA_factor : A = Op.tensor S (1 : Op (dA * dB ^ 2)) * Op.tensor (1 : Op dA)
      (U : Op (dA * dB ^ 2)) := by
    rw [hA_def, Op.tensor_mul, Matrix.mul_one, Matrix.one_mul]
  have hAdag_factor : Aᴴ = Op.tensor (1 : Op dA) (U : Op (dA * dB ^ 2))ᴴ *
      Op.tensor S (1 : Op (dA * dB ^ 2)) := by
    rw [hA_def, Op.tensor_conjTranspose, hS_herm, Op.tensor_mul, Matrix.one_mul, Matrix.mul_one]
  rw [fmDagOpMul]
  change partialTraceB ((A * fmTheta dA dB) * ((fmTheta dA dB).dag * Aᴴ)) = σA.toOp
  rw [show (A * fmTheta dA dB) * ((fmTheta dA dB).dag * Aᴴ) =
      A * (fmTheta dA dB * (fmTheta dA dB).dag) * Aᴴ from by
        rw [← ketbra_mul_op, ← op_mul_ketbra]]
  rw [hAdag_factor, hA_factor]
  rw [show Op.tensor S (1 : Op (dA * dB ^ 2)) * Op.tensor (1 : Op dA) (U : Op (dA * dB ^ 2)) *
      (fmTheta dA dB * (fmTheta dA dB).dag) *
      (Op.tensor (1 : Op dA) (U : Op (dA * dB ^ 2))ᴴ * Op.tensor S (1 : Op (dA * dB ^ 2))) =
      Op.tensor S (1 : Op (dA * dB ^ 2)) *
        (Op.tensor (1 : Op dA) (U : Op (dA * dB ^ 2)) *
          (fmTheta dA dB * (fmTheta dA dB).dag) *
          Op.tensor (1 : Op dA) (U : Op (dA * dB ^ 2))ᴴ) *
        Op.tensor S (1 : Op (dA * dB ^ 2)) from by
      simp only [Matrix.mul_assoc]]
  rw [partialTraceB_sandwich_tensor_one]
  have hone : partialTraceB (Op.tensor (1 : Op dA) (U : Op (dA * dB ^ 2)) *
      (fmTheta dA dB * (fmTheta dA dB).dag) *
      Op.tensor (1 : Op dA) (U : Op (dA * dB ^ 2))ᴴ) = (1 : Op dA) := by
    have hsandwich := one_tensor_mul_mul_one_tensor_apply
      (n := dA) (m := dA * dB ^ 2) (U : Op (dA * dB ^ 2)) (U : Op (dA * dB ^ 2))ᴴ
      (fmTheta dA dB * (fmTheta dA dB).dag)
    ext i j
    simp only [partialTraceB, Matrix.of_apply]
    have hk : ∀ k : Fin (dA * dB ^ 2),
        (Op.tensor (1 : Op dA) (U : Op (dA * dB ^ 2)) *
          (fmTheta dA dB * (fmTheta dA dB).dag) *
          Op.tensor (1 : Op dA) (U : Op (dA * dB ^ 2))ᴴ)
          (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))
          = ∑ a : Fin (dA * dB ^ 2), ∑ c : Fin (dA * dB ^ 2),
            (U : Op (dA * dB ^ 2)) k a * (fmTheta dA dB * (fmTheta dA dB).dag)
              (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c)) *
              (U : Op (dA * dB ^ 2))ᴴ c k := fun k => hsandwich i j k k
    simp_rw [hk]
    calc ∑ k : Fin (dA * dB ^ 2), ∑ a : Fin (dA * dB ^ 2), ∑ c : Fin (dA * dB ^ 2),
          (U : Op (dA * dB ^ 2)) k a * (fmTheta dA dB * (fmTheta dA dB).dag)
            (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c)) * (U : Op (dA * dB ^ 2))ᴴ c k
        = ∑ a : Fin (dA * dB ^ 2), ∑ c : Fin (dA * dB ^ 2),
            (fmTheta dA dB * (fmTheta dA dB).dag)
              (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c)) *
              ∑ k : Fin (dA * dB ^ 2),
                (U : Op (dA * dB ^ 2))ᴴ c k * (U : Op (dA * dB ^ 2)) k a := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = ∑ a : Fin (dA * dB ^ 2), ∑ c : Fin (dA * dB ^ 2),
            (fmTheta dA dB * (fmTheta dA dB).dag)
              (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c)) * (if c = a then 1 else 0) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
          congr 1
          rw [← Matrix.mul_apply, hU2, Matrix.one_apply]
      _ = ∑ a : Fin (dA * dB ^ 2),
            (fmTheta dA dB * (fmTheta dA dB).dag)
              (finProdFinEquiv (i, a)) (finProdFinEquiv (j, a)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_eq_single a]
          · rw [ite_eq_left rfl, mul_one]
          · intro c _ hc; rw [ite_eq_right hc, mul_zero]
          · intro h; exact absurd (Finset.mem_univ a) h
      _ = partialTraceB (fmTheta dA dB * (fmTheta dA dB).dag) i j := rfl
      _ = (1 : Op dA) i j := by rw [fmTheta_partialTraceB_eq_one]
  rw [hone, Matrix.mul_one, hS_sq]

/-- **`fixedMarginalHaarMeasure` is fixed-marginal at `σ̂A`.** Nahar et al.'s "every element of
    `PuriR(σ̂A)` has `Tr_R = σ̂A`", specialized to the two-stage trace `Tr_B∘Tr_E = Tr_R`.
    Proved via `ae_map_iff` (the fixed-marginal set is measurable, being a closed set for
    the induced topology on `DensityOp`) reducing to `ae_of_all` on the *pointwise*
    identity `fixedMarginalSingleRoundState_partialTraceB_eq`, true for every `U`. -/
theorem fixedMarginalHaarMeasure_isFixedMarginal (σA : DensityOp dA) (hσA : σA.toOp.PosDef) :
    IsFixedMarginalMeasure σA (fixedMarginalHaarMeasure σA hσA : DensityMeasure (dA * dB)) := by
  have : NeZero (dA * dB ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB))⟩
  have : NeZero (dA * dB) := ⟨Nat.mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  change ∀ᵐ σ ∂(fixedMarginalHaarMeasure σA hσA).measure, DensityOp.partialTraceB σ = σA
  change ∀ᵐ σ ∂(Measure.map (fixedMarginalSingleRoundState σA hσA)
    (haarProbUnitary (dA * dB ^ 2))), DensityOp.partialTraceB σ = σA
  have hT2 : T2Space (DensityOp dA) :=
    Topology.IsEmbedding.t2Space ⟨⟨rfl⟩, fun _ _ h => DensityOp.ext h⟩
  have h_meas : MeasurableSet
      (Set.ofPred (fun σ : DensityOp (dA * dB) => DensityOp.partialTraceB σ = σA)) :=
    (isClosed_eq (partialTraceB_continuous_general) continuous_const).measurableSet
  refine (MeasureTheory.ae_map_iff
    (fixedMarginalSingleRoundState_measurable σA hσA).aemeasurable h_meas).mpr ?_
  exact MeasureTheory.ae_of_all _ (fixedMarginalSingleRoundState_partialTraceB_eq σA hσA)

/-- **The `n = 1` entry identity for the maximally entangled paired projector.** The
    file-private ketbra `|θ⟩⟨θ|` (via `fmTheta`) equals, index-for-index (up to the
    `pow_one` identification `dA^1·(dA·dB²)^1 = dA·(dA·dB²)`), the public
    `maxEntangledProjectorPaired dA (dA·dB²) 1 (fmDimLe dA dB)`. -/
private lemma fmTheta_ketbra_eq_castMEP (dA dB : ℕ) [NeZero dA] [NeZero dB] :
    fmTheta dA dB * (fmTheta dA dB).dag =
      Op.castDim (by rw [pow_one, pow_one])
        (maxEntangledProjectorPaired dA (dA * dB ^ 2) 1 (fmDimLe dA dB)) := by
  have hcast : ∀ (n m : ℕ) (hnm : n = m) (M : Op n) (a b : Fin m),
      (Op.castDim hnm M) a b = M (Fin.cast hnm.symm a) (Fin.cast hnm.symm b) := by
    intro n m hnm M a b; subst hnm; rfl
  have h : dA ^ 1 * (dA * dB ^ 2) ^ 1 = dA * (dA * dB ^ 2) := by rw [pow_one, pow_one]
  have hcond : ∀ (x : Fin (dA * (dA * dB ^ 2))),
      ((finProdFinEquiv.symm x).2 = Fin.castLE (fmDimLe dA dB) (finProdFinEquiv.symm x).1)
      ↔ ((finProdFinEquiv.symm (Fin.cast h.symm x)).2 =
          finFunctionFinEquiv (fun k => Fin.castLE (fmDimLe dA dB)
            (finFunctionFinEquiv.symm (finProdFinEquiv.symm (Fin.cast h.symm x)).1 k))) := by
    intro x
    have hn2 : 0 < dA * dB ^ 2 :=
      Nat.pos_of_ne_zero (Nat.mul_ne_zero (NeZero.ne dA) (pow_ne_zero 2 (NeZero.ne dB)))
    have hq : (x : ℕ) / (dA * dB ^ 2) < dA :=
      Nat.div_lt_of_lt_mul (by rw [mul_comm (dA * dB ^ 2) dA]; exact x.isLt)
    rw [Fin.ext_iff, Fin.ext_iff, finFunctionFinEquiv_apply_val]
    simp only [finProdFinEquiv, Equiv.coe_fn_symm_mk, Fin.val_castLE, Fin.coe_modNat,
      Fin.coe_divNat, Fin.sum_univ_one, finFunctionFinEquiv_symm_apply_val, pow_zero, pow_one,
      Nat.div_one, mul_one, Fin.val_cast, Fin.val_zero]
    rw [Nat.mod_eq_of_lt hq]
  ext i j
  rw [hcast]
  simp only [ket_mul_bra_apply, Ket.dag_vec, fmTheta, maxEntangledProjectorPaired,
    Matrix.of_apply, starRingEnd_apply]
  rw [if_congr (hcond i) rfl rfl, if_congr (hcond j) rfl rfl]

theorem fixedMarginalPureState_toOp (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (U : Matrix.unitaryGroup (Fin (dA * dB ^ 2)) ℂ) :
    (fixedMarginalPureState σA hσA U).toOp =
      Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) *
        Op.castDim (by rw [pow_one, pow_one])
          (maxEntangledProjectorPaired dA (dA * dB ^ 2) 1 (fmDimLe dA dB)) *
        (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)))ᴴ := by
  change (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) * fmTheta dA dB)
      * (Op.tensor (CFC.sqrt σA.toOp) (U : Op (dA * dB ^ 2)) * fmTheta dA dB).dag = _
  rw [← op_mul_ketbra_mul_conjTranspose, fmTheta_ketbra_eq_castMEP]

end InfoTheory.Postselection

end
