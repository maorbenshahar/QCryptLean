import QCryptLean.Quantum.Symmetry.TensorPowerCommutant
import QCryptLean.InfoTheory.Postselection.SchurWeylUnitarySpan
import QCryptLean.Quantum.TensorProducts.PairedTensorCommutant
import QCryptLean.InfoTheory.Postselection.SchurWeylTwirlProjection

/-!
# QKD postselection — the E2 commutant assembly

Composes the four merged E2 sub-lemmas (`TensorPowerCommutant.lean` B9, `SchurWeylUnitarySpan.lean`
SL-Unit, `PairedTensorCommutant.lean` SL-TensorLift, `SchurWeylTwirlProjection.lean` E1) into the
three compose-level statements Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 Lemma 10 / SP1 step 8
need:

- `commutant_unitaryTensorPow_eq_permSpan` (§1a): the pure `R`-side unitary-tensor-power
  commutant equals `permSpan`.
- `commutant_pairedUnitaryTensorPow_eq_tensorPermSpan` (§1b): the paired-register commutant of
  `1_{Aⁿ} ⊗ U^{⊗n}` is the span of `X ⊗ P_R(π)` with `X` free over the whole `A`-side algebra.
- `maxEntangledUnitaryTwirl_eq_sum_tensor_permRep` (§1c): the Haar twirl of the maximally
  entangled paired projector expands as a finite sum `Σ_π X_π ⊗ P_R(π)`.

§1a/§1c build on `SL-Unit` (`commutant_unitaryTensorPow_eq_commutant_tensorPow`,
`SchurWeylUnitarySpan.lean`), consumed here, not re-derived.

As in `SchurWeylUnitarySpan.lean`, `setOf` (which delaborates to `{T | …}`) is used throughout
instead of the `{T : … | …}` set-builder notation: `open Quantum.Operators` brings the Dirac ket
`|i:n⟩` notation, whose `|` token (followed by a binder `:`) makes the set-builder form
unparseable here. The two forms produce identical `Set` terms.
-/

open Matrix Math.RepresentationTheory Quantum.Operators Quantum.TensorProducts Quantum.Symmetry
open scoped Matrix BigOperators

noncomputable section

namespace InfoTheory.Postselection

/-! ## §1a — the pure `R`-side unitary commutant -/

/-- **§1a.** On the pure `R`-side, the commutant of the unitary tensor-power family equals
`permSpan`: `Com({U^{⊗n} : U ∈ U(dR)}) = span_ℂ{P_R(π) : π ∈ Sₙ}`. Composes `SL-Unit`
(`commutant_unitaryTensorPow_eq_commutant_tensorPow`) with `SL-Bicom`
(`commutant_matrixTensorPow_eq_permSpan`, B9). No `dA`, no `dA ≤ dR` hypothesis. -/
theorem commutant_unitaryTensorPow_eq_permSpan (dR n : ℕ) [NeZero dR] [NeZero n] :
    commutant (dR ^ n)
        (Set.range fun U : Matrix.unitaryGroup (Fin dR) ℂ => Op.tensorPow (U : Op dR) n)
      = permSpan dR n := by
  have hcommutant_eq : commutant (dR ^ n)
        (Set.range fun U : Matrix.unitaryGroup (Fin dR) ℂ => Op.tensorPow (U : Op dR) n)
      = commutant (dR ^ n) (Set.range fun A : Op dR => Op.tensorPow A n) := by
    apply SetLike.coe_injective
    change setOf (fun T : Op (dR ^ n) => ∀ Y ∈
          (Set.range fun U : Matrix.unitaryGroup (Fin dR) ℂ => Op.tensorPow (U : Op dR) n),
            Commute Y T)
        = setOf (fun T : Op (dR ^ n) => ∀ Y ∈ (Set.range fun A : Op dR => Op.tensorPow A n),
            Commute Y T)
    simp only [Set.forall_mem_range]
    exact commutant_unitaryTensorPow_eq_commutant_tensorPow dR n
  rw [hcommutant_eq, commutant_matrixTensorPow_eq_permSpan]

/-! ## §1b — the span-substitution collapse and the paired-register corollary -/

/-- **Collapse lemma.** `span{X ⊗ M : X ∈ Op(dA^n), M ∈ permSpan dR n}
= span{X ⊗ P_R(π) : X ∈ Op(dA^n), π ∈ Sₙ}`: bilinearity of `Op.tensor` lets any
`M ∈ span(range P_R)` be replaced, generator-by-generator, by the raw permutation
representations, and conversely each raw `P_R(π)` already lies in `permSpan dR n`. -/
private theorem span_tensor_permSpan_eq_span_tensor_permRep
    (dA dR n : ℕ) [NeZero dA] [NeZero dR] [NeZero n] :
    Submodule.span ℂ
        (setOf fun T : Op (dA ^ n * dR ^ n) => ∃ (X : Op (dA ^ n)) (M : Op (dR ^ n)),
            M ∈ permSpan dR n ∧ T = Op.tensor X M)
      = Submodule.span ℂ
          (setOf fun T : Op (dA ^ n * dR ^ n) => ∃ (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)),
              T = Op.tensor X (permutationRepresentation dR n π)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro T ⟨X, M, hM, rfl⟩
    rw [permSpan] at hM
    induction hM using Submodule.span_induction with
    | mem M' hM' =>
        obtain ⟨π, rfl⟩ := hM'
        exact Submodule.subset_span ⟨X, π, rfl⟩
    | zero =>
        have hzero : Op.tensor X (0 : Op (dR ^ n)) = (0 : Op (dA ^ n * dR ^ n)) := by
          rw [show (0 : Op (dR ^ n)) = (0 : ℂ) • (0 : Op (dR ^ n)) by simp,
            Op.tensor_smul_right, zero_smul]
        rw [hzero]
        exact Submodule.zero_mem _
    | add M₁ M₂ _ _ h₁ h₂ =>
        rw [Op.tensor_add_right]
        exact Submodule.add_mem _ h₁ h₂
    | smul c M' _ h =>
        rw [Op.tensor_smul_right]
        exact Submodule.smul_mem _ c h
  · rw [Submodule.span_le]
    rintro T ⟨X, π, rfl⟩
    exact Submodule.subset_span ⟨X, permutationRepresentation dR n π,
      Submodule.subset_span ⟨π, rfl⟩, rfl⟩

/-- **§1b.** On the paired register, the commutant of `1_{Aⁿ} ⊗ U^{⊗n}` is the span of
`X ⊗ P_R(π)` with `X` free over all of `Op(dA^n)` (the `1 ⊗ M`-only form is FALSE by dimension
count). Composes `SL-TensorLift` (`commutant_pairedTensorFamily_eq_tensorCommutantSpan`) with
§1a, then collapses the resulting `M ∈ permSpan`-generated span down to the raw permutation
representations via `span_tensor_permSpan_eq_span_tensor_permRep`. -/
theorem commutant_pairedUnitaryTensorPow_eq_tensorPermSpan (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] :
    (setOf fun T : Op (dA ^ n * dR ^ n) => ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
        Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) T)
      = (Submodule.span ℂ
          (setOf fun T : Op (dA ^ n * dR ^ n) => ∃ (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)),
              T = Op.tensor X (permutationRepresentation dR n π))
        : Set (Op (dA ^ n * dR ^ n))) := by
  rw [← span_tensor_permSpan_eq_span_tensor_permRep dA dR n]
  have hbase := commutant_pairedTensorFamily_eq_tensorCommutantSpan (dA := dA) (dR := dR) (n := n)
    (Set.range fun U : Matrix.unitaryGroup (Fin dR) ℂ => Op.tensorPow (U : Op dR) n)
  have hLHS : (setOf fun T : Op (dA ^ n * dR ^ n) => ∀ S ∈
        (Set.range fun U : Matrix.unitaryGroup (Fin dR) ℂ => Op.tensorPow (U : Op dR) n),
        Commute (Op.tensor (1 : Op (dA ^ n)) S) T)
      = (setOf fun T : Op (dA ^ n * dR ^ n) => ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
        Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) T) := by
    ext T; simp only [Set.mem_setOf_eq, Set.forall_mem_range]
  rw [hLHS] at hbase
  rw [hbase]
  congr 1
  congr 1
  ext T
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨X, M, hM, rfl⟩
    refine ⟨X, M, ?_, rfl⟩
    rw [← commutant_unitaryTensorPow_eq_permSpan dR n]
    intro Y hY
    obtain ⟨U, rfl⟩ := hY
    exact hM (Op.tensorPow (U : Op dR) n) ⟨U, rfl⟩
  · rintro ⟨X, M, hM, rfl⟩
    refine ⟨X, M, ?_, rfl⟩
    intro S hS
    obtain ⟨U, rfl⟩ := hS
    have hmem : M ∈ permSpan dR n := hM
    rw [← commutant_unitaryTensorPow_eq_permSpan dR n] at hmem
    exact hmem (Op.tensorPow (U : Op dR) n) ⟨U, rfl⟩

/-! ## §1c — the step-8 consumer: existence of the permutation expansion -/

/-- Extraction lemma: any `T` in the span of `{X ⊗ P_R(π)}` is a genuine finite sum
`Σ_π M_π ⊗ P_R(π)` over the (finite) symmetric group, via induction on the span membership. -/
private theorem exists_sum_tensor_permRep_of_mem_span
    (dA dR n : ℕ) [NeZero dA] [NeZero dR] [NeZero n] (T : Op (dA ^ n * dR ^ n))
    (hT : T ∈ Submodule.span ℂ
        (setOf fun S : Op (dA ^ n * dR ^ n) => ∃ (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)),
            S = Op.tensor X (permutationRepresentation dR n π))) :
    ∃ M : Equiv.Perm (Fin n) → Op (dA ^ n),
      T = ∑ π : Equiv.Perm (Fin n), Op.tensor (M π) (permutationRepresentation dR n π) := by
  induction hT using Submodule.span_induction with
  | mem S hS =>
      obtain ⟨X, π₀, rfl⟩ := hS
      refine ⟨fun π => if π = π₀ then X else 0, ?_⟩
      rw [Finset.sum_eq_single π₀]
      · simp
      · intro π _ hπ
        simp only [if_neg hπ]
        have hzero : Op.tensor (0 : Op (dA ^ n)) (permutationRepresentation dR n π)
            = (0 : Op (dA ^ n * dR ^ n)) := by
          rw [show (0 : Op (dA ^ n)) = (0 : ℂ) • (0 : Op (dA ^ n)) by simp,
            Op.tensor_smul_left, zero_smul]
        exact hzero
      · intro h; exact absurd (Finset.mem_univ _) h
  | zero => exact ⟨fun _ => 0, by
      have hzero : ∀ π : Equiv.Perm (Fin n),
          Op.tensor (0 : Op (dA ^ n)) (permutationRepresentation dR n π)
            = (0 : Op (dA ^ n * dR ^ n)) := by
        intro π
        rw [show (0 : Op (dA ^ n)) = (0 : ℂ) • (0 : Op (dA ^ n)) by simp,
          Op.tensor_smul_left, zero_smul]
      simp [hzero]⟩
  | add S₁ S₂ _ _ h₁ h₂ =>
      obtain ⟨M₁, hM₁⟩ := h₁
      obtain ⟨M₂, hM₂⟩ := h₂
      refine ⟨fun π => M₁ π + M₂ π, ?_⟩
      rw [hM₁, hM₂, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun π _ => by simp [Op.tensor_add_left]
  | smul c S' _ h =>
      obtain ⟨M', hM'⟩ := h
      refine ⟨fun π => c • M' π, ?_⟩
      rw [hM', Finset.smul_sum]
      exact Finset.sum_congr rfl fun π _ => by simp [Op.tensor_smul_left]

/-- **§1c (the step-8 consumer).** The Haar twirl of the maximally entangled paired projector
expands as a finite sum `Σ_π M_π ⊗ P_R(π)` over the symmetric group (`M` explicitly non-unique
when `dR < n`). `twirlMap_maxEntangledProjectorPaired` identifies the twirl with `twirlMap` of
the projector; `twirlMap_idempotent` shows the result is a fixed point; `twirlMap_eq_iff_commute`
converts the fixed-point property into membership in §1b's commutant set; §1b rewrites this into
the span of `{X ⊗ P_R(π)}`; `exists_sum_tensor_permRep_of_mem_span` extracts the finite sum.
Currently unconsumed: SP1's proof (`SchurWeylFlatten.lean`) goes through §1b directly, without
needing the explicit sum expansion; this lemma is kept as the documented step-8 API form for
future consumers. -/
theorem maxEntangledUnitaryTwirl_eq_sum_tensor_permRep (dA dR n : ℕ)
    [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    ∃ M : Equiv.Perm (Fin n) → Op (dA ^ n),
      maxEntangledUnitaryTwirl dA dR n hdim
        = ∑ π : Equiv.Perm (Fin n), Op.tensor (M π) (permutationRepresentation dR n π) := by
  set T0 : Op (dA ^ n * dR ^ n) := twirlMap dA dR n (maxEntangledProjectorPaired dA dR n hdim)
    with hT0
  have hEq : maxEntangledUnitaryTwirl dA dR n hdim = T0 :=
    twirlMap_maxEntangledProjectorPaired dA dR n hdim
  have hFix : twirlMap dA dR n T0 = T0 := twirlMap_idempotent dA dR n _
  have hComm : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
      Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) T0 :=
    (twirlMap_eq_iff_commute dA dR n T0).mp hFix
  have hMem : T0 ∈ (setOf fun T : Op (dA ^ n * dR ^ n) => ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
      Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) T) := hComm
  rw [commutant_pairedUnitaryTensorPow_eq_tensorPermSpan dA dR n] at hMem
  obtain ⟨M, hM⟩ := exists_sum_tensor_permRep_of_mem_span dA dR n T0 hMem
  exact ⟨M, hEq.trans hM⟩

end InfoTheory.Postselection

end
