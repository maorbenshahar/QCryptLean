import QCryptLean.Quantum.Channels.CPTP.DiamondNormAncilla
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.Metrics.TraceNormIntegral

/-!
# Diamond norm — submultiplicativity, and `‖CPTP‖_◇ = 1`

`Quantum.Channels.diamondNorm` (`CPTP/DiamondNorm.lean`) is a norm on superoperators. This module
supplies the two facts that make it *composable*: a channel has diamond norm exactly `1`, and the
diamond norm of a composite is at most the product of the factors' diamond norms. Together they say
that wrapping a superoperator in further quantum processing cannot increase its diamond norm, which
is what makes a security bound of the form `‖real − ideal‖_◇ ≤ ε` survive arbitrary post-processing
with no simulator argument and no loss in `ε`.

## Main statements

* `diamondNorm_cptp_eq_one` — `‖Λ‖_◇ = 1` for every CPTP `Λ`. Both halves are proved: `≤ 1` is
  `traceNorm_mapTensorId_cptp_contractive` applied inside the defining supremum, and `1 ≤` is
  witnessed by the rank-one projector `|0⟩⟨0|` on the joint input-ancilla register, whose image
  under the CPTP map `mapTensorId Λ` is again positive semidefinite of trace `1`.
  `diamondNorm_cptp_le_one` is the upper half on its own.
* `diamondNorm_sub_le_two` — `‖Φ − Ψ‖_◇ ≤ 2` for every pair of channels.
* `diamondNorm_comp_le` — `‖Φ ∘ Λ‖_◇ ≤ ‖Φ‖_◇ · ‖Λ‖_◇`, for `Φ` Hermitian-preserving.
* `diamondNorm_postcomp_cptp_le` — `‖A ∘ Δ‖_◇ ≤ ‖Δ‖_◇` for CPTP `A` and **arbitrary** `Δ`, with no
  side condition at all.
* `diamondNorm_precomp_cptp_le` — the mirror `‖Δ ∘ B‖_◇ ≤ ‖Δ‖_◇` for CPTP `B`; this one does carry
  the Hermitian-preservation hypothesis on `Δ`, for the reason set out next.

## The domain question, and why the two sides are not symmetric

`diamondNorm Φ` for `Φ : Op n →ₗ[ℂ] Op m` is a supremum over inputs `X : Op (n * n)` of trace norm
at most `1` — general `X`, not only density operators, but at an ancilla register **pinned** to the
input dimension `n`. Composition breaks that pin: in `Φ ∘ Λ` with `Λ : Op n →ₗ[ℂ] Op m` and
`Φ : Op m →ₗ[ℂ] Op p`, the operator handed to `Φ` is `(Λ ⊗ id_n)(X) : Op (m * n)`, carrying the
ancilla `n` of the *outer* supremum while `‖Φ‖_◇` is defined at ancilla `m`. So the composition
bound needs the diamond norm at a **free** ancilla.

Two lemmas in `CPTP/DiamondNormAncilla.lean` free the ancilla, and they are not interchangeable:

* `traceNorm_mapTensorId_le_diamondNorm` holds for an arbitrary linear map but only for
  **density-operator** inputs;
* `traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving` holds for an **arbitrary**
  `W : Op (dIn * k)` with `‖W‖₁ ≤ 1` — the full general-input statement — at the price of
  `Δ Mᴴ = (Δ M)ᴴ`.

`(Λ ⊗ id_n)(X)` is not positive semidefinite for general `X`, so only the second is usable here, and
the answer to "general `X`, or `DensityOp` only?" is: **general `X`, with a Hermitian-preservation
hypothesis on the outer map**. That hypothesis is discharged by every map these bounds are applied
to — every CPTP map preserves the conjugate transpose (`cptp_preserves_conjTranspose`), hence so
does any difference of two CPTP maps, which is what a `real − ideal` difference map is — but it is a
real hypothesis and it is written into the statements rather than hidden.

`diamondNorm_postcomp_cptp_le` escapes it entirely, and that is the asymmetry: when the *outer* map
is CPTP the free-ancilla lemma is not needed at all, because
`traceNorm_mapTensorId_cptp_contractive` contracts the trace norm at **every** ancilla with no
hypothesis on the input, so the bound can be taken at the pinned ancilla of the outer supremum. That
is why the corollary the security statements want — post-composing a channel is free — is the one
with no side condition.

## Helper statements

* `traceNorm_mapTensorId_le_diamondNorm_mul_of_hermitianPreserving` is the homogeneous form
  `‖(Φ ⊗ id_k)(W)‖₁ ≤ ‖Φ‖_◇ · ‖W‖₁` of the free-ancilla bound, for `W` of *arbitrary* trace norm.
-/

open Quantum.Operators Quantum.Metrics Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-! ## The homogeneous free-ancilla bound -/

/-- **The free-ancilla bound, made homogeneous.** For a Hermitian-preserving `Φ`, every ancilla `k`
and every `W : Op (dIn * k)` — with **no** normalisation on `W` —

`‖(Φ ⊗ id_k)(W)‖₁ ≤ ‖Φ‖_◇ · ‖W‖₁`.

`traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving` is the case `‖W‖₁ ≤ 1`. The general
case follows by rescaling `W` to `(‖W‖₁ + ε)⁻¹ • W`, which is admissible for every `ε > 0`, and
letting `ε → 0`; the `ε` detour is what avoids having to rule out `‖W‖₁ = 0` separately. -/
theorem traceNorm_mapTensorId_le_diamondNorm_mul_of_hermitianPreserving
    {dIn dOut k : ℕ} [NeZero dIn] [NeZero dOut] [NeZero k]
    (Φ : Op dIn →ₗ[ℂ] Op dOut)
    (hHP : ∀ M : Op dIn, Φ Mᴴ = (Φ M)ᴴ)
    (W : Op (dIn * k)) :
    traceNorm (mapTensorId Φ W) ≤ diamondNorm Φ * traceNorm W := by
  have hD : 0 ≤ diamondNorm Φ := diamondNorm_nonneg Φ
  have hW : 0 ≤ traceNorm W := traceNorm_nonneg W
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  set c := traceNorm W with hc
  set D := diamondNorm Φ with hDdef
  have hεpos : (0:ℝ) < δ / (D + 1) := by positivity
  set ε := δ / (D + 1) with hεdef
  have hcε : (0:ℝ) < c + ε := by linarith
  have hrpos : (0:ℝ) < (c + ε)⁻¹ := inv_pos.mpr hcε
  have hnorm : ‖((((c + ε)⁻¹ : ℝ)) : ℂ)‖ = (c + ε)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hrpos.le]
  have hscale : traceNorm ((((c + ε)⁻¹ : ℝ) : ℂ) • W) ≤ 1 := by
    rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq, hnorm, ← hc]
    rw [inv_mul_le_iff₀ hcε]
    linarith
  have hb := traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving Φ hHP _ hscale
  rw [mapTensorId_smul_basic, Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq, hnorm] at hb
  have h2 : traceNorm (mapTensorId Φ W) ≤ D * (c + ε) := by
    rw [← inv_mul_le_iff₀' hcε]
    exact hb
  have h3 : D * ε ≤ δ := by
    rw [hεdef]
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by linarith : (0:ℝ) < D + 1)]
    nlinarith
  nlinarith

/-! ## `‖CPTP‖_◇ = 1` -/

/-- **A channel has diamond norm at most `1`.** Each input of the defining supremum has trace norm
at most `1`, and `mapTensorId Λ` is again CPTP, hence trace-norm contractive
(`traceNorm_mapTensorId_cptp_contractive`) with no hypothesis on the input. -/
theorem diamondNorm_cptp_le_one {n m : ℕ} [NeZero n] [NeZero m]
    (Λ : Op n →ₗ[ℂ] Op m) (hΛ : IsCPTP ⇑Λ) :
    diamondNorm Λ ≤ 1 := by
  have : NeZero (n * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  have : NeZero (m * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  refine diamondNorm_le_of_forall Λ 1 fun X hX => ?_
  exact (traceNorm_mapTensorId_cptp_contractive Λ hΛ X).trans hX

/-- **A channel has diamond norm exactly `1`.** The lower bound is attained already at the rank-one
projector `|0⟩⟨0|` on the joint input-ancilla register `Op (n * n)`: it has trace norm `1`, and
`mapTensorId Λ` is CPTP, so its image is positive semidefinite (`cptp_preserves_posSemidef`) with
trace `1`, whence trace norm `1`. -/
theorem diamondNorm_cptp_eq_one {n m : ℕ} [NeZero n] [NeZero m]
    (Λ : Op n →ₗ[ℂ] Op m) (hΛ : IsCPTP ⇑Λ) :
    diamondNorm Λ = 1 := by
  have : NeZero (n * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  have : NeZero (m * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  refine le_antisymm (diamondNorm_cptp_le_one Λ hΛ) ?_
  set X : Op (n * n) := Matrix.single 0 0 1 with hXdef
  have hXpsd : X.PosSemidef := stdBasisProj_posSemidef
  have hXtr : X.trace = 1 := stdBasisProj_trace
  have hXnorm : traceNorm X = 1 := by
    rw [traceNorm_posSemidef_eq_trace X hXpsd, hXtr]; simp
  have hcptp := mapTensorId_isCPTP (k := n) Λ hΛ
  have hOutPsd : (mapTensorId Λ X).PosSemidef :=
    cptp_preserves_posSemidef _ hcptp X hXpsd
  have hOutTr : (mapTensorId Λ X).trace = 1 := by
    rw [hcptp.2.2 X, hXtr]
  have hOut : traceNorm (mapTensorId Λ X) = 1 := by
    rw [traceNorm_posSemidef_eq_trace _ hOutPsd, hOutTr]; simp
  calc (1 : ℝ) = traceNorm (mapTensorId Λ X) := hOut.symm
    _ ≤ diamondNorm Λ :=
        traceNorm_mapTensorId_le_diamondNorm_pinned Λ X (le_of_eq hXnorm)

/-- The diamond norm of the difference of two channels is at most two. -/
theorem diamondNorm_sub_le_two {n m : ℕ} [NeZero n] [NeZero m]
    {Φ Ψ : Op n →ₗ[ℂ] Op m} (hΦ : IsCPTP ⇑Φ) (hΨ : IsCPTP ⇑Ψ) :
    diamondNorm (Φ - Ψ) ≤ 2 := by
  calc
    diamondNorm (Φ - Ψ) ≤ diamondNorm Φ + diamondNorm Ψ := diamondNorm_sub_le Φ Ψ
    _ = 2 := by rw [diamondNorm_cptp_eq_one Φ hΦ, diamondNorm_cptp_eq_one Ψ hΨ]; norm_num

/-! ## Submultiplicativity -/

/-- **Submultiplicativity of the diamond norm.**

`‖Φ ∘ Λ‖_◇ ≤ ‖Φ‖_◇ · ‖Λ‖_◇`

for `Φ` Hermitian-preserving and `Λ` arbitrary. The input `X` of the outer supremum is pushed
through `Λ` at the pinned ancilla, giving `‖(Λ ⊗ id_n)(X)‖₁ ≤ ‖Λ‖_◇`, and then through `Φ` at the
*free* ancilla `n` by the homogeneous bound
`traceNorm_mapTensorId_le_diamondNorm_mul_of_hermitianPreserving`, which is where Hermitian
preservation of the outer map is spent. See the module docstring for why the hypothesis is on `Φ`
and not on `Λ`. -/
theorem diamondNorm_comp_le {n m p : ℕ} [NeZero n] [NeZero m] [NeZero p]
    (Φ : Op m →ₗ[ℂ] Op p) (Λ : Op n →ₗ[ℂ] Op m)
    (hHP : ∀ M : Op m, Φ Mᴴ = (Φ M)ᴴ) :
    diamondNorm (Φ ∘ₗ Λ) ≤ diamondNorm Φ * diamondNorm Λ := by
  have : NeZero (n * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  have : NeZero (m * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  have : NeZero (p * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  refine diamondNorm_le_of_forall _ _ fun X hX => ?_
  rw [← mapTensorId_comp Λ Φ X]
  refine (traceNorm_mapTensorId_le_diamondNorm_mul_of_hermitianPreserving
    Φ hHP (mapTensorId Λ X)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (traceNorm_mapTensorId_le_diamondNorm_pinned Λ X hX) (diamondNorm_nonneg Φ)

/-- **Post-composing a channel is free.**

`‖A ∘ Δ‖_◇ ≤ ‖Δ‖_◇` for CPTP `A` and **arbitrary** `Δ` — no Hermitian-preservation hypothesis, no
positivity hypothesis, nothing.

This is the composability corollary the security statements want. Reading `Δ = real − ideal`, it
says that handing the protocol's output to any further quantum processing `A` cannot increase the
distinguishing advantage: a bound `‖real − ideal‖_◇ ≤ ε` is inherited by `A ∘ real − A ∘ ideal`
with the same `ε` and no simulator.

Unlike `diamondNorm_comp_le` this needs no free-ancilla step:
`traceNorm_mapTensorId_cptp_contractive` contracts the trace norm of `mapTensorId A` at every
ancilla for every input, so the estimate is made entirely inside the outer supremum, at its own
pinned ancilla. -/
theorem diamondNorm_postcomp_cptp_le {n m p : ℕ} [NeZero n] [NeZero m] [NeZero p]
    (A : Op m →ₗ[ℂ] Op p) (hA : IsCPTP ⇑A) (Δ : Op n →ₗ[ℂ] Op m) :
    diamondNorm (A ∘ₗ Δ) ≤ diamondNorm Δ := by
  have : NeZero (n * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  have : NeZero (m * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  have : NeZero (p * n) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  refine diamondNorm_le_of_forall _ _ fun X hX => ?_
  rw [← mapTensorId_comp Δ A X]
  exact (traceNorm_mapTensorId_cptp_contractive A hA _).trans
    (traceNorm_mapTensorId_le_diamondNorm_pinned Δ X hX)

/-- **Pre-composing a channel is free**, the mirror of `diamondNorm_postcomp_cptp_le`:
`‖Δ ∘ B‖_◇ ≤ ‖Δ‖_◇` for CPTP `B`. Feeding the map a state that has already been through a channel
cannot increase the diamond norm.

This side **does** carry the Hermitian-preservation hypothesis on `Δ`, because `Δ` is now the outer
map and the composite hands it an operator carrying the ancilla of the *input* register — see the
module docstring. Proof: `diamondNorm_comp_le` followed by `diamondNorm_cptp_eq_one`. -/
theorem diamondNorm_precomp_cptp_le {n m p : ℕ} [NeZero n] [NeZero m] [NeZero p]
    (Δ : Op m →ₗ[ℂ] Op p) (hHP : ∀ M : Op m, Δ Mᴴ = (Δ M)ᴴ)
    (B : Op n →ₗ[ℂ] Op m) (hB : IsCPTP ⇑B) :
    diamondNorm (Δ ∘ₗ B) ≤ diamondNorm Δ := by
  refine (diamondNorm_comp_le Δ B hHP).trans ?_
  rw [diamondNorm_cptp_eq_one B hB, mul_one]

/-- **Sandwiching by channels is free.** The two-sided form of the previous two: for CPTP `A` and
`B` and Hermitian-preserving `Δ`, `‖A ∘ Δ ∘ B‖_◇ ≤ ‖Δ‖_◇`. This is the exact statement that
"wrapping a protocol in more processing costs nothing". -/
theorem diamondNorm_sandwich_cptp_le {n m p q : ℕ} [NeZero n] [NeZero m] [NeZero p] [NeZero q]
    (A : Op p →ₗ[ℂ] Op q) (hA : IsCPTP ⇑A)
    (Δ : Op m →ₗ[ℂ] Op p) (hHP : ∀ M : Op m, Δ Mᴴ = (Δ M)ᴴ)
    (B : Op n →ₗ[ℂ] Op m) (hB : IsCPTP ⇑B) :
    diamondNorm (A ∘ₗ Δ ∘ₗ B) ≤ diamondNorm Δ :=
  (diamondNorm_postcomp_cptp_le A hA (Δ ∘ₗ B)).trans
    (diamondNorm_precomp_cptp_le Δ hHP B hB)

end Quantum.Channels

end
