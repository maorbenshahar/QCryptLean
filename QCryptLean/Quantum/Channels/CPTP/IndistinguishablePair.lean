import QCryptLean.Quantum.Channels.CPTP.DiamondNormComp
import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity

/-!
# Two post-processings that agree on the ideal are `2ε`-indistinguishable on the real

`Quantum/Channels/CPTP/DiamondNormComp.lean` says a diamond-norm bound survives pre- and
post-composition with channels, and `Quantum/Channels/CPTP/DiamondNormAncilla.lean` says a
Hermitian-preserving map's output on a normalised input is bounded by its diamond norm at a free
ancilla. This module spends both on the composability statement the real/ideal formulation of
security is read through:

> if a distinguisher's two post-processings `A₀, A₁` cannot be told apart on the **ideal** system,
> then on the **real** system they are `2‖real − ideal‖_◇`-indistinguishable, at an arbitrary
> retained reference.

Nothing here knows what the real and ideal maps *are*. They are two linear maps
`Φreal, Φideal : Op dMid →ₗ[ℂ] Op dOut'` whose difference preserves the conjugate transpose, and
the theorems below never inspect a protocol, a key register, a flag or a transcript. A protocol
supplies its own `Φreal` and `Φideal` and its own diamond-norm bound; **implementability is not a
consequence of any theorem here**, and a map satisfying these hypotheses is not thereby a channel,
let alone an LOCC one.

## Main statements

* `Quantum.Channels.sandwich_preserves_conjTranspose` — a Hermitian-preserving map stays
  Hermitian-preserving when sandwiched between channels. Both sides are
  `cptp_preserves_conjTranspose`; the hypothesis on the middle map is the only one that cannot be
  derived.
* `Quantum.Channels.traceNorm_mapTensorId_sandwich_le_diamondNorm` — the single-branch bound:
  `‖(A ∘ Δ ∘ B ⊗ id_k)(W)‖₁ ≤ ‖Δ‖_◇` for channels `A, B`, Hermitian-preserving `Δ`, and any `W`
  of trace norm at most `1`. The wrapping is collapsed by `diamondNorm_sandwich_cptp_le` and the
  ancilla is carried by `traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving`.
* `Quantum.Channels.traceNorm_mapTensorId_sandwichPair_le` — **the composition theorem.** For
  channels `A₀, A₁` on the output register and a channel `B` on the input, if
  `A₀ ∘ Φideal ∘ B = A₁ ∘ Φideal ∘ B` then for every ancilla dimension `k` and every `W` on the
  input register tensored with that ancilla, of trace norm at most `1`,

  `‖(A₀ ∘ Φreal ∘ B ⊗ id_k)(W) − (A₁ ∘ Φreal ∘ B ⊗ id_k)(W)‖₁ ≤ 2 · ε`

  whenever `‖Φreal − Φideal‖_◇ ≤ ε`. Insert `± A_i ∘ Φideal ∘ B`: the two ideal terms are equal by
  hypothesis and cancel, leaving `A_i ∘ (Φreal − Φideal) ∘ B` in each branch, each within `ε` by the
  single-branch bound, and `Quantum.Metrics.traceNorm_sub_le` adds them.
* `Quantum.Channels.traceNorm_mapTensorId_postcompPair_le` — the same at `B = id`, which is the
  form a client whose input register is the protocol's own reads directly.
* `…_of_isCPTP` variants of the last two — the same statements with the Hermitian-preservation
  hypothesis discharged from `IsCPTP Φreal` and `IsCPTP Φideal`, which is the situation of every
  real/ideal pair of physical maps.

## Hypotheses used by the proofs

* **`A₀`, `A₁`, `B` are assumed CPTP.** Complete positivity is what
  `diamondNorm_postcomp_cptp_le` and `diamondNorm_precomp_cptp_le` consume, through
  `traceNorm_mapTensorId_cptp_contractive` and `diamondNorm_cptp_eq_one`; a positive-but-not-CP map
  need not be contractive after tensoring with the identity on the reference, which is the whole
  point of the diamond norm. Together with complete positivity, trace preservation gives
  `‖B‖_◇ = 1`. These are sufficient hypotheses; no necessity result is asserted here.
* **Hermitian preservation is assumed of the difference, not separately of the two arms.** It is
what
  `traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving` and `diamondNorm_precomp_cptp_le`
  consume for the free-ancilla estimate on general `W`. This records the scope of the available
  lemmas, not a claim that Hermitian preservation is necessary for diamond-norm contraction.
  The channel-pair variants derive it from complete positivity of both arms.
* **`W` is arbitrary of trace norm at most `1`,** not a density operator: the free-ancilla step used
  is the Kitaev–Watrous one. Density-operator inputs are a special case.
* **The reference register `k` is arbitrary and is quantified inside the statement**, so the bound
  holds against a distinguisher holding an arbitrary purifying or entangled system.

References: Portmann–Renner 2021 (arXiv:2102.00021, `qkd.tex:774`, `\label{eq:qkd.security.2}`)
for the composable real/ideal shape and its distinguishing advantage over inputs entangled with a
retained register; Kitaev–Watrous for the free-ancilla reduction used at each branch.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Metrics Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-! ## 1. Sandwiching a Hermitian-preserving map -/

/-- **Sandwiching by channels preserves Hermitian preservation.** `B` and `A` each commute with
`ᴴ` because they are CPTP (`cptp_preserves_conjTranspose`), and `Δ` does by hypothesis, so the
composite does. This is the side condition `diamondNorm_sandwich_cptp_le` and the free-ancilla
lemma both ask for, and no caller has to supply it separately. -/
theorem sandwich_preserves_conjTranspose {dIn dMid dOut' dOut : ℕ}
    [NeZero dIn] [NeZero dMid] [NeZero dOut'] [NeZero dOut]
    (Δ : Op dMid →ₗ[ℂ] Op dOut') (hΔ : ∀ M : Op dMid, Δ Mᴴ = (Δ M)ᴴ)
    (A : Op dOut' →ₗ[ℂ] Op dOut) (hA : IsCPTP ⇑A)
    (B : Op dIn →ₗ[ℂ] Op dMid) (hB : IsCPTP ⇑B) (M : Op dIn) :
    (A ∘ₗ Δ ∘ₗ B) Mᴴ = ((A ∘ₗ Δ ∘ₗ B) M)ᴴ := by
  simp only [LinearMap.comp_apply]
  rw [← cptp_preserves_conjTranspose _ hB M, hΔ (B M),
    ← cptp_preserves_conjTranspose _ hA (Δ (B M))]

/-- **The single-branch bound.** For channels `A`, `B`, a Hermitian-preserving `Δ`, any ancilla
dimension `k` and any `W` of trace norm at most `1`,

`‖(A ∘ Δ ∘ B ⊗ id_k)(W)‖₁ ≤ ‖Δ‖_◇`.

`traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving` carries the ancilla for the composite
— whose own Hermitian preservation is `sandwich_preserves_conjTranspose` — and
`diamondNorm_sandwich_cptp_le` collapses the wrapping back to `Δ`. -/
theorem traceNorm_mapTensorId_sandwich_le_diamondNorm {dIn dMid dOut' dOut k : ℕ}
    [NeZero dIn] [NeZero dMid] [NeZero dOut'] [NeZero dOut] [NeZero k]
    (Δ : Op dMid →ₗ[ℂ] Op dOut') (hΔ : ∀ M : Op dMid, Δ Mᴴ = (Δ M)ᴴ)
    (A : Op dOut' →ₗ[ℂ] Op dOut) (hA : IsCPTP ⇑A)
    (B : Op dIn →ₗ[ℂ] Op dMid) (hB : IsCPTP ⇑B)
    (W : Op (dIn * k)) (hW : traceNorm W ≤ 1) :
    traceNorm (mapTensorId (A ∘ₗ Δ ∘ₗ B) W) ≤ diamondNorm Δ :=
  (traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving _
      (sandwich_preserves_conjTranspose Δ hΔ A hA B hB) W hW).trans
    (diamondNorm_sandwich_cptp_le A hA Δ hΔ B hB)

/-! ## 2. The composition theorem -/

/-- **Two post-processings that agree on the ideal are `2ε`-indistinguishable on the real.**

For linear maps `Φreal, Φideal : Op dMid →ₗ[ℂ] Op dOut'` whose difference preserves the conjugate
transpose, channels `A₀, A₁` on the output register and a channel `B` on the input, if

`A₀ ∘ Φideal ∘ B = A₁ ∘ Φideal ∘ B`

then for every ancilla dimension `k` and every `W` on the input register tensored with that
ancilla, of trace norm at most `1`,

`‖(A₀ ∘ Φreal ∘ B ⊗ id_k)(W) − (A₁ ∘ Φreal ∘ B ⊗ id_k)(W)‖₁ ≤ 2 · ε`

whenever `‖Φreal − Φideal‖_◇ ≤ ε`.

Insert `± A_i ∘ Φideal ∘ B`: the two ideal terms are equal by hypothesis and cancel, leaving
`A_i ∘ (Φreal − Φideal) ∘ B` in each branch; `traceNorm_mapTensorId_sandwich_le_diamondNorm` bounds
each by `‖Φreal − Φideal‖_◇`, and `Quantum.Metrics.traceNorm_sub_le` adds the two.

**No simulator, no ideal resource, no key register and no register split**: the statement never
mentions a protocol, and the two post-processings are otherwise arbitrary among channels. The
factor `2` comes from applying the triangle inequality through the common ideal branch. -/
theorem traceNorm_mapTensorId_sandwichPair_le {dIn dMid dOut' dOut k : ℕ}
    [NeZero dIn] [NeZero dMid] [NeZero dOut'] [NeZero dOut] [NeZero k]
    (Φreal Φideal : Op dMid →ₗ[ℂ] Op dOut')
    (hHerm : ∀ M : Op dMid, (Φreal - Φideal) Mᴴ = ((Φreal - Φideal) M)ᴴ)
    (A₀ A₁ : Op dOut' →ₗ[ℂ] Op dOut) (hA₀ : IsCPTP ⇑A₀) (hA₁ : IsCPTP ⇑A₁)
    (B : Op dIn →ₗ[ℂ] Op dMid) (hB : IsCPTP ⇑B)
    (hideal : A₀ ∘ₗ Φideal ∘ₗ B = A₁ ∘ₗ Φideal ∘ₗ B)
    (ε : ℝ) (hε : diamondNorm (Φreal - Φideal) ≤ ε)
    (W : Op (dIn * k)) (hW : traceNorm W ≤ 1) :
    traceNorm (mapTensorId (A₀ ∘ₗ Φreal ∘ₗ B) W - mapTensorId (A₁ ∘ₗ Φreal ∘ₗ B) W) ≤ 2 * ε := by
  -- One branch: the wrapped difference map is within `ε`, at the free ancilla.
  have hbranch : ∀ A : Op dOut' →ₗ[ℂ] Op dOut, IsCPTP ⇑A →
      traceNorm (mapTensorId (A ∘ₗ (Φreal - Φideal) ∘ₗ B) W) ≤ ε := fun A hA =>
    (traceNorm_mapTensorId_sandwich_le_diamondNorm _ hHerm A hA B hB W hW).trans hε
  -- The wrapped difference map is the difference of the two wrapped branches.
  have hsplit : ∀ A : Op dOut' →ₗ[ℂ] Op dOut,
      mapTensorId (A ∘ₗ (Φreal - Φideal) ∘ₗ B) W =
        mapTensorId (A ∘ₗ Φreal ∘ₗ B) W - mapTensorId (A ∘ₗ Φideal ∘ₗ B) W := by
    intro A
    rw [show A ∘ₗ (Φreal - Φideal) ∘ₗ B = (A ∘ₗ Φreal ∘ₗ B) - (A ∘ₗ Φideal ∘ₗ B) by
      rw [LinearMap.sub_comp, LinearMap.comp_sub]]
    rw [mapTensorId_linearMap_sub]
  -- The ideal cross-terms are equal, so they cancel.
  have hkey :
      mapTensorId (A₀ ∘ₗ Φreal ∘ₗ B) W - mapTensorId (A₁ ∘ₗ Φreal ∘ₗ B) W =
        mapTensorId (A₀ ∘ₗ (Φreal - Φideal) ∘ₗ B) W -
          mapTensorId (A₁ ∘ₗ (Φreal - Φideal) ∘ₗ B) W := by
    rw [hsplit A₀, hsplit A₁, hideal]
    abel
  rw [hkey]
  calc traceNorm _
      ≤ traceNorm (mapTensorId (A₀ ∘ₗ (Φreal - Φideal) ∘ₗ B) W) +
          traceNorm (mapTensorId (A₁ ∘ₗ (Φreal - Φideal) ∘ₗ B) W) := traceNorm_sub_le _ _
    _ ≤ ε + ε := add_le_add (hbranch A₀ hA₀) (hbranch A₁ hA₁)
    _ = 2 * ε := by ring

/-- **The composition theorem with nothing on the input side** —
`traceNorm_mapTensorId_sandwichPair_le` at `B = id`, which is the form a client whose input
register is the real map's own reads directly. -/
theorem traceNorm_mapTensorId_postcompPair_le {dMid dOut' dOut k : ℕ}
    [NeZero dMid] [NeZero dOut'] [NeZero dOut] [NeZero k]
    (Φreal Φideal : Op dMid →ₗ[ℂ] Op dOut')
    (hHerm : ∀ M : Op dMid, (Φreal - Φideal) Mᴴ = ((Φreal - Φideal) M)ᴴ)
    (A₀ A₁ : Op dOut' →ₗ[ℂ] Op dOut) (hA₀ : IsCPTP ⇑A₀) (hA₁ : IsCPTP ⇑A₁)
    (hideal : A₀ ∘ₗ Φideal = A₁ ∘ₗ Φideal)
    (ε : ℝ) (hε : diamondNorm (Φreal - Φideal) ≤ ε)
    (W : Op (dMid * k)) (hW : traceNorm W ≤ 1) :
    traceNorm (mapTensorId (A₀ ∘ₗ Φreal) W - mapTensorId (A₁ ∘ₗ Φreal) W) ≤ 2 * ε := by
  have h := traceNorm_mapTensorId_sandwichPair_le (k := k) Φreal Φideal hHerm A₀ A₁ hA₀ hA₁
    LinearMap.id (id_is_cptp dMid) (by simpa using hideal) ε hε W hW
  simpa using h

/-! ## 3. The physical form: both arms are channels

The Hermitian-preservation hypothesis above is a property of the *difference*, which is the minimal
thing the proof consumes. When the two arms are themselves channels — the situation of every
real/ideal pair of physical maps — it is not an extra assumption at all:
`cp_linear_sub_preserves_conjTranspose` derives it from the complete positivity of both. -/

/-- **The composition theorem for a channel pair.** `traceNorm_mapTensorId_sandwichPair_le` with the
Hermitian-preservation hypothesis discharged from `IsCPTP Φreal` and `IsCPTP Φideal`. Only complete
positivity of the two arms is spent; trace preservation is carried because `IsCPTP` is the form a
physical map is normally available in. -/
theorem traceNorm_mapTensorId_sandwichPair_le_of_isCPTP {dIn dMid dOut' dOut k : ℕ}
    [NeZero dIn] [NeZero dMid] [NeZero dOut'] [NeZero dOut] [NeZero k]
    (Φreal Φideal : Op dMid →ₗ[ℂ] Op dOut')
    (hreal : IsCPTP ⇑Φreal) (hideal' : IsCPTP ⇑Φideal)
    (A₀ A₁ : Op dOut' →ₗ[ℂ] Op dOut) (hA₀ : IsCPTP ⇑A₀) (hA₁ : IsCPTP ⇑A₁)
    (B : Op dIn →ₗ[ℂ] Op dMid) (hB : IsCPTP ⇑B)
    (hideal : A₀ ∘ₗ Φideal ∘ₗ B = A₁ ∘ₗ Φideal ∘ₗ B)
    (ε : ℝ) (hε : diamondNorm (Φreal - Φideal) ≤ ε)
    (W : Op (dIn * k)) (hW : traceNorm W ≤ 1) :
    traceNorm (mapTensorId (A₀ ∘ₗ Φreal ∘ₗ B) W - mapTensorId (A₁ ∘ₗ Φreal ∘ₗ B) W) ≤ 2 * ε :=
  traceNorm_mapTensorId_sandwichPair_le Φreal Φideal
    (cp_linear_sub_preserves_conjTranspose _ _ hreal.2.1 hideal'.2.1) A₀ A₁ hA₀ hA₁ B hB hideal ε hε
    W hW

/-- **The post-composition form for a channel pair** — `traceNorm_mapTensorId_postcompPair_le` with
the Hermitian-preservation hypothesis discharged from the complete positivity of both arms. -/
theorem traceNorm_mapTensorId_postcompPair_le_of_isCPTP {dMid dOut' dOut k : ℕ}
    [NeZero dMid] [NeZero dOut'] [NeZero dOut] [NeZero k]
    (Φreal Φideal : Op dMid →ₗ[ℂ] Op dOut')
    (hreal : IsCPTP ⇑Φreal) (hideal' : IsCPTP ⇑Φideal)
    (A₀ A₁ : Op dOut' →ₗ[ℂ] Op dOut) (hA₀ : IsCPTP ⇑A₀) (hA₁ : IsCPTP ⇑A₁)
    (hideal : A₀ ∘ₗ Φideal = A₁ ∘ₗ Φideal)
    (ε : ℝ) (hε : diamondNorm (Φreal - Φideal) ≤ ε)
    (W : Op (dMid * k)) (hW : traceNorm W ≤ 1) :
    traceNorm (mapTensorId (A₀ ∘ₗ Φreal) W - mapTensorId (A₁ ∘ₗ Φreal) W) ≤ 2 * ε :=
  traceNorm_mapTensorId_postcompPair_le Φreal Φideal
    (cp_linear_sub_preserves_conjTranspose _ _ hreal.2.1 hideal'.2.1) A₀ A₁ hA₀ hA₁ hideal ε hε W hW

end Quantum.Channels

end
