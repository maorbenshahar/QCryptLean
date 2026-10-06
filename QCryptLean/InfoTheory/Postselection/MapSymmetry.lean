import QCryptLean.Quantum.Symmetry.Covariance

/-!
# QKD postselection — map-symmetry predicates: Definitions 5, 6, 7 (G5)

Faithful transcription of the map-symmetry definitions of
Nahar–Tupkary–Zhao–Lütkenhaus–Tan 2024
(arXiv:2403.11851, `main.tex`):

- **Definition 5** (permutation-invariance, main.tex:415–421) — exactly the library's
  `Quantum.Symmetry.PermutationCovariant`, re-exported here as
  `InfoTheory.Postselection.IsPermutationInvariantMap`.
- **Definition 6** (IID-group-invariance, main.tex:513–519) —
  `InfoTheory.Postselection.IsIIDGroupInvariantMap`.
- **Definition 7** (IID-block-diagonal, main.tex:532–538) —
  `InfoTheory.Postselection.IsIIDBlockDiagonalMap`.

Definitions 6 and 7 use the per-site tensor `W_h⃗ = ⊗ᵢ W_{hᵢ}` (resp.
`P_i⃗ = ⊗ⱼ Π_{iⱼ}`) of a family of single-round operators, the tensor family
`Quantum.TensorProducts.tensorFamily`.

## Main definitions
- `InfoTheory.Postselection.IsPermutationInvariantMap` : Nahar et al. Def 5 (alias of
`PermutationCovariant`).
- `InfoTheory.Postselection.IsIIDGroupInvariantMap` : Nahar et al. Def 6.
- `InfoTheory.Postselection.IsIIDBlockDiagonalMap` : Nahar et al. Def 7.
-/

open Quantum.Operators Quantum.Channels Quantum.TensorProducts Matrix Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-- **Nahar et al. Definition 5** (permutation-invariance of maps, main.tex:415–421). A linear map
    `Δ ∈ T(Aⁿ, B)` is permutation-invariant if for every `π ∈ Sₙ` there is a
    `Gπ ∈ C(B, B)` with `Gπ ∘ Δ ∘ Wπ = Δ`, where `Wπ(·) = P_π (·) P_π†`.

    This is exactly the library's `PermutationCovariant`; Nahar et al.'s terminology is
    re-exported here for use within the postselection layer. -/
abbrev IsPermutationInvariantMap {d n dimOut : ℕ} [NeZero d] [NeZero n] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut) : Prop :=
  Quantum.Symmetry.PermutationCovariant Δ

/-- **Nahar et al. Definition 6** (IID-group-invariance of maps, main.tex:513–519).
    Given a group `H` with a unitary representation `W` on `A` (dimension `dA`), a linear map
    `Δ ∈ T(Aⁿ, B)` is IID-`H`-invariant if for every `h⃗ ∈ Hⁿ` there is a
    `G_h⃗ ∈ C(B, B)` such that `G_h⃗ ∘ Δ ∘ W_h⃗ = Δ`, where
    `W_h⃗(·) = (⊗ᵢ W_{hᵢ}) (·) (⊗ᵢ W_{hᵢ})†`. -/
structure IsIIDGroupInvariantMap {dA n dimOut : ℕ} [NeZero dA] [NeZero n] [NeZero dimOut]
    {H : Type*} (W : H → UnitaryOp dA)
    (Δ : Op (dA ^ n) →ₗ[ℂ] Op dimOut) : Prop where
  /-- For each `h⃗ ∈ Hⁿ`, a CPTP correction `G_h⃗` intertwines the per-site unitary
      conjugation `W_h⃗` through `Δ`. -/
  invariance : ∀ (h : Fin n → H), ∃ (G : Op dimOut → Op dimOut), IsCPTP G ∧
    ∀ (ρ : Op (dA ^ n)),
      Δ (tensorFamily (fun k => (W (h k)).toOp) * ρ *
          (tensorFamily (fun k => (W (h k)).toOp))ᴴ) = G (Δ ρ)

/-- **Nahar et al. Definition 7** (IID-block-diagonal maps, main.tex:532–538). Given a family of
    (orthogonal) projectors `proj : Fin k → Op A`, a linear map `Δ ∈ T(Aⁿ, B)` is
    IID-block-diagonal if

      `∑_{i⃗ ∈ [k]ⁿ} Δ ∘ P_i⃗ = Δ`,   where `P_i⃗(·) = (⊗ⱼ proj_{iⱼ}) (·) (⊗ⱼ proj_{iⱼ})†`.

    The predicate is stated relative to the given projector family `proj` (assumed
    orthogonal in Nahar et al.'s setup, `proj i * proj j = δᵢⱼ proj i`). -/
structure IsIIDBlockDiagonalMap {dA n dimOut k : ℕ} [NeZero dA] [NeZero n] [NeZero dimOut]
    (proj : Fin k → Op dA) (Δ : Op (dA ^ n) →ₗ[ℂ] Op dimOut) : Prop where
  /-- Summing `Δ` over all per-site projector strings `i⃗ ∈ [k]ⁿ` reconstructs `Δ`. -/
  block_diagonal : ∀ (ρ : Op (dA ^ n)),
    ∑ i : Fin n → Fin k,
      Δ (tensorFamily (fun j => proj (i j)) * ρ *
          (tensorFamily (fun j => proj (i j)))ᴴ) = Δ ρ

/-- **Trivial-group instance of Definition 6**: if every `W h` acts as the identity operator,
then every map is IID-`H`-invariant — the identity correction is CPTP (unitary conjugation
by `1`, `isCPTP_unitary_conjugation`) and conjugation by the identity tensor family is the
identity. -/
lemma isIIDGroupInvariantMap_const_of_toOp_eq_one {dA n dimOut : ℕ} [NeZero dA] [NeZero n]
    [NeZero dimOut] {H : Type*} (W : H → UnitaryOp dA) (hW : ∀ h, (W h).toOp = 1)
    (Δ : Op (dA ^ n) →ₗ[ℂ] Op dimOut) : IsIIDGroupInvariantMap W Δ := by
  refine ⟨fun h => ⟨fun X => X, ?_, ?_⟩⟩
  · -- the identity correction is CPTP: unitary conjugation by `1`
    have h1 : IsCPTP (fun X : Op dimOut => (1 : Op dimOut) * X * (1 : Op dimOut)ᴴ) :=
      Quantum.Symmetry.isCPTP_unitary_conjugation (1 : Op dimOut) (by simp)
    simpa using h1
  · intro ρ
    -- the per-site tensor of identity operators is the identity
    have hT : tensorFamily (fun k => (W (h k)).toOp) = (1 : Op (dA ^ n)) := by
      rw [show (fun k => (W (h k)).toOp) = fun _ => (1 : Op dA)
        from funext fun k => hW (h k), tensorFamily_one]
    simp [hT]

end InfoTheory.Postselection

end
