import QCryptLean.Quantum.Channels.CPTP.DiamondNormComp
import QCryptLean.Quantum.Channels.CPTP.Reindex

/-!
# Diamond norm under conjugation by register relabellings

A *register relabelling* is `Matrix.reindexLinearEquiv ℂ ℂ e e` for an index bijection
`e : Fin a ≃ Fin a'`: it renames the basis of a register and does nothing else. This module records
what the diamond norm makes of such a renaming on the input register, the output register, or both.

## Main statements

* `diamondNorm_reindex_conj_eq` — conjugating a map by two register relabellings leaves its diamond
  norm **unchanged**:

  `‖R_out ∘ Δ ∘ R_in‖_◇ = ‖Δ‖_◇`.

  No hypothesis on `Δ` at all: not Hermitian preservation, not positivity, not linearity beyond the
  `→ₗ[ℂ]` in its type.

* `diamondNorm_precomp_reindex_eq` — the one-sided input version, `‖Δ ∘ R_in‖_◇ = ‖Δ‖_◇`, proved by
  a different mechanism: two applications of `diamondNorm_precomp_cptp_le`, the second on the
  inverse relabelling. It charges a conjugate-transpose-preservation hypothesis on `Δ` and is the
  form a caller reaches for when only the input register is being re-read.

## Why this is an equality and not just `≤`

`Quantum.Channels.diamondNorm_sandwich_cptp_le` already gives `≤` for *any* pair of channels
sandwiching `Δ`, and a relabelling is a channel (`Quantum.Channels.reindexLinearEquiv_isCPTP`); but
that route charges a Hermitian-preservation hypothesis on `Δ`, because the general sandwich has to
free the ancilla, and the free-ancilla lemma is the Hermitian-preserving one. Relabellings escape
both the hypothesis and the free-ancilla step, for a reason that is special to them:

* an index bijection `Fin a ≃ Fin a'` forces `a = a'`, so the two supremum's ancilla registers are
  the **same size** and the estimate never leaves the pinned ancilla of the definition;
* `mapTensorId` of a relabelling is again an invertible channel, so it preserves the trace norm
  exactly (`traceNorm_mapTensorId_eq_of_cptp_inverse`) instead of merely contracting it, and it maps
  the admissible set `{X : ‖X‖₁ ≤ 1}` of one supremum **onto** that of the other.

So the two defining suprema are suprema of the same set of reals, and the relabellings drop out.

## Helper statements

* `mapTensorId_id` — `(id ⊗ id_k) = id`.
* `traceNorm_mapTensorId_eq_of_cptp_inverse` — a channel with a channel inverse is trace-norm
  preserving, at every ancilla. Contractivity (`traceNorm_mapTensorId_cptp_contractive`) applied in
  both directions.
* `reindexLinearEquiv_comp_symm` / `reindexLinearEquiv_symm_comp` — the two relabelling round trips.
* `precomp_reindex_preserves_conjTranspose` — precomposing with a relabelling preserves Hermitian
  preservation, the register-side step of every one-sided lift.
-/

open Quantum.Operators Quantum.Metrics Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-! ## Generic helpers -/

/-- **Tensoring the identity map with the identity on an ancilla is the identity.** -/
lemma mapTensorId_id {n k : ℕ} [NeZero n] [NeZero k] (X : Op (n * k)) :
    mapTensorId (LinearMap.id : Op n →ₗ[ℂ] Op n) X = X := by
  ext p q
  rw [mapTensorId_apply_eq_apply_block]
  simp only [LinearMap.id_apply, Matrix.of_apply]
  rw [← finProdFinEquiv.apply_symm_apply p, ← finProdFinEquiv.apply_symm_apply q]
  simp

/-- **A channel with a channel inverse preserves the trace norm, at every ancilla.**
`traceNorm_mapTensorId_cptp_contractive` gives `‖(A ⊗ id)(X)‖₁ ≤ ‖X‖₁`, and the same applied to the
inverse gives `‖X‖₁ = ‖(A' ⊗ id)((A ⊗ id)(X))‖₁ ≤ ‖(A ⊗ id)(X)‖₁`. -/
lemma traceNorm_mapTensorId_eq_of_cptp_inverse {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (A : Op n →ₗ[ℂ] Op m) (hA : IsCPTP ⇑A) (A' : Op m →ₗ[ℂ] Op n) (hA' : IsCPTP ⇑A')
    (hinv : A'.comp A = LinearMap.id) (X : Op (n * k)) :
    traceNorm (mapTensorId A X) = traceNorm X := by
  refine le_antisymm (traceNorm_mapTensorId_cptp_contractive A hA X) ?_
  have hback : mapTensorId (k := k) A' (mapTensorId A X) = X := by
    rw [mapTensorId_comp A A' X, hinv, mapTensorId_id]
  calc traceNorm X = traceNorm (mapTensorId (k := k) A' (mapTensorId A X)) := by rw [hback]
    _ ≤ traceNorm (mapTensorId A X) := traceNorm_mapTensorId_cptp_contractive A' hA' _

/-- A relabelling followed by its inverse relabelling is the identity. -/
lemma reindexLinearEquiv_symm_comp {a a' : ℕ} (e : Fin a ≃ Fin a') :
    (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap.comp
        (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap =
      (LinearMap.id : Op a →ₗ[ℂ] Op a) := by
  refine LinearMap.ext fun M => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
  rw [Matrix.reindexLinearEquiv_comp_apply, Equiv.self_trans_symm,
    Matrix.reindexLinearEquiv_refl_refl]
  rfl

/-- The inverse relabelling followed by the relabelling is the identity. -/
lemma reindexLinearEquiv_comp_symm {a a' : ℕ} (e : Fin a ≃ Fin a') :
    (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp
        (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap =
      (LinearMap.id : Op a' →ₗ[ℂ] Op a') := by
  simpa using reindexLinearEquiv_symm_comp e.symm

/-! ## The invariance -/

/-- **Conjugating by two register relabellings does not change the diamond norm.**

`‖R_out ∘ Δ ∘ R_in‖_◇ = ‖Δ‖_◇`, for `R_in = reindexLinearEquiv eIn eIn` on the input register and
`R_out = reindexLinearEquiv eOut eOut` on the output register — with **no hypothesis on `Δ`**.

An index bijection `eIn : Fin a ≃ Fin a'` forces `a = a'`, so both defining suprema are taken at the
same ancilla dimension and the argument never has to free the ancilla. Tensoring `R_in` with the
identity on that ancilla is again an invertible channel, hence a trace-norm-preserving bijection of
the admissible inputs (`traceNorm_mapTensorId_eq_of_cptp_inverse`), and tensoring `R_out` with the
identity preserves the trace norm of the outputs for the same reason. So the two suprema range over
the same set of reals.

`diamondNorm_sandwich_cptp_le` gives the `≤` half directly, since a relabelling is a channel
(`reindexLinearEquiv_isCPTP`), but only under a Hermitian-preservation hypothesis on `Δ`; the
statement here needs none, and it is an equality. -/
theorem diamondNorm_reindex_conj_eq {a a' b b' : ℕ}
    [NeZero a] [NeZero a'] [NeZero b] [NeZero b']
    (eIn : Fin a ≃ Fin a') (eOut : Fin b ≃ Fin b')
    (Δ : Op a' →ₗ[ℂ] Op b) :
    diamondNorm (((Matrix.reindexLinearEquiv ℂ ℂ eOut eOut).toLinearMap.comp Δ).comp
        (Matrix.reindexLinearEquiv ℂ ℂ eIn eIn).toLinearMap) = diamondNorm Δ := by
  obtain rfl : a = a' := by simpa using Fintype.card_congr eIn
  haveI : NeZero (a * a) := ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  haveI : NeZero (b * a) := ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  haveI : NeZero (b' * a) := ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  set RI := (Matrix.reindexLinearEquiv ℂ ℂ eIn eIn).toLinearMap with hRI
  set RI' := (Matrix.reindexLinearEquiv ℂ ℂ eIn.symm eIn.symm).toLinearMap with hRI'
  set RO := (Matrix.reindexLinearEquiv ℂ ℂ eOut eOut).toLinearMap with hRO
  set RO' := (Matrix.reindexLinearEquiv ℂ ℂ eOut.symm eOut.symm).toLinearMap with hRO'
  have hRIcptp : IsCPTP ⇑RI := reindexLinearEquiv_isCPTP eIn
  have hRI'cptp : IsCPTP ⇑RI' := reindexLinearEquiv_isCPTP eIn.symm
  have hROcptp : IsCPTP ⇑RO := reindexLinearEquiv_isCPTP eOut
  have hRO'cptp : IsCPTP ⇑RO' := reindexLinearEquiv_isCPTP eOut.symm
  -- The trace norm is untouched by tensoring either relabelling with the identity.
  have hIn : ∀ X : Op (a * a), traceNorm (mapTensorId (k := a) RI X) = traceNorm X := fun X =>
    traceNorm_mapTensorId_eq_of_cptp_inverse RI hRIcptp RI' hRI'cptp
      (reindexLinearEquiv_symm_comp eIn) X
  have hIn' : ∀ X : Op (a * a), traceNorm (mapTensorId (k := a) RI' X) = traceNorm X := fun X =>
    traceNorm_mapTensorId_eq_of_cptp_inverse RI' hRI'cptp RI hRIcptp
      (reindexLinearEquiv_comp_symm eIn) X
  have hOut : ∀ Y : Op (b * a), traceNorm (mapTensorId (k := a) RO Y) = traceNorm Y := fun Y =>
    traceNorm_mapTensorId_eq_of_cptp_inverse RO hROcptp RO' hRO'cptp
      (reindexLinearEquiv_symm_comp eOut) Y
  -- The composite, unfolded one relabelling at a time.
  have hsplit : ∀ X : Op (a * a),
      mapTensorId (k := a) ((RO.comp Δ).comp RI) X =
        mapTensorId (k := a) RO (mapTensorId (k := a) Δ (mapTensorId (k := a) RI X)) := by
    intro X
    rw [mapTensorId_comp Δ RO (mapTensorId RI X), mapTensorId_comp RI (RO.comp Δ) X]
  refine le_antisymm ?_ ?_
  · refine diamondNorm_le_of_forall _ _ fun X hX => ?_
    rw [hsplit X, hOut]
    exact traceNorm_mapTensorId_le_diamondNorm_pinned Δ _ (by rw [hIn X]; exact hX)
  · refine diamondNorm_le_of_forall _ _ fun Y hY => ?_
    have hX : traceNorm (mapTensorId (k := a) RI' Y) ≤ 1 := by rw [hIn' Y]; exact hY
    have hback : mapTensorId (k := a) RI (mapTensorId (k := a) RI' Y) = Y := by
      rw [mapTensorId_comp RI' RI Y, reindexLinearEquiv_comp_symm eIn, mapTensorId_id]
    have := traceNorm_mapTensorId_le_diamondNorm_pinned ((RO.comp Δ).comp RI)
      (mapTensorId (k := a) RI' Y) hX
    rwa [hsplit, hback, hOut] at this

/-! ## The one-sided input version -/

/-- **Precomposing with a register relabelling preserves Hermitian preservation.**

If `Δ` sends `Mᴴ` to `(Δ M)ᴴ` then so does `Δ ∘ R` for `R = reindexLinearEquiv ℂ ℂ e e`, because a
relabelling commutes with `ᴴ`: `Matrix.reindex e e Mᴴ = (Matrix.reindex e e M)ᴴ`.

This is the register-side step every Kitaev–Watrous lift on a relabelled input register spends, and
it is stated once here rather than re-derived at each caller.  `diamondNorm_precomp_reindex_eq`
below consumes it. -/
theorem precomp_reindex_preserves_conjTranspose {a a' p : ℕ}
    (e : Fin a ≃ Fin a') (Δ : Op a' →ₗ[ℂ] Op p)
    (hHP : ∀ M : Op a', Δ Mᴴ = (Δ M)ᴴ) (M : Op a) :
    (Δ.comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) Mᴴ =
      ((Δ.comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) M)ᴴ := by
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.reindexLinearEquiv_apply]
  rw [show Matrix.reindex e e Mᴴ = (Matrix.reindex e e M)ᴴ from by simp]
  exact hHP _

/-- **Precomposing a Hermitian-preserving map with a register relabelling leaves the diamond norm
unchanged.**

`‖Δ ∘ R‖_◇ = ‖Δ‖_◇` for `R = reindexLinearEquiv ℂ ℂ e e` the relabelling induced by
`e : Fin a ≃ Fin a'`, given that `Δ` preserves the conjugate transpose.

Both halves come from `diamondNorm_precomp_cptp_le`, which contracts the diamond norm under
precomposition by a CPTP map: `≤` applied to `Δ` and `R`, and `≥` applied to `Δ ∘ R` and the inverse
relabelling `R⁻¹`, whose composite `Δ ∘ R ∘ R⁻¹` is `Δ` by `reindexLinearEquiv_comp_symm`. That a
relabelling is CPTP is `reindexLinearEquiv_isCPTP`.

The Hermitian-preservation premise belongs to this retained signature and its proof through
`diamondNorm_precomp_cptp_le`; it is not necessary for equality under an invertible relabelling.
Specializing `diamondNorm_reindex_conj_eq` above to the identity output relabelling gives that
equality without the premise. By contrast, precomposition with a noninvertible CPTP map can
strictly decrease the norm: for `Δ : ρ ↦ ρ - (Tr ρ) • I / 2` on `Op 2` and a completely
depolarizing `B`, one has `Δ ∘ B = 0`. This example concerns generic CPTP precomposition,
not a necessity claim about relabellings. -/
theorem diamondNorm_precomp_reindex_eq {a a' p : ℕ} [NeZero a] [NeZero a'] [NeZero p]
    (e : Fin a ≃ Fin a') (Δ : Op a' →ₗ[ℂ] Op p)
    (hHP : ∀ M : Op a', Δ Mᴴ = (Δ M)ᴴ) :
    diamondNorm (Δ.comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) = diamondNorm Δ := by
  have hHPc := precomp_reindex_preserves_conjTranspose e Δ hHP
  refine le_antisymm
    (diamondNorm_precomp_cptp_le Δ hHP _ (reindexLinearEquiv_isCPTP e)) ?_
  have h := diamondNorm_precomp_cptp_le
      (Δ.comp (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) hHPc
      (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap
      (reindexLinearEquiv_isCPTP e.symm)
  rwa [LinearMap.comp_assoc, reindexLinearEquiv_comp_symm e, LinearMap.comp_id] at h

end Quantum.Channels

end
