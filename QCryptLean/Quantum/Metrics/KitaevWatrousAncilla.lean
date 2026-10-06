import QCryptLean.Quantum.Metrics.KitaevWatrous

/-!
# Kitaev–Watrous non-Hermitian reduction at a free ancilla

`Quantum.Metrics.KitaevWatrous.kw_nonhermitian_reduction` reduces a bound on
`‖(Φ ⊗ id)(ρ)‖₁` from positive semidefinite inputs to *all* inputs of trace norm at most `1`, but
only at the **square** ancilla: its input is `X : Op (n * n)`. This module states the same reduction
with the ancilla `k` free, `X : Op (n * k)`.

The `k` in the hypothesis stays pinned to `n`: `kw_nonhermitian_reduction_ancilla` assumes the PSD
bound only at the square ancilla and concludes at every ancilla. That is the completely-bounded
content of the Kitaev–Watrous argument — an ancilla of the input dimension already realises the
worst case — and it is why the steps of the proof are exactly the steps of the square-ancilla
theorem, run one register wider:

1. `kw_psd_ancilla_lift` (already stated at a free ancilla) carries the PSD bound from `n` to
   `k + k` by purifying the reduced state and extracting a substate;
2. `kw_hermitian_bound` (already stated at a free ancilla) turns the PSD bound into a Hermitian
   bound by Jordan decomposition, with no factor loss;
3. the Hermitianizing dilation `H = ½(X ⊗ |0⟩⟨1| + X† ⊗ |1⟩⟨0|)` embeds a non-Hermitian
   `X : Op (n * k)` into a Hermitian operator on `n ⊗ (k + k)` of the same trace norm, whose image
   again has the same trace norm — this is where Hermitian preservation `Φ(M†) = Φ(M)†` is used, and
   it is what avoids the factor-of-2 loss of a Cartesian decomposition.

Step 3 needs the register reindexing `Fin (d * (k + k)) ≃ Fin ((d * k) + (d * k))` that identifies
"ancilla carries the dilation flag" with "the dilation flag carries a `d * k` block", and the
statement that `mapTensorId Φ` commutes with the dilation through it. Those helpers are `private`
to `KitaevWatrous.lean`, hence inaccessible here; they are re-declared below with the ancilla
free.

## Main statement
- `Quantum.Metrics.KitaevWatrous.kw_nonhermitian_reduction_ancilla`

## References
- Kitaev (1997), "Quantum computations: algorithms and error correction"
- Watrous (2002), "Semidefinite programs for completely bounded norms"
- Watrous, "The Theory of Quantum Information" (2018), Theorem 3.51 (the non-Hermitian step) and
  Lemma 3.45 (the ancilla pullback)
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics.KitaevWatrous

/-- The dilation reindexing: an ancilla of size `k + k` on a `d`-dimensional register is the same
register as a two-block split of `d * k`. -/
private def ancillaDilationEquiv (d k : ℕ) :
    Fin (d * (k + k)) ≃ Fin ((d * k) + (d * k)) :=
  finProdFinEquiv.symm.trans
    (((Equiv.refl _).prodCongr finSumFinEquiv.symm).trans
      ((Equiv.prodSumDistrib _ _ _).trans
        ((finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv)))

private lemma fpfe_divNat {n m : ℕ} (z : Fin n × Fin m) :
    (finProdFinEquiv z).divNat = z.1 := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv z)
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.fst h).symm

private lemma fpfe_modNat {n m : ℕ} (z : Fin n × Fin m) :
    (finProdFinEquiv z).modNat = z.2 := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv z)
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.snd h).symm

@[simp] private lemma finSumFinEquiv_symm_apply_addNat_self {N : ℕ} (x : Fin N) :
    finSumFinEquiv.symm (x.addNat N) = Sum.inr x := by
  rw [show x.addNat N = Fin.natAdd N x by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm]]
  exact finSumFinEquiv_symm_apply_natAdd (m := N) (x := x)

/-- `mapTensorId Φ` at ancilla `k + k` acts on the reindexed self-adjoint dilation of
`X : Op (n * k)` exactly as `blockMap` of `mapTensorId Φ` at ancilla `k` acts on the dilation. -/
private lemma mapTensorId_selfAdjointDilation_reindex {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (X : Op (n * k)) :
    mapTensorId (k := k + k) Φ
        ((selfAdjointDilation X).submatrix
          (ancillaDilationEquiv n k) (ancillaDilationEquiv n k)) =
      (blockMap (mapTensorId (k := k) Φ) (selfAdjointDilation X)).submatrix
        (ancillaDilationEquiv m k) (ancillaDilationEquiv m k) := by
  ext p q
  rcases hp : finProdFinEquiv.symm p with ⟨a, s⟩
  rcases hq : finProdFinEquiv.symm q with ⟨b, t⟩
  rw [show p = finProdFinEquiv (a, s) by
        simpa [hp] using (finProdFinEquiv.apply_symm_apply p).symm,
      show q = finProdFinEquiv (b, t) by
        simpa [hq] using (finProdFinEquiv.apply_symm_apply q).symm]
  rcases hs : finSumFinEquiv.symm s with s' | s' <;>
    rcases ht : finSumFinEquiv.symm t with t' | t' <;>
    simp [mapTensorId, blockMap, extractBlock, selfAdjointDilation, ancillaDilationEquiv,
      hs, ht, fpfe_divNat, fpfe_modNat, Equiv.prodCongr_apply,
      Equiv.sumCongr_apply, Matrix.of_apply, finSumFinEquiv_symm_apply_castAdd]

/-- **Kitaev–Watrous reduction from PSD inputs to arbitrary inputs, at a free ancilla.**

If `Φ` is Hermitian-preserving and `‖(Φ ⊗ id_n)(ρ)‖₁ ≤ B` for every positive semidefinite `ρ` on
`n ⊗ n` of trace at most `1`, then `‖(Φ ⊗ id_k)(X)‖₁ ≤ B` for **every** ancilla dimension `k` and
**every** `X : Op (n * k)` with `‖X‖₁ ≤ 1` — Hermitian or not, positive or not.

The hypothesis is the square-ancilla one, so this strictly extends
`kw_nonhermitian_reduction`, which is the case `k = n`. The Hermitian-preservation hypothesis
`Φ(M†) = Φ(M)†` is what makes the dilation step lossless; without it the Cartesian decomposition
costs a factor of `2` (Watrous, "The Theory of Quantum Information", Theorem 3.51). -/
theorem kw_nonhermitian_reduction_ancilla {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (B : ℝ) (hB : 0 ≤ B)
    (hHP : ∀ (M : Op n), Φ M.conjTranspose = (Φ M).conjTranspose)
    (hPSD : ∀ (ρ : Op (n * n)), ρ.PosSemidef → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ ρ) ≤ B)
    (X : Op (n * k)) (hX : traceNorm X ≤ 1) :
    traceNorm (mapTensorId Φ X) ≤ B := by
  haveI : NeZero (k + k) := ⟨by have := NeZero.pos k; omega⟩
  by_cases hH : X.IsHermitian
  · exact kw_hermitian_bound (k := k) Φ B hB (kw_psd_ancilla_lift (k := k) Φ B hB hPSD) X hH hX
  · -- Non-Hermitian case: Hermitianizing dilation on the doubled ancilla `k + k`.
    let H0 : Op (n * (k + k)) :=
      (selfAdjointDilation X).submatrix
        (ancillaDilationEquiv n k) (ancillaDilationEquiv n k)
    let H : Op (n * (k + k)) := ((1 / 2 : ℂ) • H0)
    have hH0_herm : H0.IsHermitian :=
      (selfAdjointDilation_isHermitian X).submatrix (ancillaDilationEquiv n k)
    have hH0_tn : traceNorm H0 = traceNorm (selfAdjointDilation X) := by
      simpa [H0] using
        traceNorm_submatrix_equiv (selfAdjointDilation X) (ancillaDilationEquiv n k)
    have hH_herm : H.IsHermitian := by
      simp [H, Matrix.IsHermitian, hH0_herm.eq]
    have hH_eq : traceNorm H = traceNorm X := by
      rw [show traceNorm H = ‖(1 / 2 : ℂ)‖ * traceNorm H0 by
            simp [H, Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq],
        hH0_tn,
        traceNorm_selfAdjointDilation]
      norm_num
      ring_nf
    have hH_norm : traceNorm H ≤ 1 := by
      simpa [hH_eq] using hX
    have hPSD_lift := kw_psd_ancilla_lift (k := k + k) Φ B hB hPSD
    have h_bound := kw_hermitian_bound (k := k + k) Φ B hB hPSD_lift H hH_herm hH_norm
    have h_map_conj : ∀ M : Op (n * k),
        mapTensorId (k := k) Φ M.conjTranspose =
          (mapTensorId (k := k) Φ M).conjTranspose :=
      fun M => mapTensorId_preserves_conjTranspose_of_preserves_conj Φ hHP M
    have h_block :
        blockMap (mapTensorId (k := k) Φ) (selfAdjointDilation X) =
          selfAdjointDilation (mapTensorId (k := k) Φ X) :=
      Quantum.Metrics.blockMap_selfAdjointDilation_of_preserves_conj
        (Ψ := mapTensorId (k := k) Φ)
        (by
          ext p q
          simp [mapTensorId, Matrix.of_apply])
        h_map_conj X
    have h_map_H0 :
        mapTensorId (k := k + k) Φ H0 =
          (selfAdjointDilation (mapTensorId (k := k) Φ X)).submatrix
            (ancillaDilationEquiv m k) (ancillaDilationEquiv m k) := by
      have h_block_sub :
          (blockMap (mapTensorId (k := k) Φ) (selfAdjointDilation X)).submatrix
              (ancillaDilationEquiv m k) (ancillaDilationEquiv m k) =
            (selfAdjointDilation (mapTensorId (k := k) Φ X)).submatrix
              (ancillaDilationEquiv m k) (ancillaDilationEquiv m k) :=
        congrArg (fun M =>
          M.submatrix (ancillaDilationEquiv m k) (ancillaDilationEquiv m k)) h_block
      simpa [H0] using
        (mapTensorId_selfAdjointDilation_reindex Φ X).trans h_block_sub
    have h_target_eq :
        traceNorm (mapTensorId (k := k + k) Φ H) =
          traceNorm (mapTensorId (k := k) Φ X) := by
      rw [show traceNorm (mapTensorId (k := k + k) Φ H) =
            ‖(1 / 2 : ℂ)‖ * traceNorm (mapTensorId (k := k + k) Φ H0) by
            simp [H, mapTensorId_smul_basic,
              Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq],
          h_map_H0, traceNorm_submatrix_equiv, traceNorm_selfAdjointDilation]
      norm_num
      ring_nf
    rw [h_target_eq] at h_bound
    simpa using h_bound

end Quantum.Metrics.KitaevWatrous

end
