import QCryptLean.Quantum.Channels.Stinespring.Minimal.Basic

/-!
# Minimal Stinespring Transport — basis reindexing and environment minimality

This file proves that minimal Stinespring dilations are invariant under finite
input and output basis equivalences.  It provides the output-environment basis
transport used to reindex Stinespring isometries and preserves the minimal
environment dimension of transported channels.

## Main definitions
- `stinespringOutputEnvEquiv`: private equivalence reindexing the output factor of
  an output-environment tensor basis.

## Main statements
- `minimalStinespringDilation_transport_equiv`: a minimal dilation of a channel
  transports to a minimal dilation of a finitely reindexed channel with the same
  environment dimension.
-/

open Quantum.Operators Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Reindex an output-environment tensor basis by changing only the output
coordinate and leaving the environment coordinate fixed. -/
private def stinespringOutputEnvEquiv
    {m m' envDim : ℕ} (eOut : Fin m ≃ Fin m') :
    Fin (m' * envDim) ≃ Fin (m * envDim) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr eOut.symm (Equiv.refl (Fin envDim))).trans finProdFinEquiv)

/-- Rectangular row/column basis transport preserves the Stinespring isometry
equation. -/
private lemma stinespring_transport_isometry_adj_mul
    {n m n' m' envDim : ℕ}
    [NeZero n] [NeZero m] [NeZero n'] [NeZero m'] [NeZero envDim]
    [NeZero (m * envDim)] [NeZero (m' * envDim)]
    (V : Matrix (Fin (m * envDim)) (Fin n) ℂ)
    (eIn : Fin n ≃ Fin n') (eOut : Fin m ≃ Fin m')
    (hV : V† * V = 1) :
    (V.submatrix (stinespringOutputEnvEquiv (envDim := envDim) eOut) eIn.symm)† *
        V.submatrix (stinespringOutputEnvEquiv (envDim := envDim) eOut) eIn.symm =
      (1 : Op n') := by
  rw [Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  rw [hV]
  exact Matrix.submatrix_one_equiv eIn.symm

/-- Transporting the input/output bases of a Stinespring isometry transports the
recovered channel by the same output reindexing. -/
private lemma partialTraceB_stinespring_transport
    {n m n' m' envDim : ℕ}
    [NeZero n] [NeZero m] [NeZero n'] [NeZero m'] [NeZero envDim]
    [NeZero (m * envDim)] [NeZero (m' * envDim)]
    (V : Matrix (Fin (m * envDim)) (Fin n) ℂ)
    (A : Op n') (eIn : Fin n ≃ Fin n') (eOut : Fin m ≃ Fin m') :
    Quantum.TensorProducts.partialTraceB
        (V.submatrix (stinespringOutputEnvEquiv (envDim := envDim) eOut) eIn.symm *
          A *
          (V.submatrix (stinespringOutputEnvEquiv (envDim := envDim) eOut)
            eIn.symm)†) =
      (Quantum.TensorProducts.partialTraceB
        (V * A.submatrix eIn eIn * V†)).submatrix eOut.symm eOut.symm := by
  ext a b
  simp only [Quantum.TensorProducts.partialTraceB, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply, stinespringOutputEnvEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
    Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [← Equiv.sum_comp eIn.symm]
  simp only [Equiv.apply_symm_apply]

/-- Transporting the input and output bases of a recovered dilation recovers
the transported channel. -/
private lemma dilation_recovers_transport
    {n m n' m' envDim : ℕ}
    [NeZero n] [NeZero m] [NeZero n'] [NeZero m'] [NeZero envDim]
    [NeZero (m * envDim)] [NeZero (m' * envDim)]
    (Φ : Op n →ₗ[ℂ] Op m) (Ψ : Op n' →ₗ[ℂ] Op m')
    (V : Matrix (Fin (m * envDim)) (Fin n) ℂ)
    (eIn : Fin n ≃ Fin n') (eOut : Fin m ≃ Fin m')
    (h_reindex : ∀ A : Op n',
      Ψ A = (Φ (A.submatrix eIn eIn)).submatrix eOut.symm eOut.symm)
    (hV_rec : DilationRecovers (⇑Φ) V) :
    DilationRecovers (⇑Ψ)
      (V.submatrix (stinespringOutputEnvEquiv (envDim := envDim) eOut) eIn.symm) := by
  intro A
  rw [h_reindex A, hV_rec (A.submatrix eIn eIn)]
  simpa using
    (partialTraceB_stinespring_transport (V := V) A eIn eOut).symm

/-- Pulling a recovered dilation for a transported channel back along the basis
equivalences recovers the original channel. -/
private lemma dilation_recovers_pullback
    {n m n' m' envDim : ℕ}
    [NeZero n] [NeZero m] [NeZero n'] [NeZero m'] [NeZero envDim]
    [NeZero (m * envDim)] [NeZero (m' * envDim)]
    (Φ : Op n →ₗ[ℂ] Op m) (Ψ : Op n' →ₗ[ℂ] Op m')
    (W : Matrix (Fin (m' * envDim)) (Fin n') ℂ)
    (eIn : Fin n ≃ Fin n') (eOut : Fin m ≃ Fin m')
    (h_reindex : ∀ A : Op n',
      Ψ A = (Φ (A.submatrix eIn eIn)).submatrix eOut.symm eOut.symm)
    (hW_rec : DilationRecovers (⇑Ψ) W) :
    DilationRecovers (⇑Φ)
      (W.submatrix (stinespringOutputEnvEquiv (envDim := envDim) eOut.symm) eIn) := by
  intro B
  let Wback : Matrix (Fin (m * envDim)) (Fin n) ℂ :=
    W.submatrix (stinespringOutputEnvEquiv (envDim := envDim) eOut.symm) eIn
  have htransport :=
    partialTraceB_stinespring_transport
      (V := W) B eIn.symm eOut.symm
  have htransport' :
      Quantum.TensorProducts.partialTraceB (Wback * B * Wback†) =
        (Quantum.TensorProducts.partialTraceB
          (W * B.submatrix eIn.symm eIn.symm * W†)).submatrix eOut eOut := by
    simpa [Wback] using htransport
  rw [htransport']
  have hpartial :
      Quantum.TensorProducts.partialTraceB
          (W * B.submatrix eIn.symm eIn.symm * W†) =
        (Φ B).submatrix eOut.symm eOut.symm := by
    calc
      Quantum.TensorProducts.partialTraceB
          (W * B.submatrix eIn.symm eIn.symm * W†)
          = Ψ (B.submatrix eIn.symm eIn.symm) := (hW_rec _).symm
      _ = (Φ B).submatrix eOut.symm eOut.symm := by
          simpa [Matrix.submatrix_submatrix, ← Equiv.coe_trans, Equiv.self_trans_symm,
            Equiv.symm_trans_self, Equiv.coe_refl, Matrix.submatrix_id_id] using
            h_reindex (B.submatrix eIn.symm eIn.symm)
  have hpush :=
    congrArg (fun M : Op m' => M.submatrix eOut eOut) hpartial
  simpa [Matrix.submatrix_submatrix, ← Equiv.coe_trans, Equiv.self_trans_symm,
            Equiv.symm_trans_self, Equiv.coe_refl, Matrix.submatrix_id_id] using hpush.symm

/-- Transport a minimal Stinespring dilation across finite input and output
basis equivalences.

The hypothesis `h_reindex` says that `Ψ` is obtained from `Φ` by reindexing the
input basis with `eIn` and the output basis with `eOut`.  Since this is unitary
basis transport, the minimal Stinespring environment dimension is preserved. -/
theorem minimalStinespringDilation_transport_equiv
    {n m n' m' envDim : ℕ}
    [NeZero n] [NeZero m] [NeZero n'] [NeZero m'] [NeZero envDim]
    [NeZero (m * envDim)] [NeZero (m' * envDim)]
    (Φ : Op n →ₗ[ℂ] Op m) (Ψ : Op n' →ₗ[ℂ] Op m')
    (eIn : Fin n ≃ Fin n') (eOut : Fin m ≃ Fin m')
    (h_reindex : ∀ A : Op n',
      Ψ A = (Φ (A.submatrix eIn eIn)).submatrix eOut.symm eOut.symm)
    (h_dil : MinimalStinespringDilation Φ envDim) :
    Nonempty (MinimalStinespringDilation Ψ envDim) := by
  let V : Matrix (Fin (m' * envDim)) (Fin n') ℂ :=
    h_dil.isometry.submatrix (stinespringOutputEnvEquiv (envDim := envDim) eOut)
      eIn.symm
  refine ⟨
    { isometry := V
      isometry_adj_mul := ?_
      recovers := ?_
      env_minimal := ?_ }⟩
  · simpa [V] using
      stinespring_transport_isometry_adj_mul
        (V := h_dil.isometry) eIn eOut h_dil.isometry_adj_mul
  · simpa [V] using
      dilation_recovers_transport
        (Φ := Φ) (Ψ := Ψ) (V := h_dil.isometry) eIn eOut h_reindex h_dil.recovers
  · intro envDim' _ _ W hW_iso hW_rec
    haveI : NeZero (m * envDim') :=
      ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos m) (NeZero.pos envDim'))⟩
    let Wback : Matrix (Fin (m * envDim')) (Fin n) ℂ :=
      W.submatrix (stinespringOutputEnvEquiv (envDim := envDim') eOut.symm) eIn
    have hWback_iso : Wback† * Wback = (1 : Op n) := by
      simpa [Wback] using
        stinespring_transport_isometry_adj_mul
          (V := W) eIn.symm eOut.symm hW_iso
    have hWback_rec : DilationRecovers (⇑Φ) Wback := by
      simpa [Wback] using
        dilation_recovers_pullback
          (Φ := Φ) (Ψ := Ψ) (W := W) eIn eOut h_reindex hW_rec
    exact h_dil.env_minimal envDim' Wback hWback_iso hWback_rec

end Quantum.Channels
