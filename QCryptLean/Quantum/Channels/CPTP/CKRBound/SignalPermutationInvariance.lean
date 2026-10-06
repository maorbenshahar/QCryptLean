import QCryptLean.Quantum.Symmetry.SignalPermutation
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction
import QCryptLean.Quantum.Metrics.KitaevWatrousContraction
import QCryptLean.InfoTheory.DeFinetti.Purification
import QCryptLean.Quantum.Symmetry.SymmetricSubspace

/-!
# Stripping a signal-permutation pre-factor from the CKR tensor trace norm

This file isolates the low-level tensor/permutation trace-norm calculation used by the
channel-generic CKR symmetrization reduction: at a paired permutation-invariant square reference
`τ`, pre-composing a channel with the `n`-site signal permutation `permuteSignalLinear n π`
leaves the CKR tensor trace norm unchanged. Channel-independent; no BB84 or QKD-protocol object.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open Quantum.Metrics
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Tensoring the identity channel with the identity acts as the identity. -/
private lemma mapTensorId_id_eq {n k : ℕ} [NeZero n] [NeZero k]
    (x : Op (n * k)) :
    mapTensorId (LinearMap.id : Op n →ₗ[ℂ] Op n) x = x := by
  ext p q
  simp only [mapTensorId, LinearMap.id_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single p.divNat]
  · rw [Finset.sum_eq_single q.divNat]
    · simp only [finProdFinEquiv_symm_apply, single_apply_same,
        one_mul]
      rw [(finProdFinEquiv_divNat_modNat p).symm,
        (finProdFinEquiv_divNat_modNat q).symm]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    simp [ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Tensoring the signal permutation channel with the identity on an equal-sized
reference register is the corresponding left tensor-factor unitary sandwich. -/
private lemma mapTensorId_permuteSignalLinear_eq_tensor_left
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (π : Equiv.Perm (Fin n)) (x : Op ((4 ^ n) * (4 ^ n))) :
    mapTensorId (permuteSignalLinear n π) x =
      Op.tensor (permutationRepresentation 4 n π) (1 : Op (4 ^ n)) * x *
        (Op.tensor (permutationRepresentation 4 n π) (1 : Op (4 ^ n)))ᴴ := by
  have h := mapTensorId_perm_sandwich_eq_comp
    (LinearMap.id : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n)) π
    (fun y => permuteSignalLinear n π y) (permuteSignalLinear_isCPTP n π).1
    (by intro ρ; rfl) x
  simp only [mapTensorId_id_eq] at h
  exact h.symm

/-- Paired permutation invariance moves a left signal-register permutation to the
inverse unitary conjugation on the right reference register. -/
private lemma pairedPermInvariant_left_sandwich_eq_right_inv_sandwich
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (τ : DensityOp ((4 ^ n) * (4 ^ n)))
    (hτ_paired : IsPairedPermInvariant τ)
    (π : Equiv.Perm (Fin n)) :
    Op.tensor (permutationRepresentation 4 n π) (1 : Op (4 ^ n)) * τ.toOp *
        (Op.tensor (permutationRepresentation 4 n π) (1 : Op (4 ^ n)))ᴴ =
      Op.tensor (1 : Op (4 ^ n)) (permutationRepresentation 4 n π)ᴴ * τ.toOp *
        Op.tensor (1 : Op (4 ^ n)) (permutationRepresentation 4 n π) := by
  let U : Op (4 ^ n) := permutationRepresentation 4 n π
  have hτ : Op.tensor U U * τ.toOp * (Op.tensor U U)ᴴ = τ.toOp := by
    simpa [U] using hτ_paired π
  have hUU : Uᴴ * U = 1 := (permutationRepresentation_unitary 4 n π).1
  have hcalc :
      Op.tensor (1 : Op (4 ^ n)) Uᴴ *
            (Op.tensor U U * τ.toOp * (Op.tensor U U)ᴴ) *
          Op.tensor (1 : Op (4 ^ n)) U =
        Op.tensor U (1 : Op (4 ^ n)) * τ.toOp *
          (Op.tensor U (1 : Op (4 ^ n)))ᴴ := by
    simp only [Op.tensor_conjTranspose, conjTranspose_one, Matrix.mul_assoc]
    rw [show Op.tensor Uᴴ Uᴴ * Op.tensor (1 : Op (4 ^ n)) U =
        Op.tensor Uᴴ (1 : Op (4 ^ n)) by
      rw [Op.tensor_mul, mul_one, hUU]]
    rw [← Matrix.mul_assoc (Op.tensor (1 : Op (4 ^ n)) Uᴴ) (Op.tensor U U)
      (τ.toOp * Op.tensor Uᴴ (1 : Op (4 ^ n)))]
    rw [show Op.tensor (1 : Op (4 ^ n)) Uᴴ * Op.tensor U U =
        Op.tensor U (1 : Op (4 ^ n)) by
      rw [Op.tensor_mul, one_mul, hUU]]
  calc
    Op.tensor U (1 : Op (4 ^ n)) * τ.toOp * (Op.tensor U (1 : Op (4 ^ n)))ᴴ
        = Op.tensor (1 : Op (4 ^ n)) Uᴴ *
            (Op.tensor U U * τ.toOp * (Op.tensor U U)ᴴ) *
            Op.tensor (1 : Op (4 ^ n)) U := hcalc.symm
    _ = Op.tensor (1 : Op (4 ^ n)) Uᴴ * τ.toOp *
          Op.tensor (1 : Op (4 ^ n)) U := by
          rw [hτ]

/-- `mapTensorId` of a pre-composed signal permutation at a paired-invariant
state is a right-reference unitary conjugation of `mapTensorId` without the
pre-composition. -/
private lemma mapTensorId_precomp_permuteSignal_pairedPermInvariant_eq_right_conj
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    {dimOut : ℕ} [NeZero dimOut]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((4 ^ n) * (4 ^ n)))
    (hτ_paired : IsPairedPermInvariant τ)
    (π : Equiv.Perm (Fin n)) :
    let U : Op (4 ^ n) := permutationRepresentation 4 n π
    mapTensorId (Δ.comp (permuteSignalLinear n π)) τ.toOp =
      Op.tensor (1 : Op dimOut) Uᴴ * mapTensorId Δ τ.toOp *
        Op.tensor (1 : Op dimOut) U := by
  rw [← mapTensorId_comp (permuteSignalLinear n π) Δ τ.toOp]
  rw [mapTensorId_permuteSignalLinear_eq_tensor_left π τ.toOp]
  rw [pairedPermInvariant_left_sandwich_eq_right_inv_sandwich τ hτ_paired π]
  rw [Quantum.Metrics.KitaevWatrousContraction.kw_mapTensorId_right_ancilla_mul]
  rw [Quantum.Metrics.KitaevWatrousContraction.kw_mapTensorId_left_ancilla_mul]

/-- Auxiliary helper for stripping a pre-composed signal permutation from the CKR
tensor trace norm when the square reference purification is invariant under paired
round permutations. -/
theorem ckrTensorTraceNorm_precomp_permuteSignal_pairedPermInvariant_eq_aux
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    {dimOut : ℕ} [NeZero dimOut]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((4 ^ n) * (4 ^ n)))
    (hτ_paired : IsPairedPermInvariant τ)
    (π : Equiv.Perm (Fin n)) :
    ckrTensorTraceNorm (Δ.comp (permuteSignalLinear n π)) τ =
      ckrTensorTraceNorm Δ τ := by
  unfold ckrTensorTraceNorm
  let U : Op (4 ^ n) := permutationRepresentation 4 n π
  haveI : NeZero (dimOut * (4 ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hUU : Uᴴ * U = 1 := (permutationRepresentation_unitary 4 n π).1
  have hUU' : U * Uᴴ = 1 := (permutationRepresentation_unitary 4 n π).2
  rw [mapTensorId_precomp_permuteSignal_pairedPermInvariant_eq_right_conj
    Δ τ hτ_paired π]
  let V : Op (dimOut * (4 ^ n)) := Op.tensor (1 : Op dimOut) U
  have hVl : Vᴴ * V = 1 := by
    simp [V, U, Op.tensor_conjTranspose, Op.tensor_mul, hUU]
  have hVr : V * Vᴴ = 1 := by
    simp [V, U, Op.tensor_conjTranspose, Op.tensor_mul, hUU']
  apply le_antisymm
  · have h := traceNorm_cptp_contractive_general
      (fun x : Op (dimOut * (4 ^ n)) => Vᴴ * x * (Vᴴ)ᴴ)
      (isCPTP_unitary_conjugation Vᴴ (by simpa using hVr))
      (mapTensorId Δ τ.toOp)
    simpa [V, Op.tensor_conjTranspose] using h
  · have h := traceNorm_cptp_contractive_general
      (fun x : Op (dimOut * (4 ^ n)) => V * x * Vᴴ)
      (isCPTP_unitary_conjugation V hVl)
      (Vᴴ * mapTensorId Δ τ.toOp * V)
    have hcancel :
        V * (Vᴴ * mapTensorId Δ τ.toOp * V) * Vᴴ =
          mapTensorId Δ τ.toOp := by
      calc
        V * (Vᴴ * mapTensorId Δ τ.toOp * V) * Vᴴ
            = (V * Vᴴ) * mapTensorId Δ τ.toOp * (V * Vᴴ) := by
                simp only [Matrix.mul_assoc]
        _ = mapTensorId Δ τ.toOp := by
                rw [hVr]
                simp
    rw [hcancel] at h
    simpa [V, Op.tensor_conjTranspose] using h

end Quantum.Channels
