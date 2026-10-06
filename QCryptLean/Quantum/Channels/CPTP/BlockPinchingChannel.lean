import QCryptLean.Quantum.Channels.CPTP.FintypeKraus

/-!
# Block-Pinching (Computational-Basis Measurement) Channel

Moved down from `QKD.BB84.Engine.Model` (where it was mis-homed: the construction and its
statements mention no BB84 or QKD-protocol object) to the general quantum-channels layer.
The `n`-round computational-basis (block-diagonal) dephasing channel on `Op (4^n * eveDim)`,
together with its Kraus representation and CPTP proof.

## Main definitions
- `measurementChannel`: n-round computational-basis measurement channel.

## Main statements
- `measurementChannel_isCPTP`: measurement is CPTP.
- `measurementChannel_diag_apply`, `measurementChannel_apply`: the channel's block-diagonal
  entry formula.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-! ## Measurement channel -/

/-- The n-round BB84 computational-basis measurement channel.

    Kraus operators: for each `ωIdx : Fin (4^n)`,
    `K_{ωIdx} = |ωIdx⟩⟨ωIdx|_{4^n} ⊗ I_{eveDim}`, realized as
    `Matrix.reindex finProdFinEquiv finProdFinEquiv (kroneckerMap (·*·) P_ωIdx I)`.

    The channel `M ↦ Σ_{ωIdx} K_{ωIdx} · M · K_{ωIdx}†` dephases
    Alice-Bob's register in the computational basis while leaving Eve's
    ancilla untouched. -/
noncomputable def measurementChannel (n eveDim : ℕ) [NeZero eveDim] :
    Op (4 ^ n * eveDim) →ₗ[ℂ] Op (4 ^ n * eveDim) :=
  let K (ωIdx : Fin (4 ^ n)) : Op (4 ^ n * eveDim) :=
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.kroneckerMap (· * ·)
        (Matrix.single ωIdx ωIdx 1 : Op (4 ^ n))
        (1 : Op eveDim))
  { toFun := fun M =>
      ∑ ωIdx : Fin (4 ^ n), K ωIdx * M * (K ωIdx)ᴴ
    map_add' := fun A B => by
      simp only [mul_add, add_mul, ← Finset.sum_add_distrib]
    map_smul' := fun c A => by
      simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, Finset.smul_sum] }

/-- Matrix-unit Kraus operator that remaps one BB84 outcome block to another and
    leaves Eve's register untouched. -/
private noncomputable def outcomeRemapKraus (n eveDim : ℕ) [NeZero eveDim]
    (outIdx inIdx : Fin (4 ^ n)) : Op (4 ^ n * eveDim) :=
  (Matrix.single outIdx inIdx 1 : Op (4 ^ n)) ⊗ (1 : Op eveDim)

/-- The diagonal outcome-block projector used by the measurement channel. -/
private noncomputable def measurementKraus (n eveDim : ℕ) [NeZero eveDim]
    (ωIdx : Fin (4 ^ n)) : Op (4 ^ n * eveDim) :=
  outcomeRemapKraus n eveDim ωIdx ωIdx

private lemma sum_tensor_right_const {ι : Type*} [Fintype ι] {d e : ℕ}
    (A : ι → Op d) (B : Op e) :
    (∑ i, A i ⊗ B) = (∑ i, A i) ⊗ B := by
  ext p q
  simp only [Op.tensor, Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]
  rw [← Finset.sum_mul]

private lemma outcomeRemapKraus_adjoint_mul (n eveDim : ℕ) [NeZero eveDim]
    (outIdx inIdx : Fin (4 ^ n)) :
    (outcomeRemapKraus n eveDim outIdx inIdx)ᴴ *
      outcomeRemapKraus n eveDim outIdx inIdx =
    measurementKraus n eveDim inIdx := by
  rw [outcomeRemapKraus, measurementKraus, outcomeRemapKraus]
  rw [Op.tensor_conjTranspose, Matrix.conjTranspose_single, conjTranspose_one]
  rw [Op.tensor_mul, Matrix.single_mul_single_same, Matrix.one_mul]
  simp

private lemma measurementKraus_completeness (n eveDim : ℕ) [NeZero eveDim] :
    (∑ ωIdx : Fin (4 ^ n), (measurementKraus n eveDim ωIdx)ᴴ *
      measurementKraus n eveDim ωIdx) = (1 : Op (4 ^ n * eveDim)) := by
  calc
    (∑ ωIdx : Fin (4 ^ n), (measurementKraus n eveDim ωIdx)ᴴ *
      measurementKraus n eveDim ωIdx)
        = ∑ ωIdx : Fin (4 ^ n), measurementKraus n eveDim ωIdx := by
          apply Finset.sum_congr rfl
          intro ωIdx _
          exact outcomeRemapKraus_adjoint_mul n eveDim ωIdx ωIdx
    _ = (∑ ωIdx : Fin (4 ^ n), (Matrix.single ωIdx ωIdx 1 : Op (4 ^ n))) ⊗
        (1 : Op eveDim) := by
          calc
            (∑ ωIdx : Fin (4 ^ n), measurementKraus n eveDim ωIdx)
                = ∑ ωIdx : Fin (4 ^ n),
                    (Matrix.single ωIdx ωIdx 1 : Op (4 ^ n)) ⊗ (1 : Op eveDim) := by
                  simp [measurementKraus, outcomeRemapKraus]
            _ = (∑ ωIdx : Fin (4 ^ n),
                    (Matrix.single ωIdx ωIdx 1 : Op (4 ^ n))) ⊗
                  (1 : Op eveDim) :=
                  sum_tensor_right_const
                    (fun ωIdx : Fin (4 ^ n) =>
                      (Matrix.single ωIdx ωIdx 1 : Op (4 ^ n)))
                    (1 : Op eveDim)
    _ = (1 : Op (4 ^ n)) ⊗ (1 : Op eveDim) := by
          rw [Matrix.sum_single_one]
    _ = (1 : Op (4 ^ n * eveDim)) := by
          rw [Op.tensor_one]

private lemma measurementKrausMap_eq_measurementChannel (n eveDim : ℕ) [NeZero eveDim] :
    krausMapFintype (measurementKraus n eveDim) = measurementChannel n eveDim := by
  ext M
  simp [krausMapFintype, measurementChannel, measurementKraus, outcomeRemapKraus, Op.tensor]

/-- Product coordinates recover the original flattened index. -/
private lemma finProdFinEquiv_div_mod {n m : ℕ} [NeZero m] (j : Fin (n * m)) :
    j = finProdFinEquiv (j.divNat, j.modNat) := by
  ext
  simp [finProdFinEquiv, Fin.coe_divNat, Fin.coe_modNat, Nat.mod_add_div]

private lemma finProdFinEquiv_divNat {n m : ℕ} [NeZero m]
    (a : Fin n) (b : Fin m) :
    (finProdFinEquiv (a, b)).divNat = a := by
  have h := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (a, b))
  rw [finProdFinEquiv_symm_apply] at h
  exact h

/-- Row entries of a measurement Kraus projector are supported only on the
matching outcome/Eve basis vector. -/
private lemma measurementKraus_row_apply_eq (n eveDim : ℕ) [NeZero eveDim]
    (y ωIdx : Fin (4 ^ n)) (e : Fin eveDim) (j : Fin (4 ^ n * eveDim)) :
    measurementKraus n eveDim y (finProdFinEquiv (ωIdx, e)) j =
      if y = ωIdx ∧ j = finProdFinEquiv (ωIdx, e) then 1 else 0 := by
  rw [finProdFinEquiv_div_mod j]
  by_cases hy : y = ωIdx <;>
  by_cases hdiv : j.divNat = ωIdx <;>
  by_cases hmod : j.modNat = e <;>
  simp [measurementKraus, outcomeRemapKraus, Op.tensor, Matrix.single_apply,
    Matrix.one_apply, hy, hdiv, hmod] <;> aesop

/-- The BB84 measurement channel leaves diagonal outcome/Eve entries unchanged. -/
lemma measurementChannel_diag_apply (n eveDim : ℕ) [NeZero eveDim]
    (M : Op (4 ^ n * eveDim)) (ωIdx : Fin (4 ^ n)) (e : Fin eveDim) :
    (measurementChannel n eveDim M)
      (finProdFinEquiv (ωIdx, e)) (finProdFinEquiv (ωIdx, e)) =
    M (finProdFinEquiv (ωIdx, e)) (finProdFinEquiv (ωIdx, e)) := by
  rw [← measurementKrausMap_eq_measurementChannel]
  unfold krausMapFintype
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  rw [Finset.sum_eq_single ωIdx]
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, measurementKraus_row_apply_eq]
  · intro y _ hy
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, measurementKraus_row_apply_eq, hy]
  · intro h
    exact (h (Finset.mem_univ ωIdx)).elim

/-- The BB84 measurement channel preserves precisely the entries inside one
outcome block and kills coherences between different outcome blocks. -/
lemma measurementChannel_apply (n eveDim : ℕ) [NeZero eveDim]
    (M : Op (4 ^ n * eveDim)) (i j : Fin (4 ^ n * eveDim)) :
    (measurementChannel n eveDim M) i j =
      if i.divNat = j.divNat then M i j else 0 := by
  rw [finProdFinEquiv_div_mod i, finProdFinEquiv_div_mod j]
  rw [← measurementKrausMap_eq_measurementChannel]
  unfold krausMapFintype
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  by_cases h : i.divNat = j.divNat
  · rw [Finset.sum_eq_single i.divNat]
    · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, measurementKraus_row_apply_eq,
        finProdFinEquiv_divNat, h]
    · intro y _ hy
      have hy' : y ≠ j.divNat := by
        intro hyj
        exact hy (hyj.trans h.symm)
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, measurementKraus_row_apply_eq,
        hy, hy']
    · intro hmem
      exact (hmem (Finset.mem_univ i.divNat)).elim
  · simp only [finProdFinEquiv_divNat, h, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hyi : y = i.divNat
    · have hyj : y ≠ j.divNat := by
        intro hyj
        exact h (hyi.symm.trans hyj)
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, measurementKraus_row_apply_eq,
        h, hyi]
    · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, measurementKraus_row_apply_eq,
        hyi]

/-- `measurementChannel n eveDim` is CPTP.

    The Kraus operators `K_{ωIdx} = |ωIdx⟩⟨ωIdx| ⊗ I` satisfy `Σ K†K = I`
    because `Σ_{ωIdx} |ωIdx⟩⟨ωIdx| = I_{4^n}` (completeness of the standard basis). -/
theorem measurementChannel_isCPTP (n eveDim : ℕ) [NeZero eveDim]
    [NeZero (4 ^ n * eveDim)] :
    IsCPTP (⇑(measurementChannel n eveDim)) := by
  simpa [measurementKrausMap_eq_measurementChannel n eveDim] using
    (krausMapFintype_isCPTP
      (K := measurementKraus n eveDim)
      (measurementKraus_completeness n eveDim))

end Quantum.Channels

end -- noncomputable section
