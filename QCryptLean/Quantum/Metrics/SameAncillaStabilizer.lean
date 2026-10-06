import QCryptLean.Quantum.Metrics.SameAncillaPurification
import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Same-Ancilla Purification Stabilizers — projective tensor-factor uniqueness

Reusable stabilizer facts for the canonical same-ancilla purification. These
results identify when a full-rank same-ancilla purification fixed by tensor
unitaries forces the two tensor factors to agree projectively.

This file is intentionally below CKR-specific reference-state packaging: it
only talks about a full-rank density operator, a real orthogonal unitary on the
purified system, and a unitary on the same-dimensional ancilla.

## Main definitions
- This file defines no new data structures.

## Main statements
- `sameAncillaPurificationDensity_projective_stabilizer_of_tensor_fixed`:
  canonical fixedness by `U ⊗ B` forces `U` and `B` to agree up to scalar.
- `sameAncillaPurificationDensity_projective_right_unitary_of_paired_fixed`:
  right-unitary transported fixedness gives a projective conjugation relation.
- `sameAncillaPurificationDensity_paired_fixed_of_commutes`: the converse
  direction — a real orthogonal unitary commuting with `ρ` fixes the canonical
  purification under the paired action `U ⊗ U`.
- `rightTensorUnitaryConj_paired_fixed_of_commutes`: the same for a transport by
  a unitary that commutes with `U`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics.KitaevWatrousPurification

private lemma op_tensor_one_mulVec_apply {d : ℕ} (A : Op d)
    (v : Fin (d * d) → ℂ) (i j : Fin d) :
    (Op.tensor A (1 : Op d)).mulVec v (finProdFinEquiv (i, j)) =
      ∑ k : Fin d, A i k * v (finProdFinEquiv (k, j)) := by
  simp only [mulVec, dotProduct, Op.tensor, reindex_apply, submatrix_apply,
    kroneckerMap_apply, one_apply, Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  congr 1
  ext k
  simp only [Equiv.symm_apply_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]

private lemma reshapeVec_op_tensor_one_mul_ket {d : ℕ} (A : Op d)
    (ψ : Ket (d * d)) :
    reshapeVec ((Op.tensor A (1 : Op d)) * ψ).vec =
      A * reshapeVec ψ.vec := by
  ext i j
  rw [reshapeVec_apply]
  change (Op.tensor A (1 : Op d)).mulVec ψ.vec (finProdFinEquiv (i, j)) =
    (A * reshapeVec ψ.vec) i j
  rw [op_tensor_one_mulVec_apply, Matrix.mul_apply]
  simp only [reshapeVec_apply]

private lemma reshapeVec_tensor_mul_ket {d : ℕ} (A B : Op d)
    (ψ : Ket (d * d)) :
    reshapeVec ((Op.tensor A B) * ψ).vec =
      A * reshapeVec ψ.vec * Bᵀ := by
  have htensor :
      Op.tensor A B =
        Op.tensor A (1 : Op d) * Op.tensor (1 : Op d) B := by
    rw [Op.tensor_mul, Matrix.mul_one, Matrix.one_mul]
  calc
    reshapeVec ((Op.tensor A B) * ψ).vec =
        reshapeVec (((Op.tensor A (1 : Op d) *
          Op.tensor (1 : Op d) B) * ψ).vec) := by
          rw [htensor]
    _ = reshapeVec
        ((Op.tensor A (1 : Op d) *
          (Op.tensor (1 : Op d) B * ψ : Ket (d * d)) : Ket (d * d)).vec) := by
          rw [← op_op_mul_ket_assoc]
    _ = A * reshapeVec ((Op.tensor (1 : Op d) B * ψ : Ket (d * d)).vec) := by
          rw [reshapeVec_op_tensor_one_mul_ket]
    _ = A * (reshapeVec ψ.vec * Bᵀ) := by
          rw [Quantum.Channels.reshapeVec_one_tensor_mul_ket]
    _ = A * reshapeVec ψ.vec * Bᵀ := by
          rw [Matrix.mul_assoc]

private lemma cfc_sqrt_commutes_of_commutes {d : ℕ} (ρ : DensityOp d) (U : Op d)
    (hcomm : U * ρ.toOp = ρ.toOp * U) :
    U * CFC.sqrt ρ.toOp = CFC.sqrt ρ.toOp * U := by
  let : PartialOrder (Op d) := Matrix.instPartialOrder
  let : StarOrderedRing (Op d) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op d) := Matrix.instNonnegSpectrumClass
  simp only [CFC.sqrt]
  have hc : Commute ρ.toOp U := hcomm.symm
  exact (Commute.cfcₙ_nnreal hc NNReal.sqrt).symm.eq

/-- If an invertible matrix `S` commutes past `U`, then
`U * S * V = β • S` cancels to `U * V = β • 1`. -/
lemma mul_eq_smul_one_of_commute_unit_mul_eq_smul {d : ℕ}
    (S U V : Op d) (β : ℂ)
    (hS_unit : IsUnit S) (hS_comm : U * S = S * U)
    (hUSV : U * S * V = β • S) :
    U * V = β • (1 : Op d) := by
  apply hS_unit.mul_left_cancel
  calc
    S * (U * V) = (U * S) * V := by
      rw [hS_comm]
      rw [Matrix.mul_assoc]
    _ = β • S := by
      simpa [Matrix.mul_assoc] using hUSV
    _ = S * (β • (1 : Op d)) := by
      rw [Matrix.mul_smul, Matrix.mul_one]

/-- If `U` is unitary and `U * V` is scalar, then `V` is the same scalar
multiple of `U†`. -/
lemma eq_smul_conj_transpose_of_unitary_mul_eq_smul_one {d : ℕ}
    (U V : Op d) (β : ℂ)
    (hU_left : U† * U = 1)
    (hUV : U * V = β • (1 : Op d)) :
    V = β • U† := by
  calc
    V = (1 : Op d) * V := by rw [Matrix.one_mul]
    _ = (U† * U) * V := by rw [hU_left]
    _ = U† * (U * V) := by rw [Matrix.mul_assoc]
    _ = U† * (β • (1 : Op d)) := by rw [hUV]
    _ = β • U† := by
      rw [Matrix.mul_smul, Matrix.mul_one]

/-- For matrices with `Uᵀ = U†`, a scalar transpose-adjoint relation
transposes back to the same scalar relation with `U`. -/
lemma eq_smul_of_transpose_eq_smul_conj_transpose {d : ℕ}
    (U V : Op d) (β : ℂ)
    (hU_transpose : Uᵀ = U†)
    (hV_transpose : Vᵀ = β • U†) :
    V = β • U := by
  have hU_conjTranspose_transpose : U†ᵀ = U := by
    have h := congrArg Matrix.transpose hU_transpose
    simpa [Matrix.transpose_transpose] using h.symm
  have hV_transpose' := congrArg Matrix.transpose hV_transpose
  simpa [Matrix.transpose_transpose, Matrix.transpose_smul, hU_conjTranspose_transpose]
    using hV_transpose'

/-- If a left-unitary operator fixes a rank-one ket projector, then it fixes
the ket up to a global phase. -/
lemma ket_eq_mod_phase_of_unitary_ketbra_fixed {n : ℕ} [NeZero n]
    (A : Op n) (ψ : Ket n)
    (hψ_norm : ψ.dag * ψ = 1)
    (hA_adj_mul : A† * A = 1)
    (hfixed : A * (ψ * ψ.dag) * A† = ψ * ψ.dag) :
    ∃ θ : ℝ, ∀ i : Fin n,
      (A * ψ).vec i = Complex.exp (Complex.I * θ) * ψ.vec i := by
  have hAψ_norm : (A * ψ).dag * (A * ψ) = 1 := by
    rw [dag_op_mul_ket]
    rw [braop_mul_ket]
    rw [op_op_mul_ket_assoc, hA_adj_mul]
    simpa [bra_mul_ket_eq, op_mul_ket_vec] using hψ_norm
  have hket : (A * ψ) * (A * ψ).dag = ψ * ψ.dag :=
    (op_mul_ketbra_mul_conjTranspose A ψ).symm.trans hfixed
  exact ket_eq_mod_phase_of_ketbra_eq (A * ψ) ψ hAψ_norm hψ_norm hket

/-- Full-rank same-ancilla stabilizer uniqueness.

If the canonical same-ancilla purification projector of a full-rank density
operator is fixed by `U ⊗ B`, where `U` commutes with the density matrix and is a
real orthogonal unitary (`Uᵀ = U†`), then the two tensor factors agree
projectively. The scalar orientation is chosen so that transported
right-unitary conjugation lemmas can use it directly. -/
theorem sameAncillaPurificationDensity_projective_stabilizer_of_tensor_fixed
    {d : ℕ} [NeZero d] (ρ : DensityOp d) (U B : Op d)
    (hρ_posDef : ρ.toOp.PosDef)
    (hU_unitary : U† * U = 1 ∧ U * U† = 1)
    (hB_unitary : B† * B = 1 ∧ B * B† = 1)
    (hU_comm : U * ρ.toOp = ρ.toOp * U)
    (hU_transpose : Uᵀ = U†)
    (hfixed :
      Op.tensor U B * (sameAncillaPurificationDensity ρ).toOp *
          (Op.tensor U B)† =
        (sameAncillaPurificationDensity ρ).toOp) :
    ∃ α : ℂ, U = α • B := by
  let ψ : Ket (d * d) := sameAncillaPurificationKet ρ
  let S : Op d := CFC.sqrt ρ.toOp
  have hψ_norm : ψ.dag * ψ = 1 := by
    dsimp [ψ]
    exact sameAncillaPurificationKet_normalized ρ
  have hP : (sameAncillaPurificationDensity ρ).toOp = ψ * ψ.dag := by
    dsimp [ψ]
    rw [sameAncillaPurificationDensity_eq_fromPure_sameAncillaPurificationKet]
    rfl
  have hA_adj_mul : (Op.tensor U B)† * Op.tensor U B = 1 := by
    exact tensor_conj_transpose_mul_self_of_conj_transpose_mul_self
      U B hU_unitary.1 hB_unitary.1
  have hfixed_ketbra :
      Op.tensor U B * (ψ * ψ.dag) * (Op.tensor U B)† =
        ψ * ψ.dag := by
    simpa [hP] using hfixed
  obtain ⟨θ, hθ⟩ :=
    ket_eq_mod_phase_of_unitary_ketbra_fixed
      (Op.tensor U B) ψ hψ_norm hA_adj_mul hfixed_ketbra
  let β : ℂ := Complex.exp (Complex.I * θ)
  have hvec :
      reshapeVec ((Op.tensor U B * ψ).vec) = β • reshapeVec ψ.vec := by
    ext i j
    simp only [reshapeVec_apply, β]
    exact hθ (finProdFinEquiv (i, j))
  have hUSB :
      U * S * Bᵀ = β • S := by
    calc
      U * S * Bᵀ =
          reshapeVec ((Op.tensor U B * ψ).vec) := by
            rw [reshapeVec_tensor_mul_ket, sameAncillaPurificationKet_reshapeVec]
      _ = β • reshapeVec ψ.vec := hvec
      _ = β • S := by
            rw [sameAncillaPurificationKet_reshapeVec]
  have hS_comm : U * S = S * U := by
    dsimp [S]
    exact cfc_sqrt_commutes_of_commutes ρ U hU_comm
  -- `√ρ` is invertible because `ρ` is positive definite.
  have hS_unit : IsUnit S :=
    (CFC.isUnit_sqrt_iff ρ.toOp (Matrix.nonneg_iff_posSemidef.mpr hρ_posDef.posSemidef)).2
      hρ_posDef.isUnit
  have hUBt : U * Bᵀ = β • (1 : Op d) :=
    mul_eq_smul_one_of_commute_unit_mul_eq_smul S U Bᵀ β hS_unit hS_comm hUSB
  have hBt : Bᵀ = β • U† :=
    eq_smul_conj_transpose_of_unitary_mul_eq_smul_one U Bᵀ β hU_unitary.1 hUBt
  have hB : B = β • U :=
    eq_smul_of_transpose_eq_smul_conj_transpose U B β hU_transpose hBt
  refine ⟨β⁻¹, ?_⟩
  calc
    U = β⁻¹ • (β • U) := by
      rw [inv_smul_smul₀ (Complex.exp_ne_zero (Complex.I * θ))]
    _ = β⁻¹ • B := by rw [hB]

/-- Conjugating a unitary matrix by the adjoint action of a unitary again
gives a unitary matrix. -/
lemma unitary_conj_by_adjoint_unitary {d : ℕ} (U : Op d) (W : UnitaryOp d)
    (hU_unitary : U† * U = 1 ∧ U * U† = 1) :
    (W.toOp† * U * W.toOp)† * (W.toOp† * U * W.toOp) = 1 ∧
      (W.toOp† * U * W.toOp) * (W.toOp† * U * W.toOp)† = 1 := by
  constructor
  · simp only [Matrix.conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W.toOp W.toOp† (U * W.toOp),
      W.unitary_right, Matrix.one_mul]
    rw [← Matrix.mul_assoc U† U W.toOp, hU_unitary.1,
      Matrix.one_mul, W.unitary_left]
  · simp only [Matrix.conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W.toOp W.toOp† (U† * W.toOp),
      W.unitary_right, Matrix.one_mul]
    rw [← Matrix.mul_assoc U U† W.toOp, hU_unitary.2,
      Matrix.one_mul, W.unitary_left]

/-- Transported form of the same-ancilla stabilizer uniqueness.

If a right-unitary transport of the canonical same-ancilla purification is fixed
by the paired action `U ⊗ U`, then the right transport conjugates `U`
projectively. -/
theorem sameAncillaPurificationDensity_projective_right_unitary_of_paired_fixed
    {d : ℕ} [NeZero d] (ρ : DensityOp d) (U : Op d) (W : UnitaryOp d)
    (hρ_posDef : ρ.toOp.PosDef)
    (hU_unitary : U† * U = 1 ∧ U * U† = 1)
    (hU_comm : U * ρ.toOp = ρ.toOp * U)
    (hU_transpose : Uᵀ = U†)
    (hfixed :
      Op.tensor U U *
            Quantum.TensorProducts.rightTensorUnitaryConj W
              (sameAncillaPurificationDensity ρ).toOp *
          (Op.tensor U U)† =
        Quantum.TensorProducts.rightTensorUnitaryConj W
          (sameAncillaPurificationDensity ρ).toOp) :
    ∃ α : ℂ, W.toOp * U * W.toOp† = α • U := by
  let B : Op d := W.toOp† * U * W.toOp
  let P : Op (d * d) := (sameAncillaPurificationDensity ρ).toOp
  have hB_unitary : B† * B = 1 ∧ B * B† = 1 := by
    dsimp [B]
    exact unitary_conj_by_adjoint_unitary U W hU_unitary
  have hfixed_canonical :
      Op.tensor U B * (sameAncillaPurificationDensity ρ).toOp *
          (Op.tensor U B)† =
        (sameAncillaPurificationDensity ρ).toOp := by
    have hfixedP :
        Op.tensor U U * Quantum.TensorProducts.rightTensorUnitaryConj W P *
            (Op.tensor U U)† =
          Quantum.TensorProducts.rightTensorUnitaryConj W P := by
      simpa [P] using hfixed
    dsimp [B, P]
    exact Quantum.TensorProducts.right_tensor_unitary_conj_paired_fixed_to_canonical
      (sameAncillaPurificationDensity ρ).toOp U W hfixedP
  obtain ⟨α, hα⟩ :=
    sameAncillaPurificationDensity_projective_stabilizer_of_tensor_fixed
      ρ U B hρ_posDef hU_unitary hB_unitary hU_comm hU_transpose hfixed_canonical
  refine ⟨α, ?_⟩
  calc
    W.toOp * U * W.toOp† = W.toOp * (α • B) * W.toOp† := by rw [hα]
    _ = α • (W.toOp * B * W.toOp†) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = α • U := by
      congr 1
      dsimp [B]
      simp only [Matrix.mul_assoc]
      rw [W.unitary_right, Matrix.mul_one]
      rw [← Matrix.mul_assoc W.toOp W.toOp† U, W.unitary_right, Matrix.one_mul]

/-! ## Sufficient conditions for paired fixedness

The statements above turn fixedness into a projective relation.  The two below go the other
way and exhibit the paired stabilizer explicitly: it contains every real orthogonal unitary
in the commutant of `ρ`, and is transported along any unitary commuting with it.  These are
sufficient conditions.  The projective converse above allows a scalar phase and does not
by itself show that the transporting unitary commutes with the paired unitary. -/

/-- Conjugation reorders across a commuting pair. -/
private lemma conj_swap_of_mul_comm {m : ℕ} (T A P : Op m) (hcomm : T * A = A * T) :
    T * (A * P * A†) * T† = A * (T * P * T†) * A† := by
  have hdag : A† * T† = T† * A† := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hcomm
  calc
    T * (A * P * A†) * T† = (T * A) * P * (A† * T†) := by
      simp only [Matrix.mul_assoc]
    _ = (A * T) * P * (T† * A†) := by rw [hcomm, hdag]
    _ = A * (T * P * T†) * A† := by simp only [Matrix.mul_assoc]

/-- **A real orthogonal unitary in the commutant of `ρ` fixes the canonical same-ancilla
purification under the paired action.**

If `U` is unitary with `Uᵀ = U†` and `U ρ = ρ U`, then

  `(U ⊗ U) · sameAncillaPurificationDensity ρ · (U ⊗ U)† = sameAncillaPurificationDensity ρ`.

The mechanism is the vectorization identity `(A ⊗ B) vec(M) = vec(A M Bᵀ)`: the canonical
ket reshapes to `√ρ`, and the paired action sends it to `U √ρ Uᵀ = U √ρ U† = √ρ`, using that
`U` commutes with `√ρ` whenever it commutes with `ρ`.  No full-rank hypothesis is needed
here; the projective converse theorem above assumes positive definiteness of `ρ`. -/
theorem sameAncillaPurificationDensity_paired_fixed_of_commutes
    {d : ℕ} (ρ : DensityOp d) (U : Op d)
    (hU_unitary : U† * U = 1 ∧ U * U† = 1)
    (hU_comm : U * ρ.toOp = ρ.toOp * U)
    (hU_transpose : Uᵀ = U†) :
    Op.tensor U U * (sameAncillaPurificationDensity ρ).toOp * (Op.tensor U U)† =
      (sameAncillaPurificationDensity ρ).toOp := by
  have hket : (Op.tensor U U) * sameAncillaPurificationKet ρ =
      sameAncillaPurificationKet ρ := by
    refine ket_eq_of_reshapeVec_eq ?_
    rw [reshapeVec_tensor_mul_ket, sameAncillaPurificationKet_reshapeVec, hU_transpose,
      cfc_sqrt_commutes_of_commutes ρ U hU_comm, Matrix.mul_assoc, hU_unitary.2,
      Matrix.mul_one]
  have hcanon : (sameAncillaPurificationDensity ρ).toOp =
      sameAncillaPurificationKet ρ * (sameAncillaPurificationKet ρ).dag :=
    sameAncillaPurification_eq_ketbra_sameAncillaPurificationKet ρ
  calc
    Op.tensor U U * (sameAncillaPurificationDensity ρ).toOp * (Op.tensor U U)† =
        Op.tensor U U *
          (sameAncillaPurificationKet ρ * (sameAncillaPurificationKet ρ).dag) *
          (Op.tensor U U)† := by
      rw [hcanon]
    _ = (Op.tensor U U * sameAncillaPurificationKet ρ) *
          (Op.tensor U U * sameAncillaPurificationKet ρ).dag :=
      Quantum.Operators.op_mul_ketbra_mul_conjTranspose _ (sameAncillaPurificationKet ρ)
    _ = (sameAncillaPurificationDensity ρ).toOp := by rw [hket, ← hcanon]

/-- **A right-unitary transport of the canonical purification is paired-fixed as soon as the
transport commutes with the paired unitary.**

This is the transported form of `sameAncillaPurificationDensity_paired_fixed_of_commutes`,
and the exact converse of
`sameAncillaPurificationDensity_projective_right_unitary_of_paired_fixed` in the case where
the projective scalar is `1`. -/
theorem rightTensorUnitaryConj_paired_fixed_of_commutes
    {d : ℕ} (ρ : DensityOp d) (U : Op d) (W : UnitaryOp d)
    (hU_unitary : U† * U = 1 ∧ U * U† = 1)
    (hU_comm : U * ρ.toOp = ρ.toOp * U)
    (hU_transpose : Uᵀ = U†)
    (hUW : U * W.toOp = W.toOp * U) :
    Op.tensor U U *
          Quantum.TensorProducts.rightTensorUnitaryConj W
            (sameAncillaPurificationDensity ρ).toOp *
        (Op.tensor U U)† =
      Quantum.TensorProducts.rightTensorUnitaryConj W
        (sameAncillaPurificationDensity ρ).toOp := by
  have hcomm :
      Op.tensor U U * Op.tensor (1 : Op d) W.toOp =
        Op.tensor (1 : Op d) W.toOp * Op.tensor U U := by
    rw [Op.tensor_mul, Op.tensor_mul, Matrix.mul_one, Matrix.one_mul, hUW]
  rw [Quantum.TensorProducts.rightTensorUnitaryConj,
    conj_swap_of_mul_comm _ _ _ hcomm,
    sameAncillaPurificationDensity_paired_fixed_of_commutes ρ U hU_unitary hU_comm
      hU_transpose]

end Quantum.Metrics.KitaevWatrousPurification

end
