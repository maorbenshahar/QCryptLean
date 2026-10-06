import QCryptLean.Quantum.Channels.CPTP.Basic

/-!
# The twirl over a unitary involution

For a unitary involution `U` (`Uᴴ U = 1` and `U U = 1`) the operators `{1, U}` form a group of
order at most two, and averaging over the two conjugations gives the **twirl**

  `involutionTwirl U ρ = ½ (ρ + U ρ Uᴴ)`.

It is a mixed-unitary channel with Kraus operators `{1/√2, U/√2}`, and it is the projection onto
the operators that commute with `U`: it is idempotent, its outputs are `U`-invariant, and it fixes
exactly the `U`-invariant operators. Consequently it equalizes the expectation values of two
observables exchanged by `U`.

The Hadamard pair `H ⊗ H` fixes `|β₀₀⟩`, exchanges `|β₀₁⟩` and `|β₁₀⟩` and negates `|β₁₁⟩`
(`Quantum.Basis.BellStates.hadamard_tensor_hadamard_mul_bellState00` and its companions). Its
twirl is the two-qubit `X ↔ Z` basis twirl. It averages over `{1, H ⊗ H}` only, so it is not the
Bell-basis dephasing obtained by averaging over the four bilateral Paulis: an operator such as
`|β₀₁⟩⟨β₁₀| + |β₁₀⟩⟨β₀₁|` is a fixed point without being Bell-diagonal.

## Main definitions

- `Quantum.Channels.involutionTwirl U`: the linear map `ρ ↦ ½ (ρ + U ρ Uᴴ)`.
- `Quantum.Channels.involutionTwirlKraus U hU`: its Kraus representation `{1/√2, U/√2}` for a
  unitary `U`.

## Main statements

- `involutionTwirl_isCPTP`: for unitary `U` the twirl is a quantum channel;
  `involutionTwirl_trace` and `involutionTwirl_posSemidef` give trace preservation and
  positivity without a nonzero-dimension hypothesis.
- `involutionTwirl_idem`, `isIdempotentElem_involutionTwirl`: for `U U = 1` the twirl is
  idempotent.
- `involutionTwirl_eq_self_iff`: an operator is fixed exactly when it is `U`-invariant;
  `conj_conj_of_mul_self_eq_one`: for `U U = 1` conjugation by `U` undoes itself, and
  `conj_involutionTwirl`: every output is then `U`-invariant.
- `trace_mul_involutionTwirl`: the Hilbert–Schmidt adjoint of `involutionTwirl U` is
  `involutionTwirl Uᴴ`.
- `involutionTwirl_eq_of_conj_eq`, `trace_mul_involutionTwirl_eq_of_conj_eq`,
  `trace_mul_eq_of_involutionTwirl_eq_self`: two observables exchanged by `U` have the same twirl,
  the same expectation in every twirled state, and the same expectation in every
  twirl-invariant state.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

variable {n : ℕ}

/-- **The twirl over `{1, U}`**: the average `ρ ↦ ½ (ρ + U ρ Uᴴ)` of an operator and its
conjugate by `U`. For a unitary involution `U` this is the twirl over the group `{1, U}`. -/
def involutionTwirl (U : Op n) : Op n →ₗ[ℂ] Op n where
  toFun ρ := (1 / 2 : ℂ) • (ρ + U * ρ * Uᴴ)
  map_add' ρ σ := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' c ρ := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add, smul_comm c]

@[simp] theorem involutionTwirl_apply (U ρ : Op n) :
    involutionTwirl U ρ = (1 / 2 : ℂ) • (ρ + U * ρ * Uᴴ) := rfl

/-- Twirling over the trivial group does nothing. -/
@[simp] theorem involutionTwirl_one : involutionTwirl (1 : Op n) = LinearMap.id := by
  ext1 ρ
  simp only [involutionTwirl_apply, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
    LinearMap.id_apply]
  module

/-- The twirl depends on `U` only up to a phase. -/
theorem involutionTwirl_smul {c : ℂ} (hc : star c * c = 1) (U : Op n) :
    involutionTwirl (c • U) = involutionTwirl U := by
  ext1 ρ
  simp only [involutionTwirl_apply, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hc, one_smul]

/-- The twirl commutes with the adjoint. -/
theorem involutionTwirl_conjTranspose (U ρ : Op n) :
    (involutionTwirl U ρ)ᴴ = involutionTwirl U ρᴴ := by
  simp only [involutionTwirl_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  congr 1
  simp

/-- The twirl preserves positive semidefiniteness, for any `U`. -/
theorem involutionTwirl_posSemidef (U : Op n) {ρ : Op n} (hρ : ρ.PosSemidef) :
    (involutionTwirl U ρ).PosSemidef := by
  rw [involutionTwirl_apply]
  exact (hρ.add (hρ.mul_mul_conjTranspose_same U)).smul (by rw [Complex.le_def]; norm_num)

/-- For unitary `U` the twirl preserves the trace. -/
theorem involutionTwirl_trace {U : Op n} (hU : Uᴴ * U = 1) (ρ : Op n) :
    (involutionTwirl U ρ).trace = ρ.trace := by
  rw [involutionTwirl_apply, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_mul_cycle,
    hU, Matrix.one_mul, smul_eq_mul]
  ring

/-- **The Kraus representation of the twirl over a unitary `U`**: the two Kraus operators are
`1/√2` and `U/√2`, and completeness is the unitarity of `U`. -/
def involutionTwirlKraus (U : Op n) (hU : Uᴴ * U = 1) : KrausRepresentation n n where
  numOps := 2
  operators := ![((√(1 / 2) : ℝ) : ℂ) • (1 : Op n), ((√(1 / 2) : ℝ) : ℂ) • U]
  completeness := by
    have hs : (((√(1 / 2) : ℝ) : ℂ)) * ((√(1 / 2) : ℝ) : ℂ) = 1 / 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
      norm_num
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, hs, hU]
    module

/-- The Kraus representation realizes the twirl. -/
theorem involutionTwirlKraus_applyOp (U : Op n) (hU : Uᴴ * U = 1) :
    (involutionTwirlKraus U hU).applyOp = involutionTwirl U := by
  have hs : (((√(1 / 2) : ℝ) : ℂ)) * ((√(1 / 2) : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  funext ρ
  change (∑ x : Fin 2, (![(((√(1 / 2) : ℝ) : ℂ)) • (1 : Op n),
    (((√(1 / 2) : ℝ) : ℂ)) • U] x) * ρ *
      (![(((√(1 / 2) : ℝ) : ℂ)) • (1 : Op n),
        (((√(1 / 2) : ℝ) : ℂ)) • U] x)ᴴ) = _
  simp only [Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, hs, involutionTwirl_apply]
  module

/-- **For unitary `U` the twirl is a quantum channel** (a mixed-unitary one). -/
theorem involutionTwirl_isCPTP [NeZero n] {U : Op n} (hU : Uᴴ * U = 1) :
    IsCPTP (involutionTwirl U) := by
  rw [← involutionTwirlKraus_applyOp U hU]
  exact (involutionTwirlKraus U hU).is_cptp

/-- An operator is fixed by the twirl exactly when it is invariant under conjugation by `U`. -/
theorem involutionTwirl_eq_self_iff (U ρ : Op n) :
    involutionTwirl U ρ = ρ ↔ U * ρ * Uᴴ = ρ := by
  rw [involutionTwirl_apply]
  constructor
  · intro h
    have h2 : (2 : ℂ) • ((1 / 2 : ℂ) • (ρ + U * ρ * Uᴴ)) = (2 : ℂ) • ρ := by rw [h]
    rw [smul_smul] at h2
    norm_num at h2
    rw [two_smul] at h2
    exact add_left_cancel h2
  · intro h
    rw [h]
    module

/-- For an involution `U` the conjugation `ρ ↦ U ρ Uᴴ` undoes itself. -/
theorem conj_conj_of_mul_self_eq_one {U : Op n} (hU2 : U * U = 1) (ρ : Op n) :
    U * (U * ρ * Uᴴ) * Uᴴ = ρ := by
  have hU2' : Uᴴ * Uᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hU2, Matrix.conjTranspose_one]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2',
    Matrix.mul_one]

/-- For an involution `U` every output of the twirl is `U`-invariant. -/
theorem conj_involutionTwirl {U : Op n} (hU2 : U * U = 1) (ρ : Op n) :
    U * involutionTwirl U ρ * Uᴴ = involutionTwirl U ρ := by
  simp only [involutionTwirl_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, conj_conj_of_mul_self_eq_one hU2, add_comm]

/-- **For an involution `U` the twirl is idempotent.** -/
theorem involutionTwirl_idem {U : Op n} (hU2 : U * U = 1) (ρ : Op n) :
    involutionTwirl U (involutionTwirl U ρ) = involutionTwirl U ρ :=
  (involutionTwirl_eq_self_iff U _).2 (conj_involutionTwirl hU2 ρ)

/-- For an involution `U` the twirl is an idempotent linear map. -/
theorem isIdempotentElem_involutionTwirl {U : Op n} (hU2 : U * U = 1) :
    IsIdempotentElem (involutionTwirl U) :=
  LinearMap.ext fun ρ => involutionTwirl_idem hU2 ρ

/-- **The Hilbert–Schmidt adjoint of the twirl over `U` is the twirl over `Uᴴ`:**
`Tr(A · T_U(ρ)) = Tr(T_{Uᴴ}(A) · ρ)`. -/
theorem trace_mul_involutionTwirl (U A ρ : Op n) :
    (A * involutionTwirl U ρ).trace = (involutionTwirl Uᴴ A * ρ).trace := by
  have hcyc : (A * (U * ρ * Uᴴ)).trace = (Uᴴ * A * U * ρ).trace := by
    rw [show A * (U * ρ * Uᴴ) = (A * U * ρ) * Uᴴ by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm _ Uᴴ]
    simp only [Matrix.mul_assoc]
  simp only [involutionTwirl_apply, Matrix.conjTranspose_conjTranspose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, hcyc]

/-- **Two observables exchanged by an involution have the same twirl.** If `U U = 1` and
`U P Uᴴ = Q`, then also `U Q Uᴴ = P`, so both twirls are `½ (P + Q)`. -/
theorem involutionTwirl_eq_of_conj_eq {U P Q : Op n} (hU2 : U * U = 1) (hPQ : U * P * Uᴴ = Q) :
    involutionTwirl U P = involutionTwirl U Q := by
  have hQP : U * Q * Uᴴ = P := by rw [← hPQ, conj_conj_of_mul_self_eq_one hU2]
  rw [involutionTwirl_apply, involutionTwirl_apply, hPQ, hQP, add_comm]

/-- **The twirl equalizes the expectations of two observables exchanged by `U`**: for a unitary
involution `U` with `U P Uᴴ = Q`, `Tr(P · T(ρ)) = Tr(Q · T(ρ))` for every `ρ`. -/
theorem trace_mul_involutionTwirl_eq_of_conj_eq {U P Q : Op n} (hU : Uᴴ * U = 1)
    (hU2 : U * U = 1) (hPQ : U * P * Uᴴ = Q) (ρ : Op n) :
    (P * involutionTwirl U ρ).trace = (Q * involutionTwirl U ρ).trace := by
  have hself : Uᴴ = U := by
    calc Uᴴ = Uᴴ * (U * U) := by rw [hU2, Matrix.mul_one]
      _ = U := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [trace_mul_involutionTwirl, trace_mul_involutionTwirl, hself,
    involutionTwirl_eq_of_conj_eq hU2 hPQ]

/-- **On a twirl-invariant state, observables exchanged by a unitary `U` have equal
expectations**: if `U P Uᴴ = Q` and `T(ρ) = ρ`, then `Tr(P ρ) = Tr(Q ρ)`. -/
theorem trace_mul_eq_of_involutionTwirl_eq_self {U P Q ρ : Op n} (hU : Uᴴ * U = 1)
    (hPQ : U * P * Uᴴ = Q) (hρ : involutionTwirl U ρ = ρ) :
    (P * ρ).trace = (Q * ρ).trace := by
  have hinv : U * ρ * Uᴴ = ρ := (involutionTwirl_eq_self_iff U ρ).1 hρ
  have hback : Uᴴ * ρ * U = ρ := by
    conv_lhs => rw [← hinv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU,
      Matrix.mul_one]
  calc (P * ρ).trace = (P * (Uᴴ * ρ * U)).trace := by rw [hback]
    _ = (U * P * Uᴴ * ρ).trace := by
      rw [show U * P * Uᴴ * ρ = U * (P * Uᴴ * ρ) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm U]
      simp only [Matrix.mul_assoc]
    _ = (Q * ρ).trace := by rw [hPQ]

end Quantum.Channels
