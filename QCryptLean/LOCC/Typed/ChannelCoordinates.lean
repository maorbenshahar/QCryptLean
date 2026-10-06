import QCryptLean.LOCC.Typed.Channel
import QCryptLean.Quantum.Channels.CPTP.FintypeKraus

/-!
# Explicit coordinates for typed channels

This module transports typed-register linear maps and certified instrument channels to explicit
finite coordinates.  It is independent of typed protocol syntax.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace TypedLOCC

/-- Coordinate a typed-register linear map by explicit input and output equivalences. -/
noncomputable def coordinateLinear {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    {dA dB : ℕ} (eA : A ≃ Fin dA) (eB : B ≃ Fin dB) (Φ : Op A →ₗ[ℂ] Op B) :
    Quantum.Operators.Op dA →ₗ[ℂ] Quantum.Operators.Op dB :=
  (Matrix.reindexLinearEquiv ℂ ℂ eB eB).toLinearMap.comp
    (Φ.comp (Matrix.reindexLinearEquiv ℂ ℂ eA.symm eA.symm).toLinearMap)

/-- Cancelling the explicit input reindex and evaluating at explicit output indices.  This is an
input-reindex cancellation and output-index evaluation formula; it asserts neither CPTP
preservation nor naturality. -/
@[simp] theorem coordinateLinear_reindex_apply
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {dA dB : ℕ} (eA : A ≃ Fin dA) (eB : B ≃ Fin dB) (Φ : Op A →ₗ[ℂ] Op B)
    (ρ : Op A) (i j : B) :
    coordinateLinear eA eB Φ (Matrix.reindex eA eA ρ) (eB i) (eB j) = Φ ρ i j := by
  simp [coordinateLinear, LinearMap.comp_apply, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply]

/-- Entry of a coordinated map: the typed map applied to the pulled-back input operator, read at
the pulled-back output indices. -/
theorem coordinateLinear_apply
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {dA dB : ℕ} (eA : A ≃ Fin dA) (eB : B ≃ Fin dB) (Φ : Op A →ₗ[ℂ] Op B)
    (M : Quantum.Operators.Op dA) (i j : Fin dB) :
    coordinateLinear eA eB Φ M i j = Φ (M.submatrix eA eA) (eB.symm i) (eB.symm j) := by
  simp [coordinateLinear, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply]

/-- A coordinated map sends the explicit coordinates of an operator to the explicit coordinates
of its image. -/
theorem coordinateLinear_reindex
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {dA dB : ℕ} (eA : A ≃ Fin dA) (eB : B ≃ Fin dB) (Φ : Op A →ₗ[ℂ] Op B) (ρ : Op A) :
    coordinateLinear eA eB Φ (Matrix.reindex eA eA ρ) = Matrix.reindex eB eB (Φ ρ) := by
  ext i j
  obtain ⟨i', rfl⟩ := eB.surjective i
  obtain ⟨j', rfl⟩ := eB.surjective j
  rw [coordinateLinear_reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- A coordinated map preserves the trace whenever the typed map does. -/
theorem coordinateLinear_trace
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {dA dB : ℕ} (eA : A ≃ Fin dA) (eB : B ≃ Fin dB) (Φ : Op A →ₗ[ℂ] Op B)
    (hΦ : ∀ N : Op A, (Φ N).trace = N.trace) (M : Quantum.Operators.Op dA) :
    (coordinateLinear eA eB Φ M).trace = M.trace :=
  calc (coordinateLinear eA eB Φ M).trace = (Φ (M.submatrix eA eA)).trace :=
        Fintype.sum_equiv eB.symm _ _ fun i => by
          simp only [Matrix.diag_apply, coordinateLinear_apply]
    _ = (M.submatrix eA eA).trace := hΦ _
    _ = M.trace := Fintype.sum_equiv eA _ _ fun a => by
          simp only [Matrix.diag_apply, Matrix.submatrix_apply]

/-- Coordinating a structural operator reindexing by the corresponding composed input
coordinates cancels it exactly. -/
theorem coordinateLinear_reindexOp_cancel
    {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {d : ℕ}
    (E' : α ≃ β) (eY : β ≃ Fin d) :
    coordinateLinear (E'.trans eY) eY (reindexOp E') = LinearMap.id := by
  apply LinearMap.ext
  intro rho
  ext i j
  simp [coordinateLinear, reindexOp, LinearMap.comp_apply,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply]

/-- Explicit coordinate changes preserve composition. -/
theorem coordinateLinear_comp {A B C : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] {dA dB dC : ℕ}
    (eA : A ≃ Fin dA) (eB : B ≃ Fin dB) (eC : C ≃ Fin dC)
    (Φ : Op A →ₗ[ℂ] Op B) (Ψ : Op B →ₗ[ℂ] Op C) :
    coordinateLinear eA eC (Ψ.comp Φ) =
      (coordinateLinear eB eC Ψ).comp (coordinateLinear eA eB Φ) := by
  ext ρ i j
  simp [coordinateLinear, LinearMap.comp_apply, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply]

/-- Coordinates a matrix-conjugation map by reindexing its Kraus matrix. -/
theorem coordinateMatrixConj_eq {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {dA dB : ℕ} (eA : A ≃ Fin dA) (eB : B ≃ Fin dB) (K : Matrix B A ℂ) :
    coordinateLinear eA eB (matrixConjLinear K) =
      matrixConjLinear (Matrix.reindex eB eA K) := by
  ext ρ i j
  simp only [coordinateLinear, matrixConjLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, Equiv.symm_symm, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.submatrix_apply, Matrix.conjTranspose_submatrix]
  have hρ : ρ = (ρ.submatrix eA eA).submatrix eA.symm eA.symm := by
    ext a b
    simp
  have hmul : K.submatrix eB.symm eA.symm * ρ =
      (K * ρ.submatrix eA eA).submatrix eB.symm eA.symm := by
    calc
      _ = K.submatrix eB.symm eA.symm *
          (ρ.submatrix eA eA).submatrix eA.symm eA.symm := by rw [← hρ]
      _ = _ := Matrix.submatrix_mul_equiv _ _ _ eA.symm _
  rw [hmul]
  exact congrFun (congrFun
    (Matrix.submatrix_mul_equiv
      (K * ρ.submatrix eA eA) Kᴴ eB.symm eA.symm eB.symm).symm i) j

/-- Explicit coordinate changes preserve subtraction of finite-dimensional linear maps.  This is
coordinate bookkeeping for real-minus-ideal maps. -/
theorem coordinateLinear_sub {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {dA dB : ℕ} (eA : A ≃ Fin dA) (eB : B ≃ Fin dB)
    (real ideal : Op A →ₗ[ℂ] Op B) :
    coordinateLinear eA eB (real - ideal) =
      coordinateLinear eA eB real - coordinateLinear eA eB ideal := by
  apply LinearMap.ext
  intro ρ
  ext i j
  simp [coordinateLinear, LinearMap.comp_apply,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply]

/-- Explicit coordinate changes commute with finite sums of linear maps. -/
theorem coordinateLinear_sum {A B κ : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype κ]
    {dA dB : ℕ} (eA : A ≃ Fin dA) (eB : B ≃ Fin dB)
    (Φ : κ → (Op A →ₗ[ℂ] Op B)) :
    coordinateLinear eA eB (∑ x, Φ x) = ∑ x, coordinateLinear eA eB (Φ x) := by
  ext ρ i j
  simp [coordinateLinear, LinearMap.comp_apply, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply, LinearMap.sum_apply]

/-- **A complete instrument gives a CPTP channel in any explicit finite coordinates.**  This is
the arbitrary-finite-type form of `Quantum.Channels.krausMapFintype_isCPTP`; the internal Kraus
fibre is flattened only inside the proof. -/
theorem Instrument.coordinateChannel_isCPTP {A B Outcome : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype Outcome]
    {dA dB : ℕ} [NeZero dA] [NeZero dB] (eA : A ≃ Fin dA) (eB : B ≃ Fin dB)
    (I : Instrument A B Outcome) :
    Quantum.Channels.IsCPTP ⇑(coordinateLinear eA eB I.channel) := by
  let K : I.Branch → Matrix (Fin dB) (Fin dA) ℂ := fun b =>
    Matrix.reindex eB eA (I.flatKraus b)
  have hmap : coordinateLinear eA eB I.channel =
      Quantum.Channels.krausMapFintype K := by
    apply LinearMap.ext
    intro ρ
    simp only [coordinateLinear, Instrument.channel, Instrument.operation, matrixConjLinear,
      LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv,
      Matrix.reindex_apply, Equiv.symm_symm, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, map_sum, Quantum.Channels.krausMapFintype,
      Matrix.conjTranspose_submatrix, K]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro o ho
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Instrument.flatKraus]
    symm
    have hρ : ρ = (ρ.submatrix eA eA).submatrix eA.symm eA.symm := by
      ext i j
      simp
    have hmul :
        (I.kraus o r).submatrix eB.symm eA.symm * ρ =
          (I.kraus o r * ρ.submatrix eA eA).submatrix eB.symm eA.symm := by
      calc
        _ = (I.kraus o r).submatrix eB.symm eA.symm *
            (ρ.submatrix eA eA).submatrix eA.symm eA.symm := by rw [← hρ]
        _ = _ := Matrix.submatrix_mul_equiv _ _ _ eA.symm _
    rw [hmul]
    exact Matrix.submatrix_mul_equiv _ _ _ eA.symm _
  rw [hmap]
  apply Quantum.Channels.krausMapFintype_isCPTP K
  rw [Fintype.sum_sigma]
  simp only [K, Matrix.reindex_apply, Instrument.flatKraus,
    Matrix.conjTranspose_submatrix]
  simp_rw [Matrix.submatrix_mul_equiv]
  ext i j
  have hc := congrFun (congrFun I.complete (eA.symm i)) (eA.symm j)
  simpa [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.one_apply] using hc

end TypedLOCC
