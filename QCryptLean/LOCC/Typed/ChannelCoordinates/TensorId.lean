import QCryptLean.LOCC.Typed.ChannelCoordinates
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity

/-!
# Typed-register maps tensored with the identity on a right factor

For a typed-register linear map `Φ : Op A →ₗ[ℂ] Op A'` and a finite type `C`,
`tensorIdLinear C Φ : Op (A × C) →ₗ[ℂ] Op (A' × C)` is `Φ ⊗ id_C`: the `(c, c')` block of the
output is `Φ` applied to the `(c, c')` block of the input.  It is functorial in `Φ`, and it keeps
the trace of every diagonal block when `Φ` preserves the trace.

In explicit product coordinates it is the numeral `Quantum.Channels.mapTensorIdLinear`
(`mapTensorIdLinear_coordinateLinear`, `mapTensorIdLinear_eq_coordinateLinear`).
-/

open scoped Matrix BigOperators

open Matrix

namespace TypedLOCC

variable {A A' A'' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype A''] [DecidableEq A''] [Fintype C] [DecidableEq C]

/-- **`Φ ⊗ id_C`**: apply `Φ` in every block of the untouched right factor `C`. -/
def tensorIdLinear (C : Type) [Fintype C] [DecidableEq C] (Φ : Op A →ₗ[ℂ] Op A') :
    Op (A × C) →ₗ[ℂ] Op (A' × C) where
  toFun M := Matrix.of fun p q => Φ (M.submatrix (fun a => (a, p.2)) (fun a => (a, q.2))) p.1 q.1
  map_add' M N := by
    ext p q
    rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply,
      show (M + N).submatrix (fun a => (a, p.2)) (fun a => (a, q.2)) =
        M.submatrix (fun a => (a, p.2)) (fun a => (a, q.2)) +
          N.submatrix (fun a => (a, p.2)) (fun a => (a, q.2)) from rfl,
      map_add, Matrix.add_apply]
  map_smul' c M := by
    ext p q
    rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply,
      show (c • M).submatrix (fun a => (a, p.2)) (fun a => (a, q.2)) =
        c • M.submatrix (fun a => (a, p.2)) (fun a => (a, q.2)) from rfl,
      map_smul, Matrix.smul_apply, RingHom.id_apply]

@[simp] theorem tensorIdLinear_apply (Φ : Op A →ₗ[ℂ] Op A') (M : Op (A × C)) (p q : A' × C) :
    tensorIdLinear C Φ M p q =
      Φ (M.submatrix (fun a => (a, p.2)) (fun a => (a, q.2))) p.1 q.1 :=
  rfl

/-- Every block of `Φ ⊗ id_C` is `Φ` applied to the corresponding input block. -/
theorem tensorIdLinear_submatrix (Φ : Op A →ₗ[ℂ] Op A') (M : Op (A × C)) (c c' : C) :
    (tensorIdLinear C Φ M).submatrix (fun a => (a, c)) (fun a => (a, c')) =
      Φ (M.submatrix (fun a => (a, c)) (fun a => (a, c'))) :=
  rfl

@[simp] theorem tensorIdLinear_id : tensorIdLinear C (LinearMap.id : Op A →ₗ[ℂ] Op A) =
    LinearMap.id :=
  rfl

theorem tensorIdLinear_comp (Φ : Op A →ₗ[ℂ] Op A') (Ψ : Op A' →ₗ[ℂ] Op A'') :
    tensorIdLinear C (Ψ.comp Φ) = (tensorIdLinear C Ψ).comp (tensorIdLinear C Φ) :=
  rfl

/-- `Φ ⊗ id_C` preserves conjugate transposes when `Φ` does. -/
theorem tensorIdLinear_conjTranspose (Φ : Op A →ₗ[ℂ] Op A')
    (hΦ : ∀ N : Op A, Φ Nᴴ = (Φ N)ᴴ) (M : Op (A × C)) :
    tensorIdLinear C Φ Mᴴ = (tensorIdLinear C Φ M)ᴴ := by
  ext p q
  rw [tensorIdLinear_apply, Matrix.conjTranspose_apply, tensorIdLinear_apply,
    ← Matrix.conjTranspose_submatrix, hΦ, Matrix.conjTranspose_apply]

/-- `Φ ⊗ id_C` keeps the trace of every diagonal block when `Φ` preserves the trace. -/
theorem tensorIdLinear_trace_block (Φ : Op A →ₗ[ℂ] Op A')
    (hΦ : ∀ N : Op A, (Φ N).trace = N.trace) (M : Op (A × C)) (c : C) :
    ∑ a, tensorIdLinear C Φ M (a, c) (a, c) = ∑ a, M (a, c) (a, c) :=
  hΦ (M.submatrix (fun a => (a, c)) (fun a => (a, c)))

/-- **In explicit product coordinates `Φ ⊗ id_C` is the numeral `mapTensorIdLinear`** of the
coordinated map. -/
theorem mapTensorIdLinear_coordinateLinear {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (eA : A ≃ Fin n) (eA' : A' ≃ Fin m) (eC : C ≃ Fin k) (Φ : Op A →ₗ[ℂ] Op A') :
    Quantum.Channels.mapTensorIdLinear (k := k) (coordinateLinear eA eA' Φ) =
      coordinateLinear ((eA.prodCongr eC).trans finProdFinEquiv)
        ((eA'.prodCongr eC).trans finProdFinEquiv) (tensorIdLinear C Φ) := by
  apply LinearMap.ext
  intro X
  ext p q
  obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective q
  change Quantum.Channels.mapTensorId (coordinateLinear eA eA' Φ) X _ _ = _
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [Equiv.symm_apply_apply, coordinateLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    tensorIdLinear_apply, Prod.map_apply]
  refine congrArg (fun N => Φ N (eA'.symm i) (eA'.symm j)) ?_
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.trans_apply, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.apply_symm_apply]

/-- **The numeral `mapTensorIdLinear` is `Φ ⊗ id_C`** in the product coordinates that keep the
numeral first factor and enumerate the control type `C`. -/
theorem mapTensorIdLinear_eq_coordinateLinear {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (eC : C ≃ Fin k) (Φ : Quantum.Operators.Op n →ₗ[ℂ] Quantum.Operators.Op m) :
    Quantum.Channels.mapTensorIdLinear (k := k) Φ =
      coordinateLinear (((Equiv.refl (Fin n)).prodCongr eC).trans finProdFinEquiv)
        (((Equiv.refl (Fin m)).prodCongr eC).trans finProdFinEquiv) (tensorIdLinear C Φ) := by
  rw [← mapTensorIdLinear_coordinateLinear]
  rfl

end TypedLOCC
