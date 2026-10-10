import QCryptLean.Quantum.Operators.BraKetAlgebra

/-!
# Ket and bra module compatibility

The group and module projections recover the primitive operation instances definitionally.
Natural and integer scalar actions are pointwise, and generic additive and module identities
apply directly to kets and bras.
-/

open Quantum.Operators

-- Compare entire operation records, including the data used by notation.
example {n : Type*} :
    (inferInstance : AddCommGroup (Ket n)).toAdd = (inferInstance : Add (Ket n)) := rfl

example {n : Type*} :
    (inferInstance : AddCommGroup (Ket n)).toZero = (inferInstance : Zero (Ket n)) := rfl

example {n : Type*} :
    (inferInstance : AddCommGroup (Ket n)).toNeg = (inferInstance : Neg (Ket n)) := rfl

example {n : Type*} :
    (inferInstance : AddCommGroup (Ket n)).toSub = (inferInstance : Sub (Ket n)) := rfl

example {n : Type*} :
    (inferInstance : Module ℂ (Ket n)).toSMul = (inferInstance : SMul ℂ (Ket n)) := rfl

example {n : Type*} :
    (inferInstance : AddCommGroup (Bra n)).toAdd = (inferInstance : Add (Bra n)) := rfl

example {n : Type*} :
    (inferInstance : AddCommGroup (Bra n)).toZero = (inferInstance : Zero (Bra n)) := rfl

example {n : Type*} :
    (inferInstance : AddCommGroup (Bra n)).toNeg = (inferInstance : Neg (Bra n)) := rfl

example {n : Type*} :
    (inferInstance : AddCommGroup (Bra n)).toSub = (inferInstance : Sub (Bra n)) := rfl

example {n : Type*} :
    (inferInstance : Module ℂ (Bra n)).toSMul = (inferInstance : SMul ℂ (Bra n)) := rfl

example {n : Type*} (k : ℕ) (ψ : Ket n) : (k • ψ).vec = k • ψ.vec := rfl

example {n : Type*} (k : ℤ) (ψ : Ket n) : (k • ψ).vec = k • ψ.vec := rfl

example {n : Type*} (k : ℕ) (β : Bra n) : (k • β).vec = k • β.vec := rfl

example {n : Type*} (k : ℤ) (β : Bra n) : (k • β).vec = k • β.vec := rfl

example {n : Type*} (ψ φ : Ket n) : ψ + φ - φ = ψ := by simp

example {n : Type*} (β γ : Bra n) : β + γ - γ = β := by simp

example {n : Type*} (c d : ℂ) (ψ φ : Ket n) :
    (c + d) • (ψ + φ) = c • ψ + c • φ + (d • ψ + d • φ) := by
  rw [add_smul, smul_add, smul_add]

example {n : Type*} (c d : ℂ) (β γ : Bra n) :
    (c + d) • (β + γ) = c • β + c • γ + (d • β + d • γ) := by
  rw [add_smul, smul_add, smul_add]

example {n : Type*} (ψ : Ket n) : (∑ _ : Fin 2, ψ) = (2 : ℂ) • ψ := by
  simp [two_smul]

example {n : Type*} (β : Bra n) : (∑ _ : Fin 2, β) = (2 : ℂ) • β := by
  simp [two_smul]

-- Scalar distribution follows Mathlib; add_smul and scalar reassociation stay explicit.
example {n : Type*} (c : ℂ) (ψ φ : Ket n) (P : Ket n → Prop)
    (h : P (c • (ψ + φ) + 0)) : P (c • ψ + c • φ) := by
  simp at h
  guard_hyp h : P (c • ψ + c • φ)
  assumption

example {n : Type*} (c : ℂ) (β γ : Bra n) (P : Bra n → Prop)
    (h : P (c • (β + γ) + 0)) : P (c • β + c • γ) := by
  simp at h
  guard_hyp h : P (c • β + c • γ)
  assumption

example {n : Type*} (c d : ℂ) (ψ : Ket n) (P : Ket n → Prop)
    (h : P ((c + d) • ψ + 0)) : P ((c + d) • ψ) := by
  simp at h
  guard_hyp h :ₛ P ((c + d) • ψ)
  assumption

example {n : Type*} (c d : ℂ) (β : Bra n) (P : Bra n → Prop)
    (h : P ((c + d) • β + 0)) : P ((c + d) • β) := by
  simp at h
  guard_hyp h :ₛ P ((c + d) • β)
  assumption

example {n : Type*} (c d : ℂ) (ψ : Ket n) (P : Ket n → Prop)
    (h : P (c • (d • ψ) + 0)) : P (c • (d • ψ)) := by
  simp at h
  guard_hyp h :ₛ P (c • (d • ψ))
  assumption

example {n : Type*} (c d : ℂ) (β : Bra n) (P : Bra n → Prop)
    (h : P (c • (d • β) + 0)) : P (c • (d • β)) := by
  simp at h
  guard_hyp h :ₛ P (c • (d • β))
  assumption

example {n : Type*} (c d : ℂ) (ψ : Ket n) : c • (d • ψ) = (c * d) • ψ := by
  rw [smul_smul]

example {n : Type*} (c d : ℂ) (β : Bra n) : c • (d • β) = (c * d) • β := by
  rw [smul_smul]

-- Dagger propagation agrees with generic scalar distribution and sign normalization.
example {n : Type*} (β γ : Bra n) : (β + γ).dag = β.dag + γ.dag := by simp

example {n : Type*} (β γ : Bra n) : (β - γ).dag = β.dag - γ.dag := by simp

example {n : Type*} (β : Bra n) : (-β).dag = -β.dag := by simp

example {n : Type*} (c : ℂ) (β γ : Bra n) :
    (c • (β + γ)).dag = star c • (β + γ).dag := by simp

example {n : Type*} (c : ℂ) (β γ : Bra n) :
    (c • (β - γ)).dag = star c • (β - γ).dag := by simp

example {n : Type*} (c : ℂ) (β : Bra n) :
    (c • (-β)).dag = star c • (-β).dag := by simp

example {n : Type*} (c : ℂ) (β γ : Bra n) :
    ((-c) • (β + γ)).dag = -(star c • β.dag) + -(star c • γ.dag) := by simp

example {n : Type*} (ψ φ : Ket n) : (ψ + φ).dag = ψ.dag + φ.dag := by simp

example {n : Type*} (ψ φ : Ket n) : (ψ - φ).dag = ψ.dag - φ.dag := by simp

example {n : Type*} (ψ : Ket n) : (-ψ).dag = -ψ.dag := by simp

example {n : Type*} (c : ℂ) (ψ φ : Ket n) :
    (c • (ψ + φ)).dag = star c • (ψ + φ).dag := by simp

example {n : Type*} (c : ℂ) (ψ φ : Ket n) :
    (c • (ψ - φ)).dag = star c • (ψ - φ).dag := by simp

example {n : Type*} (c : ℂ) (ψ : Ket n) :
    (c • (-ψ)).dag = star c • (-ψ).dag := by simp

example {n : Type*} (c : ℂ) (ψ φ : Ket n) :
    ((-c) • (ψ + φ)).dag = -(star c • ψ.dag) + -(star c • φ.dag) := by simp
