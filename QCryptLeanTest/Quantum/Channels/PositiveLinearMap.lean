import QCryptLean.Quantum.Channels.Adjoint

/-! # Adjoint preservation for quantum operations -/
open Quantum.Operators Quantum.Channels Matrix

example {X Y : Type*} [Finite X] [Finite Y] (Φ : Operation X Y)
    (h : IsCompletelyPositive Φ) (W : Op X) : Φ Wᴴ = (Φ W)ᴴ :=
  h.conjTranspose_apply W

example {X Y : Type*} [Fintype X] (N : Matrix Y X ℂ) (W : Op X) :
    krausMap (fun _ : Unit => N) Wᴴ = (krausMap (fun _ : Unit => N) W)ᴴ := by
  simp [krausMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]
