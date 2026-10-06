import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.TensorProducts.Rectangular
import QCryptLean.QKD.KeyedOutputRegister
import Mathlib.Data.Nat.Init

/-!
# The accept/abort flag blocks of a flagged two-key output register

`QKD.keyedFlagOutDim ℓ Dinner` is `K_A ⊗ K_B ⊗ (flag ⊗ inner transcript)`.  This module is the
algebra of its **flag factor**: the two rank-one flag operators, the two block projectors they
generate on the whole output register, the numeral digit that reads the flag, and the
transcript-diagonality predicate the block decomposition needs.

Nothing here mentions a protocol, a program or a channel.  It is register algebra, deliberately
placed below both the numeral `QKD.BB84.Model` development and the typed `TypedLOCC` development, so
that a consumer of the flag blocks need not import either.  Its entrywise arithmetic is the
general tensor-product API — the entry formula `Quantum.TensorProducts.Op_tensor_apply_finProd`
and the digit readings `Quantum.TensorProducts.finProdFinEquiv_symm_fst_val`/`_snd_val` —
together with Mathlib's `Nat.ext_div_mod`, which identifies a numeral by its quotient and
remainder.

Whether the digit `QKD.flagDigit` reads *is* a protocol's accept flag is a fact about that
protocol's typed program. In the BB84 model, the transcript word ends in the one-bit accept
cell, which fixes that interpretation.

## Main definitions
- `QKD.acceptFlagOp`, `QKD.abortFlagOp`: the two flag-factor operators, `|f⟩⟨f| ⊗ 1`.
- `QKD.acceptProjOp`, `QKD.abortProjOp`: the two block projectors on the whole output register.
- `QKD.flagDigit`: the numeral digit, `i % (2 * D) / D`.
- `QKD.TranscriptDiag`: diagonality in the transcript register, on index numerals.

## Main statements
- `QKD.flagBlock_eq_diagonal`: a flag block is a diagonal projector, at either flag value.
- `QKD.acceptProjOp_add_abortProjOp`: accept and abort exhaust the flag register.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace QKD

/-! ## 2. The flag blocks -/

/-- The accept block of the transcript: flag value `0`. -/
def acceptFlagOp (Dinner : ℕ) : Op (2 * Dinner) :=
  Op.tensor (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) (1 : Op Dinner)

/-- The abort block of the transcript: flag value `1`. -/
def abortFlagOp (Dinner : ℕ) : Op (2 * Dinner) :=
  Op.tensor (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) (1 : Op Dinner)

/-- The accept projector on the full output register. -/
def acceptProjOp (ℓ Dinner : ℕ) : Op (QKD.keyedFlagOutDim ℓ Dinner) :=
  Op.tensor (1 : Op (2 ^ ℓ * 2 ^ ℓ)) (acceptFlagOp Dinner)

/-- The abort projector on the full output register. -/
def abortProjOp (ℓ Dinner : ℕ) : Op (QKD.keyedFlagOutDim ℓ Dinner) :=
  Op.tensor (1 : Op (2 ^ ℓ * 2 ^ ℓ)) (abortFlagOp Dinner)

/-- The flag digit of an output index. -/
def flagDigit (Dinner : ℕ) (i : ℕ) : ℕ := i % (2 * Dinner) / Dinner

/-- **A flag block is a diagonal projector.** Both `acceptProjOp` and `abortProjOp` are instances,
at `f = 0` and `f = 1`; every algebraic fact about them below is a consequence. -/
theorem flagBlock_eq_diagonal (s D : ℕ) (f : Fin 2) :
    Op.tensor (1 : Op s) (Op.tensor (Matrix.single f f (1 : ℂ)) (1 : Op D))
      = Matrix.diagonal (fun i : Fin (s * (2 * D)) =>
          if (i : ℕ) % (2 * D) / D = (f : ℕ) then (1 : ℂ) else 0) := by
  ext i j
  rw [Matrix.diagonal_apply, Op_tensor_apply_finProd, Op_tensor_apply_finProd, Matrix.one_apply,
    Matrix.one_apply, Matrix.single_apply]
  simp only [Fin.ext_iff, finProdFinEquiv_symm_fst_val, finProdFinEquiv_symm_snd_val]
  by_cases hE : (i : ℕ) = (j : ℕ)
  · rw [if_pos hE, hE]
    simp only [if_true, and_self, one_mul, mul_one]
    exact if_congr eq_comm rfl rfl
  · rw [if_neg hE]
    by_cases hA : (i : ℕ) / (2 * D) = (j : ℕ) / (2 * D)
    · rw [if_pos hA, one_mul]
      by_cases hC : (i : ℕ) % (2 * D) % D = (j : ℕ) % (2 * D) % D
      · rw [if_pos hC, mul_one, if_neg]
        rintro ⟨hb1, hb2⟩
        exact hE (Nat.ext_div_mod hA (Nat.ext_div_mod (hb1.symm.trans hb2) hC))
      · rw [if_neg hC, mul_zero]
    · rw [if_neg hA, zero_mul]

theorem acceptProjOp_eq_diagonal (ℓ Dinner : ℕ) :
    acceptProjOp ℓ Dinner
      = Matrix.diagonal (fun i : Fin (QKD.keyedFlagOutDim ℓ Dinner) =>
          if flagDigit Dinner (i : ℕ) = 0 then (1 : ℂ) else 0) := by
  rw [acceptProjOp, acceptFlagOp, flagBlock_eq_diagonal]
  rfl

theorem abortProjOp_eq_diagonal (ℓ Dinner : ℕ) :
    abortProjOp ℓ Dinner
      = Matrix.diagonal (fun i : Fin (QKD.keyedFlagOutDim ℓ Dinner) =>
          if flagDigit Dinner (i : ℕ) = 1 then (1 : ℂ) else 0) := by
  rw [abortProjOp, abortFlagOp, flagBlock_eq_diagonal]
  rfl

/-- **Appending a low digit does not move the flag digit.** A digit read at modulus `I` survives
multiplying the modulus by `N` and shifting the index by a low `N`-digit `a < N`: a register
appended *below* the whole numeral cannot reach the flag.

This is what lets a flag statement at a bare inner transcript dimension be read at the enlarged
modulus of a protocol that appends further public data underneath — `QKD.flagDigit` is
modulus-sensitive (`flagDigit 2 2 = 1` while `flagDigit 6 2 = 0`), so the lift is a theorem and
not a rewriting convention. -/
theorem flagDigit_lowDigit (I N a b : ℕ) (hI : 0 < I) (ha : a < N) :
    flagDigit (I * N) (a + N * b) = flagDigit I b := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le a) ha
  have hsplit : a + N * b = (a + N * (b % (2 * I))) + (2 * (I * N)) * (b / (2 * I)) := by
    conv_lhs => rw [← Nat.div_add_mod b (2 * I)]
    ring
  have hbm : b % (2 * I) < 2 * I := Nat.mod_lt _ (by omega)
  have hlt : a + N * (b % (2 * I)) < 2 * (I * N) := by
    have : N * (b % (2 * I)) ≤ N * (2 * I - 1) := Nat.mul_le_mul_left _ (by omega)
    nlinarith [Nat.sub_add_cancel (show 1 ≤ 2 * I by omega)]
  have hcomm : I * N = N * I := Nat.mul_comm I N
  rw [flagDigit, flagDigit, hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rcases Nat.lt_or_ge (b % (2 * I)) I with h | h
  · have hm : N * (b % (2 * I) + 1) ≤ N * I := Nat.mul_le_mul_left N (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt h]
  · have hm : N * I ≤ N * (b % (2 * I)) := Nat.mul_le_mul_left N h
    rw [Nat.div_eq_of_lt_le (show 1 * (I * N) ≤ a + N * (b % (2 * I)) by omega)
        (show a + N * (b % (2 * I)) < (1 + 1) * (I * N) by omega),
      Nat.div_eq_of_lt_le (show 1 * I ≤ b % (2 * I) by omega)
        (show b % (2 * I) < (1 + 1) * I by omega)]

/-- The flag digit is a bit. -/
theorem flagDigit_lt_two (D : ℕ) (i : ℕ) : flagDigit D i < 2 := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp [flagDigit]
  · have h : i % (2 * D) < 2 * D := Nat.mod_lt _ (by omega)
    exact (Nat.div_lt_iff_lt_mul hD).mpr h

/-- **Accept and abort exhaust the flag register.** -/
theorem acceptProjOp_add_abortProjOp (ℓ D : ℕ) :
    acceptProjOp ℓ D + abortProjOp ℓ D = 1 := by
  rw [acceptProjOp_eq_diagonal, abortProjOp_eq_diagonal, Matrix.diagonal_add,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  have h2 := flagDigit_lt_two D (i : ℕ)
  by_cases h0 : flagDigit D (i : ℕ) = 0
  · rw [if_pos h0, if_neg (by omega), add_zero]
  · rw [if_neg h0, if_pos (by omega), zero_add]

theorem acceptProjOp_mul_self (ℓ D : ℕ) :
    acceptProjOp ℓ D * acceptProjOp ℓ D = acceptProjOp ℓ D := by
  rw [acceptProjOp_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split <;> simp

theorem abortProjOp_mul_self (ℓ D : ℕ) :
    abortProjOp ℓ D * abortProjOp ℓ D = abortProjOp ℓ D := by
  rw [abortProjOp_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split <;> simp

theorem acceptProjOp_mul_abortProjOp (ℓ D : ℕ) :
    acceptProjOp ℓ D * abortProjOp ℓ D = 0 := by
  rw [acceptProjOp_eq_diagonal, abortProjOp_eq_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_zero]
  congr 1
  funext i
  by_cases h0 : flagDigit D (i : ℕ) = 0
  · rw [if_neg (show ¬ flagDigit D (i : ℕ) = 1 by omega), mul_zero]
  · rw [if_neg h0, zero_mul]

theorem acceptProjOp_conjTranspose (ℓ D : ℕ) : (acceptProjOp ℓ D)ᴴ = acceptProjOp ℓ D := by
  rw [acceptProjOp_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply, apply_ite (star : ℂ → ℂ), star_one, star_zero]

theorem abortProjOp_conjTranspose (ℓ D : ℕ) : (abortProjOp ℓ D)ᴴ = abortProjOp ℓ D := by
  rw [abortProjOp_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply, apply_ite (star : ℂ → ℂ), star_one, star_zero]

/-! ### The flag operators, at the transcript register alone

These are the forms the key-replacement Kraus operators are built from, so they are proved directly
in tensor form rather than through the diagonal reading. -/

theorem acceptFlagOp_mul_self (D : ℕ) : acceptFlagOp D * acceptFlagOp D = acceptFlagOp D := by
  rw [acceptFlagOp, Op.tensor_mul, Matrix.single_mul_single_same, one_mul, Matrix.one_mul]

theorem acceptFlagOp_conjTranspose (D : ℕ) : (acceptFlagOp D)ᴴ = acceptFlagOp D := by
  rw [acceptFlagOp, Op.tensor_conjTranspose, Matrix.conjTranspose_single, star_one,
    Matrix.conjTranspose_one]

theorem acceptFlagOp_mul_abortFlagOp (D : ℕ) : acceptFlagOp D * abortFlagOp D = 0 := by
  rw [acceptFlagOp, abortFlagOp, Op.tensor_mul]
  rw [show Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) *
      Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) = 0 from ?_]
  · ext i j
    simp only [Op_tensor_apply_finProd, Matrix.zero_apply, zero_mul]
  · ext i j
    simp [Matrix.mul_apply, Matrix.single_apply]

/-! ## Transcript diagonality, on index numerals -/

/-- **Diagonality in the transcript register**, stated on index numerals: the transcript digit of an
index `i` of `Fin (s * D)` is `i % D`. -/
def TranscriptDiag {s D : ℕ} (M : Op (s * D)) : Prop :=
  ∀ i j : Fin (s * D), (i : ℕ) % D ≠ (j : ℕ) % D → M i j = 0

theorem transcriptDiag_sum {s D : ℕ} {κ : Type*} [Fintype κ] (f : κ → Op (s * D))
    (h : ∀ x, TranscriptDiag (f x)) : TranscriptDiag (∑ x, f x) := by
  intro i j hij
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun x _ => h x i j hij

/-- **Transcript diagonality survives a value-preserving re-spelling of the register.**
`Quantum.Operators.Op.castDim` moves an operator between two numeral names for the same dimension
without moving any entry, so the only thing that has to match is the transcript modulus. -/
theorem transcriptDiag_castDim {s D s' D' : ℕ} (h : s * D = s' * D') (hD : D = D')
    {M : Op (s * D)} (hM : TranscriptDiag M) :
    TranscriptDiag (s := s') (D := D') (Op.castDim h M) := by
  intro i j hij
  rw [Op.castDim_apply]
  refine hM _ _ ?_
  simpa only [Fin.val_cast, hD] using hij

end QKD

end
