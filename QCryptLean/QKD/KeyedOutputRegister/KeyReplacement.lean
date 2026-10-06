import QCryptLean.QKD.KeyedOutputRegister.FlagBlocks
import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.LOCC.Local
import QCryptLean.Quantum.TensorProducts.PartialTrace
import Mathlib.Data.Matrix.Basis

/-!
# `keyReplace`: the key-replacement channel of a flagged two-key output register

The key-replacement functor used to define the derived fixed-output ideal channel. It acts on
`QKD.keyedFlagOutDim ℓ Dinner` and depends only on the register layout `(ℓ, Dinner)`: on accept
it discards both key registers and writes one fresh uniform key into both; on the whole abort
block it is the identity, preserving arbitrary ambient abort-key values and coherences.

It is fixed independently of any program. If `[NeZero D]` and `1 ≤ ℓ`,
`QKD.keyReplace_ne_id` shows that it is not the identity, using a nonzero accept-block operator
annihilated by `QKD.keyReplace_keyCoherence`.

Its accept branch implements the fresh-key replacement described before Definition 4 of
Nahar--Tupkary--Zhao--Lütkenhaus--Tan 2024 (arXiv:2403.11851, `main.tex:394-400`).
The library's fixed-output abort encoding agrees with a literal abort resource only for programs
proved to blank both abort keys; that separate condition is recorded downstream, in the BB84
model layer.

Like `QCryptLean.QKD.KeyedOutputRegister.FlagBlocks`, this module is below both the
numeral `QKD.BB84.Model` and the typed `TypedLOCC` developments: both must apply the *same*
functor.

## Main definitions
- `QKD.freshKeyKraus`, `QKD.keyReplaceAccept`: the accept branch and its Kraus family.
- `QKD.acceptSandwich`, `QKD.abortSandwich`: the two flag events as superoperators.
- `QKD.keyReplace`, `QKD.keyReplaceKraus`: the functor and its complete Kraus family.

## Main statements
- `QKD.keyReplace_isCPTP`: assuming `[NeZero D]`, it is a channel; the `√` normalises the
  `2 ^ ℓ` fresh-key branches.
- `QKD.keyReplace_abort`: it is the identity on the abort block.
- `QKD.keyReplace_keyCoherence`: for distinct key labels it annihilates the accept-block operator
  off-diagonal in the key-`A` register (no dimension hypothesis).
- `QKD.keyReplace_ne_id`: assuming `[NeZero D]` and `1 ≤ ℓ`, the channel is not the identity map —
  it annihilates a nonzero off-diagonal operator.
- `QKD.acceptSandwich_add_abortSandwich_of_transcriptDiag`: the two events exhaust a
  transcript-diagonal state.
- `QKD.abortBranchAgreement_of_transcriptDiag`: on the abort block a transcript-diagonal channel
  and its key replacement agree — the abort half of the design, stated about the functor and the
  output register alone, with no program, protocol or syntax in sight.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Matrix
open LOCC
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace QKD

/-! ## 4. `keyReplace`: the ideal is a functor of the register layout, never of the program -/

/-- The Kraus operator of the accept branch of `keyReplace`, in the branch `(k, a, b)`: it reads
both key registers out (`⟨a|`, `⟨b|`) and writes the *same* fresh value `k` into both, inside the
accept block. The `√` is exactly what normalises the `2^ℓ` fresh-key branches. -/
def freshKeyKraus (ℓ Dinner : ℕ) (k a b : Fin (2 ^ ℓ)) : Op (QKD.keyedFlagOutDim ℓ Dinner) :=
  (((Real.sqrt ((2 : ℝ) ^ ℓ))⁻¹ : ℝ) : ℂ) •
    Op.tensor (Op.tensor (Matrix.single k a (1 : ℂ)) (Matrix.single k b (1 : ℂ)))
      (acceptFlagOp Dinner)

/-- The accept part of `keyReplace`: discard both key registers and write one fresh uniform key into
both, inside the accept block. -/
def keyReplaceAccept (ℓ Dinner : ℕ) :
    Op (QKD.keyedFlagOutDim ℓ Dinner) →ₗ[ℂ] Op (QKD.keyedFlagOutDim ℓ Dinner) :=
  ∑ p : Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ),
    matrixConjLinear (freshKeyKraus ℓ Dinner p.1 p.2.1 p.2.2)

/-- The accept event as a superoperator, `ρ ↦ P ρ P`. -/
def acceptSandwich (ℓ Dinner : ℕ) :
    Op (QKD.keyedFlagOutDim ℓ Dinner) →ₗ[ℂ] Op (QKD.keyedFlagOutDim ℓ Dinner) :=
  matrixConjLinear (acceptProjOp ℓ Dinner)

/-- The abort event as a superoperator. -/
def abortSandwich (ℓ Dinner : ℕ) :
    Op (QKD.keyedFlagOutDim ℓ Dinner) →ₗ[ℂ] Op (QKD.keyedFlagOutDim ℓ Dinner) :=
  matrixConjLinear (abortProjOp ℓ Dinner)

/-- **The key-replacement functor.** A fixed function of `(ℓ, Dinner)` — the register layout — and
of **nothing else**: it never sees the program, so it cannot be tuned to make a particular protocol
look secure. On the accept block it discards both key registers and writes one fresh uniform key
into both; on the abort block it is the identity. Composing it after the real channel defines the
derived fixed-output ideal channel. -/
def keyReplace (ℓ Dinner : ℕ) :
    Op (QKD.keyedFlagOutDim ℓ Dinner) →ₗ[ℂ] Op (QKD.keyedFlagOutDim ℓ Dinner) :=
  keyReplaceAccept ℓ Dinner + abortSandwich ℓ Dinner

theorem keyReplace_eq_accept_add_abort (ℓ Dinner : ℕ) :
    keyReplace ℓ Dinner = keyReplaceAccept ℓ Dinner + abortSandwich ℓ Dinner := rfl

/-! ### The flag algebra of the two events -/

theorem acceptSandwich_acceptSandwich (ℓ D : ℕ) (ρ : Op (QKD.keyedFlagOutDim ℓ D)) :
    acceptSandwich ℓ D (acceptSandwich ℓ D ρ) = acceptSandwich ℓ D ρ := by
  simp only [acceptSandwich, matrixConjLinear_apply]
  rw [conj_mul_conj, acceptProjOp_mul_self]

theorem acceptSandwich_idem (ℓ D : ℕ) :
    (acceptSandwich ℓ D).comp (acceptSandwich ℓ D) = acceptSandwich ℓ D :=
  LinearMap.ext fun ρ => acceptSandwich_acceptSandwich ℓ D ρ

theorem acceptSandwich_abortSandwich (ℓ D : ℕ) (ρ : Op (QKD.keyedFlagOutDim ℓ D)) :
    acceptSandwich ℓ D (abortSandwich ℓ D ρ) = 0 := by
  simp only [acceptSandwich, abortSandwich, matrixConjLinear_apply]
  rw [conj_mul_conj, acceptProjOp_mul_abortProjOp, Matrix.zero_mul, Matrix.zero_mul]

theorem acceptSandwich_comp_abortSandwich (ℓ D : ℕ) :
    (acceptSandwich ℓ D).comp (abortSandwich ℓ D) = 0 :=
  LinearMap.ext fun ρ => acceptSandwich_abortSandwich ℓ D ρ

/-- **The accept projector on a diagonal matrix unit** keeps the unit when the flag digit is `0`
and kills it otherwise.  This is the whole content of "the accept block of a diagonally supported
channel is the sub-sum over its accepting branches", and it is a fact about the flagged register
alone: no program, no protocol and no index layout occurs. -/
theorem acceptSandwich_single (ℓ D : ℕ) (i : Fin (QKD.keyedFlagOutDim ℓ D)) (c : ℂ) :
    acceptSandwich ℓ D (Matrix.single i i c) =
      (if flagDigit D (i : ℕ) = 0 then (1 : ℂ) else 0) • Matrix.single i i c := by
  rw [acceptSandwich, matrixConjLinear_apply, acceptProjOp_conjTranspose,
    acceptProjOp_eq_diagonal]
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_ne p i with rfl | hp
  · rcases eq_or_ne q p with rfl | hq
    · by_cases h : flagDigit D (q : ℕ) = 0 <;> simp [h]
    · simp [Ne.symm hq]
  · simp [Ne.symm hp]

/-- The abort counterpart of `QKD.acceptSandwich_single`. -/
theorem abortSandwich_single (ℓ D : ℕ) (i : Fin (QKD.keyedFlagOutDim ℓ D)) (c : ℂ) :
    abortSandwich ℓ D (Matrix.single i i c) =
      (if flagDigit D (i : ℕ) = 1 then (1 : ℂ) else 0) • Matrix.single i i c := by
  rw [abortSandwich, matrixConjLinear_apply, abortProjOp_conjTranspose,
    abortProjOp_eq_diagonal]
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_ne p i with rfl | hp
  · rcases eq_or_ne q p with rfl | hq
    · by_cases h : flagDigit D (q : ℕ) = 1 <;> simp [h]
    · simp [Ne.symm hq]
  · simp [Ne.symm hp]

theorem abortSandwich_abortSandwich (ℓ D : ℕ) (ρ : Op (QKD.keyedFlagOutDim ℓ D)) :
    abortSandwich ℓ D (abortSandwich ℓ D ρ) = abortSandwich ℓ D ρ := by
  simp only [abortSandwich, matrixConjLinear_apply]
  rw [conj_mul_conj, abortProjOp_mul_self]

/-! ### `keyReplace` against the flag blocks -/

theorem acceptProjOp_mul_freshKeyKraus (ℓ D : ℕ) (k a b : Fin (2 ^ ℓ)) :
    acceptProjOp ℓ D * freshKeyKraus ℓ D k a b = freshKeyKraus ℓ D k a b := by
  rw [freshKeyKraus, acceptProjOp, Matrix.mul_smul, Op.tensor_mul, Matrix.one_mul,
    acceptFlagOp_mul_self]

theorem freshKeyKraus_mul_abortProjOp (ℓ D : ℕ) (k a b : Fin (2 ^ ℓ)) :
    freshKeyKraus ℓ D k a b * abortProjOp ℓ D = 0 := by
  rw [freshKeyKraus, abortProjOp, Matrix.smul_mul, Op.tensor_mul, Matrix.mul_one,
    acceptFlagOp_mul_abortFlagOp, Op.tensor_zero_right, smul_zero]

/-- **The accept event fixes the fresh-key part of `keyReplace`.** -/
theorem acceptSandwich_keyReplaceAccept (ℓ D : ℕ) (ρ : Op (QKD.keyedFlagOutDim ℓ D)) :
    acceptSandwich ℓ D (keyReplaceAccept ℓ D ρ) = keyReplaceAccept ℓ D ρ := by
  simp only [acceptSandwich, keyReplaceAccept, LinearMap.sum_apply, matrixConjLinear_apply]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conj_mul_conj, acceptProjOp_mul_freshKeyKraus]

theorem acceptSandwich_comp_keyReplaceAccept (ℓ D : ℕ) :
    (acceptSandwich ℓ D).comp (keyReplaceAccept ℓ D) = keyReplaceAccept ℓ D :=
  LinearMap.ext fun ρ => acceptSandwich_keyReplaceAccept ℓ D ρ

/-- **`keyReplace` is the identity on the abort block** — the half of the design that makes the
abort-agreement theorem work. -/
theorem keyReplace_abort (ℓ D : ℕ) (ρ : Op (QKD.keyedFlagOutDim ℓ D)) :
    keyReplace ℓ D (abortSandwich ℓ D ρ) = abortSandwich ℓ D ρ := by
  rw [keyReplace, LinearMap.add_apply, abortSandwich_abortSandwich]
  rw [show keyReplaceAccept ℓ D (abortSandwich ℓ D ρ) = 0 from ?_, zero_add]
  simp only [keyReplaceAccept, abortSandwich, LinearMap.sum_apply, matrixConjLinear_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [conj_mul_conj, freshKeyKraus_mul_abortProjOp, Matrix.zero_mul, Matrix.zero_mul]

/-! ### `keyReplace` is a channel -/

theorem freshKeyKraus_adj_mul (ℓ D : ℕ) (k a b : Fin (2 ^ ℓ)) :
    (freshKeyKraus ℓ D k a b)ᴴ * freshKeyKraus ℓ D k a b
      = ((((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : ℂ) •
          Op.tensor (Op.tensor (Matrix.single a a (1 : ℂ)) (Matrix.single b b (1 : ℂ)))
            (acceptFlagOp D) := by
  rw [freshKeyKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  · rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by positivity)]
  · rw [Op.tensor_conjTranspose, Op.tensor_conjTranspose, Op.tensor_mul, Op.tensor_mul,
      Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one,
      Matrix.single_mul_single_same, Matrix.single_mul_single_same, one_mul,
      acceptFlagOp_conjTranspose, acceptFlagOp_mul_self]

theorem sum_freshKeyKraus_adj_mul (ℓ D : ℕ) :
    ∑ p : Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ),
        (freshKeyKraus ℓ D p.1 p.2.1 p.2.2)ᴴ * freshKeyKraus ℓ D p.1 p.2.1 p.2.2
      = acceptProjOp ℓ D := by
  have hab : ∑ a : Fin (2 ^ ℓ), ∑ b : Fin (2 ^ ℓ),
      Op.tensor (Op.tensor (Matrix.single a a (1 : ℂ)) (Matrix.single b b (1 : ℂ)))
        (acceptFlagOp D) = acceptProjOp ℓ D := by
    rw [acceptProjOp,
      show (1 : Op (2 ^ ℓ * 2 ^ ℓ)) = Op.tensor (1 : Op (2 ^ ℓ)) (1 : Op (2 ^ ℓ)) from
        Op.tensor_one.symm,
      ← Matrix.sum_single_one (m := Fin (2 ^ ℓ)) (α := ℂ)]
    simp only [Op.tensor_finsetSum_left, Op.tensor_finsetSum_right]
    exact Finset.sum_comm
  simp_rw [freshKeyKraus_adj_mul]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, ← Finset.smul_sum]
  simp_rw [hab]
  have hscal : ∀ z : ℂ, z = 1 → z • acceptProjOp ℓ D = acceptProjOp ℓ D := by
    intro z hz; rw [hz, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  refine hscal _ ?_
  push_cast
  field_simp

/-- The Kraus family of `keyReplace`: one branch per fresh key and read-out pair, plus the abort
projector. -/
def keyReplaceKraus (ℓ Dinner : ℕ)
    (o : Option (Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ))) :
    Op (QKD.keyedFlagOutDim ℓ Dinner) :=
  match o with
  | none => abortProjOp ℓ Dinner
  | some p => freshKeyKraus ℓ Dinner p.1 p.2.1 p.2.2

@[simp] theorem keyReplaceKraus_none (ℓ D : ℕ) :
    keyReplaceKraus ℓ D none = abortProjOp ℓ D := rfl

@[simp] theorem keyReplaceKraus_some (ℓ D : ℕ) (p : Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ)) :
    keyReplaceKraus ℓ D (some p) = freshKeyKraus ℓ D p.1 p.2.1 p.2.2 := rfl

theorem keyReplace_eq_krausMapFintype (ℓ D : ℕ) :
    keyReplace ℓ D = krausMapFintype (keyReplaceKraus ℓ D) := by
  refine LinearMap.ext fun ρ => ?_
  change keyReplaceAccept ℓ D ρ + abortSandwich ℓ D ρ
    = ∑ o : Option (Fin (2 ^ ℓ) × Fin (2 ^ ℓ) × Fin (2 ^ ℓ)),
        keyReplaceKraus ℓ D o * ρ * (keyReplaceKraus ℓ D o)ᴴ
  rw [Fintype.sum_option]
  simp only [keyReplaceAccept, abortSandwich, LinearMap.sum_apply, matrixConjLinear_apply,
    keyReplaceKraus_none, keyReplaceKraus_some]
  exact add_comm _ _

theorem sum_keyReplaceKraus_complete (ℓ D : ℕ) :
    ∑ o, (keyReplaceKraus ℓ D o)ᴴ * keyReplaceKraus ℓ D o = 1 := by
  rw [Fintype.sum_option]
  simp only [keyReplaceKraus_none, keyReplaceKraus_some]
  rw [abortProjOp_conjTranspose, abortProjOp_mul_self, sum_freshKeyKraus_adj_mul, add_comm,
    acceptProjOp_add_abortProjOp]

/-- For `[NeZero D]`, `keyReplace` is a channel. The `√` in `freshKeyKraus` makes the `2^ℓ`
fresh-key branches normalise: the completeness sum is `acceptProjOp`, and the abort branch supplies
`abortProjOp`. -/
theorem keyReplace_isCPTP (ℓ D : ℕ) [NeZero D] : IsCPTP ⇑(keyReplace ℓ D) := by
  rw [keyReplace_eq_krausMapFintype]
  exact krausMapFintype_isCPTP _ (sum_keyReplaceKraus_complete ℓ D)

/-! ## 5. Accept and abort exhaust a denotation -/

/-- **Accept and abort exhaust a transcript-diagonal state.** -/
theorem acceptSandwich_add_abortSandwich_of_transcriptDiag (ℓ D : ℕ)
    (ρ : Op (QKD.keyedFlagOutDim ℓ D))
    (h : TranscriptDiag (s := 2 ^ ℓ * 2 ^ ℓ) (D := 2 * D) ρ) :
    acceptSandwich ℓ D ρ + abortSandwich ℓ D ρ = ρ := by
  ext i j
  simp only [acceptSandwich, abortSandwich, matrixConjLinear_apply, Matrix.add_apply]
  rw [acceptProjOp_conjTranspose, abortProjOp_conjTranspose, acceptProjOp_eq_diagonal,
    abortProjOp_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_mul]
  by_cases hf : flagDigit D (i : ℕ) = flagDigit D (j : ℕ)
  · have h2 := flagDigit_lt_two D (i : ℕ)
    by_cases h0 : flagDigit D (i : ℕ) = 0
    · rw [ite_eq_left h0, ite_eq_left (hf ▸ h0 : flagDigit D (j : ℕ) = 0),
        ite_eq_right (show ¬ flagDigit D (i : ℕ) = 1 by omega),
        ite_eq_right (show ¬ flagDigit D (j : ℕ) = 1 by omega)]
      ring
    · rw [ite_eq_right h0, ite_eq_right (fun hc => h0 (hf.trans hc)),
        ite_eq_left (show flagDigit D (i : ℕ) = 1 by omega),
        ite_eq_left (show flagDigit D (j : ℕ) = 1 by rw [← hf]; omega)]
      ring
  · have hρ : ρ i j = 0 := by
      refine h i j fun hmod => hf ?_
      unfold flagDigit
      rw [hmod]
    rw [hρ]
    ring

/-! ## 6. Abort agreement, for any transcript-diagonal channel

The two statements below are the abort half of the design, and they are about the **functor and
the output register only**: the hypothesis is that the channel's outputs are transcript-diagonal,
expressed directly as vanishing between distinct transcript blocks. Neither statement requires
a program or protocol syntax.

`keyReplace` is the identity on the whole abort block, so `Φ − keyReplace ∘ Φ` is supported in the
accept block: the real and ideal arms agree wherever the flag says abort. -/

/-- **The accept event fixes the key-replacement gap, pointwise.**  For any transcript-diagonal
output operator `ρ`, `ρ − keyReplace ρ` is its own accept block. -/
theorem acceptSandwich_sub_keyReplace_of_transcriptDiag (ℓ D : ℕ)
    (ρ : Op (QKD.keyedFlagOutDim ℓ D))
    (h : TranscriptDiag (s := 2 ^ ℓ * 2 ^ ℓ) (D := 2 * D) ρ) :
    acceptSandwich ℓ D (ρ - keyReplace ℓ D ρ) = ρ - keyReplace ℓ D ρ := by
  have hpinch := acceptSandwich_add_abortSandwich_of_transcriptDiag ℓ D ρ h
  have hid : keyReplace ℓ D ρ = keyReplaceAccept ℓ D ρ + abortSandwich ℓ D ρ := rfl
  rw [map_sub, hid, map_add, acceptSandwich_keyReplaceAccept, acceptSandwich_abortSandwich]
  calc acceptSandwich ℓ D ρ - (keyReplaceAccept ℓ D ρ + 0)
      = (acceptSandwich ℓ D ρ + abortSandwich ℓ D ρ)
          - (keyReplaceAccept ℓ D ρ + abortSandwich ℓ D ρ) := by
        rw [add_zero]; abel
    _ = ρ - keyReplace ℓ D ρ := by rw [hpinch, hid]

/-- **The accept event fixes the key-replacement gap of a transcript-diagonal channel**, at the
level of maps. -/
theorem acceptSandwich_comp_sub_keyReplace_comp {s : ℕ} (ℓ D : ℕ)
    (Φ : Op s →ₗ[ℂ] Op (QKD.keyedFlagOutDim ℓ D))
    (h : ∀ ρ, TranscriptDiag (s := 2 ^ ℓ * 2 ^ ℓ) (D := 2 * D) (Φ ρ)) :
    (acceptSandwich ℓ D).comp (Φ - (keyReplace ℓ D).comp Φ) = Φ - (keyReplace ℓ D).comp Φ :=
  LinearMap.ext fun ρ => acceptSandwich_sub_keyReplace_of_transcriptDiag ℓ D (Φ ρ) (h ρ)

/-- 🚩 **Abort agreement, as a property of the output register.**  Outside the accept block a
transcript-diagonal channel and its key-replacement agree exactly.

In the protocol *schemes* the analogous statement is an assumed field
(`PMQKDProtocol.abortAgreement`).
Here it is a theorem with a hypothesis that every program discharges by construction. -/
theorem abortBranchAgreement_of_transcriptDiag {s : ℕ} (ℓ D : ℕ)
    (Φ : Op s →ₗ[ℂ] Op (QKD.keyedFlagOutDim ℓ D))
    (h : ∀ ρ, TranscriptDiag (s := 2 ^ ℓ * 2 ^ ℓ) (D := 2 * D) (Φ ρ)) :
    ((LinearMap.id : Op (QKD.keyedFlagOutDim ℓ D) →ₗ[ℂ] Op (QKD.keyedFlagOutDim ℓ D)) -
        acceptSandwich ℓ D).comp (Φ - (keyReplace ℓ D).comp Φ) = 0 := by
  rw [LinearMap.sub_comp, LinearMap.id_comp, acceptSandwich_comp_sub_keyReplace_comp ℓ D Φ h,
    sub_self]

/-! ## Nonidentity -/

/-! For `[NeZero D]` and `1 ≤ ℓ`, an accept-block off-diagonal operator witnesses nonidentity.
The following lemmas compute its image under key replacement. -/

theorem abortFlagOp_mul_acceptFlagOp (D : ℕ) : abortFlagOp D * acceptFlagOp D = 0 := by
  rw [acceptFlagOp, abortFlagOp, Op.tensor_mul]
  rw [show Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) *
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) = 0 from ?_]
  · ext i j
    simp only [Op_tensor_apply_finProd, Matrix.zero_apply, zero_mul]
  · ext i j
    simp [Matrix.mul_apply, Matrix.single_apply]

theorem opTensor_zero_left {n m : ℕ} (B : Op m) : Op.tensor (0 : Op n) B = 0 := by
  ext i j
  simp only [Op_tensor_apply_finProd, Matrix.zero_apply, zero_mul]

/-- Conjugating an off-diagonal matrix unit by a rank-one read-and-write kills it. -/
theorem single_conj_single_eq_zero {d : ℕ} (k a u v : Fin d) (huv : u ≠ v) :
    Matrix.single k a (1 : ℂ) * Matrix.single u v (1 : ℂ) * Matrix.single a k (1 : ℂ) = 0 := by
  by_cases hau : a = u
  · subst hau
    rw [Matrix.single_mul_single_same, one_mul,
      Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm huv)]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ hau, Matrix.zero_mul]

/-- A fresh-key branch, applied to an accept-block operator, acts on the two key registers
independently: it reads them out and writes `k` into both. -/
theorem freshKeyKraus_conj (ℓ D : ℕ) (k a b : Fin (2 ^ ℓ)) (XA XB : Op (2 ^ ℓ)) :
    freshKeyKraus ℓ D k a b * Op.tensor (Op.tensor XA XB) (acceptFlagOp D)
        * (freshKeyKraus ℓ D k a b)ᴴ
      = ((((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : ℂ) •
          Op.tensor (Op.tensor (Matrix.single k a (1 : ℂ) * XA * Matrix.single a k (1 : ℂ))
            (Matrix.single k b (1 : ℂ) * XB * Matrix.single b k (1 : ℂ))) (acceptFlagOp D) := by
  rw [freshKeyKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  congr 1
  · rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by positivity)]
  · rw [Op.tensor_conjTranspose, Op.tensor_conjTranspose, Matrix.conjTranspose_single,
      Matrix.conjTranspose_single, star_one, acceptFlagOp_conjTranspose,
      Op.tensor_mul, Op.tensor_mul, Op.tensor_mul, Op.tensor_mul,
      acceptFlagOp_mul_self, acceptFlagOp_mul_self]

/-- For distinct key labels `u ≠ v`, key replacement annihilates the accept-block operator
with key-A factor `Matrix.single u v 1`. This holds for every transcript dimension `D`. -/
theorem keyReplace_keyCoherence (ℓ D : ℕ) (u v : Fin (2 ^ ℓ)) (huv : u ≠ v) :
    keyReplace ℓ D
        (Op.tensor (Op.tensor (Matrix.single u v (1 : ℂ)) (Matrix.single u u (1 : ℂ)))
          (acceptFlagOp D)) = 0 := by
  rw [keyReplace, LinearMap.add_apply]
  have habort : abortSandwich ℓ D
      (Op.tensor (Op.tensor (Matrix.single u v (1 : ℂ)) (Matrix.single u u (1 : ℂ)))
        (acceptFlagOp D)) = 0 := by
    simp only [abortSandwich, matrixConjLinear_apply, abortProjOp]
    rw [Op.tensor_mul, abortFlagOp_mul_acceptFlagOp, Op.tensor_zero_right, Matrix.zero_mul]
  have haccept : keyReplaceAccept ℓ D
      (Op.tensor (Op.tensor (Matrix.single u v (1 : ℂ)) (Matrix.single u u (1 : ℂ)))
        (acceptFlagOp D)) = 0 := by
    simp only [keyReplaceAccept, LinearMap.sum_apply, matrixConjLinear_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [freshKeyKraus_conj, single_conj_single_eq_zero _ _ _ _ huv, opTensor_zero_left,
      opTensor_zero_left, smul_zero]
  rw [habort, haccept, add_zero]

/-- If `[NeZero D]` and `1 ≤ ℓ`, key replacement differs from the identity: it annihilates a
nonzero accept-block off-diagonal operator. This witness is not a density state. -/
theorem keyReplace_ne_id (ℓ D : ℕ) [NeZero D] (hℓ : 1 ≤ ℓ) :
    keyReplace ℓ D
      ≠ (LinearMap.id : Op (QKD.keyedFlagOutDim ℓ D) →ₗ[ℂ] Op (QKD.keyedFlagOutDim ℓ D)) := by
  have h2 : 1 < 2 ^ ℓ := by
    calc 1 < 2 := by norm_num
      _ = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  set u : Fin (2 ^ ℓ) := ⟨0, by omega⟩ with hu
  set v : Fin (2 ^ ℓ) := ⟨1, by omega⟩ with hv
  have huv : u ≠ v := by
    rw [hu, hv, Ne, Fin.mk.injEq]
    omega
  set ρ : Op (QKD.keyedFlagOutDim ℓ D) :=
    Op.tensor (Op.tensor (Matrix.single u v (1 : ℂ)) (Matrix.single u u (1 : ℂ)))
      (acceptFlagOp D) with hρ
  have hzero : keyReplace ℓ D ρ = 0 := keyReplace_keyCoherence ℓ D u v huv
  have hne : ρ ≠ 0 := by
    intro hc
    have hentry := congrFun (congrFun hc
        (finProdFinEquiv (finProdFinEquiv (u, u),
          finProdFinEquiv ((0 : Fin 2), (0 : Fin D)))))
      (finProdFinEquiv (finProdFinEquiv (v, u), finProdFinEquiv ((0 : Fin 2), (0 : Fin D))))
    rw [hρ] at hentry
    simp only [Op_tensor_apply_finProd, acceptFlagOp, Equiv.symm_apply_apply, Matrix.single_apply,
      Matrix.one_apply, Matrix.zero_apply, and_self, ite_true] at hentry
    norm_num at hentry
  intro hcon
  rw [hcon] at hzero
  exact hne hzero

end QKD

end
