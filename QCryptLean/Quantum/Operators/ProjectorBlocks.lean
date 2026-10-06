import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Complementary projector blocks and Löwner support absorption

Fix a projector `P` and its complement `Q = 1 - P`.  Every operator `A` splits into its four
`{P, Q}` blocks

  `A = P·A·P + Q·A·Q + (Q·A·P + P·A·Q)`,

and, once `P` is idempotent, the two diagonal blocks carry the whole trace, so the
complementary block obeys the mass-conservation identity `Tr (Q·A·Q) = Tr A − Tr (P·A·P)`.

The second half of the file is the interaction of this splitting with the Löwner order.  If a
reference operator `B` is *fixed* by `P` (`B·P = B`, equivalently `B·Q = 0`), then every
positive semidefinite `A ⪯ B` is fixed by `P` as well: Löwner domination contains the support
(`Quantum.Operators.opLe_mul_right_eq_zero_of_psd`), so `A` cannot leak into `range Q`.
Consequently a state-supported summand splits off the blocks of a sum `C + D` cleanly, and a
bulk term `c·B` in `A − c·B` contributes only to the `P`-block; the residual retains the
complementary and off-diagonal blocks of `A`.

`P` is not assumed idempotent except where the trace identity needs it, and Hermiticity of `P`
is used only to mirror a right-sided statement to the left.

## Main statements

* `Quantum.Operators.proj_compl_decomposition` — the four-block decomposition, valid in any
  ring for an arbitrary `p`, since it only expands `a = (p + (1 - p)) * a * (p + (1 - p))`.
* `Quantum.Operators.trace_compl_block`, `Quantum.Operators.trace_re_compl_block` — the
  complementary-block trace identity for an idempotent `P`.
* `Quantum.Operators.mul_compl_proj_of_opLe`, `Quantum.Operators.compl_proj_mul_of_opLe`,
  `Quantum.Operators.mul_proj_of_opLe`, `Quantum.Operators.proj_mul_of_opLe` — the left/right
  zero and identity laws for a positive semidefinite operator dominated by a `P`-supported
  reference.
* `Quantum.Operators.proj_block_add_of_opLe`,
  `Quantum.Operators.compl_proj_offDiag_add_of_opLe`,
  `Quantum.Operators.proj_compl_offDiag_add_of_opLe` — the blocks of `C + D` when `C ⪯ B`.
* `Quantum.Operators.proj_block_sub_smul`, `Quantum.Operators.compl_block_sub_smul`,
  `Quantum.Operators.compl_proj_offDiag_sub_smul`,
  `Quantum.Operators.proj_compl_offDiag_sub_smul` — the four blocks of `A − c·B`.

The Löwner bound on `A − c·B` assembled from these blocks is
`Quantum.Operators.opLe_smul_one_of_compl_block_psd`, in
`QCryptLean.Quantum.Operators.PSDTraceBound`, where the spectral input
`opLe_smul_one_of_psd_diag_add_offdiag` lives.

## References

* R. Bhatia, *Matrix Analysis*: the 2×2 block form induced by an orthogonal projection
  (Chapter I) and the Löwner order on positive operators (Chapter V).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Quantum.Operators

/-! ### The four blocks of an operator -/

/-- **Two-block decomposition relative to `p` and `1 - p`.**

`a = p·a·p + (1 − p)·a·(1 − p) + ((1 − p)·a·p + p·a·(1 − p))` in any ring.  Only
`p + (1 - p) = 1` is used, so no idempotence, Hermiticity or positivity is required; the
regrouping into a diagonal pair and an off-diagonal pair is what makes it useful once `p` is a
projector. -/
theorem proj_compl_decomposition {R : Type*} [Ring R] (p a : R) :
    a = p * a * p + (1 - p) * a * (1 - p) + ((1 - p) * a * p + p * a * (1 - p)) := by
  conv_lhs => rw [show a = (p + (1 - p)) * a * (p + (1 - p)) by
    rw [add_sub_cancel, one_mul, mul_one]]
  rw [add_mul, add_mul, mul_add, mul_add]
  abel

/-- **Complementary-block trace identity.** For an idempotent `P`,
`Tr ((1 − P)·A·(1 − P)) = Tr A − Tr (P·A·P)`.

Trace cyclicity kills both off-diagonal blocks and collapses `Tr (P·A·P)` to `Tr (P·A)`, so
the two diagonal blocks share the whole trace.  This is a scalar statement: it bounds the
complementary block's trace mass without any control of its operator norm. -/
theorem trace_compl_block {n : ℕ} {P : Op n} (hP : P * P = P) (A : Op n) :
    ((1 - P) * A * (1 - P)).trace = A.trace - (P * A * P).trace := by
  have key : (1 - P) * A * (1 - P) = A - P * A - A * P + P * A * P := by noncomm_ring
  have h1 : (A * P).trace = (P * A).trace := Matrix.trace_mul_comm A P
  have h2 : (P * A * P).trace = (P * A).trace := by
    rw [Matrix.trace_mul_comm (P * A) P, ← Matrix.mul_assoc, hP]
  rw [key]
  simp only [Matrix.trace_add, Matrix.trace_sub, h1, h2]
  ring

/-- The real part of `trace_compl_block`, the form a scalar floor is usually compared with. -/
theorem trace_re_compl_block {n : ℕ} {P : Op n} (hP : P * P = P) (A : Op n) :
    ((1 - P) * A * (1 - P)).trace.re = A.trace.re - (P * A * P).trace.re := by
  rw [trace_compl_block hP, Complex.sub_re]

/-! ### Löwner support absorption by a projector

Throughout this section `B` is a reference operator fixed by `P` on the relevant side, and `A`
is positive semidefinite with `A ⪯ B`.  Domination then forces `A` to be fixed by `P` too. -/

variable {n : ℕ} {P A B : Op n}

/-- **A Löwner-dominated positive semidefinite operator is annihilated by the complementary
projector — right form.** If `B·P = B` and `A ⪯ B` with `A` positive semidefinite, then
`A·(1 − P) = 0`: the columns of `1 − P` lie in `ker B`, hence in `ker A`. -/
theorem mul_compl_proj_of_opLe (hBP : B * P = B) (hA : A.PosSemidef) (hAB : opLe A B) :
    A * (1 - P) = 0 := by
  refine opLe_mul_right_eq_zero_of_psd hA hAB ?_
  rw [Matrix.mul_sub, Matrix.mul_one, hBP, sub_self]

/-- **The projector fixes a Löwner-dominated positive semidefinite operator — right form.**
`A·P = A` for positive semidefinite `A ⪯ B` with `B·P = B`. -/
theorem mul_proj_of_opLe (hBP : B * P = B) (hA : A.PosSemidef) (hAB : opLe A B) :
    A * P = A := by
  have h := mul_compl_proj_of_opLe hBP hA hAB
  rw [Matrix.mul_sub, Matrix.mul_one] at h
  exact (eq_of_sub_eq_zero h).symm

/-- **Left form of `mul_compl_proj_of_opLe`.** `(1 − P)·A = 0`, by conjugate transposition:
`A` is Hermitian because it is positive semidefinite, and `1 − P` is Hermitian because `P` is. -/
theorem compl_proj_mul_of_opLe (hP : P.IsHermitian) (hBP : B * P = B)
    (hA : A.PosSemidef) (hAB : opLe A B) : (1 - P) * A = 0 := by
  have h := congrArg Matrix.conjTranspose (mul_compl_proj_of_opLe hBP hA hAB)
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.eq,
    hA.isHermitian.eq, Matrix.conjTranspose_zero] at h

/-- **Left form of `mul_proj_of_opLe`.** `P·A = A`. -/
theorem proj_mul_of_opLe (hP : P.IsHermitian) (hBP : B * P = B)
    (hA : A.PosSemidef) (hAB : opLe A B) : P * A = A := by
  have h := compl_proj_mul_of_opLe hP hBP hA hAB
  rw [Matrix.sub_mul, Matrix.one_mul] at h
  exact (eq_of_sub_eq_zero h).symm

/-! ### Blocks of a sum with a dominated summand

For `A = C + D` with `C` positive semidefinite and `C ⪯ B`, the summand `C` sits entirely
inside the `P`-block: the complementary block and both off-diagonal blocks of `C + D` are
those of the deviation `D` alone, while the `P`-block keeps `C` in full. -/

/-- The off-diagonal block `(1 − P)·(C + D)·P` sees only the deviation `D`. -/
theorem compl_proj_offDiag_add_of_opLe {C : Op n} (hP : P.IsHermitian) (hBP : B * P = B)
    (hC : C.PosSemidef) (hCB : opLe C B) (D : Op n) :
    (1 - P) * (C + D) * P = (1 - P) * D * P := by
  rw [Matrix.mul_add, Matrix.add_mul, compl_proj_mul_of_opLe hP hBP hC hCB, Matrix.zero_mul,
    zero_add]

/-- The off-diagonal block `P·(C + D)·(1 − P)` sees only the deviation `D`. -/
theorem proj_compl_offDiag_add_of_opLe {C : Op n} (hBP : B * P = B)
    (hC : C.PosSemidef) (hCB : opLe C B) (D : Op n) :
    P * (C + D) * (1 - P) = P * D * (1 - P) := by
  have hCQ : P * C * (1 - P) = 0 := by
    rw [Matrix.mul_assoc, mul_compl_proj_of_opLe hBP hC hCB, Matrix.mul_zero]
  rw [Matrix.mul_add, Matrix.add_mul, hCQ, zero_add]

/-- The `P`-block of `C + D` retains the dominated summand `C` in full, plus the `P`-block of
the deviation: `P·(C + D)·P = C + P·D·P`. -/
theorem proj_block_add_of_opLe {C : Op n} (hP : P.IsHermitian) (hBP : B * P = B)
    (hC : C.PosSemidef) (hCB : opLe C B) (D : Op n) :
    P * (C + D) * P = C + P * D * P := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, mul_proj_of_opLe hBP hC hCB,
    proj_mul_of_opLe hP hBP hC hCB]

/-! ### Blocks of a bulk-subtracted operator

If `P` fixes `B` on both sides, the bulk `c·B` survives exactly on the `P`-block of `A − c·B`
and disappears from every block meeting `1 − P`. -/

/-- `P·(A − c·B)·P = P·A·P − c·B`. -/
theorem proj_block_sub_smul (hPB : P * B = B) (hBP : B * P = B) (A : Op n) (c : ℂ) :
    P * (A - c • B) * P = P * A * P - c • B := by
  rw [Matrix.mul_sub, mul_smul_comm, hPB, Matrix.sub_mul, smul_mul_assoc, hBP]

/-- `(1 − P)·(A − c·B)·(1 − P) = (1 − P)·A·(1 − P)`. -/
theorem compl_block_sub_smul (hPB : P * B = B) (A : Op n) (c : ℂ) :
    (1 - P) * (A - c • B) * (1 - P) = (1 - P) * A * (1 - P) := by
  have hQB : (1 - P) * B = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPB, sub_self]
  have h : (1 - P) * (A - c • B) = (1 - P) * A := by
    rw [Matrix.mul_sub, mul_smul_comm, hQB, smul_zero, sub_zero]
  rw [h]

/-- `(1 − P)·(A − c·B)·P = (1 − P)·A·P`. -/
theorem compl_proj_offDiag_sub_smul (hPB : P * B = B) (A : Op n) (c : ℂ) :
    (1 - P) * (A - c • B) * P = (1 - P) * A * P := by
  have hQB : (1 - P) * B = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPB, sub_self]
  rw [Matrix.mul_sub, mul_smul_comm, hQB, smul_zero, sub_zero]

/-- `P·(A − c·B)·(1 − P) = P·A·(1 − P)`. -/
theorem proj_compl_offDiag_sub_smul (hBP : B * P = B) (A : Op n) (c : ℂ) :
    P * (A - c • B) * (1 - P) = P * A * (1 - P) := by
  have hBQ : B * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hBP, sub_self]
  have h : (A - c • B) * (1 - P) = A * (1 - P) := by
    rw [Matrix.sub_mul, smul_mul_assoc, hBQ, smul_zero, sub_zero]
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]

/-- The bulk-subtracted operator rewritten in its four blocks: the bulk `c·B` sits inside the
`P`-block and the complementary block is that of `A` alone. -/
theorem sub_smul_eq_blocks (hPB : P * B = B) (hBP : B * P = B) (A : Op n) (c : ℂ) :
    A - c • B = (1 - P) * A * (1 - P)
      + ((P * A * P - c • B) + ((1 - P) * A * P + P * A * (1 - P))) := by
  have hdec := proj_compl_decomposition P (A - c • B)
  rw [proj_block_sub_smul hPB hBP A c, compl_block_sub_smul hPB A c,
    compl_proj_offDiag_sub_smul hPB A c, proj_compl_offDiag_sub_smul hBP A c] at hdec
  rw [hdec]
  abel

/-- How the absorption laws are used: a reference `B` supported on `range P` absorbs every
positive semidefinite `A ⪯ B`, so `A` has no complementary block at all and the complementary
block of a sum `A + D` is that of the deviation `D` alone. -/
example {D : Op n} (hP : P.IsHermitian) (hBP : B * P = B)
    (hA : A.PosSemidef) (hAB : opLe A B) :
    (1 - P) * (A + D) * (1 - P) = (1 - P) * D * (1 - P) := by
  rw [Matrix.mul_add, Matrix.add_mul, compl_proj_mul_of_opLe hP hBP hA hAB, Matrix.zero_mul,
    zero_add]

end Quantum.Operators
