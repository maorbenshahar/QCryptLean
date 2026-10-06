import QCryptLean.Quantum.Symmetry.SymmetricSubspace
import QCryptLean.Quantum.BellStates
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized

/-!
# Bell de Finetti domination — the `x = 4` (exponent `d − 1 = 3`) postselection core

Generic, protocol-independent infrastructure for the Nahar et al. 2024 (`arXiv:2403.11851`)
symmetry-improved de Finetti reduction (§II.B, Lemma 2 / Theorem 2 / Corollary 2.2),
specialised to the **diagonal bilateral-Pauli (Bell) group**
`G = {I⊗I, X⊗X, Y⊗Y, Z⊗Z} ≅ ℤ₂ × ℤ₂` acting on `ℂ⁴ = ℂ²_A ⊗ ℂ²_B`.

`G` has `4` one-dimensional Bell irreps (`Σ mᵢ² = 4`), so the de Finetti cost collapses to
`g_{n,4} = dim Symⁿ(ℂ⁴) = C(n+3,3) ≤ (n+1)³`, the exponent `3` improvement over the generic
`x = d² = 16` (`(n+1)^15`). Because the `4` Bell blocks are `1`-dimensional, the domination needs
**no** Schur–Weyl `Symⁿ(⊕Vᵢ)` decomposition: in the joint Bell basis it is a diagonal scalar
inequality `multinomial(T)·λ_T ≤ 1` (just `Tr ρ = 1` over the type classes), with Dirichlet moments
`τ_T = 3!∏nᵢ!/(n+3)!`.

This protocol-independent module supplies the twirl, the diagonality predicate, the de Finetti
reference state, and the domination statement. Protocol covariance is a separate hypothesis.

## Main definitions
- `bb84BellSinglePairTwirlGroup`: the `4` group operators `[I⊗I, X⊗X, Y⊗Y, Z⊗Z]` on `ℂ⁴`.
- `bellTwirlUnitary`: `U_{g⃗} = ⊗ₐ G(g⃗ a)`, the per-string twirl unitary, a
  `Quantum.TensorProducts.tensorFamily` of bilateral Paulis.
- `bb84BellTwirl`: the IID bilateral-Pauli twirl channel `ρ ↦ 4^{-n} Σ_{g⃗} U_{g⃗} ρ U_{g⃗}†`.
- `IsIIDBellDiagonal`: fixed point of `bb84BellTwirl` (≡ joint-Bell-basis diagonal).
- `bellRotation`: the fixed Bell→computational basis change `V^{⊗n}` (`V|β_k⟩ = |k⟩`), used to
phrase
  Bell-basis diagonality.
- `bb84BellDeFinettiState`: the Bell-sector symmetric de Finetti reference, the Bell-twirl
  (dephasing) of the normalized symmetric projector `C(n+3,3)⁻¹ · P_sym` (equivalently the
  diagonal Dirichlet-moment operator).

## Main statements
- `bb84BellSinglePairTwirlGroup_unitary`, `bellTwirlUnitary_unitary`: the group/string operators are
  unitary.
- `bb84BellSinglePairTwirlGroup_zero_eq` … `bb84BellSinglePairTwirlGroup_three_eq`: the four group
  elements as explicit `4×4` matrices in the computational basis.
- `bb84BellTwirl_trace`, `bb84BellTwirl_posSemidef`: the twirl preserves trace and positivity.
- `iidBellDiagonal_iff_bellBasis_diagonal`: IID-`G`-invariance ⟺ joint-Bell-basis diagonal.
- `bb84_bellSym_deFinetti_domination`: for permutation-invariant IID-Bell-diagonal `ρ`,
  `ρ ≤ C(n+3,3) · τ_Bell` (Löwner order).

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B, Lemma 1
(`:260`),
Lemma 2 (`:334`), Theorem 2 (`:221`), Corollary 2.2 (`:359`); CKR (2009) `arXiv:0809.3019`
substate Lemma 1; Renner thesis `arXiv:quant-ph/0512258v2` Lemma 4.2.2.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Gates Quantum.Basis.BellStates
open Math.RepresentationTheory Matrix InfoTheory.SmoothMinEntropy
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Symmetry

/-- Auxiliary: `(4^n : ℂ)⁻¹ ≥ 0` (it is a positive real cast). -/
private theorem complex_inv_natPow_nonneg (n : ℕ) : (0 : ℂ) ≤ (4 ^ n : ℂ)⁻¹ := by
  rw [show (4 ^ n : ℂ) = (((4 : ℝ) ^ n : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_inv]
  exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (by positivity))

/-- Auxiliary: `(k : ℂ)⁻¹ ≥ 0` for a natural number `k`. -/
private theorem complex_inv_natCast_nonneg (k : ℕ) : (0 : ℂ) ≤ (k : ℂ)⁻¹ := by
  rw [show (k : ℂ) = ((k : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_inv]
  exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg k))

/-!
## The Bell twirl group, the twirl channel, and the diagonality predicate
-/

/-- **The diagonal bilateral-Pauli (Bell) group on `ℂ⁴`.**

`bb84BellSinglePairTwirlGroup = ![I⊗I, X⊗X, Y⊗Y, Z⊗Z]`, the four group unitaries of
`G ≅ ℤ₂ × ℤ₂` whose commutant is the Bell-diagonal operators. Element `0` is the `4×4` identity
`I⊗I = 1`; the others are the bilateral Paulis. Explicit; no `Classical.choose`. -/
def bb84BellSinglePairTwirlGroup : Fin 4 → Op 4 :=
  ![(1 : Op 4),
    (Op.tensor pauliX pauliX : Op 4),
    (Op.tensor pauliY pauliY : Op 4),
    (Op.tensor pauliZ pauliZ : Op 4)]

/-- Each Bell-group operator is unitary: `(G k)† · G k = 1`. -/
theorem bb84BellSinglePairTwirlGroup_unitary (k : Fin 4) :
    (bb84BellSinglePairTwirlGroup k)ᴴ * bb84BellSinglePairTwirlGroup k = (1 : Op 4) := by
  fin_cases k
  · change (1 : Op 4)ᴴ * (1 : Op 4) = 1
    rw [Matrix.conjTranspose_one, Matrix.one_mul]
  · change (Op.tensor pauliX pauliX)ᴴ * Op.tensor pauliX pauliX = 1
    exact tensor_conj_transpose_mul_self_of_conj_transpose_mul_self _ _ pauliX_unitary
        pauliX_unitary
  · change (Op.tensor pauliY pauliY)ᴴ * Op.tensor pauliY pauliY = 1
    exact tensor_conj_transpose_mul_self_of_conj_transpose_mul_self _ _ pauliY_unitary
        pauliY_unitary
  · change (Op.tensor pauliZ pauliZ)ᴴ * Op.tensor pauliZ pauliZ = 1
    exact tensor_conj_transpose_mul_self_of_conj_transpose_mul_self _ _ pauliZ_unitary
        pauliZ_unitary

/-- **The per-string twirl unitary `U_{g⃗} = ⊗ₐ G(g⃗ a)`** for `g⃗ ∈ (Fin 4)ⁿ`. -/
def bellTwirlUnitary (n : ℕ) (g : Fin n → Fin 4) : Op (4 ^ n) :=
  tensorFamily fun a => bb84BellSinglePairTwirlGroup (g a)

/-- Each per-string twirl unitary is unitary. -/
theorem bellTwirlUnitary_unitary (n : ℕ) (g : Fin n → Fin 4) :
    (bellTwirlUnitary n g)ᴴ * bellTwirlUnitary n g = 1 :=
  conjTranspose_tensorFamily_mul_self fun a => bb84BellSinglePairTwirlGroup_unitary (g a)

/-- **The IID bilateral-Pauli (Bell) twirl channel** on `(ℂ⁴)^{⊗n}`:
`bb84BellTwirl n ρ = 4^{-n} Σ_{g⃗} U_{g⃗} ρ U_{g⃗}†`.

This is the per-round Bell dephasing map; its fixed points are exactly the joint-Bell-diagonal
operators. Explicit; no `Classical.choose`. -/
def bb84BellTwirl (n : ℕ) (M : Op (4 ^ n)) : Op (4 ^ n) :=
  (4 ^ n : ℂ)⁻¹ • ∑ g : Fin n → Fin 4, bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ

/-- **The Bell twirl preserves trace**: `Tr(bb84BellTwirl n M) = Tr M`. Each `U_{g⃗} M U_{g⃗}†` has
trace `Tr M` by cyclicity and unitarity, and there are `4^n` strings. -/
theorem bb84BellTwirl_trace (n : ℕ) (M : Op (4 ^ n)) :
    (bb84BellTwirl n M).trace = M.trace := by
  unfold bb84BellTwirl
  rw [Matrix.trace_smul, Matrix.trace_sum]
  have hterm : ∀ g : Fin n → Fin 4,
      (bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ).trace = M.trace := by
    intro g
    rw [Matrix.trace_mul_comm (bellTwirlUnitary n g * M) (bellTwirlUnitary n g)ᴴ,
      ← Matrix.mul_assoc, bellTwirlUnitary_unitary, Matrix.one_mul]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul, smul_eq_mul, ← mul_assoc,
    show ((4 ^ n : ℕ) : ℂ) = (4 : ℂ) ^ n from by push_cast; ring,
    inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (4 : ℂ) ≠ 0)), one_mul]

/-- **The Bell twirl preserves positivity**: if `M` is PSD then so is `bb84BellTwirl n M`. -/
theorem bb84BellTwirl_posSemidef (n : ℕ) {M : Op (4 ^ n)} (hM : M.PosSemidef) :
    (bb84BellTwirl n M).PosSemidef := by
  unfold bb84BellTwirl
  exact (Matrix.posSemidef_sum Finset.univ
      (fun g _ => hM.mul_mul_conjTranspose_same (bellTwirlUnitary n g))).smul
    (complex_inv_natPow_nonneg n)

/-- **IID-`G`-invariance (joint-Bell-diagonality).** `ρ` is a fixed point of the IID Bell twirl.

By `iidBellDiagonal_iff_bellBasis_diagonal` this is equivalent to `ρ` being diagonal in the `n`-fold
joint Bell basis. This is the load-bearing structural hypothesis of the de Finetti domination. -/
def IsIIDBellDiagonal {n : ℕ} (ρ : Op (4 ^ n)) : Prop := bb84BellTwirl n ρ = ρ

/-!
## The dephasing characterization (joint-Bell-basis diagonality)
-/

/-- The four Bell states as an indexed orthonormal basis of `ℂ⁴`. -/
def bellKet : Fin 4 → Ket 4 := ![bellState00, bellState01, bellState10, bellState11]

/-- **The single-pair Bell rotation `V`** (`V|β_k⟩ = |k⟩`): entries
`V i j = conj((β_i).vec j)`. -/
def bellSinglePairRotation : Op 4 :=
  Matrix.of fun i j => (starRingEnd ℂ) ((bellKet i).vec j)

/-- **The fixed Bell→computational basis change `V^{⊗n}`** (`V|β_k⟩ = |k⟩`), as the tensor power of
the single-pair Bell rotation. Conjugating by `V^{⊗n}` reads off the joint **Bell**-basis of `ρ` in
the computational basis, so `(V^{⊗n} · ρ · V^{⊗n}†).IsDiag` says `ρ` is joint-Bell-diagonal. -/
def bellRotation (n : ℕ) : Op (4 ^ n) :=
  tensorFamily fun _ : Fin n => bellSinglePairRotation

/-!
### Single-pair layer: the explicit `4×4` Bell rotation, the character table, and orthogonality

Every single-pair fact is a finite computation with explicit `!![…]` matrices. Each matrix is
computed once, as a whole, and reused:
* the Pauli matrices and the Kronecker product of two `2×2` matrices (`pauliX_eq_matrix`,
  `Op.tensor_fin_two_eq_matrix`) give the four Bell-group elements
  (`bb84BellSinglePairTwirlGroup_zero_eq` … `bb84BellSinglePairTwirlGroup_three_eq`);
* the Bell kets (`bellState00_vec` …) are the rows of the integer matrix `Bexp` scaled by `(√2)⁻¹`
  (`bellKet_vec`);
* products of explicit matrices are evaluated row by row (`Matrix.cons_mul`, `Matrix.cons_vecMul`).
-/

/-- Explicit matrix of the Bell-group element `G 0 = I ⊗ I`: the identity. -/
theorem bb84BellSinglePairTwirlGroup_zero_eq :
    bb84BellSinglePairTwirlGroup 0 = !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1] := by
  change (1 : Op 4) = _
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Explicit matrix of the Bell-group element `G 1 = X ⊗ X`: the anti-diagonal permutation
`|ab⟩ ↦ |(1-a)(1-b)⟩`. -/
theorem bb84BellSinglePairTwirlGroup_one_eq :
    bb84BellSinglePairTwirlGroup 1 = !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0] := by
  change Op.tensor pauliX pauliX = _
  rw [pauliX_eq_matrix, Op.tensor_fin_two_eq_matrix]
  simp only [mul_zero, mul_one]

/-- Explicit matrix of the Bell-group element `G 2 = Y ⊗ Y`: the anti-diagonal signed permutation
(`i · i = (-i) · (-i) = -1` on the corners, `i · (-i) = 1` in the middle). -/
theorem bb84BellSinglePairTwirlGroup_two_eq :
    bb84BellSinglePairTwirlGroup 2 = !![0,0,0,(-1); 0,0,1,0; 0,1,0,0; (-1),0,0,0] := by
  change Op.tensor pauliY pauliY = _
  rw [pauliY_eq_matrix, Op.tensor_fin_two_eq_matrix]
  simp only [mul_zero, zero_mul, mul_neg, neg_mul, neg_neg, neg_zero, Complex.I_mul_I]

/-- Explicit matrix of the Bell-group element `G 3 = Z ⊗ Z`: the diagonal sign `(-1)^(a+b)`. -/
theorem bb84BellSinglePairTwirlGroup_three_eq :
    bb84BellSinglePairTwirlGroup 3 = !![1,0,0,0; 0,(-1),0,0; 0,0,(-1),0; 0,0,0,1] := by
  change Op.tensor pauliZ pauliZ = _
  rw [pauliZ_eq_matrix, Op.tensor_fin_two_eq_matrix]
  simp only [mul_zero, mul_one, mul_neg, neg_neg, neg_zero]

/-- The integer matrix `B` with `bellSinglePairRotation = (√2)⁻¹ • B`. -/
private def Bexp : Op 4 := !![1,0,0,1; 0,1,1,0; 1,0,0,(-1); 0,1,(-1),0]

/-- The `ℤ₂×ℤ₂` character table `χ_k(p)` (rows `k = I,XX,YY,ZZ`; columns `p = β₀₀,β₀₁,β₁₀,β₁₁`),
each `±1`: the eigenvalue of the bilateral Pauli `G k` on Bell state `p`. -/
private def bellCharE : Fin 4 → Fin 4 → ℂ :=
  ![![1,1,1,1], ![1,1,-1,-1], ![-1,1,1,-1], ![1,-1,1,-1]]

/-- A diagonal `4×4` matrix as an explicit matrix. Each entry holds by definitional unfolding. -/
private theorem diagonal_fin_four (d : Fin 4 → ℂ) :
    Matrix.diagonal d = !![d 0, 0, 0, 0; 0, d 1, 0, 0; 0, 0, d 2, 0; 0, 0, 0, d 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The Bell kets are the rows of `Bexp`**, normalised: `|β_p⟩ = (√2)⁻¹ • Bexp p`. Each Bell ket
is `(√2)⁻¹ (|ab⟩ ± |a'b'⟩)`, and `|ab⟩` is the basis vector of index `2a + b`. -/
private theorem bellKet_vec (p : Fin 4) :
    (bellKet p).vec = (Real.sqrt 2 : ℂ)⁻¹ • Bexp p := by
  fin_cases p
  exacts [bellState00_vec, bellState01_vec, bellState10_vec, bellState11_vec]

private theorem Bexp_conjTranspose :
    (Bexp)ᴴ = !![1,0,1,0; 0,1,0,1; 0,1,0,(-1); 1,0,(-1),0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Bexp, Matrix.conjTranspose_apply]

/-- `Bexp` is real: `Bexpᴴ = Bexpᵀ` (both are the explicit transpose). -/
private theorem Bexp_conjTranspose_eq_transpose : (Bexp)ᴴ = (Bexp)ᵀ := by
  -- `transposeᵣ` transposes an explicit matrix literal by unfolding, so `rfl` closes the goal.
  rw [Bexp_conjTranspose, ← Matrix.transposeᵣ_eq]
  rfl

private theorem bellSPR_eq : bellSinglePairRotation = (Real.sqrt 2 : ℂ)⁻¹ • Bexp := by
  ext i j
  -- `V i j = conj ((√2)⁻¹ · Bexp i j) = (√2)⁻¹ · conj (Bexp i j)`, and `Bexp` is real.
  have hreal : (starRingEnd ℂ) (Bexp i j) = Bexp i j := by
    simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, starRingEnd_apply] using
      congrFun (congrFun Bexp_conjTranspose_eq_transpose j) i
  rw [bellSinglePairRotation, Matrix.of_apply, bellKet_vec, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul, map_mul, map_inv₀, Complex.conj_ofReal, hreal]

/-- `B · G k · Bᴴ = 2 · diag(χ_k)`: the integer-matrix core of the single-pair diagonalisation,
evaluated row by row from the explicit matrices. -/
private theorem BGB (k : Fin 4) :
    Bexp * bb84BellSinglePairTwirlGroup k * (Bexp)ᴴ = (2:ℂ) • Matrix.diagonal (bellCharE k) := by
  rw [Bexp_conjTranspose, Bexp, diagonal_fin_four]
  -- for each group element, multiply out the three explicit `4×4` matrices
  fin_cases k <;>
    simp [bb84BellSinglePairTwirlGroup_zero_eq, bb84BellSinglePairTwirlGroup_one_eq,
      bb84BellSinglePairTwirlGroup_two_eq, bb84BellSinglePairTwirlGroup_three_eq, bellCharE] <;>
    norm_num

/-- The single-pair Bell rotation diagonalises every bilateral Pauli: `V · G k · V† = diag(χ_k)`. -/
private theorem bellSPR_diag (k : Fin 4) :
    bellSinglePairRotation * bb84BellSinglePairTwirlGroup k * (bellSinglePairRotation)ᴴ =
      Matrix.diagonal (bellCharE k) := by
  -- `V = c • B` with the real scalar `c = (√2)⁻¹`, so `V G V† = c² • (B G Bᴴ) = ½ • 2 • diag χ_k`.
  have hc : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [bellSPR_eq, Matrix.conjTranspose_smul, hc, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, inv_sqrt_two_mul_self, BGB, smul_smul,
    one_div_mul_cancel two_ne_zero, one_smul]

/-- The rows of `V` are the Bell bras, so `V · V† = 1` is exactly Bell-basis orthonormality
(`bellStates_orthonormal`). -/
private theorem bellSPR_mul_conjTranspose :
    bellSinglePairRotation * (bellSinglePairRotation)ᴴ = 1 := by
  ext i j
  have hortho := bellStates_orthonormal i j
  simp only at hortho
  rw [bra_mul_ket_eq] at hortho
  rw [Matrix.mul_apply, Matrix.one_apply, ← hortho]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, bellSinglePairRotation, Matrix.of_apply, Matrix.of_apply,
    Ket.dag_vec, starRingEnd_apply, starRingEnd_apply, star_star, bellKet, starRingEnd_apply]

private theorem bellSPR_unitary : (bellSinglePairRotation)ᴴ * bellSinglePairRotation = 1 :=
  mul_eq_one_comm.mpr bellSPR_mul_conjTranspose

/-- Single-pair character orthogonality (the `ℤ₂×ℤ₂` column orthogonality of the Bell table). -/
private theorem bellCharOrtho (p q : Fin 4) :
    (4:ℂ)⁻¹ * ∑ k : Fin 4, bellCharE k p * star (bellCharE k q) = if p = q then 1 else 0 := by
  simp only [Fin.sum_univ_four, bellCharE, Matrix.cons_val]
  fin_cases p <;> fin_cases q <;> norm_num

/-!
### `n`-fold layer: the Bell rotation is unitary and diagonalises each per-string twirl unitary
-/

/-- **The fixed Bell→computational basis change `V^{⊗n}` is an isometry**: `(V^{⊗n})† · V^{⊗n} = 1`.
Tensor power of the unitary single-pair Bell rotation. -/
theorem bellRotation_unitary (n : ℕ) : (bellRotation n)ᴴ * bellRotation n = 1 :=
  conjTranspose_tensorFamily_mul_self fun _ => bellSPR_unitary

/-- **The fixed Bell→computational basis change `V^{⊗n}` is co-isometric**: `V^{⊗n} · (V^{⊗n})† = 1`
(the square-matrix companion of `bellRotation_unitary`). -/
theorem bellRotation_mul_conjTranspose (n : ℕ) : bellRotation n * (bellRotation n)ᴴ = 1 :=
  mul_eq_one_comm.mpr (bellRotation_unitary n)

/-- Per-string phase function `∏ₐ χ_{g a}(string i at position a)`. -/
private def phaseDg (n : ℕ) (g : Fin n → Fin 4) (i : Fin (4 ^ n)) : ℂ :=
  ∏ a : Fin n, bellCharE (g a) ((@finFunctionFinEquiv 4 n).symm i a)

private theorem bellRot_conj_twirlUnitary (n : ℕ) (g : Fin n → Fin 4) :
    bellRotation n * bellTwirlUnitary n g * (bellRotation n)ᴴ = Matrix.diagonal (phaseDg n g) := by
  simp only [bellRotation, bellTwirlUnitary, conjTranspose_tensorFamily, tensorFamily_mul,
    bellSPR_diag, tensorFamily_diagonal]
  rfl

/-- The `n`-fold character orthogonality: `4⁻ⁿ Σ_g χ_g(i) χ_g(j)* = δ_{ij}`. -/
private theorem charOrthoN (n : ℕ) (i j : Fin (4 ^ n)) :
    ((4:ℂ) ^ n)⁻¹ * ∑ g : Fin n → Fin 4, phaseDg n g i * star (phaseDg n g j) =
      if i = j then 1 else 0 := by
  have hsummand : ∀ g : Fin n → Fin 4,
      phaseDg n g i * star (phaseDg n g j) =
        ∏ a : Fin n, (bellCharE (g a) ((@finFunctionFinEquiv 4 n).symm i a) *
          star (bellCharE (g a) ((@finFunctionFinEquiv 4 n).symm j a))) := by
    intro g
    simp only [phaseDg, star_prod, ← Finset.prod_mul_distrib]
  simp_rw [hsummand]
  rw [← Fintype.prod_sum (f := fun (a : Fin n) (k : Fin 4) =>
      bellCharE k ((@finFunctionFinEquiv 4 n).symm i a) *
        star (bellCharE k ((@finFunctionFinEquiv 4 n).symm j a)))]
  rw [show ((4:ℂ) ^ n)⁻¹ = ∏ _a : Fin n, (4:ℂ)⁻¹ by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow]]
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun a _ => bellCharOrtho ((@finFunctionFinEquiv 4 n).symm i a)
    ((@finFunctionFinEquiv 4 n).symm j a))]
  rw [Finset.prod_boole]
  congr 1
  · simp only [eq_iff_iff]
    constructor
    · intro h; exact (@finFunctionFinEquiv 4 n).symm.injective (funext (fun a => h a
        (Finset.mem_univ a)))
    · intro h a _; rw [h]

/-- **The core dephasing identity**: conjugating the Bell twirl by `V^{⊗n}` keeps only the diagonal
(in the joint Bell basis) of `V^{⊗n} M V^{⊗n}†` — character orthogonality kills the rest. -/
private theorem bellTwirl_conj_diag (n : ℕ) (M : Op (4 ^ n)) (i j : Fin (4 ^ n)) :
    (bellRotation n * bb84BellTwirl n M * (bellRotation n)ᴴ) i j =
      if i = j then (bellRotation n * M * (bellRotation n)ᴴ) i j else 0 := by
  set W := bellRotation n with hW
  set R := W * M * Wᴴ with hR
  have hexpand : W * bb84BellTwirl n M * Wᴴ =
      ((4:ℂ) ^ n)⁻¹ • ∑ g : Fin n → Fin 4,
        (Matrix.diagonal (phaseDg n g)) * R * (Matrix.diagonal (phaseDg n g))ᴴ := by
    unfold bb84BellTwirl
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    refine congrArg (((4:ℂ) ^ n)⁻¹ • ·) (Finset.sum_congr rfl fun g _ => ?_)
    have hWW : Wᴴ * W = 1 := bellRotation_unitary n
    have hDg : W * bellTwirlUnitary n g * Wᴴ = Matrix.diagonal (phaseDg n g) :=
      bellRot_conj_twirlUnitary n g
    have hDgH : W * (bellTwirlUnitary n g)ᴴ * Wᴴ = (Matrix.diagonal (phaseDg n g))ᴴ := by
      rw [← hDg]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      noncomm_ring
    calc W * (bellTwirlUnitary n g * M * (bellTwirlUnitary n g)ᴴ) * Wᴴ
        = (W * bellTwirlUnitary n g * Wᴴ) * (W * M * Wᴴ) * (W * (bellTwirlUnitary n g)ᴴ * Wᴴ) := by
          rw [show (W * bellTwirlUnitary n g * Wᴴ) * (W * M * Wᴴ) * (W * (bellTwirlUnitary n g)ᴴ *
              Wᴴ)
                = W * bellTwirlUnitary n g * (Wᴴ * W) * M * (Wᴴ * W) * (bellTwirlUnitary n g)ᴴ * Wᴴ
              from by noncomm_ring, hWW]
          simp only [Matrix.mul_one]
          noncomm_ring
      _ = Matrix.diagonal (phaseDg n g) * R * (Matrix.diagonal (phaseDg n g))ᴴ := by
          rw [hR, hDg, hDgH]
  rw [hexpand, Matrix.smul_apply, Matrix.sum_apply]
  have hentry : ∀ g : Fin n → Fin 4,
      ((Matrix.diagonal (phaseDg n g)) * R * (Matrix.diagonal (phaseDg n g))ᴴ) i j =
        (phaseDg n g i * star (phaseDg n g j)) * R i j := by
    intro g
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Pi.star_apply]
    ring
  simp_rw [hentry]
  rw [← Finset.sum_mul, smul_eq_mul, ← mul_assoc, charOrthoN]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij, one_mul]
  · rw [if_neg hij, if_neg hij, zero_mul]

/-- **IID-`G`-invariance ⟺ joint-Bell-basis diagonality** (Nahar et al. §2.1 dephasing
equation).

For the abelian Bell group the four Bell states are joint eigenvectors with the four distinct
characters of `ℤ₂ × ℤ₂`, so on `(ℂ⁴)^{⊗n}` the twirl `4^{-n} Σ_{g⃗} U_{g⃗} (·) U_{g⃗}†` dephases in
the joint Bell basis: it kills exactly the off-diagonal Bell-basis matrix elements (character
orthogonality). Hence `ρ` is a twirl fixed point iff `V^{⊗n} ρ V^{⊗n}†` is diagonal (its
off-diagonal
entries `i ≠ j` vanish). -/
theorem iidBellDiagonal_iff_bellBasis_diagonal {n : ℕ} (ρ : Op (4 ^ n)) :
    IsIIDBellDiagonal ρ ↔
      ∀ i j, i ≠ j → (bellRotation n * ρ * (bellRotation n)ᴴ) i j = 0 := by
  unfold IsIIDBellDiagonal
  set W := bellRotation n with hW
  have hWW : Wᴴ * W = 1 := bellRotation_unitary n
  have expand : ∀ mtx : Op (4 ^ n), Wᴴ * (W * mtx * Wᴴ) * W = mtx := by
    intro mtx
    rw [show Wᴴ * (W * mtx * Wᴴ) * W = (Wᴴ * W) * mtx * (Wᴴ * W) from by noncomm_ring, hWW,
      Matrix.one_mul, Matrix.mul_one]
  constructor
  · intro h i j hij
    have hd := bellTwirl_conj_diag n ρ i j
    rw [h] at hd
    rw [hd, if_neg hij]
  · intro h
    have key : W * bb84BellTwirl n ρ * Wᴴ = W * ρ * Wᴴ := by
      ext i j
      rw [bellTwirl_conj_diag]
      by_cases hij : i = j
      · rw [if_pos hij, hij]
      · rw [if_neg hij]; exact (h i j hij).symm
    calc bb84BellTwirl n ρ = Wᴴ * (W * bb84BellTwirl n ρ * Wᴴ) * W := (expand _).symm
      _ = Wᴴ * (W * ρ * Wᴴ) * W := by rw [key]
      _ = ρ := expand _

/-!
## The Bell-sector de Finetti reference state and the domination
-/

/-- The Bell-sector symmetric subspace dimension `C(n+3,3) = dim Symⁿ(ℂ⁴)`, equal to
`Tr(symmetricProjector 4 n)`. -/
theorem symmetricProjector_four_trace (n : ℕ) [NeZero n] :
    (symmetricProjector 4 n).trace = (Nat.choose (n + 3) 3 : ℂ) := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  rw [symmetricProjector_trace 4 n]
  norm_num

/-- The symmetric projector on `(ℂ⁴)^{⊗n}` is positive semidefinite (it is a projector
`P = P† · P`). -/
theorem symmetricProjector_four_posSemidef (n : ℕ) [NeZero n] :
    (symmetricProjector 4 n).PosSemidef := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  obtain ⟨hidem, hherm⟩ := symmetricProjector_is_projector 4 n
  have h := Matrix.posSemidef_conjTranspose_mul_self (symmetricProjector 4 n)
  rwa [hherm, hidem] at h

/-- The normalized symmetric projector `C(n+3,3)⁻¹ · P_sym` is positive semidefinite. -/
theorem symmetricProjector_four_smul_posSemidef (n : ℕ) [NeZero n] :
    ((Nat.choose (n + 3) 3 : ℂ)⁻¹ • symmetricProjector 4 n).PosSemidef :=
  (symmetricProjector_four_posSemidef n).smul (complex_inv_natCast_nonneg _)

/-- **The Bell-sector symmetric de Finetti reference as a density operator.**

`τ_Bell = bb84BellTwirl n (C(n+3,3)⁻¹ · P_sym)`: the Bell-twirl (dephasing) of the normalized
symmetric projector. The dephasing collapses the symmetric projector's off-diagonal Bell-basis
entries, yielding the diagonal Dirichlet-moment operator `τ_T = 3!∏nᵢ!/(n+3)!`. Positivity and trace
`1` follow from `bb84BellTwirl_posSemidef`/`bb84BellTwirl_trace` and
`symmetricProjector_four_trace`.
Explicit; no `Classical.choose`. -/
def bb84BellDeFinettiDensity (n : ℕ) [NeZero n] : DensityOp (4 ^ n) where
  toOp := bb84BellTwirl n ((Nat.choose (n + 3) 3 : ℂ)⁻¹ • symmetricProjector 4 n)
  isHermitian :=
    (bb84BellTwirl_posSemidef n (symmetricProjector_four_smul_posSemidef n)).isHermitian
  pos_semidef := fun v =>
    posSemidef_re_quadraticForm_nonneg
      (bb84BellTwirl_posSemidef n (symmetricProjector_four_smul_posSemidef n)) v
  trace_one := by
    rw [bb84BellTwirl_trace, Matrix.trace_smul, symmetricProjector_four_trace, smul_eq_mul,
      inv_mul_cancel₀]
    exact_mod_cast (Nat.choose_pos (by omega)).ne'

/-- **The Bell-sector symmetric de Finetti reference** `τ_Bell` as a sub-normalized density operator
(Nahar et al. Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry). See `bb84BellDeFinettiDensity` for the
construction. -/
def bb84BellDeFinettiState (n : ℕ) [NeZero n] : SubDensityOp (4 ^ n) :=
  DensityOp.toSubDensityOp (bb84BellDeFinettiDensity n)

@[simp]
theorem bb84BellDeFinettiState_toOp (n : ℕ) [NeZero n] :
    (bb84BellDeFinettiState n).toOp =
      bb84BellTwirl n ((Nat.choose (n + 3) 3 : ℂ)⁻¹ • symmetricProjector 4 n) := rfl

/-- A Bell twirl output is jointly Bell-diagonal (it is a twirl fixed point). Local companion of
`QKD.BB84.Engine.bb84BellTwirl_isIIDBellDiagonal`, kept here so the de Finetti
reference lemma below stays within the general quantum-symmetry layer. -/
private theorem bb84BellTwirl_isIIDBellDiagonal_local (n : ℕ) (M : Op (4 ^ n)) :
    IsIIDBellDiagonal (bb84BellTwirl n M) := by
  rw [iidBellDiagonal_iff_bellBasis_diagonal]
  intro i j hij
  rw [bellTwirl_conj_diag, if_neg hij]

/-- The single-block Bell de Finetti reference is jointly Bell-diagonal (it is a Bell twirl
output, hence a twirl fixed point). -/
theorem bb84BellDeFinettiDensity_isIIDBellDiagonal (n : ℕ) [NeZero n] :
    IsIIDBellDiagonal (bb84BellDeFinettiDensity n).toOp :=
  bb84BellTwirl_isIIDBellDiagonal_local n _

/-!
### Reduction of the domination to the per-Bell-type scalar bound
-/

theorem bb84BellTwirl_smul (n : ℕ) (c : ℂ) (M : Op (4 ^ n)) :
    bb84BellTwirl n (c • M) = c • bb84BellTwirl n M := by
  unfold bb84BellTwirl
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
  rw [smul_comm]

private theorem deFinetti_smul_eq (n : ℕ) [NeZero n] :
    (Nat.choose (n + 3) 3 : ℂ) • (bb84BellDeFinettiState n).toOp =
      bb84BellTwirl n (symmetricProjector 4 n) := by
  rw [bb84BellDeFinettiState_toOp, ← bb84BellTwirl_smul, smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast (Nat.choose_pos (by omega)).ne'), one_smul]

private theorem bellRotation_comm_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    bellRotation n * permutationRepresentation 4 n σ =
      permutationRepresentation 4 n σ * bellRotation n :=
  tensorFamily_mul_permutationRepresentation _ σ

private theorem bellRotation_comm_symProj (n : ℕ) [NeZero n] :
    bellRotation n * symmetricProjector 4 n = symmetricProjector 4 n * bellRotation n := by
  simp only [symmetricProjector, symmetricProjectorRep]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => bellRotation_comm_perm n σ)

theorem bellRot_conj_symProj (n : ℕ) [NeZero n] :
    bellRotation n * symmetricProjector 4 n * (bellRotation n)ᴴ = symmetricProjector 4 n := by
  rw [bellRotation_comm_symProj, Matrix.mul_assoc, bellRotation_mul_conjTranspose, Matrix.mul_one]

private theorem posSemidef_conj_iff (n : ℕ) (M : Op (4 ^ n)) :
    (bellRotation n * M * (bellRotation n)ᴴ).PosSemidef ↔ M.PosSemidef := by
  constructor
  · intro hM
    have h2 := hM.mul_mul_conjTranspose_same (bellRotation n)ᴴ
    rw [Matrix.conjTranspose_conjTranspose] at h2
    have he : (bellRotation n)ᴴ * (bellRotation n * M * (bellRotation n)ᴴ) * bellRotation n = M :=
        by
      rw [show (bellRotation n)ᴴ * (bellRotation n * M * (bellRotation n)ᴴ) * bellRotation n
            = ((bellRotation n)ᴴ * bellRotation n) * M * ((bellRotation n)ᴴ * bellRotation n)
          from by noncomm_ring, bellRotation_unitary, Matrix.one_mul, Matrix.mul_one]
    rwa [he] at h2
  · intro hM
    exact hM.mul_mul_conjTranspose_same (bellRotation n)

theorem twirl_symProj_diag (n : ℕ) [NeZero n] :
    bellRotation n * bb84BellTwirl n (symmetricProjector 4 n) * (bellRotation n)ᴴ
      = Matrix.diagonal (fun i => symmetricProjector 4 n i i) := by
  ext i j
  rw [bellTwirl_conj_diag, bellRot_conj_symProj, Matrix.diagonal_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij, hij]
  · rw [if_neg hij, if_neg hij]

/-- **Every joint-Bell-basis diagonal entry of the symmetric projector is a strictly positive
real.**
The diagonal average `⟨i|P_sym|i⟩ = (1/n!) Σ_σ (U_σ)ᵢᵢ` receives the contribution `1/n!` from the
identity permutation (which fixes `i`), and every other permutation term `(U_σ)ᵢᵢ ∈ {0,1}` is
nonnegative.  Hence `⟨i|P_sym|i⟩ ≥ 1/n! > 0`. -/
private theorem symmetricProjector_four_diag_pos (n : ℕ) [NeZero n] (i : Fin (4 ^ n)) :
    0 < symmetricProjector 4 n i i := by
  classical
  set e := @finFunctionFinEquiv 4 n with he
  have hsum : symmetricProjector 4 n i i
      = (1 / (Nat.factorial n : ℂ)) *
          (((Finset.univ.filter
              (fun σ : Equiv.Perm (Fin n) => e.symm i = e.symm i ∘ ⇑σ.symm)).card : ℕ) : ℂ) := by
    simp only [symmetricProjector, symmetricProjectorRep, Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul, permutationRepresentation, Matrix.of_apply, ← he]
    rw [Finset.sum_boole]
  have hcardpos : 0 < (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => e.symm i = e.symm i ∘ ⇑σ.symm)).card := by
    rw [Finset.card_pos]
    exact ⟨1, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by simp [pull_end]⟩⟩
  rw [hsum]
  have hreal : (1 / (Nat.factorial n : ℂ)) *
        (((Finset.univ.filter
            (fun σ : Equiv.Perm (Fin n) => e.symm i = e.symm i ∘ ⇑σ.symm)).card : ℕ) : ℂ)
      = (((1 / (Nat.factorial n : ℝ)) *
          ((Finset.univ.filter
            (fun σ : Equiv.Perm (Fin n) => e.symm i = e.symm i ∘ ⇑σ.symm)).card : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hreal, Complex.zero_lt_real]
  apply mul_pos
  · exact div_pos one_pos (by exact_mod_cast Nat.factorial_pos n)
  · exact_mod_cast hcardpos

/-- **The Bell-sector symmetric de Finetti reference `τ_Bell` is positive definite** (full rank
`C(n+3,3) = dim Symⁿ(ℂ⁴)`, Nahar et al. Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry).

In the joint Bell basis `τ_Bell` is the diagonal Dirichlet-moment operator: by `twirl_symProj_diag`
and `bb84BellTwirl_smul`, `bellRotation · τ_Bell · bellRotation† = C(n+3,3)⁻¹ · diag(⟨i|P_sym|i⟩)`,
whose diagonal entries are strictly positive (`symmetricProjector_four_diag_pos`). A diagonal matrix
with strictly positive entries is positive definite (`Matrix.PosDef.diagonal`), and conjugation by
the unitary `bellRotation` preserves positive definiteness
(`Matrix.PosDef.mul_mul_conjTranspose_same`).  This is the Bell analogue of
`ckrDeFinettiState_toOp_posDef`, the full-rank witness the τ-side smooth-min-entropy reference
requires. -/
theorem bb84BellDeFinettiDensity_posDef (n : ℕ) [NeZero n] :
    (bb84BellDeFinettiDensity n).toOp.PosDef := by
  set W := bellRotation n with hW
  set Dg : Fin (4 ^ n) → ℂ :=
    fun i => (Nat.choose (n + 3) 3 : ℂ)⁻¹ * symmetricProjector 4 n i i with hDg
  have hdiag : W * (bb84BellDeFinettiDensity n).toOp * Wᴴ = Matrix.diagonal Dg := by
    have h1 : (bb84BellDeFinettiDensity n).toOp
        = (Nat.choose (n + 3) 3 : ℂ)⁻¹ • bb84BellTwirl n (symmetricProjector 4 n) :=
      bb84BellTwirl_smul n _ _
    rw [h1, Matrix.mul_smul, Matrix.smul_mul, twirl_symProj_diag]
    ext i j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, hDg, smul_eq_mul]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, hij]
    · rw [if_neg hij, if_neg hij, mul_zero]
  have hDpd : (Matrix.diagonal Dg).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    rw [hDg]
    refine mul_pos ?_ (symmetricProjector_four_diag_pos n i)
    have hcast : (Nat.choose (n + 3) 3 : ℂ)⁻¹ = (((Nat.choose (n + 3) 3 : ℝ)⁻¹ : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.zero_lt_real]
    exact inv_pos.mpr (by exact_mod_cast Nat.choose_pos (show 3 ≤ n + 3 by omega))
  have hWunit : IsUnit (Wᴴ) := IsUnit.of_mul_eq_one W (bellRotation_unitary n)
  have hBinj : Function.Injective fun v => Matrix.vecMul v (Wᴴ) :=
    Matrix.vecMul_injective_of_isUnit hWunit
  have hkey : (bb84BellDeFinettiDensity n).toOp = Wᴴ * Matrix.diagonal Dg * (Wᴴ)ᴴ := by
    rw [← hdiag, Matrix.conjTranspose_conjTranspose,
      show Wᴴ * (W * (bb84BellDeFinettiDensity n).toOp * Wᴴ) * W
          = (Wᴴ * W) * (bb84BellDeFinettiDensity n).toOp * (Wᴴ * W) from by noncomm_ring,
      bellRotation_unitary, Matrix.one_mul, Matrix.mul_one]
  rw [hkey]
  exact hDpd.mul_mul_conjTranspose_same hBinj

private theorem rho_conj_diag (n : ℕ) (ρ : Op (4 ^ n)) (hρ : IsIIDBellDiagonal ρ) :
    bellRotation n * ρ * (bellRotation n)ᴴ
      = Matrix.diagonal (fun i => (bellRotation n * ρ * (bellRotation n)ᴴ) i i) := by
  ext i j
  rw [Matrix.diagonal_apply]
  by_cases hij : i = j
  · rw [if_pos hij, hij]
  · rw [if_neg hij]
    exact (iidBellDiagonal_iff_bellBasis_diagonal ρ).mp hρ i j hij

/-- **The per-Bell-type bound** (the whole arithmetic content of the domination): the joint-Bell
diagonal entry `λ_i = ⟨β_i|ρ|β_i⟩` is at most the symmetric-projector diagonal `⟨i|P_sym|i⟩`,
because permutation-invariance makes `λ` constant on each type orbit and `Σ multinomial(T)·λ_T = 1`.
The orbit/stabiliser counting is packaged as a coset bound on permutation fibres. -/
private theorem domination_per_index (n : ℕ) [NeZero n] (ρ : Op (4 ^ n))
    (hρ_psd : ρ.PosSemidef) (hρ_trace : ρ.trace = 1)
    (hρ_perm : ∀ σ : Equiv.Perm (Fin n),
      permutationRepresentation 4 n σ * ρ = ρ * permutationRepresentation 4 n σ)
    (i : Fin (4 ^ n)) :
    (bellRotation n * ρ * (bellRotation n)ᴴ) i i ≤ symmetricProjector 4 n i i := by
  set W := bellRotation n with hWdef
  set e := @finFunctionFinEquiv 4 n with hedef
  set M := W * ρ * Wᴴ with hMdef
  have hMpsd : M.PosSemidef := (posSemidef_conj_iff n ρ).mpr hρ_psd
  have hMtr : M.trace = 1 := by
    rw [hMdef, Matrix.trace_mul_comm, ← Matrix.mul_assoc, bellRotation_unitary, Matrix.one_mul,
      hρ_trace]
  have hMinv : ∀ σ : Equiv.Perm (Fin n),
      permutationRepresentation 4 n σ * M * (permutationRepresentation 4 n σ)ᴴ = M := by
    intro σ
    have c1 : permutationRepresentation 4 n σ * W = W * permutationRepresentation 4 n σ :=
      (bellRotation_comm_perm n σ).symm
    have c2 : Wᴴ * (permutationRepresentation 4 n σ)ᴴ = (permutationRepresentation 4 n σ)ᴴ * Wᴴ :=
        by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, c1]
    have huu : permutationRepresentation 4 n σ * (permutationRepresentation 4 n σ)ᴴ = 1 :=
      (permutationRepresentation_unitary 4 n σ).2
    rw [hMdef]
    calc permutationRepresentation 4 n σ * (W * ρ * Wᴴ) * (permutationRepresentation 4 n σ)ᴴ
        = (permutationRepresentation 4 n σ * W) * ρ * (Wᴴ * (permutationRepresentation 4 n σ)ᴴ) :=
            by
          noncomm_ring
      _ = (W * permutationRepresentation 4 n σ) * ρ * ((permutationRepresentation 4 n σ)ᴴ * Wᴴ) :=
          by
          rw [c1, c2]
      _ = W * (permutationRepresentation 4 n σ * ρ) * (permutationRepresentation 4 n σ)ᴴ * Wᴴ := by
          noncomm_ring
      _ = W * (ρ * permutationRepresentation 4 n σ) * (permutationRepresentation 4 n σ)ᴴ * Wᴴ := by
          rw [hρ_perm σ]
      _ = W * ρ * (permutationRepresentation 4 n σ * (permutationRepresentation 4 n σ)ᴴ) * Wᴴ := by
          noncomm_ring
      _ = W * ρ * Wᴴ := by rw [huu, Matrix.mul_one]
  have horb : ∀ σ : Equiv.Perm (Fin n),
      M i i = M (e (e.symm i ∘ σ)) (e (e.symm i ∘ σ)) := by
    intro σ
    have hp := permRep_conj_entry σ M i i
    rw [hMinv σ] at hp
    exact hp
  classical
  set pidx : Equiv.Perm (Fin n) → Fin (4 ^ n) := fun σ => e (e.symm i ∘ σ) with hpidx
  set cnt : Fin (4 ^ n) → ℕ :=
    fun k => (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => pidx σ = k)).card with hcnt
  have hcoset : ∀ k, cnt k ≤ cnt i := by
    intro k
    rcases Finset.eq_empty_or_nonempty
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => pidx σ = k)) with hemp | hne
    · simp only [hcnt, hemp, Finset.card_empty]; exact Nat.zero_le _
    · obtain ⟨τ, hτ⟩ := hne
      rw [Finset.mem_filter] at hτ
      simp only [hcnt]
      apply Finset.card_le_card_of_injOn (fun σ => σ * τ⁻¹)
      · intro σ hσ
        rw [Finset.mem_coe, Finset.mem_filter] at hσ
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hcomp : e.symm i ∘ ⇑σ = e.symm i ∘ ⇑τ := by
          have h1 : pidx σ = pidx τ := hσ.2.trans hτ.2.symm
          simp only [hpidx] at h1
          exact e.injective h1
        change pidx (σ * τ⁻¹) = i
        simp only [hpidx]
        have hfix : e.symm i ∘ ⇑(σ * τ⁻¹) = e.symm i := by
          funext a
          simp only [Function.comp_apply, Equiv.Perm.coe_mul, Equiv.Perm.inv_def]
          have h2 := congr_fun hcomp (τ.symm a)
          simp only [Function.comp_apply, Equiv.apply_symm_apply] at h2
          exact h2
        rw [hfix, Equiv.apply_symm_apply]
      · intro a _ b _ hab
        exact mul_right_cancel hab
  have hMsum : (∑ σ : Equiv.Perm (Fin n), M (pidx σ) (pidx σ)) = ∑ k, cnt k • M k k := by
    have hexp : ∀ σ : Equiv.Perm (Fin n),
        M (pidx σ) (pidx σ) = ∑ k, (if pidx σ = k then M k k else 0) := by
      intro σ
      rw [Finset.sum_ite_eq Finset.univ (pidx σ) (fun k => M k k), if_pos (Finset.mem_univ _)]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_filter, Finset.sum_const]
  have hMii : (Nat.factorial n) • M i i = ∑ k, cnt k • M k k := by
    rw [← hMsum,
      show (∑ σ : Equiv.Perm (Fin n), M (pidx σ) (pidx σ))
          = ∑ _σ : Equiv.Perm (Fin n), M i i from
        Finset.sum_congr rfl (fun σ _ => (horb σ).symm),
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hbound : (∑ k, cnt k • M k k) ≤ (cnt i) • (1 : ℂ) := by
    calc (∑ k, cnt k • M k k) ≤ ∑ k, cnt i • M k k :=
          Finset.sum_le_sum (fun k _ => nsmul_le_nsmul_left hMpsd.diag_nonneg (hcoset k))
      _ = cnt i • ∑ k, M k k := by rw [← Finset.smul_sum]
      _ = cnt i • M.trace := rfl
      _ = cnt i • (1 : ℂ) := by rw [hMtr]
  have hPii : (Nat.factorial n) • symmetricProjector 4 n i i = (cnt i : ℂ) := by
    rw [nsmul_eq_mul]
    simp only [symmetricProjector, symmetricProjectorRep, Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul]
    simp only [Finset.mul_sum]
    have hbridge : ∀ σ : Equiv.Perm (Fin n),
        (Nat.factorial n : ℂ) * (1 / Nat.factorial n * permutationRepresentation 4 n σ i i)
          = (if pidx σ⁻¹ = i then (1 : ℂ) else 0) := by
      intro σ
      rw [← mul_assoc, mul_one_div, div_self (by exact_mod_cast (Nat.factorial_pos n).ne'), one_mul]
      simp only [permutationRepresentation, Matrix.of_apply, ← hedef]
      have hiff : (e.symm i = e.symm i ∘ ⇑σ.symm) ↔ (pidx σ⁻¹ = i) := by
        simp only [hpidx, Equiv.Perm.inv_def]
        constructor
        · intro h; rw [← h]; exact Equiv.apply_symm_apply e i
        · intro h
          exact (e.injective (h.trans (Equiv.apply_symm_apply e i).symm)).symm
      simp only [hiff]
    rw [Finset.sum_congr rfl (fun σ _ => hbridge σ)]
    rw [Fintype.sum_bijective (fun σ : Equiv.Perm (Fin n) => σ⁻¹) inv_involutive.bijective
        (fun σ => if pidx σ⁻¹ = i then (1 : ℂ) else 0)
        (fun σ => if pidx σ = i then (1 : ℂ) else 0) (fun σ => rfl)]
    rw [Finset.sum_boole]
  have hcmp : (Nat.factorial n) • M i i ≤ (Nat.factorial n) • symmetricProjector 4 n i i := by
    rw [hMii, hPii]
    calc (∑ k, cnt k • M k k) ≤ (cnt i) • (1 : ℂ) := hbound
      _ = (cnt i : ℂ) := by rw [nsmul_eq_mul, mul_one]
  rw [nsmul_eq_mul, nsmul_eq_mul] at hcmp
  exact le_of_mul_le_mul_left hcmp (by exact_mod_cast Nat.factorial_pos n)

/-- **the Bell de Finetti domination** (Nahar et al. Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂`
symmetry).

For a permutation-invariant, jointly-Bell-diagonal density `ρ` on `(ℂ⁴)^{⊗n}`,
`ρ ≤ C(n+3,3) · τ_Bell` in the Löwner order. Both sides are diagonal in the joint Bell basis, so the
inequality collapses to the per-type scalar bound `λ_T ≤ 1/multinomial(T) = C(n+3,3)·τ_T`, which is
just `Σ_T multinomial(T)·λ_T = Tr ρ = 1` together with nonnegativity (the `1`-dimensional Bell
blocks make the Schur–Weyl machinery unnecessary). -/
theorem bb84_bellSym_deFinetti_domination {n : ℕ} [NeZero n] (ρ : Op (4 ^ n))
    (hρ_psd : ρ.PosSemidef) (hρ_trace : ρ.trace = 1)
    (hρ_perm : ∀ σ : Equiv.Perm (Fin n),
      permutationRepresentation 4 n σ * ρ = ρ * permutationRepresentation 4 n σ)
    (hρ_bell : IsIIDBellDiagonal ρ) :
    ρ ≤ (Nat.choose (n + 3) 3 : ℂ) • (bb84BellDeFinettiState n).toOp := by
  rw [deFinetti_smul_eq, Matrix.le_iff, ← posSemidef_conj_iff n]
  have hdiff : bellRotation n * (bb84BellTwirl n (symmetricProjector 4 n) - ρ) * (bellRotation n)ᴴ
      = Matrix.diagonal (fun i => symmetricProjector 4 n i i -
          (bellRotation n * ρ * (bellRotation n)ᴴ) i i) := by
    conv_lhs => rw [Matrix.mul_sub, Matrix.sub_mul, twirl_symProj_diag, rho_conj_diag n ρ hρ_bell]
    rw [← Matrix.diagonal_sub]
  rw [hdiff, Matrix.posSemidef_diagonal_iff]
  intro i
  rw [sub_nonneg]
  exact domination_per_index n ρ hρ_psd hρ_trace hρ_perm i

/-!
## The Bell-doubling isometry `W`

The fixed isometry `W : ℂ⁴ → ℂ¹⁶` sending each Bell ket `|β_c⟩ ↦ |β_c⟩ ⊗ |β_c⟩`, used to present the
Bell de Finetti reference as a Haar IID integral (the `(n+1)^{15} → (n+1)^{3}` postselection
collapse,
Nahar et al. Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry).  `W = (Vᴴ ⊗ Vᴴ) · COPY · V`, `V =
bellSinglePairRotation`, `COPY|c⟩ = |c⟩⊗|c⟩`.
-/

/-- The single-round `n = 1` Bell rotation is the single-pair Bell rotation `V`. -/
private theorem bellRotation_one : bellRotation 1 = bellSinglePairRotation := by
  rw [bellRotation, tensorFamily_fin_one]
  rfl

/-- `partialTraceB` is invariant under conjugating the traced (right) factor by an isometry
`Op.tensor 1 A` / `Op.tensor 1 B` with `B * A = 1`. -/
private theorem partialTraceB_one_tensor_conj {n m : ℕ} (A B : Op m) (M : Op (n * m))
    (hBA : B * A = 1) :
    partialTraceB (Op.tensor (1 : Op n) A * M * Op.tensor (1 : Op n) B) = partialTraceB M := by
  ext i j
  simp only [partialTraceB, Matrix.of_apply]
  simp_rw [one_tensor_mul_mul_one_tensor_apply]
  calc
    (∑ k : Fin m, ∑ a : Fin m, ∑ c : Fin m,
        A k a * M (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c)) * B c k)
        = ∑ a : Fin m, ∑ c : Fin m,
            (∑ k : Fin m, B c k * A k a) *
              M (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
    _ = ∑ a : Fin m, ∑ c : Fin m,
          (B * A) c a * M (finProdFinEquiv (i, a)) (finProdFinEquiv (j, c)) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Matrix.mul_apply]
    _ = ∑ a : Fin m, M (finProdFinEquiv (i, a)) (finProdFinEquiv (j, a)) := by
          rw [hBA]
          simp only [Matrix.one_apply]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_eq_single a]
          · simp
          · intro c _ hc; simp [hc]
          · intro h; exact (h (Finset.mem_univ a)).elim

/-- **The computational-doubling isometry** `COPY|c⟩ = |c⟩ ⊗ |c⟩`, the fixed `0/1` matrix
`COPY = ∑_c (e_c ⊗ e_c) e_cᵀ` (`Op.tensor` index convention `finProdFinEquiv`).  Explicit; no
`Classical.choose`. -/
noncomputable def bellDoublingCopy : Matrix (Fin (4 * 4)) (Fin 4) ℂ :=
  Matrix.of fun I j => if I = finProdFinEquiv (j, j) then (1 : ℂ) else 0

/-- **The Bell-doubling isometry** `W = (Vᴴ ⊗ Vᴴ) · COPY · V`, `V = bellSinglePairRotation`: a
`16×4`
matrix with `W|β_c⟩ = |β_c⟩ ⊗ |β_c⟩`.  Explicit; no `Classical.choose`. -/
noncomputable def bellDoublingIsometry : Matrix (Fin (4 * 4)) (Fin 4) ℂ :=
  Op.tensor (bellSinglePairRotation)ᴴ (bellSinglePairRotation)ᴴ
    * bellDoublingCopy * bellSinglePairRotation

/-- `Cᴴ · C = 𝟙₄`: the doubling matrix is a (left) isometry. -/
private theorem bellDoublingCopy_conjTranspose_mul :
    (bellDoublingCopy)ᴴ * bellDoublingCopy = (1 : Op 4) := by
  ext j j'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstar : ∀ I : Fin (4 * 4),
      (bellDoublingCopy)ᴴ j I * bellDoublingCopy I j'
        = (if I = finProdFinEquiv (j, j) then (1 : ℂ) else 0)
            * (if I = finProdFinEquiv (j', j') then (1 : ℂ) else 0) := by
    intro I
    simp only [Matrix.conjTranspose_apply, bellDoublingCopy, Matrix.of_apply]
    rw [show (star (if I = finProdFinEquiv (j, j) then (1 : ℂ) else 0))
          = (if I = finProdFinEquiv (j, j) then (1 : ℂ) else 0) from by split <;> simp]
  simp_rw [hstar]
  rw [Finset.sum_eq_single (finProdFinEquiv (j, j))]
  · rw [if_pos rfl, one_mul]
    by_cases hjj : j = j'
    · subst hjj; simp
    · rw [if_neg (fun h => hjj (congrArg Prod.fst (finProdFinEquiv.injective h))), if_neg hjj]
  · intro I _ hI; rw [if_neg hI, zero_mul]
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- `(Vᴴ)_{i c} = (β_c).vec i`. -/
private theorem bellSPR_conjTranspose_apply (i c : Fin 4) :
    (bellSinglePairRotation)ᴴ i c = (bellKet c).vec i := by
  simp only [Matrix.conjTranspose_apply, bellSinglePairRotation, Matrix.of_apply,
    starRingEnd_apply, star_star]

/-- **`W` is an isometry**: `Wᴴ · W = 𝟙₄`. -/
theorem bellDoublingIsometry_isometry :
    (bellDoublingIsometry)ᴴ * bellDoublingIsometry = (1 : Op 4) := by
  have hVV : (bellSinglePairRotation)ᴴ * bellSinglePairRotation = 1 := bellSPR_unitary
  have hVV' : bellSinglePairRotation * (bellSinglePairRotation)ᴴ = 1 :=
    mul_eq_one_comm.mpr hVV
  have htVV : Op.tensor bellSinglePairRotation bellSinglePairRotation
      * Op.tensor (bellSinglePairRotation)ᴴ (bellSinglePairRotation)ᴴ = 1 := by
    rw [Op.tensor_mul, hVV', Op.tensor_one]
  unfold bellDoublingIsometry
  simp only [Matrix.conjTranspose_mul, Op.tensor_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Op.tensor bellSinglePairRotation bellSinglePairRotation)
      (Op.tensor (bellSinglePairRotation)ᴴ (bellSinglePairRotation)ᴴ), htVV, Matrix.one_mul,
    ← Matrix.mul_assoc (bellDoublingCopy)ᴴ bellDoublingCopy,
    bellDoublingCopy_conjTranspose_mul, Matrix.one_mul, hVV]

/-- **Bell-doubling**: `W|β_c⟩ = |β_c⟩ ⊗ |β_c⟩`. -/
theorem bellDoublingIsometry_bellDouble (c : Fin 4) :
    bellDoublingIsometry *ᵥ (bellKet c).vec = (Ket.tensor (bellKet c) (bellKet c)).vec := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  -- V *ᵥ |β_c⟩ = e_c (Bell orthonormality)
  have hV : bellSinglePairRotation *ᵥ (bellKet c).vec = (fun i => if i = c then (1 : ℂ) else 0) :=
      by
    funext i
    have hortho := bellStates_orthonormal i c
    simp only at hortho
    rw [Matrix.mulVec, dotProduct]
    have : bellKet = ![bellState00, bellState01, bellState10, bellState11] := rfl
    calc (∑ j, bellSinglePairRotation i j * (bellKet c).vec j)
        = ((bellKet i).dag * (bellKet c) : ℂ) := by
          rw [bra_mul_ket_eq]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Ket.dag_vec]
          simp only [bellSinglePairRotation, Matrix.of_apply, starRingEnd_apply]
      _ = if i = c then (1 : ℂ) else 0 := hortho
  -- C *ᵥ e_c = e_{(c,c)}
  have hC : bellDoublingCopy *ᵥ (fun i => if i = c then (1 : ℂ) else 0)
      = (fun I => if I = finProdFinEquiv (c, c) then (1 : ℂ) else 0) := by
    funext I
    rw [Matrix.mulVec, dotProduct]
    simp only [bellDoublingCopy, Matrix.of_apply]
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [show bellDoublingIsometry *ᵥ (bellKet c).vec
        = Op.tensor (bellSinglePairRotation)ᴴ (bellSinglePairRotation)ᴴ *ᵥ
            (bellDoublingCopy *ᵥ (bellSinglePairRotation *ᵥ (bellKet c).vec)) by
      unfold bellDoublingIsometry
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec], hV, hC]
  funext I
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (finProdFinEquiv (c, c))]
  · rw [if_pos rfl, mul_one, Op_tensor_apply_finProd, Ket.tensor_vec]
    simp only [Equiv.symm_apply_apply, bellSPR_conjTranspose_apply]
  · intro J _ hJ; rw [if_neg hJ, mul_zero]
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- Closed form of the `COPY`-sandwich entry:
`(COPY · σ · COPYᴴ)_{I,J} = Σ_{a,b} [I = (a,a)] σ_{a,b} [J = (b,b)]`. -/
private theorem bellDoublingCopy_sandwich_apply (σ : Op 4) (I J : Fin (4 * 4)) :
    (bellDoublingCopy * σ * (bellDoublingCopy)ᴴ) I J
      = ∑ a : Fin 4, ∑ b : Fin 4,
          (if I = finProdFinEquiv (a, a) then (1 : ℂ) else 0) * σ a b
            * (if J = finProdFinEquiv (b, b) then (1 : ℂ) else 0) := by
  rw [Matrix.mul_apply]
  have hstar : ∀ b : Fin 4,
      (bellDoublingCopy)ᴴ b J = (if J = finProdFinEquiv (b, b) then (1 : ℂ) else 0) := by
    intro b
    simp only [Matrix.conjTranspose_apply, bellDoublingCopy, Matrix.of_apply]
    split <;> simp
  simp_rw [hstar, Matrix.mul_apply, bellDoublingCopy, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The `COPY`-sandwich partial trace picks the Bell-basis diagonal:
`partialTraceB (COPY · σ · COPYᴴ) = diag (fun c ↦ σ c c)`. -/
private theorem bellDoublingCopy_sandwich_partialTraceB (σ : Op 4) :
    partialTraceB (bellDoublingCopy * σ * (bellDoublingCopy)ᴴ)
      = Matrix.diagonal (fun c => σ c c) := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  ext i j
  rw [partialTraceB, Matrix.of_apply, Matrix.diagonal_apply]
  simp_rw [bellDoublingCopy_sandwich_apply]
  -- collapse the `a` and `b` sums against the indicators (only `a = i = k`, `b = j = k`)
  have hia : ∀ k a : Fin 4,
      (if finProdFinEquiv (i, k) = finProdFinEquiv (a, a) then (1 : ℂ) else 0)
        = (if a = i ∧ a = k then (1 : ℂ) else 0) := by
    intro k a
    refine if_congr ?_ rfl rfl
    rw [finProdFinEquiv.apply_eq_iff_eq, Prod.mk.injEq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  have hjb : ∀ k b : Fin 4,
      (if finProdFinEquiv (j, k) = finProdFinEquiv (b, b) then (1 : ℂ) else 0)
        = (if b = j ∧ b = k then (1 : ℂ) else 0) := by
    intro k b
    refine if_congr ?_ rfl rfl
    rw [finProdFinEquiv.apply_eq_iff_eq, Prod.mk.injEq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  simp_rw [hia, hjb]
  -- now Σ_k Σ_a Σ_b [a=i∧a=k] σ_{a,b} [b=j∧b=k]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · intro a _ ha; rw [Finset.sum_eq_zero]; intro b _; simp [ha]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intro k _ hk
      rw [Finset.sum_eq_zero]; intro a _; rw [Finset.sum_eq_zero]; intro b _
      have hne : ¬ (a = i ∧ a = k) := fun h => hk (h.1 ▸ h.2).symm
      simp [hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · rw [if_neg hij, Finset.sum_eq_zero]
    intro k _
    rw [Finset.sum_eq_zero]; intro a _; rw [Finset.sum_eq_zero]; intro b _
    by_cases ha : a = i ∧ a = k
    · by_cases hb : b = j ∧ b = k
      · exact absurd (ha.1.symm.trans (ha.2.trans (hb.2.symm.trans hb.1))) hij
      · simp [hb]
    · simp [ha]

/-- **marginal is the single-round Bell twirl**:
`partialTraceB (W · ρ · Wᴴ) = bb84BellTwirl 1 ρ`. -/
theorem bellDoublingIsometry_partialTraceB (ρ : Op 4) :
    partialTraceB (bellDoublingIsometry * ρ * (bellDoublingIsometry)ᴴ) = bb84BellTwirl 1 ρ := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  set V := bellSinglePairRotation with hVdef
  have hVV : Vᴴ * V = 1 := bellSPR_unitary
  have hVV' : V * Vᴴ = 1 := mul_eq_one_comm.mpr hVV
  have ht1 : Op.tensor Vᴴ (1 : Op 4) * Op.tensor (1 : Op 4) Vᴴ = Op.tensor Vᴴ Vᴴ := by
    rw [Op.tensor_mul, Matrix.mul_one, Matrix.one_mul]
  have ht2 : Op.tensor (1 : Op 4) V * Op.tensor V (1 : Op 4) = Op.tensor V V := by
    rw [Op.tensor_mul, Matrix.one_mul, Matrix.mul_one]
  -- factor W ρ Wᴴ into the form `(Vᴴ ⊗ 1)·(1 ⊗ Vᴴ)·(C σ Cᴴ)·(1 ⊗ V)·(V ⊗ 1)`
  have hfac : bellDoublingIsometry * ρ * (bellDoublingIsometry)ᴴ
      = Op.tensor Vᴴ (1 : Op 4) *
          (Op.tensor (1 : Op 4) Vᴴ * (bellDoublingCopy * (V * ρ * Vᴴ) * (bellDoublingCopy)ᴴ)
            * Op.tensor (1 : Op 4) V) *
          Op.tensor V (1 : Op 4) := by
    unfold bellDoublingIsometry
    simp only [Matrix.conjTranspose_mul, Op.tensor_conjTranspose,
      Matrix.conjTranspose_conjTranspose, ← hVdef]
    rw [← ht1, ← ht2]
    simp only [Matrix.mul_assoc]
  -- the single-round twirl as a Bell-basis dephasing of ρ
  have hdiag : V * bb84BellTwirl 1 ρ * Vᴴ = Matrix.diagonal (fun c => (V * ρ * Vᴴ) c c) := by
    ext i j
    have hcd := bellTwirl_conj_diag 1 ρ i j
    rw [bellRotation_one, ← hVdef] at hcd
    rw [hcd, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
  have hTwirl : bb84BellTwirl 1 ρ = Vᴴ * Matrix.diagonal (fun c => (V * ρ * Vᴴ) c c) * V := by
    rw [← hdiag,
      show Vᴴ * (V * bb84BellTwirl 1 ρ * Vᴴ) * V
          = (Vᴴ * V) * bb84BellTwirl 1 ρ * (Vᴴ * V) from by noncomm_ring,
      hVV, Matrix.one_mul, Matrix.mul_one]
  rw [hfac, partialTraceB_sandwich_tensor_one,
    partialTraceB_one_tensor_conj Vᴴ V _ hVV',
    bellDoublingCopy_sandwich_partialTraceB, hTwirl]

/-! ### decl M — the single-round twirl factorization of a tensor power -/

/-- Per-string IID twirl conjugation distributes over a tensor power:
`U_g · M^{⊗n} · U_gᴴ = ⊗_a (G(g a) · M · G(g a)ᴴ)`. -/
private theorem bellTwirlUnitary_conj_tensorPow {n : ℕ} (g : Fin n → Fin 4) (M : Op 4) :
    bellTwirlUnitary n g * Op.tensorPow M n * (bellTwirlUnitary n g)ᴴ
      = tensorFamily fun a => bb84BellSinglePairTwirlGroup (g a) * M *
          (bb84BellSinglePairTwirlGroup (g a))ᴴ := by
  simp only [bellTwirlUnitary, Op.tensorPow_eq_tensorFamily, conjTranspose_tensorFamily,
    tensorFamily_mul]

/-- The single-round Bell twirl is the bilateral-Pauli average `4⁻¹ • Σ_k G_k M G_kᴴ`. -/
private theorem bb84BellTwirl_one_eq (M : Op 4) :
    bb84BellTwirl 1 M
      = (4 : ℂ)⁻¹ • ∑ k : Fin 4,
          bb84BellSinglePairTwirlGroup k * M * (bb84BellSinglePairTwirlGroup k)ᴴ := by
  have hbu : ∀ g : Fin 1 → Fin 4,
      bellTwirlUnitary 1 g = bb84BellSinglePairTwirlGroup (g 0) := by
    intro g; rw [bellTwirlUnitary, tensorFamily_fin_one]; rfl
  have hsum : (∑ g : Fin 1 → Fin 4,
        bellTwirlUnitary 1 g * M * (bellTwirlUnitary 1 g)ᴴ)
      = ∑ k : Fin 4,
          bb84BellSinglePairTwirlGroup k * M * (bb84BellSinglePairTwirlGroup k)ᴴ := by
    rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin 4)).symm
      (fun g => bellTwirlUnitary 1 g * M * (bellTwirlUnitary 1 g)ᴴ)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hbu]
    simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  unfold bb84BellTwirl
  rw [show (4 ^ 1 : ℂ)⁻¹ = (4 : ℂ)⁻¹ from by norm_num, hsum]

/-- **decl M — single-round twirl factorization of a tensor power**:
`bb84BellTwirl n (M^{⊗n}) = (bb84BellTwirl 1 M)^{⊗n}`. -/
theorem bb84BellTwirl_tensorPow (n : ℕ) (M : Op 4) :
    bb84BellTwirl n (Op.tensorPow M n) = Op.tensorPow (bb84BellTwirl 1 M) n := by
  -- RHS: the tensor power of the single-site average is the average over twirl strings
  rw [Op.tensorPow_eq_tensorFamily (bb84BellTwirl 1 M), bb84BellTwirl_one_eq,
    tensorFamily_const_smul, inv_pow, tensorFamily_sum]
  -- LHS: distribute the IID twirl group over the tensor power
  unfold bb84BellTwirl
  simp_rw [bellTwirlUnitary_conj_tensorPow]

end Quantum.Symmetry
