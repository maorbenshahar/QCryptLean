import QCryptLean.Quantum.Bases.MutuallyUnbiased
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# The `n`-qubit Walsh–Hadamard basis

The `n`-fold Hadamard (conjugate, BB84 `X`-) basis of `ℂ^{2ⁿ}` is the concrete witness for the
flat/mutually-unbiased abstraction `Quantum.Bases.IsMutuallyUnbiased`.
Indexing both the coordinates and the basis by `n`-bit strings through the binary-digit
equivalence `bitIndex : Fin (2ⁿ) ≃ (Fin n → Bool)`, the basis kets are

  `|e⟩_H := 2^{-n/2} ∑_w (-1)^{⟨w, e⟩} |w⟩`,   `⟨w, e⟩ = #{i : wᵢ ∧ eᵢ}`,

so every coordinate has modulus `2^{-n/2}` — exactly flatness against the computational basis.

Everything rests on one identity, the **Walsh character sum** (orthogonality of the characters
of `(ℤ/2)ⁿ`):

  `∑_{x} (-1)^{⟨y,x⟩ + ⟨z,x⟩} = 2ⁿ · [y = z]`.

Writing the sign as a *product over coordinates* makes this a product of independent two-term
sums (`Fintype.prod_sum`), each equal to `2` or `0` — one line of algebra per coordinate instead
of an induction on the bit length.

From the character sum the basis is simultaneously shown to be orthonormal, complete, and flat
against the computational basis; combining flatness with the support bound of
`IsMutuallyUnbiased` gives the Bouman–Fehr uncertainty estimate for states with small
Walsh-basis support.  Because the Walsh index type is literally `Fin n → Bool`, a support set is
a `Finset (Fin n → Bool)` and Hamming-ball counting applies to it verbatim.

## Main definitions

* `Quantum.Bases.bitIndex` — the binary-digit equivalence `Fin (2ⁿ) ≃ (Fin n → Bool)`.
* `Quantum.Bases.walshSign` — the character `(-1)^{⟨x,y⟩}`, as a product over coordinates.
* `Quantum.Bases.walshKet` — the Walsh–Hadamard basis ket indexed by a bit string.

## Main statements

* `Quantum.Bases.sum_walshSign_mul` — the Walsh character sum.
* `Quantum.Bases.walshKet_orthonormal` — `⟨e|f⟩_H = δ_{e,f}`.
* `Quantum.Bases.walshKet_complete` — `∑_e |e⟩_H⟨e|_H = 1`.
* `Quantum.Bases.stdKet_walshKet_mutuallyUnbiased` — **flatness**: the computational and
  Walsh–Hadamard bases of `ℂ^{2ⁿ}` are mutually unbiased.
-/

open Quantum.Operators
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Quantum.Bases

variable {n : ℕ}

/-! ## Bit-string coordinates -/

/-- **Binary-digit coordinates.**  The explicit (choice-free) equivalence
`Fin (2ⁿ) ≃ (Fin n → Bool)` sending an index to its `n` binary digits.  It is the composition of
Mathlib's base-`2` digit expansion `finFunctionFinEquiv` with `Fin 2 ≃ Bool`. -/
def bitIndex (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Bool) :=
  finFunctionFinEquiv.symm.trans (Equiv.piCongrRight fun _ => finTwoEquiv)

/-! ## The Walsh character -/

/-- **The Walsh character** `(-1)^{⟨x, y⟩}` of the group `(ℤ/2)ⁿ`, where `⟨x, y⟩` is the number of
coordinates on which `x` and `y` are both `true`.  It is written as a product over coordinates,
which is what makes the orthogonality relation a coordinatewise computation. -/
def walshSign (x y : Fin n → Bool) : ℂ :=
  ∏ i, if x i && y i then (-1 : ℂ) else 1

/-- The Walsh character is symmetric: `(-1)^{⟨x,y⟩} = (-1)^{⟨y,x⟩}`. -/
lemma walshSign_comm (x y : Fin n → Bool) : walshSign x y = walshSign y x := by
  unfold walshSign
  exact Finset.prod_congr rfl fun i _ => by rw [Bool.and_comm]

/-- The Walsh character is real: it is a product of `±1`. -/
@[simp] lemma conj_walshSign (x y : Fin n → Bool) : conj (walshSign x y) = walshSign x y := by
  unfold walshSign
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => by split <;> simp

/-- The Walsh character has unit modulus. -/
@[simp] lemma normSq_walshSign (x y : Fin n → Bool) : Complex.normSq (walshSign x y) = 1 := by
  unfold walshSign
  rw [map_prod]
  exact Finset.prod_eq_one fun i _ => by split <;> simp

/-- The Walsh character is `(-1)^{|{i : xᵢ ∧ yᵢ}|}`: the product form is the usual sign of the
bitwise inner product. -/
lemma walshSign_eq_neg_one_pow (x y : Fin n → Bool) :
    walshSign x y = (-1 : ℂ) ^ (Finset.univ.filter fun i => x i && y i).card := by
  unfold walshSign
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-! ## The Walsh character sum (orthogonality) -/

/-- **Walsh orthogonality.**  Summing the product of two Walsh characters over all bit strings
gives `2ⁿ` when the characters agree and `0` otherwise:

  `∑_{x} (-1)^{⟨y,x⟩} (-1)^{⟨z,x⟩} = 2ⁿ · [y = z]`.

Because the character is a product over coordinates, the sum factors into `n` independent
two-term sums `1 + (-1)^{y_i}(-1)^{z_i}`, each equal to `2` when `y_i = z_i` and to `0`
otherwise. -/
theorem sum_walshSign_mul (y z : Fin n → Bool) :
    (∑ x : Fin n → Bool, walshSign y x * walshSign z x) = if y = z then (2 : ℂ) ^ n else 0 := by
  classical
  -- Write the summand as a product over coordinates and exchange product and sum.
  have hterm : ∀ x : Fin n → Bool, walshSign y x * walshSign z x =
      ∏ i, ((if y i && x i then (-1 : ℂ) else 1) * (if z i && x i then (-1 : ℂ) else 1)) := by
    intro x
    unfold walshSign
    rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  rw [← Fintype.prod_sum
    (f := fun (i : Fin n) (bi : Bool) =>
      (if y i && bi then (-1 : ℂ) else 1) * (if z i && bi then (-1 : ℂ) else 1))]
  -- Each coordinate contributes `2` if the two bits agree and `0` otherwise.
  have hcoord : ∀ i : Fin n,
      (∑ bi : Bool, (if y i && bi then (-1 : ℂ) else 1) * (if z i && bi then (-1 : ℂ) else 1)) =
        if y i = z i then (2 : ℂ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases hy : y i <;> cases hz : z i <;> norm_num
  rw [Finset.prod_congr rfl fun i _ => hcoord i]
  by_cases h : y = z
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ z i := by
      by_contra hcon
      exact h (funext fun i => not_not.mp (fun hne => hcon ⟨i, hne⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-! ## The Walsh–Hadamard basis -/

/-- The normalization `√(2ⁿ)` is nonzero. -/
lemma walsh_sqrt_ne_zero (n : ℕ) : ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]
  exact Real.sqrt_ne_zero'.mpr (by positivity)

/-- The normalization squares to `2ⁿ`. -/
lemma walsh_sqrt_mul_self (n : ℕ) :
    ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) * ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) = (2 : ℂ) ^ n := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-- **The Walsh–Hadamard basis ket** `|e⟩_H = 2^{-n/2} ∑_w (-1)^{⟨w,e⟩} |w⟩` of `ℂ^{2ⁿ}`,
indexed by the bit string `e`.  Physically this is the `n`-qubit BB84 `X`-basis state. -/
def walshKet (e : Fin n → Bool) : Ket (2 ^ n) :=
  ⟨fun w => walshSign (bitIndex n w) e / ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ)⟩

@[simp] lemma walshKet_vec (e : Fin n → Bool) (w : Fin (2 ^ n)) :
    (walshKet e).vec w = walshSign (bitIndex n w) e / ((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) := rfl

/-- The Walsh character sum transported to the coordinate index `Fin (2ⁿ)`. -/
lemma sum_walshSign_bitIndex_mul (y z : Fin n → Bool) :
    (∑ w : Fin (2 ^ n), walshSign (bitIndex n w) y * walshSign (bitIndex n w) z) =
      if y = z then (2 : ℂ) ^ n else 0 := by
  rw [Equiv.sum_comp (bitIndex n) fun x => walshSign x y * walshSign x z]
  rw [Finset.sum_congr rfl fun x _ => by rw [walshSign_comm x y, walshSign_comm x z]]
  exact sum_walshSign_mul y z

/-- **Orthonormality of the Walsh–Hadamard basis:** `⟨e|f⟩_H = δ_{e,f}`. -/
theorem walshKet_orthonormal (e f : Fin n → Bool) :
    ((walshKet e).dag * walshKet f : ℂ) = if e = f then 1 else 0 := by
  classical
  have hne := walsh_sqrt_ne_zero n
  rw [bra_mul_ket_eq]
  have hterm : ∀ w : Fin (2 ^ n),
      (walshKet e).dag.vec w * (walshKet f).vec w =
        walshSign (bitIndex n w) e * walshSign (bitIndex n w) f * ((2 : ℂ) ^ n)⁻¹ := by
    intro w
    simp only [Ket.dag_vec, walshKet_vec, map_div₀, conj_walshSign, Complex.conj_ofReal]
    rw [div_mul_div_comm, walsh_sqrt_mul_self, div_eq_mul_inv]
  rw [Finset.sum_congr rfl fun w _ => hterm w, ← Finset.sum_mul,
    sum_walshSign_bitIndex_mul e f]
  have h2n : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  by_cases h : e = f
  · rw [if_pos h, if_pos h, mul_inv_cancel₀ h2n]
  · rw [if_neg h, if_neg h, zero_mul]

/-- **Completeness of the Walsh–Hadamard basis:** `∑_e |e⟩_H⟨e|_H = 1` on `ℂ^{2ⁿ}`. -/
theorem walshKet_complete :
    (∑ e : Fin n → Bool, walshKet e * (walshKet e).dag) = (1 : Op (2 ^ n)) := by
  classical
  have hne := walsh_sqrt_ne_zero n
  have h2n : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  ext i j
  rw [Matrix.sum_apply]
  have hterm : ∀ e : Fin n → Bool,
      (walshKet e * (walshKet e).dag) i j =
        walshSign (bitIndex n i) e * walshSign (bitIndex n j) e * ((2 : ℂ) ^ n)⁻¹ := by
    intro e
    rw [ket_mul_bra_apply]
    simp only [Ket.dag_vec, walshKet_vec, map_div₀, conj_walshSign, Complex.conj_ofReal]
    rw [div_mul_div_comm, walsh_sqrt_mul_self, div_eq_mul_inv]
  rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.sum_mul,
    sum_walshSign_mul (bitIndex n i) (bitIndex n j), Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos (congrArg (bitIndex n) h), mul_inv_cancel₀ h2n]
  · rw [if_neg h, if_neg fun hb => h ((bitIndex n).injective hb), zero_mul]

/-! ## Flatness against the computational basis -/

/-- **The computational and Walsh–Hadamard bases of `ℂ^{2ⁿ}` are mutually unbiased.**

Every overlap `⟨w | e⟩_H` has squared modulus `1/2ⁿ`, since the Walsh character has unit modulus
and the normalization is `2^{-n/2}`.  This is the concrete witness making the flat-basis support
and surprisal bounds of `QCryptLean.Quantum.Bases.MutuallyUnbiased` non-vacuous, and it
is the mutual unbiasedness of the BB84 `Z`- and `X`-bases for `n` qubits. -/
theorem stdKet_walshKet_mutuallyUnbiased (n : ℕ) :
    IsMutuallyUnbiased (stdKet (2 ^ n)) (walshKet (n := n)) := by
  intro w e
  rw [stdKet_dag_mul, walshKet_vec, Complex.normSq_div, normSq_walshSign,
    Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

end Quantum.Bases

end
