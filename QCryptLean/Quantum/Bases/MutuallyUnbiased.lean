import QCryptLean.Quantum.Operators.BraKet.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Flat (mutually unbiased) families of kets and the support–overlap bound

Two families of kets on the same `d`-dimensional space are **mutually unbiased**, or *flat*
relative to each other, when every overlap has squared modulus exactly `1/d`.  The computational
and Walsh–Hadamard bases of `ℂ^{2ⁿ}` are the standard example
(`QCryptLean.Quantum.Bases.WalshHadamard`).

The point of flatness is an *uncertainty* statement: a state whose expansion in one of the two
families is carried by only `|J|` indices cannot concentrate probability in the other family.
Concretely, for `ψ = ∑_{e ∈ J} α_e |b_e⟩` with `∑_{e ∈ J} ‖α_e‖² = 1`,

  `‖⟨a_w | ψ⟩‖² ≤ |J| / d`   for every `w`,

so every outcome of the `a`-measurement carries at least `log₂(d/|J|)` bits of surprisal.  This is
the analytic ingredient of Bouman–Fehr's Corollary 1
([arXiv:0907.4246v5](https://arxiv.org/abs/0907.4246)), where `a` is the computational basis, `b`
is the Hadamard basis, and `J` is a Hamming ball.

**Scope warning.** The bounds here are *unconditional*: they bound the outcome probability of the
state `ψ` alone and say nothing about an adversary holding a purifying register `E`.  Conditioning
can only help a guesser, so these statements do **not** imply a bound on `H_min(X|E)`.  The
conditional statement is the separate superposition penalty
(`QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.SuperpositionPenalty`).

## Design notes

* `Ket d` carries `Add`, `SMul` and `Zero` but no bundled `AddCommMonoid`, so a finite linear
  combination is introduced explicitly as `Ket.combination`; the support hypothesis is then the
  honest equation `ψ = Ket.combination J α b` rather than a bespoke predicate.
* The core estimate `normSq_bra_mul_combination_le` assumes only a *bound* `c` on the overlaps
  over `J`, needs no normalization, no orthogonality and no sign condition on `c`, and is stated
  for an arbitrary bra.  Flatness and normalization are then two separate specializations.
* Normalization `∑_{e ∈ J} ‖α_e‖² = 1` is *derivable* from orthonormality of `b` on `J` together
  with `⟨ψ|ψ⟩ = 1` (`Ket.combination_inner_self_of_orthonormalOn`), so callers holding a genuine
  unit vector need not supply it by hand.
* `d = 0`, `J = ∅` and `α = 0` are all admitted; in the logarithmic corollary the positivity of
  the outcome probability *forces* `0 < d` and `0 < |J|`, so neither is assumed.

## Main definitions

* `Quantum.Operators.Ket.combination` — the finite combination `∑_{e ∈ J} α_e • b_e`.
* `Quantum.Bases.IsMutuallyUnbiased` — flatness of one ket family relative to another.

## Main statements

* `Quantum.Operators.bra_mul_combination` — linearity of the pairing over a combination.
* `Quantum.Operators.Ket.combination_inner_self_of_orthonormalOn` — Parseval on the support.
* `Quantum.Bases.normSq_bra_mul_combination_le` — the support–overlap Cauchy–Schwarz bound.
* `Quantum.Bases.IsMutuallyUnbiased.normSq_combination_le_card_div` — the flat form `≤ |J|/d`.
* `Quantum.Bases.IsMutuallyUnbiased.logb_card_div_le_neg_logb_normSq` — the surprisal form
  `log₂(d/|J|) ≤ −log₂ ‖⟨a_w|ψ⟩‖²`.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Quantum.Operators

variable {d : ℕ} {ι : Type*}

/-! ## Reading a coordinate with a computational bra -/

/-- **The computational bra reads off a coordinate:** `⟨w | ψ⟩ = ψ.vec w`.  This is the
measurement-outcome amplitude of `ψ` in the computational basis. -/
lemma stdKet_dag_mul (w : Fin d) (ψ : Ket d) : ((stdKet d w).dag * ψ : ℂ) = ψ.vec w := by
  rw [bra_mul_ket_eq, Finset.sum_eq_single w]
  · simp [Ket.dag_vec, stdKet_apply]
  · intro i _ hiw
    simp only [Ket.dag_vec, stdKet_apply]
    rw [ite_eq_right fun h => hiw h.symm]
    simp
  · intro h
    exact absurd (Finset.mem_univ w) h

/-! ## Finite combinations of kets -/

/-- **The finite combination** `∑_{e ∈ J} α_e • b_e` of a family of kets, given coordinatewise
because `Ket d` has no bundled `AddCommMonoid` instance.  `J = ∅` gives the zero ket. -/
def Ket.combination (J : Finset ι) (α : ι → ℂ) (b : ι → Ket d) : Ket d :=
  ⟨fun i => ∑ e ∈ J, α e * (b e).vec i⟩

@[simp] lemma Ket.combination_vec (J : Finset ι) (α : ι → ℂ) (b : ι → Ket d) (i : Fin d) :
    (Ket.combination J α b).vec i = ∑ e ∈ J, α e * (b e).vec i := rfl

@[simp] lemma Ket.combination_empty (α : ι → ℂ) (b : ι → Ket d) :
    Ket.combination (∅ : Finset ι) α b = 0 := by
  ext i
  simp [Ket.combination]

/-- **Linearity of the bra–ket pairing over a combination:**
`⟨φ | ∑_{e ∈ J} α_e b_e⟩ = ∑_{e ∈ J} α_e ⟨φ | b_e⟩`. -/
lemma bra_mul_combination (φ : Bra d) (J : Finset ι) (α : ι → ℂ) (b : ι → Ket d) :
    (φ * Ket.combination J α b : ℂ) = ∑ e ∈ J, α e * (φ * b e : ℂ) := by
  simp only [bra_mul_ket_eq, Ket.combination_vec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Parseval on the support.**  If the kets `b_e`, `e ∈ J`, are orthonormal, then
`⟨ψ|ψ⟩ = ∑_{e ∈ J} ‖α_e‖²` for `ψ = ∑_{e ∈ J} α_e b_e`.  Consequently a *normalized* combination
automatically satisfies the normalization hypothesis `∑_{e ∈ J} ‖α_e‖² = 1` of the bounds below,
which therefore need not be assumed separately by callers holding a unit vector. -/
lemma Ket.combination_inner_self_of_orthonormalOn [DecidableEq ι] (J : Finset ι) (α : ι → ℂ)
    (b : ι → Ket d)
    (horth : ∀ e ∈ J, ∀ f ∈ J, ((b e).dag * b f : ℂ) = if e = f then 1 else 0) :
    ((Ket.combination J α b).dag * Ket.combination J α b : ℂ) =
      ((∑ e ∈ J, Complex.normSq (α e) : ℝ) : ℂ) := by
  -- `⟨b f | ψ⟩ = α f` by orthonormality, hence `⟨ψ | b f⟩ = conj (α f)`.
  have hcoeff : ∀ f ∈ J, ((Ket.combination J α b).dag * b f : ℂ) = conj (α f) := by
    intro f hf
    have hfwd : ((b f).dag * Ket.combination J α b : ℂ) = α f := by
      rw [bra_mul_combination, Finset.sum_congr rfl fun e he => by rw [horth f hf e he]]
      simp [Finset.sum_ite_eq, hf]
    have hswap : ((Ket.combination J α b).dag * b f : ℂ) =
        star ((b f).dag * Ket.combination J α b : ℂ) :=
      Ket.inner_conj (Ket.combination J α b) (b f)
    rw [hswap, hfwd]
    rfl
  rw [bra_mul_combination, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun e he => by rw [hcoeff e he, Complex.mul_conj]

/-! ## Parseval for a complete family -/

/-- **Parseval's identity.**  If a family of kets resolves the identity, `∑_w |a_w⟩⟨a_w| = 1`,
then the measurement probabilities it assigns to any ket sum to that ket's squared norm:

  `∑_w ‖⟨a_w | ψ⟩‖² = ⟨ψ|ψ⟩`.

Only completeness is used — the family need not be orthonormal, and `ψ` need not be normalized.
This is what lets the total weight of a measured hybrid state be computed from the state's norm
rather than assumed. -/
lemma sum_normSq_bra_mul_of_complete {W : Type*} [Fintype W] (a : W → Ket d)
    (hcomplete : (∑ w, a w * (a w).dag) = (1 : Op d)) (ψ : Ket d) :
    ((∑ w, Complex.normSq ((a w).dag * ψ) : ℝ) : ℂ) = (ψ.dag * ψ : ℂ) := by
  have hterm : ∀ w : W, ((Complex.normSq ((a w).dag * ψ) : ℝ) : ℂ) =
      ∑ i, ∑ j, conj (ψ.vec i) * ((a w * (a w).dag : Op d) i j) * ψ.vec j := by
    intro w
    rw [← Complex.mul_conj, bra_mul_ket_eq, map_sum]
    simp only [Ket.dag_vec, map_mul, Complex.conj_conj]
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [ket_mul_bra_apply, Ket.dag_vec]
    ring
  rw [Complex.ofReal_sum, Finset.sum_congr rfl fun w _ => hterm w]
  rw [Finset.sum_comm]
  have hswap : (∑ i, ∑ w : W, ∑ j, conj (ψ.vec i) * ((a w * (a w).dag : Op d) i j) * ψ.vec j) =
      ∑ i, ∑ j, conj (ψ.vec i) * ((1 : Op d) i j) * ψ.vec j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.sum_apply, hcomplete]
  rw [hswap, bra_mul_ket_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [Ket.dag_vec]
  · intro j _ hji
    rw [Matrix.one_apply_ne fun h => hji h.symm]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

end Quantum.Operators

namespace Quantum.Bases

open Quantum.Operators

variable {d : ℕ} {ι κ : Type*}

/-! ## Flatness / mutual unbiasedness -/

/-- **Mutual unbiasedness (flatness).**  Two families of kets on the same `d`-dimensional space
are mutually unbiased when every overlap has squared modulus exactly `1/d`:

  `‖⟨a_x | b_y⟩‖² = 1/d`   for all `x`, `y`.

For two orthonormal bases this is the standard notion of mutually unbiased bases: measuring an
element of one basis in the other gives the uniform distribution.  The definition is stated for
arbitrary index types so that either family may be a sub-family or a differently indexed basis. -/
def IsMutuallyUnbiased (a : κ → Ket d) (b : ι → Ket d) : Prop :=
  ∀ (x : κ) (y : ι), Complex.normSq ((a x).dag * b y) = 1 / (d : ℝ)

/-- Mutual unbiasedness is symmetric, since `‖⟨a|b⟩‖² = ‖conj ⟨b|a⟩‖² = ‖⟨b|a⟩‖²`. -/
lemma IsMutuallyUnbiased.symm {a : κ → Ket d} {b : ι → Ket d} (h : IsMutuallyUnbiased a b) :
    IsMutuallyUnbiased b a := by
  intro y x
  have hswap : ((b y).dag * a x : ℂ) = star ((a x).dag * b y : ℂ) := Ket.inner_conj (b y) (a x)
  rw [hswap, show star ((a x).dag * b y : ℂ) = conj ((a x).dag * b y : ℂ) from rfl,
    Complex.normSq_conj]
  exact h x y

/-! ## The support–overlap bound -/

/-- **Support–overlap Cauchy–Schwarz bound.**  If every overlap `⟨φ | b_e⟩` with `e ∈ J` has
squared modulus at most `c`, then

  `‖⟨φ | ∑_{e ∈ J} α_e b_e⟩‖² ≤ (∑_{e ∈ J} ‖α_e‖²) · (|J| · c)`.

No normalization, orthogonality or sign hypothesis is needed: `J = ∅` gives `0 ≤ 0`, and
nonnegativity of `c` (when `J ≠ ∅`) is already implied by the overlap bound. -/
theorem normSq_bra_mul_combination_le (φ : Bra d) (J : Finset ι) (α : ι → ℂ) (b : ι → Ket d)
    {c : ℝ} (hb : ∀ e ∈ J, Complex.normSq ((φ * b e : ℂ)) ≤ c) :
    Complex.normSq ((φ * Ket.combination J α b : ℂ)) ≤
      (∑ e ∈ J, Complex.normSq (α e)) * ((J.card : ℝ) * c) := by
  rw [bra_mul_combination]
  have htri : ‖∑ e ∈ J, α e * (φ * b e : ℂ)‖ ≤ ∑ e ∈ J, ‖α e‖ * ‖(φ * b e : ℂ)‖ :=
    (norm_sum_le J _).trans_eq (Finset.sum_congr rfl fun e _ => norm_mul _ _)
  have hsq : ‖∑ e ∈ J, α e * (φ * b e : ℂ)‖ ^ 2 ≤ (∑ e ∈ J, ‖α e‖ * ‖(φ * b e : ℂ)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hCS : (∑ e ∈ J, ‖α e‖ * ‖(φ * b e : ℂ)‖) ^ 2 ≤
      (∑ e ∈ J, ‖α e‖ ^ 2) * ∑ e ∈ J, ‖(φ * b e : ℂ)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq J (fun e => ‖α e‖) fun e => ‖(φ * b e : ℂ)‖
  have hoverlap : (∑ e ∈ J, ‖(φ * b e : ℂ)‖ ^ 2) ≤ (J.card : ℝ) * c := by
    have h1 : (∑ e ∈ J, ‖(φ * b e : ℂ)‖ ^ 2) ≤ ∑ _e ∈ J, c :=
      Finset.sum_le_sum fun e he => by rw [← Complex.normSq_eq_norm_sq]; exact hb e he
    simpa [Finset.sum_const, nsmul_eq_mul] using h1
  have hcoeff : (0 : ℝ) ≤ ∑ e ∈ J, ‖α e‖ ^ 2 := Finset.sum_nonneg fun e _ => sq_nonneg _
  calc Complex.normSq (∑ e ∈ J, α e * (φ * b e : ℂ))
      = ‖∑ e ∈ J, α e * (φ * b e : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
    _ ≤ (∑ e ∈ J, ‖α e‖ ^ 2) * ∑ e ∈ J, ‖(φ * b e : ℂ)‖ ^ 2 := hsq.trans hCS
    _ ≤ (∑ e ∈ J, ‖α e‖ ^ 2) * ((J.card : ℝ) * c) := mul_le_mul_of_nonneg_left hoverlap hcoeff
    _ = (∑ e ∈ J, Complex.normSq (α e)) * ((J.card : ℝ) * c) := by
        simp [Complex.normSq_eq_norm_sq]

/-- **The flat-family support bound.**  For families `a`, `b` mutually unbiased in dimension `d`,
a combination of the `b`-kets supported on `J` has every `a`-overlap bounded by

  `‖⟨a_w | ∑_{e ∈ J} α_e b_e⟩‖² ≤ (∑_{e ∈ J} ‖α_e‖²) · (|J| / d)`. -/
theorem IsMutuallyUnbiased.normSq_combination_le {a : κ → Ket d} {b : ι → Ket d}
    (h : IsMutuallyUnbiased a b) (w : κ) (J : Finset ι) (α : ι → ℂ) :
    Complex.normSq (((a w).dag * Ket.combination J α b : ℂ)) ≤
      (∑ e ∈ J, Complex.normSq (α e)) * ((J.card : ℝ) / d) := by
  have hbase := normSq_bra_mul_combination_le (a w).dag J α b (c := 1 / (d : ℝ))
    fun e _ => le_of_eq (h w e)
  rwa [show (J.card : ℝ) * (1 / (d : ℝ)) = (J.card : ℝ) / d from by rw [mul_one_div]] at hbase

/-- **Bouman–Fehr's flat-basis probability bound.**  A *normalized* combination supported on `J`
in a flat family has every conjugate outcome probability bounded by `|J|/d`. -/
theorem IsMutuallyUnbiased.normSq_combination_le_card_div {a : κ → Ket d} {b : ι → Ket d}
    (h : IsMutuallyUnbiased a b) (w : κ) (J : Finset ι) (α : ι → ℂ)
    (hnorm : ∑ e ∈ J, Complex.normSq (α e) = 1) :
    Complex.normSq (((a w).dag * Ket.combination J α b : ℂ)) ≤ (J.card : ℝ) / d := by
  simpa [hnorm] using h.normSq_combination_le w J α

/-! ## The surprisal form -/

/-- **Surprisal form of the flat-family bound.**  If the outcome `w` of the `a`-measurement has
positive probability on a normalized `b`-combination supported on `J`, then its surprisal is at
least `log₂(d/|J|)`:

  `log₂(d / |J|) ≤ −log₂ ‖⟨a_w | ψ⟩‖²`.

Both `0 < d` and `0 < |J|` are *derived* from positivity of the probability — an empty support or
a zero-dimensional space forces the overlap to vanish — so neither is a hypothesis.  Logarithms
are base two, matching the min-entropy convention; the bound is the per-outcome (unconditional)
surprisal `−log₂ p_w ≥ log₂ d − log₂ |J|`. -/
theorem IsMutuallyUnbiased.logb_card_div_le_neg_logb_normSq {a : κ → Ket d} {b : ι → Ket d}
    (h : IsMutuallyUnbiased a b) (w : κ) (J : Finset ι) (α : ι → ℂ)
    (hnorm : ∑ e ∈ J, Complex.normSq (α e) = 1)
    (hpos : 0 < Complex.normSq (((a w).dag * Ket.combination J α b : ℂ))) :
    Real.logb 2 ((d : ℝ) / (J.card : ℝ)) ≤
      -Real.logb 2 (Complex.normSq (((a w).dag * Ket.combination J α b : ℂ))) := by
  have hbound := h.normSq_combination_le_card_div w J α hnorm
  have hmono : Real.logb 2 (Complex.normSq (((a w).dag * Ket.combination J α b : ℂ))) ≤
      Real.logb 2 ((J.card : ℝ) / d) :=
    Real.logb_le_logb_of_le one_lt_two hpos hbound
  have hflip : Real.logb 2 ((J.card : ℝ) / d) = -Real.logb 2 ((d : ℝ) / (J.card : ℝ)) := by
    rw [← Real.logb_inv, inv_div]
  rw [hflip] at hmono
  linarith

/-- The dimension and the support are forced to be nonempty by a positive outcome probability;
recorded separately because both facts are used implicitly by the surprisal bound. -/
lemma IsMutuallyUnbiased.pos_of_normSq_pos {b : ι → Ket d} {φ : Bra d} {J : Finset ι} {α : ι → ℂ}
    (hpos : 0 < Complex.normSq ((φ * Ket.combination J α b : ℂ))) : 0 < d ∧ 0 < J.card := by
  constructor
  · rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · exfalso; subst hd0; rw [bra_mul_ket_eq] at hpos; simp at hpos
    · exact hd0
  · rcases Nat.eq_zero_or_pos J.card with hJ0 | hJ0
    · exfalso
      rw [Finset.card_eq_zero.mp hJ0, Ket.combination_empty, bra_mul_ket_eq] at hpos
      simp at hpos
    · exact hJ0

end Quantum.Bases

end
