import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Error-Verification Correctness (joint, not conditional)

This file supplies the joint correctness bound for error verification, the gap
flagged in the security review of the postselection technique, arXiv:2502.10340,
§5.4.6 (with the explicit attack on p. 27).  The bound is on the BB84 chain:
`Protocols/.../InnerBudget.lean`'s `bb84_differAndAccept_weight_le_two_pow_neg_lEV`
consumes
`errorVerification_outcome_joint_correctness_of_universal` below.

The joint bound follows from the almost-universal-2 property alone. The conditional form
fails by the explicit counterexample `conditional_correctness_fails`.

## The gap

Error verification hashes Alice's and Bob's sifted keys `S_A, S_B` with a hash
function `h` drawn from a δ-almost-universal-2 family and *accepts* iff the
hashes match (`h S_A = h S_B`). The **common mistake** is to claim that the
*conditional* probability

    Pr[S_A ≠ S_B | EV accepts]

is small. The review exhibits an adversarial strategy on p. 27 for which this
conditional is ≈ 1: Eve can force `S_A ≠ S_B` deterministically while still
passing the test on the collisions the family cannot avoid, so conditioning on
acceptance says essentially nothing.

The **correct** correctness condition, matching the composable-security
definition (§4.3, Renner-style), is the *joint* probability

    Pr[S_A ≠ S_B  ∧  EV accepts] ≤ ε_cor.

δ-almost-universal-2 hashing delivers exactly this joint bound, and it needs
**only** the almost-universal-2 defining property — never the (false)
conditional statement:

    Pr[h(S_A) = h(S_B) | S_A ≠ S_B] ≤ δ                              (AU2)
  ⟹ Pr[differ ∧ accept]
        = Σ_{a≠b} Pr[S_A=a, S_B=b] · Pr_h[h(a)=h(b)]
        ≤ Σ_{a≠b} Pr[S_A=a, S_B=b] · δ
        ≤ δ · Pr[differ] ≤ δ.

The bound holds for an **arbitrary** (even adversarial, worst-case) joint
distribution of `(S_A, S_B)`; that is the whole point, and it is what the
review's deterministic attack respects.

## Main definitions

- `IsAlmostUniversal2 H δ`: a δ-almost-universal-2 hash family (finite set `H`
  of functions `S → T`), i.e. for every pair of distinct inputs the number of
  functions on which they collide is at most `δ · |H|`.
- `collisionProb H a b`: the probability `Pr_{h ∼ Unif(H)}[h a = h b]` that a
  uniformly chosen hash collides on the fixed pair `(a, b)`.
- `IsJointDist p`: a joint distribution on `S × S` (nonnegative, total mass 1),
  modelling an arbitrary/adversarial law of `(S_A, S_B)`.
- `jointDifferAcceptProb p H`: the joint probability
  `Pr[S_A ≠ S_B ∧ h(S_A) = h(S_B)]` under distribution `p` and uniform `h`.

### Seed-indexed siblings

A protocol's hash family is given as a *seed-indexed* map `h : Sd → S → T` with
the uniform law on the seed type `Sd`, not as a `Finset` of functions; and the
weight it hands this file is the *accept-branch* law, which is sub-normalised.
The following mirror the above in that form.

- `collisionProbIdx h a b`: `Pr_{s ∼ Unif(Sd)}[h s a = h s b]`.
- `jointDifferAcceptProbIdx p h`: the seed-indexed joint differ-and-accept
  probability.

## Main statements

- `collisionProb_le_delta`: for a δ-AU2 family, `collisionProb H a b ≤ δ` on
  distinct inputs.
- `errorVerification_joint_correctness`: for a δ-AU2 family, uniform hash choice
  and any joint distribution `p`, `jointDifferAcceptProb p H ≤ δ`.
- `errorVerification_joint_correctness_strong`: the strongly-universal-2
  specialization gives `ε_cor ≤ 1 / |T| = 2^{-t}` for a `t`-bit tag.
- `collisionProbIdx_le_delta`, `errorVerification_joint_correctness_indexed`,
  `errorVerification_joint_correctness_indexed_of_universal`: the seed-indexed
  forms, stated at a **sub-normalised** weight (`∑ p ≤ 1`) so that a quantum
  accept-branch law can be substituted directly. Each of these lemmas' extra
  hypothesis is literally `QuantumHashFamily.isUniversal`
  (`InfoTheory/QuantumLHL/RandomnessExtractor.lean`), so a proved 2-universality
  result discharges it verbatim.
- `errorVerification_outcome_joint_correctness_of_universal`: the same bound with
  the joint law presented the way a measurement supplies it — a weight `w` over an
  outcome type `Ω`, the two reconciled strings `A ω`, `B ω` read off the outcome,
  and a seed-free accept condition `acc ω` alongside the hash gate. This is the
  form consumed by the BB84 error-verification charge
  (`bb84_differAndAccept_weight_le_two_pow_neg_lEV`).

## References

- Security review, arXiv:2502.10340, §5.4.6 and §4.3 (composable security).
- Renner (2005) PhD thesis, arXiv:quant-ph/0512258 (composable correctness).
-/

open scoped BigOperators

namespace InfoTheory.Postselection.ErrorVerification

variable {S T : Type*}

/-!
## δ-almost-universal-2 hash families
-/

/-- A finite hash family `H ⊆ (S → T)` is **δ-almost-universal-2** if for every
    pair of distinct inputs `x ≠ y`, the number of hash functions in `H` on
    which they collide is at most `δ · |H|`.

    Dividing by `|H|`, this is the standard collision bound
    `Pr_{h ∼ Unif(H)}[h x = h y] ≤ δ`.  The special case `δ = 1 / |T|` is the
    exact (2-)universal / strongly-universal-2 family.

    Security review, arXiv:2502.10340, §5.4.6. -/
def IsAlmostUniversal2 [DecidableEq T] (H : Finset (S → T)) (δ : ℝ) : Prop :=
  ∀ x y : S, x ≠ y →
    ((H.filter (fun h => h x = h y)).card : ℝ) ≤ δ * H.card

/-- The collision probability of a uniformly random hash from `H` on the fixed
    pair `(a, b)`:  `Pr_{h ∼ Unif(H)}[h a = h b] = |{h ∈ H : h a = h b}| / |H|`. -/
noncomputable def collisionProb [DecidableEq T] (H : Finset (S → T)) (a b : S) : ℝ :=
  ((H.filter (fun h => h a = h b)).card : ℝ) / H.card

/-- On distinct inputs, a δ-AU2 family has collision probability at most `δ`.
    This is the AU2 defining property, restated at the probability level. -/
lemma collisionProb_le_delta [DecidableEq T] {H : Finset (S → T)} {δ : ℝ}
    (hH : IsAlmostUniversal2 H δ) (hne : H.Nonempty) {a b : S} (hab : a ≠ b) :
    collisionProb H a b ≤ δ := by
  have hcard : (0 : ℝ) < H.card := by
    exact_mod_cast Finset.card_pos.mpr hne
  rw [collisionProb, div_le_iff₀ hcard]
  exact hH a b hab

/-- `collisionProb` is always nonnegative. -/
lemma collisionProb_nonneg [DecidableEq T] (H : Finset (S → T)) (a b : S) :
    0 ≤ collisionProb H a b := by
  unfold collisionProb
  apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-!
## Joint distribution of (S_A, S_B) and the joint accept-and-differ probability
-/

/-- A joint distribution of `(S_A, S_B)` on `S × S`: nonnegative weights summing
    to 1.  This models an **arbitrary, possibly adversarial** law of Alice's and
    Bob's sifted keys, including the deterministic worst case in which Eve fixes
    a single pair `(a, b)` with `a ≠ b` (the review's p. 27 attack). -/
structure IsJointDist [Fintype S] (p : S × S → ℝ) : Prop where
  nonneg : ∀ ab, 0 ≤ p ab
  total : ∑ ab, p ab = 1

/-- The **joint** probability that the keys differ *and* error verification
    accepts:  `Pr[S_A ≠ S_B ∧ h(S_A) = h(S_B)]`, taken over the joint law `p`
    of `(S_A, S_B)` and an independent uniform hash `h ∼ Unif(H)`.

    Because `S_A, S_B` and `h` are independent, this factors pairwise into
    `Σ_{a ≠ b} p(a, b) · Pr_h[h a = h b]`. -/
noncomputable def jointDifferAcceptProb [Fintype S] [DecidableEq S] [DecidableEq T]
    (p : S × S → ℝ) (H : Finset (S → T)) : ℝ :=
  ∑ ab : S × S, if ab.1 ≠ ab.2 then p ab * collisionProb H ab.1 ab.2 else 0

/-!
## Error-verification correctness (the joint bound)
-/

/-- **Error-verification correctness (joint form).**

    For a δ-almost-universal-2 hash family `H`, a uniformly random hash choice,
    and *any* joint distribution `p` of `(S_A, S_B)` — including the adversarial,
    worst-case laws the review considers — the joint probability that the keys
    differ and error verification nonetheless accepts is at most `δ`:

        Pr[S_A ≠ S_B ∧ h(S_A) = h(S_B)] ≤ δ.

    This is the correctness guarantee required by composable security (§4.3),
    and it follows from the AU2 property alone.  It closes the §5.4.6 gap: the
    review's attack breaks the *conditional* claim, but the *joint* bound proved
    here is exactly what security needs, and it survives that attack.

    Security review, arXiv:2502.10340, §5.4.6. -/
theorem errorVerification_joint_correctness [Fintype S] [DecidableEq S] [DecidableEq T]
    {H : Finset (S → T)} {δ : ℝ} (hδ : 0 ≤ δ)
    (hH : IsAlmostUniversal2 H δ) (hne : H.Nonempty)
    {p : S × S → ℝ} (hp : IsJointDist p) :
    jointDifferAcceptProb p H ≤ δ := by
  unfold jointDifferAcceptProb
  -- Bound each term:  [a≠b] · p(a,b) · collisionProb ≤ δ · p(a,b).
  have hterm : ∀ ab : S × S,
      (if ab.1 ≠ ab.2 then p ab * collisionProb H ab.1 ab.2 else 0) ≤ δ * p ab := by
    intro ab
    split_ifs with hab
    · calc p ab * collisionProb H ab.1 ab.2
          ≤ p ab * δ := by
            apply mul_le_mul_of_nonneg_left (collisionProb_le_delta hH hne hab) (hp.nonneg ab)
        _ = δ * p ab := mul_comm _ _
    · exact mul_nonneg hδ (hp.nonneg ab)
  calc ∑ ab : S × S, (if ab.1 ≠ ab.2 then p ab * collisionProb H ab.1 ab.2 else 0)
      ≤ ∑ ab : S × S, δ * p ab := Finset.sum_le_sum (fun ab _ => hterm ab)
    _ = δ * ∑ ab : S × S, p ab := by rw [Finset.mul_sum]
    _ = δ := by rw [hp.total, mul_one]

/-!
## Strongly-universal-2 specialization

A strongly-universal-2 family with output the `t`-bit tags `T` is δ-AU2 with
`δ = 1 / |T|`.  For `T = Fin (2^t)` this is `2^{-t}`, the standard error-
verification correctness parameter `ε_cor`.
-/

/-- **Strongly-universal-2 corollary.**  If `H` is `(1/|T|)`-almost-universal-2
    (the strongly-universal-2 / exact-universal case), the joint differ-and-
    accept probability is bounded by the reciprocal of the tag-space size,
    `ε_cor ≤ 1 / |T|`. -/
theorem errorVerification_joint_correctness_strong
    [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    {H : Finset (S → T)}
    (hH : IsAlmostUniversal2 H (1 / Fintype.card T)) (hne : H.Nonempty)
    {p : S × S → ℝ} (hp : IsJointDist p) :
    jointDifferAcceptProb p H ≤ 1 / Fintype.card T := by
  have hδ : (0 : ℝ) ≤ 1 / Fintype.card T :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  exact errorVerification_joint_correctness hδ hH hne hp

/-!
## Seed-indexed hash families

The statements above range over a `Finset` of hash *functions*.  Concrete
constructions — notably the BB84 privacy-amplification/error-verification
families — are instead **seed-indexed**: a map `h : Sd → S → T` from a finite
seed type `Sd`, with the uniform choice taken over *seeds*, not over the image
set of functions.  The two agree only when `s ↦ h s` is injective, which a hash
family need not satisfy and which is in any case the wrong thing to prove: the
probability that matters is the one over the seed randomness actually consumed
by the protocol.

The seed-indexed forms below therefore restate the collision probability, the
joint differ-and-accept probability and the correctness bound directly over
`Sd`.  The mathematics is unchanged — the proof of
`errorVerification_joint_correctness` transfers verbatim — but the statements
now compose with a `QuantumHashFamily`-style seed-indexed family without any
image-Finset detour.
-/

/-- The collision probability of a **uniformly random seed** on the fixed pair
    `(a, b)`, for a seed-indexed hash family `h : Sd → S → T`:

        Pr_{s ∼ Unif(Sd)}[h s a = h s b] = |{s : h s a = h s b}| / |Sd|.

    This is the seed-indexed counterpart of `collisionProb`; the average is over
    the seed type `Sd`, which is the randomness the protocol actually samples. -/
noncomputable def collisionProbIdx {S T Sd : Type*} [Fintype Sd] [DecidableEq T]
    (h : Sd → S → T) (a b : S) : ℝ :=
  ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ) / Fintype.card Sd

/-- `collisionProbIdx` is always nonnegative, being a ratio of cardinalities. -/
lemma collisionProbIdx_nonneg {S T Sd : Type*} [Fintype Sd] [DecidableEq T]
    (h : Sd → S → T) (a b : S) : 0 ≤ collisionProbIdx h a b := by
  unfold collisionProbIdx
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- On distinct inputs, a seed-indexed family satisfying the δ-almost-universal-2
    counting bound has collision probability at most `δ`.  This is the
    seed-indexed counterpart of `collisionProb_le_delta`: the counting hypothesis
    `|{s : h s a = h s b}| ≤ δ · |Sd|` divided through by the (positive)
    seed count. -/
lemma collisionProbIdx_le_delta {S T Sd : Type*} [Fintype Sd] [Nonempty Sd] [DecidableEq T]
    (h : Sd → S → T) {δ : ℝ}
    (hAU : ∀ a b : S, a ≠ b →
      ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ) ≤ δ * Fintype.card Sd)
    {a b : S} (hab : a ≠ b) :
    collisionProbIdx h a b ≤ δ := by
  have hcard : (0 : ℝ) < Fintype.card Sd := by
    exact_mod_cast Fintype.card_pos (α := Sd)
  rw [collisionProbIdx, div_le_iff₀ hcard]
  exact hAU a b hab

/-- The **joint** probability that the keys differ *and* seed-indexed error
    verification accepts:  `Pr[S_A ≠ S_B ∧ h s (S_A) = h s (S_B)]`, taken over the
    joint law `p` of `(S_A, S_B)` and an independent uniform seed `s ∼ Unif(Sd)`.

    Independence of `(S_A, S_B)` from the seed factors this pairwise into
    `Σ_{a ≠ b} p(a, b) · Pr_s[h s a = h s b]`, the seed-indexed counterpart of
    `jointDifferAcceptProb`. -/
noncomputable def jointDifferAcceptProbIdx {S T Sd : Type*} [Fintype S] [DecidableEq S]
    [Fintype Sd] [DecidableEq T] (p : S × S → ℝ) (h : Sd → S → T) : ℝ :=
  ∑ ab : S × S, if ab.1 ≠ ab.2 then p ab * collisionProbIdx h ab.1 ab.2 else 0

/-- **Error-verification correctness, seed-indexed joint form.**

    For a seed-indexed hash family `h : Sd → S → T` whose collision counts obey
    the δ-almost-universal-2 bound `|{s : h s a = h s b}| ≤ δ · |Sd|` on distinct
    inputs, a uniformly random seed, and *any* joint weight `p` of `(S_A, S_B)` —
    including the adversarial, worst-case laws of the review — the joint
    probability that the keys differ and error verification nonetheless accepts
    is at most `δ`:

        Pr[S_A ≠ S_B ∧ h s (S_A) = h s (S_B)] ≤ δ.

    This is `errorVerification_joint_correctness` with the uniform average taken
    over seeds rather than over a `Finset` of functions, which is the form a
    concrete seed-indexed family (e.g. the BB84 hash family) supplies directly.

    **The sub-normalised mass hypothesis is deliberate.**  The weight `p` is
    required only to be nonnegative with `∑ ab, p ab ≤ 1`, *not* to be a
    normalised distribution (`IsJointDist`, which demands `∑ ab, p ab = 1`).  A
    quantum protocol hands this lemma the *accept-branch* weight — the joint law
    of `(S_A, S_B)` restricted to the parameter-estimation-passing outcomes —
    which is sub-normalised, its deficit being the abort probability.  Requiring
    equality would make the bound unusable at that call site.  The bound is
    monotone in the total mass, so the sub-normalised form is strictly stronger
    and costs nothing: do not "tidy" it back to `IsJointDist`.

    Security review, arXiv:2502.10340, §5.4.6. -/
theorem errorVerification_joint_correctness_indexed
    {S T Sd : Type*} [Fintype S] [DecidableEq S] [DecidableEq T] [Fintype Sd] [Nonempty Sd]
    (h : Sd → S → T) {δ : ℝ} (hδ : 0 ≤ δ)
    (hAU : ∀ a b : S, a ≠ b →
      ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ) ≤ δ * Fintype.card Sd)
    {p : S × S → ℝ} (hp_nonneg : ∀ ab, 0 ≤ p ab) (hp_total : ∑ ab, p ab ≤ 1) :
    jointDifferAcceptProbIdx p h ≤ δ := by
  unfold jointDifferAcceptProbIdx
  -- Bound each term:  [a≠b] · p(a,b) · collisionProbIdx ≤ δ · p(a,b).
  have hterm : ∀ ab : S × S,
      (if ab.1 ≠ ab.2 then p ab * collisionProbIdx h ab.1 ab.2 else 0) ≤ δ * p ab := by
    intro ab
    split_ifs with hab
    · calc p ab * collisionProbIdx h ab.1 ab.2
          ≤ p ab * δ := by
            exact mul_le_mul_of_nonneg_left (collisionProbIdx_le_delta h hAU hab) (hp_nonneg ab)
        _ = δ * p ab := mul_comm _ _
    · exact mul_nonneg hδ (hp_nonneg ab)
  calc ∑ ab : S × S, (if ab.1 ≠ ab.2 then p ab * collisionProbIdx h ab.1 ab.2 else 0)
      ≤ ∑ ab : S × S, δ * p ab := Finset.sum_le_sum (fun ab _ => hterm ab)
    _ = δ * ∑ ab : S × S, p ab := by rw [Finset.mul_sum]
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hp_total hδ
    _ = δ := mul_one δ

/-- **Strongly-universal seed-indexed corollary.**

    If the seed-indexed family `h` is (exactly) universal — on distinct inputs at
    most a `1/|T|` fraction of the seeds collide, i.e.
    `|{s : h s a = h s b}| ≤ |Sd| / |T|`, which is the defining property of a
    universal hash family as stated seed-indexed — then the joint differ-and-
    accept probability is bounded by the reciprocal of the tag-space size:

        Pr[S_A ≠ S_B ∧ h s (S_A) = h s (S_B)] ≤ 1 / |T|.

    For `T` the `t`-bit tags this is the standard error-verification correctness
    parameter `ε_cor = 2^{-t}`.  It is the seed-indexed counterpart of
    `errorVerification_joint_correctness_strong`, obtained by rewriting
    `|Sd| / |T| = (1 / |T|) · |Sd|` and applying
    `errorVerification_joint_correctness_indexed` at `δ = 1 / |T|`.  As there,
    the weight `p` is only required to be sub-normalised (`∑ ab, p ab ≤ 1`), the
    form a quantum accept branch supplies. -/
theorem errorVerification_joint_correctness_indexed_of_universal
    {S T Sd : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] [Nonempty T]
    [Fintype Sd] [Nonempty Sd] (h : Sd → S → T)
    (hU : ∀ a b : S, a ≠ b →
      ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ)
        ≤ (Fintype.card Sd : ℝ) / (Fintype.card T : ℝ))
    {p : S × S → ℝ} (hp_nonneg : ∀ ab, 0 ≤ p ab) (hp_total : ∑ ab, p ab ≤ 1) :
    jointDifferAcceptProbIdx p h ≤ 1 / Fintype.card T := by
  have hδ : (0 : ℝ) ≤ 1 / Fintype.card T :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  refine errorVerification_joint_correctness_indexed h hδ (fun a b hab => ?_) hp_nonneg hp_total
  have hrw : (Fintype.card Sd : ℝ) / (Fintype.card T : ℝ)
      = (1 / Fintype.card T) * Fintype.card Sd := by ring
  rw [← hrw]
  exact hU a b hab

/-- **Error-verification correctness at an outcome-indexed sub-normalised weight.**

The form a measurement-outcome-indexed protocol supplies.  Instead of a law on key pairs, the
protocol hands over

* an outcome type `Ω` with a nonnegative weight `w` of total mass at most `1` (the Born weights of
  the round-outcome strings, sub-normalised because only part of the outcome space is retained),
* the two reconciled strings `A ω`, `B ω` read off each outcome,
* a further accept condition `acc ω` that does **not** read the seed (the parameter-estimation
  test), and
* the seed-indexed hash family `h`, the error-verification gate being `h s (A ω) = h s (B ω)`.

The conclusion bounds the seed-averaged joint mass of "the strings differ **and** every accept
condition holds" by `1 / |T|`.  It is `errorVerification_joint_correctness_indexed_of_universal`
composed with the grouping of outcomes into key pairs: the induced pair law
`p (a, b) = ∑_{ω : (A ω, B ω) = (a, b), acc ω} w ω` is nonnegative with total mass at most `1`,
which is exactly the sub-normalised hypothesis pair that lemma takes.

**Joint, never conditional.**  As throughout this file, the bound is on the *joint* event; the
conditional `Pr[differ | accept]` is not bounded by `1/|T|`
(`conditional_correctness_fails`). -/
theorem errorVerification_outcome_joint_correctness_of_universal
    {S T Sd Ω : Type*} [Finite S] [DecidableEq S] [Fintype T] [DecidableEq T] [Nonempty T]
    [Fintype Sd] [Nonempty Sd] [Fintype Ω]
    (h : Sd → S → T)
    (hU : ∀ a b : S, a ≠ b →
      ((Finset.univ.filter (fun s => h s a = h s b)).card : ℝ)
        ≤ (Fintype.card Sd : ℝ) / (Fintype.card T : ℝ))
    (A B : Ω → S) (acc : Ω → Bool) (w : Ω → ℝ)
    (hw_nonneg : ∀ ω, 0 ≤ w ω) (hw_total : ∑ ω, w ω ≤ 1) :
    (1 / (Fintype.card Sd : ℝ)) *
        ∑ s : Sd, ∑ ω : Ω,
          (if A ω ≠ B ω ∧ (acc ω && decide (h s (A ω) = h s (B ω))) = true then w ω else 0)
      ≤ 1 / Fintype.card T := by
  classical
  have : Fintype S := Fintype.ofFinite S
  set p : S × S → ℝ :=
    fun ab => ∑ ω : Ω, if (A ω, B ω) = ab ∧ acc ω = true then w ω else 0 with hpdef
  have hp_nonneg : ∀ ab, 0 ≤ p ab := by
    intro ab
    refine Finset.sum_nonneg fun ω _ => ?_
    by_cases hc : (A ω, B ω) = ab ∧ acc ω = true
    · simpa [hc] using hw_nonneg ω
    · simp [hc]
  have hp_total : ∑ ab : S × S, p ab ≤ 1 := by
    have hswap : ∑ ab : S × S, p ab = ∑ ω : Ω, (if acc ω = true then w ω else 0) := by
      rw [hpdef, Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases hacc : acc ω = true
      · simp [hacc]
      · simp [hacc]
    rw [hswap]
    refine le_trans (Finset.sum_le_sum fun ω _ => ?_) hw_total
    by_cases hacc : acc ω = true
    · simp [hacc]
    · simpa [hacc] using hw_nonneg ω
  -- Both sides reduce to the same per-outcome sum.
  have hLHS : (1 / (Fintype.card Sd : ℝ)) *
        ∑ s : Sd, ∑ ω : Ω,
          (if A ω ≠ B ω ∧ (acc ω && decide (h s (A ω) = h s (B ω))) = true then w ω else 0) =
      ∑ ω : Ω,
        (if A ω ≠ B ω ∧ acc ω = true then w ω * collisionProbIdx h (A ω) (B ω) else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hc : A ω ≠ B ω ∧ acc ω = true
    · rw [ite_eq_left hc]
      have hcond : ∀ s : Sd,
          (if A ω ≠ B ω ∧ (acc ω && decide (h s (A ω) = h s (B ω))) = true then w ω else 0) =
            (if h s (A ω) = h s (B ω) then w ω else 0) := by
        intro s
        by_cases hs : h s (A ω) = h s (B ω)
        · simp [hs, hc.1, hc.2]
        · simp [hs]
      rw [Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) => hcond s]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [collisionProbIdx]
      ring
    · rw [ite_eq_right hc]
      have hzero : ∀ s : Sd,
          (if A ω ≠ B ω ∧ (acc ω && decide (h s (A ω) = h s (B ω))) = true then w ω else 0)
            = 0 := by
        intro s
        refine ite_eq_right ?_
        rintro ⟨hne, hacc⟩
        exact hc ⟨hne, (Bool.and_eq_true _ _ |>.mp hacc).1⟩
      rw [Finset.sum_eq_zero fun s _ => hzero s, mul_zero]
  have hRHS : jointDifferAcceptProbIdx p h =
      ∑ ω : Ω,
        (if A ω ≠ B ω ∧ acc ω = true then w ω * collisionProbIdx h (A ω) (B ω) else 0) := by
    rw [jointDifferAcceptProbIdx]
    have hexp : ∀ ab : S × S,
        (if ab.1 ≠ ab.2 then p ab * collisionProbIdx h ab.1 ab.2 else 0) =
          ∑ ω : Ω, (if ab.1 ≠ ab.2 then
            (if (A ω, B ω) = ab ∧ acc ω = true then w ω else 0) *
              collisionProbIdx h ab.1 ab.2 else 0) := by
      intro ab
      by_cases hab : ab.1 ≠ ab.2
      · simp only [ite_eq_left hab, hpdef, Finset.sum_mul]
      · simp [hab]
    rw [Finset.sum_congr rfl fun ab (_ : ab ∈ Finset.univ) => hexp ab, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_eq_single (A ω, B ω)]
    · by_cases hc : A ω ≠ B ω ∧ acc ω = true
      · simp [hc.1, hc.2]
      · by_cases hne : A ω ≠ B ω
        · have hacc : ¬ acc ω = true := fun ha => hc ⟨hne, ha⟩
          simp [hne, hacc]
        · simp [hne]
    · intro ab _ hne
      by_cases hab : ab.1 ≠ ab.2
      · simp [hab, Ne.symm hne]
      · simp [hab]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [hLHS, ← hRHS]
  exact errorVerification_joint_correctness_indexed_of_universal h hU hp_nonneg hp_total

/-!
## Counterexample: the *conditional* claim fails (review's p. 27 attack)

The following spells out, concretely, why the correctness guarantee must be the
*joint* probability and not the conditional one. It mirrors the attack in
arXiv:2502.10340 §5.4.6 (p. 27): Eve forces `S_A ≠ S_B` deterministically, so
`{S_A ≠ S_B}` is the *certain* event; hence

    Pr[S_A ≠ S_B | EV accepts] = 1,

no matter how small `δ` is — the conditional is *not* bounded by `δ`. Yet the
joint probability `Pr[S_A ≠ S_B ∧ EV accepts]` still obeys the `≤ δ` bound
proved above. This is exactly why `errorVerification_joint_correctness` is
stated at the joint level.

We instantiate this with the smallest nontrivial example:
`S = T = Bool`, the two-function family `H = {id, const false}`, and the
adversarial distribution `p` deterministically concentrated on the distinct
pair `(true, false)`.
-/

/-- The probability that EV accepts, `Pr[h(S_A) = h(S_B)]`, under joint law `p`
    and uniform `h`. Used only to phrase the conditional in the counterexample. -/
noncomputable def acceptProb [Fintype S] [DecidableEq T]
    (p : S × S → ℝ) (H : Finset (S → T)) : ℝ :=
  ∑ ab : S × S, p ab * collisionProb H ab.1 ab.2

/-- The adversarial two-function family `{id, const false} ⊆ (Bool → Bool)`. -/
def attackFamily : Finset (Bool → Bool) := {id, fun _ => false}

/-- The adversarial distribution: point mass on the distinct pair `(true, false)`. -/
noncomputable def attackDist : Bool × Bool → ℝ :=
  fun ab => if ab = (true, false) then 1 else 0

/-- The full family has two members. -/
private lemma attackFamily_card : attackFamily.card = 2 := by decide

/-- On the distinct pair `(true, false)`, exactly one hash (`const false`)
    collides, so the collision probability is `1/2`. -/
private lemma attackFamily_collision_true_false :
    collisionProb attackFamily true false = 1 / 2 := by
  have h1 : (attackFamily.filter (fun h => h true = h false)).card = 1 := by decide
  simp [collisionProb, h1, attackFamily_card]

/-- `attackFamily` is `(1/|Bool|) = 1/2`-almost-universal-2. -/
example : IsAlmostUniversal2 attackFamily (1 / Fintype.card Bool) := by
  intro x y hxy
  -- On any distinct Bool pair, exactly one of the two functions collides.
  have hcard : (attackFamily.filter (fun h => h x = h y)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro f hf g hg
    -- `id` never collides on distinct inputs, so any colliding fn is `const false`.
    simp only [attackFamily, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hf hg
    rcases hf.1 with hf1 | hf1 <;> rcases hg.1 with hg1 | hg1 <;>
      subst hf1 <;> subst hg1 <;> first
        | rfl
        | (exact absurd (hf.2) (by simpa [id] using hxy))
        | (exact absurd (hg.2) (by simpa [id] using hxy))
  calc ((attackFamily.filter (fun h => h x = h y)).card : ℝ)
      ≤ 1 := by exact_mod_cast hcard
    _ = (1 / Fintype.card Bool) * attackFamily.card := by
        rw [attackFamily_card, Fintype.card_bool]; norm_num

/-- The joint differ-and-accept probability of the attack is `1/2` — matching the
    `≤ δ = 1/2` bound (`errorVerification_joint_correctness`). The whole mass is
    on the distinct pair `(true, false)`, whose collision probability is `1/2`. -/
example : jointDifferAcceptProb attackDist attackFamily = 1 / 2 := by
  rw [jointDifferAcceptProb, Fintype.sum_prod_type]
  simp only [attackDist, Fintype.sum_bool, Bool.true_eq_false, ne_eq,
    Prod.mk.injEq]
  rw [attackFamily_collision_true_false]
  norm_num

/-- **The conditional fails.** Under the same attack EV accepts with probability
    `1/2` (all of it from the distinct pair `(true, false)`), so the *conditional*
    `Pr[S_A ≠ S_B | accept] = joint / accept = (1/2) / (1/2) = 1`.  Eve forced the
    keys to differ, so conditioning on acceptance gives no security. This is
    exactly the review's objection to the conditional claim (arXiv:2502.10340,
    §5.4.6, p. 27): the conditional is `1`, unbounded by any `δ`, while the joint
    stays `≤ δ = 1/2`. -/
theorem conditional_correctness_fails :
    jointDifferAcceptProb attackDist attackFamily
      / acceptProb attackDist attackFamily = 1 := by
  have hj : jointDifferAcceptProb attackDist attackFamily = 1 / 2 := by
    rw [jointDifferAcceptProb, Fintype.sum_prod_type]
    simp only [attackDist, Fintype.sum_bool, Bool.true_eq_false, ne_eq,
      Prod.mk.injEq]
    rw [attackFamily_collision_true_false]; norm_num
  have ha : acceptProb attackDist attackFamily = 1 / 2 := by
    rw [acceptProb, Fintype.sum_prod_type]
    simp only [attackDist, Fintype.sum_bool, Prod.mk.injEq]
    rw [attackFamily_collision_true_false]; norm_num
  rw [hj, ha]; norm_num

end InfoTheory.Postselection.ErrorVerification
