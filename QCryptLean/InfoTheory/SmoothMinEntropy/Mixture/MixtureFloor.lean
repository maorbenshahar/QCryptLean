import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.Smooth
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Order
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SuperpositionDephasing.PurifiedDistance

/-!
# Smooth entropy floors for mixtures

Component witnesses with exponential feasible coefficients combine into a mixture witness.
Purified-distance control gives a canonical smooth entropy floor, including zero mixture weight.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## Finite-mixture CQ state constructor -/

/-- The mixture sub-density block `Σ_z p_z • (comp z).stateMap x` for a finite family
of CQ states with nonnegative weights summing to one.

Per-block sub-normalization holds because `(comp z).stateMap x` has trace `≤ 1`
(`CQState.classicalMarginal_le_one`) and `∑_z p_z = 1`. -/
def finMixBlock {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (comp : Z → CQState X n) (x : X) : SubDensityOp n where
  toOp := ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp
  isHermitian := by
    have hpsd : (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp).PosSemidef := by
      apply Matrix.posSemidef_sum
      intro z _
      exact (posSemidefOp_implies_mathlib ((comp z).stateMap x).toPosSemidefOp).smul
        (RCLike.ofReal_nonneg.mpr (hp_nonneg z))
    exact hpsd.isHermitian
  pos_semidef := by
    intro v
    have hpsd : (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp).PosSemidef := by
      apply Matrix.posSemidef_sum
      intro z _
      exact (posSemidefOp_implies_mathlib ((comp z).stateMap x).toPosSemidefOp).smul
        (RCLike.ofReal_nonneg.mpr (hp_nonneg z))
    exact posSemidef_re_quadraticForm_nonneg hpsd v
  trace_le_one := by
    have htrace : (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp).trace.re
        = ∑ z, p z * ((comp z).stateMap x).trace := by
      rw [Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rfl
    rw [htrace]
    calc ∑ z, p z * ((comp z).stateMap x).trace
        ≤ ∑ z, p z * 1 := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          exact mul_le_mul_of_nonneg_left
            ((comp z).classicalMarginal_le_one x) (hp_nonneg z)
      _ = ∑ z, p z := by simp
      _ = 1 := hp_sum

/-- The finite mixture of a family of CQ states with nonnegative weights summing to
one. Each classical block is the nonnegative convex combination of the component
blocks. -/
def finMix {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (comp : Z → CQState X n) : CQState X n where
  stateMap x := finMixBlock p hp_nonneg hp_sum comp x
  weight_le_one := by
    have hblock : ∀ x : X, (finMixBlock p hp_nonneg hp_sum comp x).trace
        = ∑ z, p z * ((comp z).stateMap x).trace := by
      intro x
      change (∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp).trace.re
        = ∑ z, p z * ((comp z).stateMap x).trace
      rw [Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rfl
    have hswap : ∑ x : X, (finMixBlock p hp_nonneg hp_sum comp x).trace
        = ∑ z, p z * (∑ x : X, ((comp z).stateMap x).trace) := by
      simp_rw [hblock, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hswap]
    calc ∑ z, p z * (∑ x : X, ((comp z).stateMap x).trace)
        ≤ ∑ z, p z * 1 := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          exact mul_le_mul_of_nonneg_left (comp z).weight_le_one (hp_nonneg z)
      _ = ∑ z, p z := by simp
      _ = 1 := hp_sum

@[simp]
lemma finMix_stateMap_toOp {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (comp : Z → CQState X n) (x : X) :
    ((finMix p hp_nonneg hp_sum comp).stateMap x).toOp
      = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp :=
  rfl

/-! ## 3a. Unsmoothed convexity floor (pure PSD convexity, Nahar et al. B22 / Renner 6.25) -/

/-- **Feasibility of a mixture.** If a scalar `t` is feasible for every component
of a nonnegative convex combination, it is feasible for the mixture.

`t·σ − ρ_A(x) = Σ_z p_z (t·σ − (comp z)_A(x))` is a nonnegative-weighted sum of PSD
blocks, hence PSD. (Nahar et al. B22, the SDP convexity step.) -/
lemma isFeasible_mixture {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) {t : ℝ}
    (ht : ∀ z, isFeasible (comp z) σ t) : isFeasible ρ σ t := by
  classical
  have hZne : Nonempty Z := by
    rcases isEmpty_or_nonempty Z with hE | hN
    · exfalso; rw [Finset.sum_of_isEmpty] at hp_sum; norm_num at hp_sum
    · exact hN
  refine ⟨(ht (Classical.arbitrary Z)).1, fun x => ?_⟩
  -- Rewrite both sides as nonneg-weighted sums over `z`.
  have hlhs : (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp := hmix x
  have hrhs : (Complex.ofReal t • σ.toOp)
      = ∑ z, (p z : ℂ) • (Complex.ofReal t • σ.toOp) := by
    rw [← Finset.sum_smul]
    have : (∑ z, (p z : ℂ)) = 1 := by
      rw [← Complex.ofReal_sum, hp_sum]; norm_num
    rw [this, one_smul]
  rw [hlhs, hrhs]
  apply Quantum.Channels.opLe_sum
  intro z
  exact opLe_smul_nonneg (hp_nonneg z) ((ht z).2 x)

/-- A zero-weight CQ state has every block equal to zero. -/
private lemma stateMap_toOp_eq_zero_of_weight_zero {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (hw : ∑ x : X, (ρ.stateMap x).trace = 0) (x : X) :
    (ρ.stateMap x).toOp = 0 := by
  have hnonneg : ∀ y : X, 0 ≤ (ρ.stateMap y).trace := fun y => (ρ.stateMap y).trace_nonneg
  have hx_zero : (ρ.stateMap x).trace = 0 :=
    le_antisymm
      (by
        have := Finset.single_le_sum (f := fun y => (ρ.stateMap y).trace)
          (fun y _ => hnonneg y) (Finset.mem_univ x)
        rw [hw] at this; exact this)
      (hnonneg x)
  have hpsd : ((ρ.stateMap x).toOp).PosSemidef :=
    posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp
  have htrace_c : (ρ.stateMap x).toOp.trace = 0 := by
    rw [SubDensityOp.trace_complex_eq, hx_zero]; simp
  exact hpsd.trace_eq_zero_iff.mp htrace_c

/-! ## 3b. Smoothing transfer (Nahar et al. B21 / Renner Eq. 3.59) -/

/-- Sub-normalization generalized-fidelity correction for a finite `Fintype`-indexed
nonnegative convex combination, obtained from the `ℕ`-indexed
`InfoTheory.SmoothMinEntropy.weighted_mixture_fidelityGen_ge` by transporting along an embedding
`Z ↪ ℕ`. -/
private lemma weighted_mixture_fidelityGen_ge_univ
    {Z : Type*} [Fintype Z] [Nonempty Z]
    (w a u v : Z → ℝ) (c : ℝ)
    (hw : ∀ z, 0 ≤ w z) (ha : ∀ z, 0 ≤ a z) (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z)
    (hc1 : c ≤ 1) (hsum : ∑ z, w z = 1)
    (hcomp : ∀ z, c ≤ a z + Real.sqrt (u z * v z)) :
    c ≤ (∑ z, w z * a z) +
        Real.sqrt ((∑ z, w z * u z) * (∑ z, w z * v z)) := by
  classical
  set e : Z ↪ ℕ := (Fintype.equivFin Z).toEmbedding.trans Fin.valEmbedding with he
  have hinv : ∀ z, Function.invFun e (e z) = z := Function.leftInverse_invFun e.injective
  set wN : ℕ → ℝ := fun s => w (Function.invFun e s) with hwN
  set aN : ℕ → ℝ := fun s => a (Function.invFun e s) with haN
  set uN : ℕ → ℝ := fun s => u (Function.invFun e s) with huN
  set vN : ℕ → ℝ := fun s => v (Function.invFun e s) with hvN
  have hwNe : ∀ z, wN (e z) = w z := fun z => by simp only [hwN, hinv]
  have haNe : ∀ z, aN (e z) = a z := fun z => by simp only [haN, hinv]
  have huNe : ∀ z, uN (e z) = u z := fun z => by simp only [huN, hinv]
  have hvNe : ∀ z, vN (e z) = v z := fun z => by simp only [hvN, hinv]
  set S : Finset ℕ := Finset.univ.map e with hSdef
  have hsumN : ∀ (g : Z → ℝ) (gN : ℕ → ℝ), (∀ z, gN (e z) = g z) →
      ∑ s ∈ S, gN s = ∑ z, g z := by
    intro g gN hge
    rw [hSdef, Finset.sum_map]
    exact Finset.sum_congr rfl (fun z _ => hge z)
  have key := InfoTheory.SmoothMinEntropy.weighted_mixture_fidelityGen_ge S wN aN uN vN c 0
    (fun s hs => by obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs; rw [hwNe]; exact hw z)
    (fun s hs => by obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs; rw [haNe]; exact ha z)
    (fun s hs => by obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs; rw [huNe]; exact hu z)
    (fun s hs => by obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs; rw [hvNe]; exact hv z)
    le_rfl hc1
    (by rw [zero_add, hsumN w wN hwNe]; exact hsum)
    (fun s hs => by
      obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hs
      rw [haNe, huNe, hvNe]; exact hcomp z)
  have e1 : ∑ s ∈ S, wN s * aN s = ∑ z, w z * a z :=
    hsumN (fun z => w z * a z) (fun s => wN s * aN s)
      (fun z => by rw [hwNe, haNe])
  have e2 : ∑ s ∈ S, wN s * uN s = ∑ z, w z * u z :=
    hsumN (fun z => w z * u z) (fun s => wN s * uN s)
      (fun z => by rw [hwNe, huNe])
  have e3 : ∑ s ∈ S, wN s * vN s = ∑ z, w z * v z :=
    hsumN (fun z => w z * v z) (fun s => wN s * vN s)
      (fun z => by rw [hwNe, hvNe])
  rw [e1, e2, e3] at key
  simpa only [zero_add] using key

/-- **Smoothing transfer for a finite CQ mixture (Nahar et al. B21 / Renner [46] Eq. 3.59).**

If each component of one nonnegative convex combination is within purified distance
`ε` of the corresponding component of another, the two mixtures themselves are within
purified distance `ε`. (`a z`/`b z` are the components, `ρ`/`ρ'` the assembled
mixtures with the same weights `p`.)

This is the lone genuinely-quantum step in the mixture floor. It is Nahar et al.'s only appeal
to Renner Eq. 3.59: blockwise super-additivity of the Uhlmann fidelity under merging
the per-component classical flag,
`F(Σ_z p_z a_z, Σ_z p_z b_z) ≥ Σ_z p_z F(a_z, b_z)`, combined with the Tomamichel
§3.3.1 sub-normalization correction.

The proof works directly on the single register `X`. For each classical block `x`,
the mixed blocks `Σ_z p_z (a z)_x`, `Σ_z p_z (b z)_x` are floored by
`Quantum.Metrics.fidelity_sum_le_fidelity_sum` (the finite fidelity super-additivity =
classical-flag discard of Renner Eq. 3.59) together with
`InfoTheory.SmoothMinEntropy.fidelity_smul_block_eq`
to extract the weights. Summing over `x` via
`CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity` gives a generalized-fidelity
floor for the assembled mixtures, which `weighted_mixture_fidelityGen_ge` turns into the
purified-distance bound. The single-register statement is the object the discrete
consumer (`smoothMinEntropy_mixture_ge_inf_component`) requires. -/
theorem CQState.purifiedDistance_mixture_le_max
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (a b : Z → CQState X n) (ρ ρ' : CQState X n)
    (hρ : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((a z).stateMap x).toOp)
    (hρ' : ∀ x : X, (ρ'.stateMap x).toOp = ∑ z, (p z : ℂ) • ((b z).stateMap x).toOp)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcomp : ∀ z, CQState.purifiedDistance (a z) (b z) ≤ ε) :
    CQState.purifiedDistance ρ ρ' ≤ ε := by
  classical
  have hZne : Nonempty Z := by
    rcases isEmpty_or_nonempty Z with hE | hN
    · exfalso; rw [Finset.sum_of_isEmpty] at hp_sum; norm_num at hp_sum
    · exact hN
  have : NeZero (Fintype.card Z) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card Z) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (n * Fintype.card X) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  -- (I) Super-additive fidelity lower bound for the mixture joint density.
  have hI :
      (∑ z, p z * Quantum.Metrics.fidelity
          (a z).toJointDensity.toPosSemidefOp (b z).toJointDensity.toPosSemidefOp)
        ≤ Quantum.Metrics.fidelity
          ρ.toJointDensity.toPosSemidefOp ρ'.toJointDensity.toPosSemidefOp := by
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity ρ ρ']
    -- Per classical block `x`, super-additivity floors the mixed block fidelity.
    have hper : ∀ x : X,
        (∑ z, p z * Quantum.Metrics.fidelity
            ((a z).stateMap x).toPosSemidefOp ((b z).stateMap x).toPosSemidefOp)
          ≤ Quantum.Metrics.fidelity
            (ρ.stateMap x).toPosSemidefOp (ρ'.stateMap x).toPosSemidefOp := by
      intro x
      have hpsdA : ∀ z, ((p z : ℂ) • ((a z).stateMap x).toOp).PosSemidef := fun z =>
        (posSemidefOp_implies_mathlib ((a z).stateMap x).toPosSemidefOp).smul
          (RCLike.ofReal_nonneg.mpr (hp_nonneg z))
      have hpsdB : ∀ z, ((p z : ℂ) • ((b z).stateMap x).toOp).PosSemidef := fun z =>
        (posSemidefOp_implies_mathlib ((b z).stateMap x).toPosSemidefOp).smul
          (RCLike.ofReal_nonneg.mpr (hp_nonneg z))
      set PA : Z → PosSemidefOp n := fun z =>
        ⟨⟨(p z : ℂ) • ((a z).stateMap x).toOp, (hpsdA z).isHermitian⟩,
         fun v => posSemidef_re_quadraticForm_nonneg (hpsdA z) v⟩ with hPA
      set PB : Z → PosSemidefOp n := fun z =>
        ⟨⟨(p z : ℂ) • ((b z).stateMap x).toOp, (hpsdB z).isHermitian⟩,
         fun v => posSemidef_re_quadraticForm_nonneg (hpsdB z) v⟩ with hPB
      have hPAtoOp : ∀ z, (PA z).toOp = (p z : ℂ) • ((a z).stateMap x).toOp := fun z => rfl
      have hPBtoOp : ∀ z, (PB z).toOp = (p z : ℂ) • ((b z).stateMap x).toOp := fun z => rfl
      have hsmul : ∀ z, Quantum.Metrics.fidelity (PA z) (PB z)
          = p z * Quantum.Metrics.fidelity
              ((a z).stateMap x).toPosSemidefOp ((b z).stateMap x).toPosSemidefOp := fun z =>
        InfoTheory.SmoothMinEntropy.fidelity_smul_block_eq (hp_nonneg z)
          ((a z).stateMap x).toPosSemidefOp ((b z).stateMap x).toPosSemidefOp
          (PA z) (PB z) (hPAtoOp z) (hPBtoOp z)
      have hsumA : (∑ z, PA z).toOp = (ρ.stateMap x).toOp := by
        rw [PosSemidefOp.sum_toOp, hρ x]
      have hsumB : (∑ z, PB z).toOp = (ρ'.stateMap x).toOp := by
        rw [PosSemidefOp.sum_toOp, hρ' x]
      calc (∑ z, p z * Quantum.Metrics.fidelity
              ((a z).stateMap x).toPosSemidefOp ((b z).stateMap x).toPosSemidefOp)
          = ∑ z, Quantum.Metrics.fidelity (PA z) (PB z) :=
            (Finset.sum_congr rfl (fun z _ => hsmul z)).symm
        _ ≤ Quantum.Metrics.fidelity (∑ z, PA z) (∑ z, PB z) :=
            Quantum.Metrics.fidelity_sum_le_fidelity_sum PA PB
        _ = Quantum.Metrics.fidelity
              (ρ.stateMap x).toPosSemidefOp (ρ'.stateMap x).toPosSemidefOp :=
            Quantum.Metrics.fidelity_congr hsumA hsumB
    calc (∑ z, p z * Quantum.Metrics.fidelity
            (a z).toJointDensity.toPosSemidefOp (b z).toJointDensity.toPosSemidefOp)
        = ∑ z, ∑ x, p z * Quantum.Metrics.fidelity
            ((a z).stateMap x).toPosSemidefOp ((b z).stateMap x).toPosSemidefOp := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity (a z) (b z),
            Finset.mul_sum]
      _ = ∑ x, ∑ z, p z * Quantum.Metrics.fidelity
            ((a z).stateMap x).toPosSemidefOp ((b z).stateMap x).toPosSemidefOp :=
          Finset.sum_comm
      _ ≤ ∑ x, Quantum.Metrics.fidelity
            (ρ.stateMap x).toPosSemidefOp (ρ'.stateMap x).toPosSemidefOp :=
          Finset.sum_le_sum (fun x _ => hper x)
  -- (II)/(III) Trace-deficit identities.
  have hblock_a : ∀ x : X,
      (ρ.stateMap x).trace = ∑ z, p z * ((a z).stateMap x).trace := by
    intro x
    unfold SubDensityOp.trace
    rw [hρ x, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hblock_b : ∀ x : X,
      (ρ'.stateMap x).trace = ∑ z, p z * ((b z).stateMap x).trace := by
    intro x
    unfold SubDensityOp.trace
    rw [hρ' x, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have htr_a : ρ.toJointDensity.trace = ∑ z, p z * (a z).toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum,
      show (∑ x, (ρ.stateMap x).trace)
          = ∑ x, ∑ z, p z * ((a z).stateMap x).trace from
        Finset.sum_congr rfl (fun x _ => hblock_a x), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [CQState.toJointDensity_trace_eq_sum, Finset.mul_sum]
  have htr_b : ρ'.toJointDensity.trace = ∑ z, p z * (b z).toJointDensity.trace := by
    rw [CQState.toJointDensity_trace_eq_sum,
      show (∑ x, (ρ'.stateMap x).trace)
          = ∑ x, ∑ z, p z * ((b z).stateMap x).trace from
        Finset.sum_congr rfl (fun x _ => hblock_b x), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [CQState.toJointDensity_trace_eq_sum, Finset.mul_sum]
  have hu_sum : (∑ z, p z * (1 - (a z).toJointDensity.trace))
      = 1 - ρ.toJointDensity.trace := by
    have hexp : ∑ z, p z * (1 - (a z).toJointDensity.trace)
        = (∑ z, p z) - ∑ z, p z * (a z).toJointDensity.trace := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    rw [hexp, hp_sum, htr_a]
  have hv_sum : (∑ z, p z * (1 - (b z).toJointDensity.trace))
      = 1 - ρ'.toJointDensity.trace := by
    have hexp : ∑ z, p z * (1 - (b z).toJointDensity.trace)
        = (∑ z, p z) - ∑ z, p z * (b z).toJointDensity.trace := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    rw [hexp, hp_sum, htr_b]
  -- Per-component generalized-fidelity lower bound from the purified-distance hyp.
  have hcompfg : ∀ z, Real.sqrt (1 - ε ^ 2) ≤
      Quantum.Metrics.fidelity (a z).toJointDensity.toPosSemidefOp
          (b z).toJointDensity.toPosSemidefOp
        + Real.sqrt ((1 - (a z).toJointDensity.trace)
            * (1 - (b z).toJointDensity.trace)) := by
    intro z
    have hpd := hcomp z
    unfold CQState.purifiedDistance at hpd
    have h := InfoTheory.SmoothMinEntropy.fidelityGen_ge_sqrt_one_sub_sq_of_purifiedDistance_le
      (a z).toJointDensity (b z).toJointDensity hε hpd
    unfold fidelityGen at h
    exact h
  have hc1 : Real.sqrt (1 - ε ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (sub_le_self 1 (sq_nonneg ε))
  -- Assemble the generalized-fidelity floor via the sub-normalization correction.
  have hkey := weighted_mixture_fidelityGen_ge_univ p
    (fun z => Quantum.Metrics.fidelity (a z).toJointDensity.toPosSemidefOp
      (b z).toJointDensity.toPosSemidefOp)
    (fun z => 1 - (a z).toJointDensity.trace)
    (fun z => 1 - (b z).toJointDensity.trace)
    (Real.sqrt (1 - ε ^ 2))
    hp_nonneg
    (fun z => Quantum.Metrics.fidelity_nonneg_posSemidefOp _ _)
    (fun z => (a z).toJointDensity.one_sub_trace_nonneg)
    (fun z => (b z).toJointDensity.one_sub_trace_nonneg)
    hc1 hp_sum hcompfg
  have hfg_ge : Real.sqrt (1 - ε ^ 2)
      ≤ fidelityGen ρ.toJointDensity ρ'.toJointDensity := by
    calc Real.sqrt (1 - ε ^ 2)
        ≤ (∑ z, p z * Quantum.Metrics.fidelity (a z).toJointDensity.toPosSemidefOp
              (b z).toJointDensity.toPosSemidefOp)
            + Real.sqrt ((∑ z, p z * (1 - (a z).toJointDensity.trace))
                * (∑ z, p z * (1 - (b z).toJointDensity.trace))) := hkey
      _ = (∑ z, p z * Quantum.Metrics.fidelity (a z).toJointDensity.toPosSemidefOp
              (b z).toJointDensity.toPosSemidefOp)
            + Real.sqrt ((1 - ρ.toJointDensity.trace)
                * (1 - ρ'.toJointDensity.trace)) := by rw [hu_sum, hv_sum]
      _ ≤ Quantum.Metrics.fidelity ρ.toJointDensity.toPosSemidefOp
              ρ'.toJointDensity.toPosSemidefOp
            + Real.sqrt ((1 - ρ.toJointDensity.trace)
                * (1 - ρ'.toJointDensity.trace)) := add_le_add hI le_rfl
      _ = fidelityGen ρ.toJointDensity ρ'.toJointDensity := rfl
  -- Convert the generalized-fidelity floor into the purified-distance bound.
  -- `√(1 - ε²) ≤ F_gen` squares to `1 - ε² ≤ F_gen²`.
  have hfgsq : 1 - ε ^ 2 ≤ fidelityGen ρ.toJointDensity ρ'.toJointDensity ^ 2 :=
    (Real.sqrt_le_iff.mp hfg_ge).2
  unfold CQState.purifiedDistance InfoTheory.SmoothMinEntropy.purifiedDistance
  calc Real.sqrt (1 - fidelityGen ρ.toJointDensity ρ'.toJointDensity ^ 2)
      ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt (sub_le_comm.mp hfgsq)
    _ = ε := Real.sqrt_sq hε

/-- A finite convex mixture inherits every common extended conditional entropy floor.
Zero components and zero mixtures are admitted; nonpositive floors hold by clipping. -/
theorem conditionalMinEntropy_mixture_ge_inf_component
    {X : Type*} [Fintype X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ)
    (hfloor : ∀ z, ENNReal.ofReal k ≤ conditionalMinEntropy (comp z) σ) :
    ENNReal.ofReal k ≤ conditionalMinEntropy ρ σ := by
  by_cases hk : k ≤ 0
  · simp only [ENNReal.ofReal_of_nonpos hk, zero_le]
  · exact ofReal_le_conditionalMinEntropy_of_isFeasible ρ σ k
      (isFeasible_mixture p hp_nonneg hp_sum comp ρ hmix σ fun z =>
        isFeasible_of_ofReal_le_conditionalMinEntropy (comp z) σ (lt_of_not_ge hk)
          (hfloor z))

/-- A finite convex mixture inherits common extended smooth entropy floors by mixing
feasible witnesses. No boundedness or feasibility assumption on the whole ball is needed. -/
theorem smoothMinEntropy_mixture_ge_inf_component
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ)
    (hfloor : ∀ z, ENNReal.ofReal k ≤ smoothMinEntropy ε (comp z) σ) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
  classical
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hlt
  have hex : ∀ z, ∃ τ : CQState X n,
      CQState.purifiedDistance (comp z) τ ≤ ε ∧ isFeasible τ σ (2 ^ (-(r : ℝ))) := by
    intro z
    obtain ⟨τ, hd, _, hτ⟩ :=
      smoothMinEntropy_exists_approx (comp z) σ r (hlt.trans_le (hfloor z))
    exact ⟨τ, hd, isFeasible_of_ofReal_le_conditionalMinEntropy τ σ hr
      (by simpa only [ENNReal.ofReal_coe_nnreal] using hτ.le)⟩
  choose comp' hd ht using hex
  let ρ' := finMix p hp_nonneg hp_sum comp'
  have hρ'mix := finMix_stateMap_toOp p hp_nonneg hp_sum comp'
  have hpd := CQState.purifiedDistance_mixture_le_max p hp_nonneg hp_sum
    comp comp' ρ ρ' hmix hρ'mix hε hd
  simpa only [ENNReal.ofReal_coe_nnreal] using
    smoothMinEntropy_ge_of_isFeasible ρ ρ' σ r hpd
      (isFeasible_mixture p hp_nonneg hp_sum comp' ρ' hρ'mix σ ht)


/-- A zero-weight CQ state has real conditional min-entropy at most zero. -/
lemma conditionalMinEntropyReal_le_zero_of_weight_zero {X : Type*} [Fintype X]
    {n : ℕ} (ρ : CQState X n) (σ : SubDensityOp n)
    (hw : ∑ x : X, (ρ.stateMap x).trace = 0) :
    conditionalMinEntropyReal ρ σ ≤ 0 := by
  -- All blocks are 0, so 0 is feasible, so minFeasibleLambda = 0, so value = 0.
  have hblocks : ∀ x : X, (ρ.stateMap x).toOp = 0 :=
    stateMap_toOp_eq_zero_of_weight_zero ρ hw
  have hfeas0 : isFeasible ρ σ 0 := by
    refine ⟨le_refl 0, fun x => ?_⟩
    intro v
    rw [hblocks x]
    simp only [quadraticForm, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re,
      Complex.ofReal_zero, zero_smul, le_refl]
  have hlam_le0 : minFeasibleLambda ρ σ ≤ 0 :=
    minFeasibleLambda_le_of_isFeasible ρ σ hfeas0
  have hlam0 : minFeasibleLambda ρ σ = 0 :=
    le_antisymm hlam_le0 (minFeasibleLambda_nonneg ρ σ)
  unfold conditionalMinEntropyReal
  rw [hlam0]; simp

/-- A probability mixture of feasible components inherits their common signed conditional
entropy floor. -/
theorem conditionalMinEntropyReal_mixture_ge_inf_component
    {X : Type*} [Fintype X] [Nonempty X] {n : ℕ} {Z : Type*} [Fintype Z]
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ)
    (hfeas_comp : ∀ z, hasFeasibleLambda (comp z) σ)
    (hfloor : ∀ z, k ≤ conditionalMinEntropyReal (comp z) σ) :
    k ≤ conditionalMinEntropyReal ρ σ := by
  classical
  -- Each component optimum is ≤ 2^(−k); hence each component is feasible at 2^(−k).
  have hlamz_le : ∀ z, minFeasibleLambda (comp z) σ ≤ 2 ^ (-k) := fun z =>
    minFeasibleLambda_le_pow_neg_k_of_conditionalMinEntropyReal_le
      (comp z) σ k (hfloor z)
  have hfeas_t : ∀ z, isFeasible (comp z) σ (2 ^ (-k)) := fun z =>
    isFeasible_mono_t
      (isFeasible_minFeasibleLambda_of_hasFeasibleLambda (comp z) σ (hfeas_comp z))
      (hlamz_le z)
  -- The mixture is feasible at 2^(−k), so minFeasibleLambda ρ σ ≤ 2^(−k).
  have hρ_feas : isFeasible ρ σ (2 ^ (-k)) :=
    isFeasible_mixture p hp_nonneg hp_sum comp ρ hmix σ hfeas_t
  have hρ_le : minFeasibleLambda ρ σ ≤ 2 ^ (-k) :=
    minFeasibleLambda_le_of_isFeasible ρ σ hρ_feas
  rcases lt_or_eq_of_le (minFeasibleLambda_nonneg ρ σ) with hpos | hzero
  · -- Positive optimum: the standard −log₂ flip.
    exact conditionalMinEntropyReal_le_of_minFeasibleLambda_pos_le_pow_neg_k
      ρ σ k hpos hρ_le
  · -- Boundary: minFeasibleLambda ρ σ = 0 ⇒ ρ has zero total weight ⇒ a positive-weight
    -- component is the zero state, whose floor gives k ≤ 0 = value.
    have hval0 : conditionalMinEntropyReal ρ σ = 0 := by
      unfold conditionalMinEntropyReal; rw [← hzero]; simp
    rw [hval0]
    -- ρ has zero total weight.
    have hρ_weight_zero : ∑ x : X, (ρ.stateMap x).trace = 0 := by
      by_contra hne
      have hpos_w : 0 < ∑ x : X, (ρ.stateMap x).trace :=
        lt_of_le_of_ne (Finset.sum_nonneg fun x _ => (ρ.stateMap x).trace_nonneg)
          (Ne.symm hne)
      have hfeasρ : hasFeasibleLambda ρ σ := ⟨_, hρ_feas⟩
      have := minFeasibleLambda_pos_of_hasFeasibleLambda_of_weight_pos ρ σ hpos_w hfeasρ
      rw [← hzero] at this; exact lt_irrefl 0 this
    -- The mixture trace identity: 0 = ∑_z p_z · weight(comp z).
    have hblock : ∀ x : X, (ρ.stateMap x).trace
        = ∑ z, p z * ((comp z).stateMap x).trace := by
      intro x
      have hx := hmix x
      unfold SubDensityOp.trace
      rw [hx, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    have htrace_id : (0 : ℝ) = ∑ z, p z * (∑ x : X, ((comp z).stateMap x).trace) := by
      rw [← hρ_weight_zero]
      simp_rw [hblock, Finset.mul_sum]
      rw [Finset.sum_comm]
    -- Some component z₀ has positive weight p z₀ but zero state-weight.
    obtain ⟨z₀, hz₀_pos⟩ : ∃ z, 0 < p z := by
      by_contra hnone
      push Not at hnone
      have : ∑ z, p z = 0 := by
        apply Finset.sum_eq_zero
        intro z _
        exact le_antisymm (hnone z) (hp_nonneg z)
      rw [hp_sum] at this; norm_num at this
    have hcomp_w_zero : ∑ x : X, ((comp z₀).stateMap x).trace = 0 := by
      have hterm_nonneg : ∀ z, 0 ≤ p z * (∑ x : X, ((comp z).stateMap x).trace) :=
        fun z => mul_nonneg (hp_nonneg z)
          (Finset.sum_nonneg fun x _ => ((comp z).stateMap x).trace_nonneg)
      have hz₀_term : p z₀ * (∑ x : X, ((comp z₀).stateMap x).trace) = 0 := by
        have hsum0 : ∑ z, p z * (∑ x : X, ((comp z).stateMap x).trace) = 0 :=
          htrace_id.symm
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hterm_nonneg z)).mp hsum0
          z₀ (Finset.mem_univ z₀)
      rcases mul_eq_zero.mp hz₀_term with hp0 | hw0
      · exact absurd hp0 (ne_of_gt hz₀_pos)
      · exact hw0
    -- The floor for z₀ gives k ≤ value(comp z₀) ≤ 0.
    exact le_trans (hfloor z₀)
      (conditionalMinEntropyReal_le_zero_of_weight_zero (comp z₀) σ hcomp_w_zero)

/-- A probability mixture inherits a common signed smooth component floor when its smoothing set
is bounded above. -/
theorem smoothMinEntropyReal_mixture_ge_inf_component
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    {Z : Type*} [Fintype Z]
    (ε : ℝ) (hε : 0 ≤ ε)
    (p : Z → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1)
    (comp : Z → CQState X n) (ρ : CQState X n)
    (hmix : ∀ x : X, (ρ.stateMap x).toOp = ∑ z, (p z : ℂ) • ((comp z).stateMap x).toOp)
    (σ : SubDensityOp n) (k : ℝ)
    (hbdd : BddAbove (Set.ofPred (isInSmoothedSetReal ε ρ σ)))
    (hfeas_comp_ball : ∀ z, ∀ ρ' : CQState X n,
      CQState.purifiedDistance (comp z) ρ' ≤ ε → hasFeasibleLambda ρ' σ)
    (hfloor : ∀ z, k ≤ smoothMinEntropyReal ε (comp z) σ) :
    k ≤ smoothMinEntropyReal ε ρ σ := by
  classical
  have hZne : Nonempty Z := by
    rcases isEmpty_or_nonempty Z with hE | hN
    · exfalso; rw [Finset.sum_of_isEmpty] at hp_sum; norm_num at hp_sum
    · exact hN
  -- It suffices to prove `k ≤ smoothMinEntropyReal ε ρ σ + ν` for every ν > 0.
  refine le_of_forall_pos_le_add (fun ν hν => ?_)
  -- Per-component near-optimal approximants at level `k − ν`.
  have hex : ∀ z, ∃ ρ' : CQState X n,
      CQState.purifiedDistance (comp z) ρ' ≤ ε ∧
        k - ν ≤ conditionalMinEntropyReal ρ' σ := by
    intro z
    exact smoothMinEntropyReal_exists_approx ε hε (comp z) σ (k - ν)
      (by linarith [hfloor z])
  choose comp' hd he using hex
  -- Assemble the mixture approximant ρ' = Σ_z p_z · comp'_z.
  set ρ' : CQState X n := finMix p hp_nonneg hp_sum comp' with hρ'_def
  have hρ'_mix : ∀ x : X, (ρ'.stateMap x).toOp
      = ∑ z, (p z : ℂ) • ((comp' z).stateMap x).toOp := fun x =>
    finMix_stateMap_toOp p hp_nonneg hp_sum comp' x
  -- (i) the unsmoothed floor on the approximant.
  have hfeas' : ∀ z, hasFeasibleLambda (comp' z) σ := fun z =>
    hfeas_comp_ball z (comp' z) (hd z)
  have hfloor' : k - ν ≤ conditionalMinEntropyReal ρ' σ :=
    conditionalMinEntropyReal_mixture_ge_inf_component
      p hp_nonneg hp_sum comp' ρ' hρ'_mix σ (k - ν) hfeas' he
  -- (ii) the smoothing transfer: ρ' is in the ε-ball of ρ.
  have hpd : CQState.purifiedDistance ρ ρ' ≤ ε :=
    CQState.purifiedDistance_mixture_le_max p hp_nonneg hp_sum comp comp' ρ ρ'
      hmix hρ'_mix hε hd
  -- Combine via the sSup approximation closure.
  have hk_le : k - ν ≤ smoothMinEntropyReal ε ρ σ :=
    smoothMinEntropyReal_ge_of_hmin_approx_of_bddAbove ε ρ σ (k - ν) ρ' hbdd hpd hfloor'
  linarith

end InfoTheory.SmoothMinEntropy
