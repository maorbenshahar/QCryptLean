import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.ClassicalAnnounceKernel
import QCryptLean.QKD.BB84.Engine.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash

/-!
# The BB84 classical announcement `(syn, evTag)` costs `leakEC + ℓEV` bits

The protocol announces two classical messages that are deterministic functions of Alice's key string
`x : KeyBitString n peSel`: the error-correction syndrome `ec.syndrome x` (`leakEC` bits) and the
error-verification tag `verificationTag n ℓEV peSel t x` (`ℓEV` bits, computed under the uniformly
drawn and publicly announced error-verification seed `t`). This file builds the announce kernel for
that pair and charges it against the smooth conditional min-entropy of `x`.

The entropy statement is the one-sided classical-side-information bound of Renner 2005
(arXiv:quant-ph/0512258v2) Lemma 3.1.10 / Cor. 3.1.11, `H_min^ε(X | E C) ≥ H_min^ε(X | E) − log|C|`,
available as `InfoTheory.SmoothMinEntropy.smoothMinEntropy_tensorLeftKernel_ge_sub_log`
(`ClassicalAnnounceKernel.lean`). All that is needed here is the *domination constant* of the
BB84 kernel.

## Register orientation

The charge is taken in the **announcements-high** orientation: the announced register sits in the
high digits of the quantum register, `d_C * (eveDim · dimR)`, which is the layout the pass-support
bridge needs (its digit string is fixed by `pePassOutIndex`, `SiftedPEAnnounce.lean`). That is
why the kernel used here is `CQState.tensorLeftKernel` against the reference
`SubDensityOp.maxMixedTensor`, not the `…RightKernel…` / `tensorMaxMixed` pair: `Op.tensor A B`
places `A` in the high digit, so the right kernel would leave the announcements low.

## The domination constant

`smoothMinEntropy_tensorRightKernel_ge_sub_log` charges `log₂ c`, where `c` is any constant with
`K x ≼ c · (1/d_C) · 1`. The register the kernel lives on is

`d_C = 2 ^ leakEC * (|S_EV| * 2 ^ ℓEV)`,   `S_EV = KeyHashSeed n ℓEV peSel`,

and the generic bound `opLe_toOp_dim_smul_maxMixed` yields only `c = d_C`, i.e. a charge of
`leakEC + ℓEV + log₂|S_EV|` bits. That is not the cost of the announcement: `|S_EV| = 2 ^
(ℓEV·n_K)`, so the generic route charges `ℓEV·n_K` extra bits, which the protocol's key-rate budget
(`Budgets.lean`) does not fund.

`opLe_uniformSeededAnnounce_smul_maxMixed` is the structured bound that gives the true constant.
The seed register carries the *uniform* distribution and the tag is a function of the seed, so the
seed-and-tag factor is `(1/|S|)·Π(g)` for the rank-`|S|` graph projector
`Π(g) = ∑_j |j⟩⟨j| ⊗ |g j⟩⟨g j| ≼ 1`, whence

`(1/|S|)·Π(g) ≼ (1/|S|)·1 = 2 ^ ℓEV · (1 / (|S|·2 ^ ℓEV)) · 1`,

i.e. the seed dimension contributes `1` and only the tag dimension `2 ^ ℓEV` is charged. Tensoring
with the syndrome projector's `2 ^ leakEC` gives `c = 2 ^ (leakEC + ℓEV)`, a charge of exactly
`leakEC + ℓEV` bits. This constant is tight: the kernel's largest eigenvalue is exactly
`1/|S| = c / d_C`.

## Funding

The protocol's key-rate condition (`Budgets.lean`) prices
`2·leakEC·log 2 + 2·ℓEV·log 2` on its cost side, and the leftover-hashing cap consumes an entropy
loss doubled, so the one-sided `(leakEC + ℓEV)`-bit charge proved here is exactly funded, while the
generic `d_C` route is not.

## Main definitions
- `seedGraphProj`: the graph projector `∑_j |j⟩⟨j| ⊗ |g j⟩⟨g j|` on a seed ⊗ tag register.
- `uniformSeededAnnounce`: the uniformly seeded announcement block `(1/|S|)·Π(g)`.
- `stdProj`: the computational-basis projector `|i⟩⟨i|` as a normalised sub-density operator.
- `bb84AnnounceKernel`: the `(syn, seed, evTag)` announce kernel.

## Main statements
- `opLe_uniformSeededAnnounce_smul_maxMixed`: the structured domination, constant `2 ^ ℓEV`.
- `opLe_bb84AnnounceKernel_smul_maxMixed`: the kernel's domination, constant `2 ^ (leakEC + ℓEV)`.
- `bb84_smoothMinEntropy_announce_ge_sub_leak`: the resulting `leakEC + ℓEV` bit charge.

References: Renner 2005 (arXiv:quant-ph/0512258v2) Lemma 3.1.10, Cor. 3.1.11; Nahar, Tupkary, Zhao,
Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C and App. B Eq. (B17); Tomamichel 2016 §6.1–6.2.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open QKD.BB84
open QKD.BB84.Engine
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The uniformly seeded announcement block -/

/-- **The graph projector of a seed-indexed announcement.**

On the register `seed ⊗ tag` of dimension `S * m`, `seedGraphProj g = ∑_j |j⟩⟨j| ⊗ |g j⟩⟨g j|`:
the rank-`S` orthogonal projector onto the graph of `g`. It is the un-normalised carrier of an
announcement whose value `g j` is a deterministic function of the announced seed `j`. -/
def seedGraphProj {S m : ℕ} (g : Fin S → Fin m) : Op (S * m) :=
  ∑ j : Fin S,
    Op.tensor (stdKet S j * (stdKet S j).dag) (stdKet m (g j) * (stdKet m (g j)).dag)

/-- The graph projector is diagonal in the computational basis of `seed ⊗ tag`, supported exactly
on the graph `{(j, g j)}`. -/
lemma seedGraphProj_eq_diagonal {S m : ℕ} (g : Fin S → Fin m) :
    seedGraphProj g =
      Matrix.diagonal fun k =>
        if (finProdFinEquiv.symm k).2 = g (finProdFinEquiv.symm k).1 then (1 : ℂ) else 0 := by
  ext k l
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨c, d⟩, rfl⟩ := finProdFinEquiv.surjective l
  rw [seedGraphProj, Matrix.sum_apply]
  simp only [Op_tensor_apply_finProd, Equiv.symm_apply_apply, ket_mul_bra_apply, Ket.dag_vec,
    stdKet_apply, Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
    apply_ite (starRingEnd ℂ), map_one, map_zero]
  rw [Finset.sum_eq_single a]
  · by_cases hac : a = c
    · subst hac
      by_cases hbd : b = d
      · subst hbd
        by_cases hg : g a = b
        · simp [hg]
        · have hg' : ¬ (b = g a) := fun h => hg h.symm
          simp [hg, hg']
      · by_cases h1 : g a = b <;> by_cases h2 : g a = d <;> simp_all
    · simp [hac]
  · intro j _ hj
    simp only [hj, ite_false, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The graph projector is positive semidefinite. -/
lemma seedGraphProj_posSemidef {S m : ℕ} (g : Fin S → Fin m) :
    (seedGraphProj g).PosSemidef := by
  rw [seedGraphProj_eq_diagonal, Matrix.posSemidef_diagonal_iff]
  intro i
  split_ifs
  · exact zero_le_one
  · exact le_refl 0

/-- `Π(g) ≼ 1`: the graph projector is a projector, so it is dominated by the identity **without**
paying its rank. This is the step that keeps the seed dimension out of the announce charge. -/
lemma opLe_seedGraphProj_one {S m : ℕ} (g : Fin S → Fin m) :
    opLe (seedGraphProj g) (1 : Op (S * m)) := by
  apply opLe_of_posSemidef_sub
  rw [seedGraphProj_eq_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub,
    Matrix.posSemidef_diagonal_iff]
  intro i
  split_ifs
  · simp
  · simp

/-- The graph projector has trace `S`: one basis vector `|j, g j⟩` per seed. -/
lemma seedGraphProj_trace {S m : ℕ} (g : Fin S → Fin m) :
    (seedGraphProj g).trace = (S : ℂ) := by
  rw [seedGraphProj_eq_diagonal, Matrix.trace_diagonal,
    ← Equiv.sum_comp (finProdFinEquiv (m := S) (n := m))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **The uniformly seeded announcement block.**

`(1/|S|) ∑_j |j⟩⟨j| ⊗ |g j⟩⟨g j|`: the announced seed is uniform on `Fin S`, and conditioned on it
the announced value is the deterministic `g j`. This is the joint `(seed, tag)` announcement of the
error-verification step; its normalisation is checked in `uniformSeededAnnounce_trace`. -/
def uniformSeededAnnounce {S m : ℕ} (g : Fin S → Fin m) : SubDensityOp (S * m) where
  toOp := (Complex.ofReal (1 / (S : ℝ))) • seedGraphProj g
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, (seedGraphProj_posSemidef g).isHermitian]
    simp
  pos_semidef := by
    intro v
    rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg (by positivity)
      (posSemidef_re_quadraticForm_nonneg (seedGraphProj_posSemidef g) v)
  trace_le_one := by
    rw [Matrix.trace_smul, seedGraphProj_trace, smul_eq_mul, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    rcases Nat.eq_zero_or_pos S with hS | hS
    · simp [hS]
    · rw [one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hS.ne')]

@[simp] lemma uniformSeededAnnounce_toOp {S m : ℕ} (g : Fin S → Fin m) :
    (uniformSeededAnnounce g).toOp = (Complex.ofReal (1 / (S : ℝ))) • seedGraphProj g := rfl

/-- The uniformly seeded announcement block is normalised. -/
lemma uniformSeededAnnounce_trace {S m : ℕ} [NeZero S] (g : Fin S → Fin m) :
    (uniformSeededAnnounce g).trace = 1 := by
  change ((Complex.ofReal (1 / (S : ℝ))) • seedGraphProj g).trace.re = 1
  rw [Matrix.trace_smul, seedGraphProj_trace, smul_eq_mul, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.ofReal_re, one_div,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne S))]

/-- **The structured announce constant: `2 ^ ℓEV`, not `|S| · 2 ^ ℓEV`.**

A uniformly seeded announcement on `seed ⊗ tag` is dominated by `m` times the maximally mixed state
of the *joint* register, where `m` is the **tag** dimension alone. The seed factor is already
normalised on its own register and therefore contributes the constant `1`, exactly as recorded on
`opLe_toOp_dim_smul_maxMixed`; the generic bound there would give `S · m` instead.

`(1/S)·Π(g) ≼ (1/S)·1 = m · (1/(S·m))·1`, using `Π(g) ≼ 1` (`opLe_seedGraphProj_one`). -/
lemma opLe_uniformSeededAnnounce_smul_maxMixed {S m : ℕ} [NeZero (S * m)] (g : Fin S → Fin m) :
    opLe (uniformSeededAnnounce g).toOp
      ((Complex.ofReal (m : ℝ)) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (S * m))).toOp) := by
  have hSm : S * m ≠ 0 := NeZero.ne _
  have hS : (S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; simp at hSm)
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; simp at hSm)
  have hrhs :
      (Complex.ofReal (m : ℝ)) •
          (DensityOp.toSubDensityOp (DensityOp.maxMixed (S * m))).toOp
        = (Complex.ofReal (1 / (S : ℝ))) • (1 : Op (S * m)) := by
    rw [toSubDensityOp_maxMixed_toOp_eq, smul_smul]
    congr 1
    have hSC : (S : ℂ) ≠ 0 := by exact_mod_cast Complex.ofReal_ne_zero.mpr hS
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast Complex.ofReal_ne_zero.mpr hm
    push_cast
    field_simp
  rw [uniformSeededAnnounce_toOp, hrhs]
  exact opLe_smul_nonneg (by positivity) (opLe_seedGraphProj_one g)

/-! ## The computational-basis projector -/

/-- `|i⟩⟨i|`, the computational-basis projector, as a normalised sub-density operator. This is the
carrier of a deterministic classical announcement of the value `i`. -/
def stdProj (d : ℕ) (i : Fin d) : SubDensityOp d :=
  DensityOp.toSubDensityOp (DensityOp.fromPure (stdKet d i) (stdKet_braket_self i))

@[simp] lemma stdProj_toOp (d : ℕ) (i : Fin d) :
    (stdProj d i).toOp = stdKet d i * (stdKet d i).dag := rfl

@[simp] lemma stdProj_trace (d : ℕ) (i : Fin d) : (stdProj d i).trace = 1 :=
  toSubDensityOp_trace _

/-- The maximally mixed states of two registers tensor to the maximally mixed state of the joint
register. -/
lemma toSubDensityOp_maxMixed_tensor (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] :
    Op.tensor (DensityOp.toSubDensityOp (DensityOp.maxMixed a)).toOp
        (DensityOp.toSubDensityOp (DensityOp.maxMixed b)).toOp
      = (DensityOp.toSubDensityOp (DensityOp.maxMixed (a * b))).toOp := by
  rw [toSubDensityOp_maxMixed_toOp_eq, toSubDensityOp_maxMixed_toOp_eq,
    toSubDensityOp_maxMixed_toOp_eq, Op.smul_tensor_smul, Op.tensor_one]
  congr 1
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have hb : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne b)
  push_cast
  field_simp

/-! ## The BB84 announce kernel -/

/-- **The classical-announce kernel.**

Indexed by the classical secret `x : KeyBitString n peSel` (Alice's key string), the announced
block on the register `syn ⊗ (seed ⊗ evTag)` is

`|ec.syndrome x⟩⟨ec.syndrome x| ⊗ (1/|S_EV|) ∑_t |t⟩⟨t| ⊗ |verificationTag n ℓEV peSel t x⟩⟨…|`,

with the error-verification seed register `S_EV = KeyHashSeed n ℓEV peSel` indexed by
`Fintype.equivFin` (the same enumeration convention the protocol registers use, e.g.
`Concrete/Real.lean`).

Both messages are deterministic functions of the secret, which is why the free-ancilla seam
`smoothMinEntropy_le_condTensor_decoupled_ancilla` does not apply to them and the announce kernel
`smoothMinEntropy_tensorRightKernel_ge_sub_log` does.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C. -/
def bb84AnnounceKernel {n leakEC : ℕ} (ℓEV : ℕ) (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (x : KeyBitString n peSel) :
    SubDensityOp (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV)) :=
  (stdProj (2 ^ leakEC) (ec.syndrome x)).tensor
    (uniformSeededAnnounce fun j =>
      verificationTag n ℓEV peSel
        ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm j) x)

/-- The announce kernel is normalised on every value of the secret: a projector tensored with a
uniform mixture of projectors. -/
lemma bb84AnnounceKernel_trace {n leakEC : ℕ} (ℓEV : ℕ) (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (x : KeyBitString n peSel) :
    (bb84AnnounceKernel ℓEV peSel ec x).trace = 1 := by
  rw [bb84AnnounceKernel, SubDensityOp.tensor_trace, stdProj_trace,
    uniformSeededAnnounce_trace, mul_one]

/-- **The announce kernel is dominated at `c = 2 ^ (leakEC + ℓEV)`.**

The syndrome projector contributes its register dimension `2 ^ leakEC`
(`opLe_toOp_dim_smul_maxMixed`, tight for a deterministic classical message), and the uniformly
seeded `(seed, evTag)` block contributes only the tag dimension `2 ^ ℓEV`
(`opLe_uniformSeededAnnounce_smul_maxMixed`) — **not** `|S_EV| · 2 ^ ℓEV`.

Via `smoothMinEntropy_tensorRightKernel_ge_sub_log` this is a charge of exactly `leakEC + ℓEV`
bits, which the protocol's key-rate budget funds. -/
lemma opLe_bb84AnnounceKernel_smul_maxMixed {n leakEC : ℕ} (ℓEV : ℕ) (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (x : KeyBitString n peSel) :
    opLe (bb84AnnounceKernel ℓEV peSel ec x).toOp
      ((Complex.ofReal ((2 : ℝ) ^ (leakEC + ℓEV))) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed
          (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV)))).toOp) := by
  set S := Fintype.card (KeyHashSeed n ℓEV peSel) with hSdef
  set g : Fin S → Fin (2 ^ ℓEV) := fun j =>
    verificationTag n ℓEV peSel ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm j) x
    with hgdef
  -- The syndrome factor: a deterministic classical message on `Fin (2 ^ leakEC)`.
  have hP : opLe (stdProj (2 ^ leakEC) (ec.syndrome x)).toOp
      ((Complex.ofReal ((2 : ℝ) ^ leakEC)) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (2 ^ leakEC))).toOp) := by
    have h := opLe_toOp_dim_smul_maxMixed (stdProj (2 ^ leakEC) (ec.syndrome x))
    rwa [show ((2 ^ leakEC : ℕ) : ℂ) = Complex.ofReal ((2 : ℝ) ^ leakEC) by push_cast; ring] at h
  -- The seed-and-tag factor: the structured bound, tag dimension only.
  have hU : opLe (uniformSeededAnnounce g).toOp
      ((Complex.ofReal ((2 : ℝ) ^ ℓEV)) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (S * 2 ^ ℓEV))).toOp) := by
    have h := opLe_uniformSeededAnnounce_smul_maxMixed g
    rwa [show (((2 ^ ℓEV : ℕ) : ℝ) : ℂ) = Complex.ofReal ((2 : ℝ) ^ ℓEV) by push_cast; ring] at h
  have hmmA :
      ((Complex.ofReal ((2 : ℝ) ^ leakEC)) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (2 ^ leakEC))).toOp).PosSemidef :=
    (posSemidefOp_implies_mathlib
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (2 ^ leakEC))).toPosSemidefOp).smul
      (Complex.zero_le_real.mpr (by positivity))
  have hmmB :
      ((Complex.ofReal ((2 : ℝ) ^ ℓEV)) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (S * 2 ^ ℓEV))).toOp).PosSemidef :=
    (posSemidefOp_implies_mathlib
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (S * 2 ^ ℓEV))).toPosSemidefOp).smul
      (Complex.zero_le_real.mpr (by positivity))
  have htensor := opLe_tensor_psd (stdProj (2 ^ leakEC) (ec.syndrome x)).isHermitian hmmA
    (posSemidefOp_implies_mathlib (uniformSeededAnnounce g).toPosSemidefOp)
    hmmB.isHermitian hP hU
  have hrhs :
      Op.tensor
          ((Complex.ofReal ((2 : ℝ) ^ leakEC)) •
            (DensityOp.toSubDensityOp (DensityOp.maxMixed (2 ^ leakEC))).toOp)
          ((Complex.ofReal ((2 : ℝ) ^ ℓEV)) •
            (DensityOp.toSubDensityOp (DensityOp.maxMixed (S * 2 ^ ℓEV))).toOp)
        = (Complex.ofReal ((2 : ℝ) ^ (leakEC + ℓEV))) •
            (DensityOp.toSubDensityOp
              (DensityOp.maxMixed (2 ^ leakEC * (S * 2 ^ ℓEV)))).toOp := by
    rw [Op.smul_tensor_smul, toSubDensityOp_maxMixed_tensor, ← Complex.ofReal_mul]
    congr 2
    rw [pow_add]
  rw [hrhs] at htensor
  exact htensor

/-- **The classical-announce charge.**

Announcing the error-correction syndrome and the seeded error-verification tag into Eve's
conditioning register costs at most `leakEC + ℓEV` bits of smooth conditional min-entropy of
Alice's key string, at the **same** smoothing radius `ε`:

`H_min^ε(E : X) ≤ H_min^ε(syn, seed, evTag, E : X) + ofReal (leakEC + ℓEV)`,

with the announced registers in the **high** digits of the conditioning register
(`CQState.tensorLeftKernel`), the layout the pass-support bridge consumes.

This is Renner 2005 (arXiv:quant-ph/0512258v2) Lemma 3.1.10 / Cor. 3.1.11 — the one-sided
`log|C|` charge for classical side information that is a function of the secret — instantiated at
this announcement through `smoothMinEntropy_tensorLeftKernel_ge_sub_log`. It is **half** the
`2·log₂ d_R` a free quantum register extension of the same size would cost
(`smoothMinEntropy_extension_freeRef_ge_marginal_sub_twice_log_dim_sameRadius`), and it does not
pay the error-verification seed dimension at all.

The additive extended-entropy comparison also applies when the smoothing ball contains zero. -/
theorem bb84_smoothMinEntropy_announce_ge_sub_leak
    {n leakEC dE : ℕ} [NeZero dE] (ℓEV : ℕ) (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC)
    (ε : ℝ)
    (ρ : CQState (KeyBitString n peSel) dE) (σ : SubDensityOp dE) :
    smoothMinEntropy ε ρ σ ≤
      smoothMinEntropy ε (ρ.tensorLeftKernel (bb84AnnounceKernel ℓEV peSel ec))
        (σ.maxMixedTensor
          (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV))) +
        ENNReal.ofReal ((leakEC : ℝ) + (ℓEV : ℝ)) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hcharge : Real.log ((2 : ℝ) ^ (leakEC + ℓEV)) / Real.log 2 = (leakEC : ℝ) + (ℓEV : ℝ) := by
    rw [Real.log_pow]
    push_cast
    field_simp
  have hc : (1 : ℝ) ≤ (2 : ℝ) ^ (leakEC + ℓEV) := one_le_pow₀ one_le_two
  have h := smoothMinEntropy_tensorLeftKernel_ge_sub_log ε ρ σ
    (bb84AnnounceKernel ℓEV peSel ec) hc
    (bb84AnnounceKernel_trace ℓEV peSel ec)
    (opLe_bb84AnnounceKernel_smul_maxMixed ℓEV peSel ec)
  rwa [hcharge] at h

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
