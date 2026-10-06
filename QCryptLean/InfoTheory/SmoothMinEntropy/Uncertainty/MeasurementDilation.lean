import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.BipartiteMinMax
import QCryptLean.InfoTheory.SmoothMinEntropy.DataProcessing.IsometryConjugation
import QCryptLean.Quantum.TensorProducts.PartialTrace
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Order
import QCryptLean.Quantum.Matrix.Reindex

/-!
# Measurement (Stinespring) dilations and the `W = U Vᴴ` conjugation — rank-1 projective case

The operator-algebra heart of the Tomamichel–Renner smooth entropic-uncertainty proof
(arXiv:1009.2015, `tr.tex:285–359`), specialized to the **rank-1 projective** measurements that the
finite-key BB84 arc (TLGR, arXiv:1103.4130) actually uses.

## References

The operator identities below use Tomamichel–Renner, arXiv:1009.2015, `tr.tex:285–359`.
The overlap constant `c := max_{x,z} |⟨x|z⟩|²` (`eqn:overlap`, `tr.tex:150–151`) is also
Tomamichel's textbook definition: arXiv:1504.00233, `apps.tex:174`, `\label{eq:defc}`,
`c = max_{x,y} |⟨φ_x|ϑ_y⟩|²`.

Theorem `th:ur` in arXiv:1504.00233, `apps.tex:183–216` (label at `apps.tex:185`), gives the
uncertainty relation via CPTP data processing. That proof differs from the explicit `U`, `V`,
`W` operator algebra in Tomamichel–Renner's `eqn:mo6`, `eqn:mo8`, `eqn:mo9`, and `eqn:mo10`.

## What TR does (`tr.tex:285–293`, ε = 0, pure case)

> *"It will be helpful to describe the two measurements in the Stinespring dilation picture as
> isometries followed by a partial trace. Let `U` be the isometry from A to A, X and X′ given by
> `U := Σ_x |x⟩ ⊗ |x⟩ ⊗ √M_x`. The isometry stores two copies of the measurement outcome in the
> registers X and X′ and the post-measurement state in A. Analogously,
> `V := Σ_z |z⟩ ⊗ |z⟩ ⊗ √N_z`."*

The proof then applies the **partial isometry** `W := U Vᴴ` (`tr.tex:335`) followed by a partial
trace over X′ and A, and reduces the smooth min-entropy chain to the operator implication
`eqn:mo6` (`tr.tex:321–326`)

  `2^{-λ} · 1_Z ⊗ σ_{Z′AB} ≥ ρ_{ZZ′AB}  ⟹  2^{-λ} · c · 1_X ⊗ σ_B ≥ ρ_{XB}` ,

whose engine is the conjugation-and-partial-trace computation `eqn:mo8/mo9` (`tr.tex:344–359`)

  `Tr_{X′A}( W (1_Z ⊗ σ_{Z′AB}) Wᴴ )
      = Σ_{x,z} |x⟩⟨x| ⊗ ⟨z| Tr_A( √N_z M_x √N_z σ_{Z′AB} ) |z⟩
      ≤ c · 1_X ⊗ σ_B` ,

using the pointwise operator bound `√N_z M_x √N_z = |√N_z √M_x|² ≤ c · 1_A` (`tr.tex:356–358`),
where `c := max_{x,z} ‖√M_x √N_z‖²` (`eqn:overlap`; see
arXiv:1504.00233, `apps.tex:174`, `\label{eq:defc}`) and `q := log₂ (1/c)`.

## Rank-1 projective scope (honest boundary)

A **rank-1 projective** measurement in an orthonormal basis `{|x⟩}` has POVM elements the rank-1
projectors `M_x = |x⟩⟨x|`, for which `√M_x = M_x` (a projector is its own positive square root).
This file therefore works throughout with the projectors directly and never invokes a matrix square
root: the dilation isometry is `U := Σ_x |x⟩ ⊗ |x⟩ ⊗ |x⟩⟨x|`. In this case the overlap constant is
exactly the basis overlap `c = max_{x,z} |⟨x|z⟩|²` (for BB84's mutually-unbiased pair, `c = 1/2` per
round; this instantiation is not stated here), and the pointwise bound sharpens to
`√N_z M_x √N_z = |⟨x|z⟩|² · |z⟩⟨z| ≤ c · 1_A` (`sqrtN_M_sqrtN_opLe_overlapConst_smul_one`).

**Scope: rank-one projective measurements.** TLGR's finite-key BB84 proof needs only
the two projective key/check bases; the general-POVM dilation (with a genuine `CFC.sqrt √M_x`) is
a different construction. The `Naimark` general-POVM
isometry
(`NaimarkDilation.lean`, one outcome register) is a different construction and is not reused.

## Operators on the dilated global states

Every operator here lives on the coherent dilated registers
(`X ⊗ X′ ⊗ A ⊗ B`, `Z ⊗ Z′ ⊗ A ⊗ B`); the measurement enters only as data processing (the
`W`-conjugation + partial trace) on top of the global state, never as a measured classical–quantum
duality. The `mo6` transport (`measDilation_mo6_transport`) is stated as a Löwner-order implication
between operators on those dilated registers, so it composes with the pure-state marginals supplied
by the ε = 0 core without any CQ object appearing here.

## Layering

* **Object layer.** `RankOneProjectiveBasis`, the projectors `proj`, the
  `proj_isHermitian` / `proj_posSemidef` / `proj_idem` / completeness facts, and the dilation
  isometry `dilationIso` with its certificate `dilationIso_isometry` (`Uᴴ U = 1`).
* **Partial-isometry layer.** `partialIsometryW := U Vᴴ` and
  `partialIsometryW_dagger_mul_self_eq` (`Wᴴ W = V Vᴴ`), the identity the TR chain consumes at
  `tr.tex:335`.
* **Overlap-bound layer.** The rank-1 pointwise operator inequality
  `sqrtN_M_sqrtN_opLe_overlapConst_smul_one` — the mathematically load-bearing `eqn:mo9` input —
  the overlap constant `overlapConst` with `overlapConst_nonneg`, and the derived preparation
  quality `preparationQuality` (`q = −log₂ c`).
* **Transport layer.** The `mo6` feasibility transport `measDilation_mo6_transport`,
  from the positive-map monotonicity of the conjugation + partial-trace map (`measConjTraceMap`),
  and its instance `measDilation_mo6`, whose reference bound
  `measConjTraceMap_one_tensor_reference_opLe` (`eqn:mo8/mo9`) is the explicit
  `Tr_{X′A}`-of-`W`-conjugation identity `measConjTraceMap_one_tensor_reference_eq` followed by
  the overlap domination.

The entropy-level consumers of this file are `PureCoreUncertainty.lean` (the recovery identity
`eqn:mo10`) and `MeasurementTransport.lean` / `SmoothUncertaintyRelation.lean` (the `D_max` and
smooth-min-entropy transports).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## Rank-1 projective measurement bases and their projectors
-/

/-- A **rank-1 projective measurement** on a `d`-dimensional system: an orthonormal basis `{|x⟩}` of
`ℂ^d`. The associated POVM elements are the rank-1 projectors `M_x = |x⟩⟨x|` (`proj`), for which
`√M_x = M_x`, so the TR dilation can use the projectors directly (see the module docstring). -/
structure RankOneProjectiveBasis (d : ℕ) where
  /-- The basis vectors `|x⟩`, indexed by the outcome `x`. -/
  vec : Fin d → Ket d
  /-- Orthonormality `⟨x|x'⟩ = δ_{x,x'}`. -/
  orthonormal : ∀ i j, (vec i).dag * (vec j) = if i = j then 1 else 0
  /-- Completeness `Σ_x |x⟩⟨x| = 1` (the resolution of the identity). -/
  complete : ∑ i, vec i * (vec i).dag = 1

namespace RankOneProjectiveBasis

variable {d : ℕ}

/-- The rank-1 projector `M_x = |x⟩⟨x|`, the POVM element of outcome `x`. In the rank-1 projective
case this equals its own positive square root `√M_x`, so it plays both roles in the TR dilation. -/
def proj (P : RankOneProjectiveBasis d) (x : Fin d) : Op d :=
  P.vec x * (P.vec x).dag

/-- `M_x` is Hermitian: `(|x⟩⟨x|)ᴴ = |x⟩⟨x|`. -/
lemma proj_isHermitian (P : RankOneProjectiveBasis d) (x : Fin d) :
    (P.proj x).IsHermitian := by
  unfold proj Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, ket_mul_bra_apply, Ket.dag_vec, RCLike.star_def,
    map_mul, Complex.conj_conj, mul_comm]

/-- `M_x` is idempotent: `|x⟩⟨x| · |x⟩⟨x| = |x⟩⟨x|`, using `⟨x|x⟩ = 1`. This is the identity that
lets a projector serve as its own square root in the rank-1 case. -/
lemma proj_idem (P : RankOneProjectiveBasis d) (x : Fin d) :
    P.proj x * P.proj x = P.proj x := by
  unfold proj
  rw [ketbra_mul_ketbra, P.orthonormal x x, ite_eq_left rfl, one_smul]

/-- **Orthonormality in trace form:** `Tr(|x⟩⟨x'|) = ⟨x'|x⟩ = δ_{x,x'}`. -/
lemma trace_vec_ketbra (P : RankOneProjectiveBasis d) (x x' : Fin d) :
    (P.vec x * (P.vec x').dag).trace = if x = x' then (1 : ℂ) else 0 := by
  have ho := P.orthonormal x' x
  rw [bra_mul_ket_eq] at ho
  simp only [Ket.dag_vec, starRingEnd_apply] at ho
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, ket_mul_bra_apply, Ket.dag_vec, starRingEnd_apply]
  rw [Finset.sum_congr rfl (fun i _ => mul_comm ((P.vec x).vec i) (star ((P.vec x').vec i))), ho]
  by_cases h : x = x' <;> simp [h, eq_comm]

/-- The rank-1 projectors are unit-trace: `Tr |x⟩⟨x| = 1`. -/
@[simp] lemma proj_trace (P : RankOneProjectiveBasis d) (x : Fin d) : (P.proj x).trace = 1 := by
  rw [proj, P.trace_vec_ketbra x x, ite_eq_left rfl]

end RankOneProjectiveBasis

/-!
## The dilation isometry `U = Σ_x |x⟩ ⊗ |x⟩ ⊗ |x⟩⟨x|`

The three output registers are `X`, `X′` (two copies of the outcome) and `A` (the post-measurement
system), each of dimension `d`, so `U : ℂ^d → ℂ^(d·d·d)`. In the rank-1 case the third tensor factor
is the projector `|x⟩⟨x|`, and column-wise `U|x'⟩ = |x'⟩ ⊗ |x'⟩ ⊗ |x'⟩` (the "diagonal copy"): each
term `|x⟩ ⊗ |x⟩ ⊗ (|x⟩⟨x|)` is the rectangular outer product `(|x⟩⊗|x⟩⊗|x⟩) · ⟨x|`.
-/

namespace RankOneProjectiveBasis

variable {d : ℕ}

/-- The "diagonal copy" ket `|x⟩ ⊗ |x⟩ ⊗ |x⟩ ∈ ℂ^(d·d·d)` appearing as the range vector of the
`x`-th term of the dilation isometry. -/
def dilationKet (P : RankOneProjectiveBasis d) (x : Fin d) : Ket (d * d * d) :=
  P.vec x ⊗ P.vec x ⊗ P.vec x

/-- The dilation kets are orthonormal: `⟨x'|x⟩³ = δ_{x',x}`, since the inner product of a triple
tensor factors as the cube of the basis inner product and `δ³ = δ`. -/
lemma dilationKet_inner (P : RankOneProjectiveBasis d) (x' x : Fin d) :
    (P.dilationKet x').dag * (P.dilationKet x) = if x' = x then 1 else 0 := by
  unfold dilationKet
  rw [Ket.dag_tensor, Ket.dag_tensor, bra_tensor_mul_ket_tensor, bra_tensor_mul_ket_tensor,
    P.orthonormal x' x]
  by_cases h : x' = x <;> simp [h]

/-- **The measurement dilation isometry** `U := Σ_x |x⟩_X ⊗ |x⟩_{X′} ⊗ |x⟩⟨x|_A`
(`tr.tex:287–288`, rank-1 case). Explicit rectangular matrix `ℂ^d → ℂ^(d·d·d)`: column `j`, row `i`
is `Σ_x (|x⟩⊗|x⟩⊗|x⟩)_i · conj (|x⟩_j)`, i.e. the sum of the rectangular outer products
`(dilationKet x) · ⟨x|`. -/
def dilationIso (P : RankOneProjectiveBasis d) : Matrix (Fin (d * d * d)) (Fin d) ℂ :=
  fun i j => ∑ x, (P.dilationKet x).vec i * (P.vec x).dag.vec j

/-- **Isometry certificate** `Uᴴ U = 1` (`tr.tex:288–289`, "the isometry stores two copies …").
The Gram matrix collapses via the ket-tensor inner product `⟨x'|x⟩³` and orthonormality `δ³ = δ`,
leaving `Σ_x |x⟩⟨x| = 1` by completeness. -/
theorem dilationIso_isometry (P : RankOneProjectiveBasis d) :
    (P.dilationIso)ᴴ * P.dilationIso = 1 := by
  ext c c'
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, dilationIso, Ket.dag_vec, star_sum, star_mul', star_star,
    starRingEnd_apply]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  have hinner : ∀ i j : Fin d,
      (∑ x, star ((P.dilationKet i).vec x) * (P.vec i).vec c
          * ((P.dilationKet j).vec x * star ((P.vec j).vec c')))
        = ((P.vec i).vec c * star ((P.vec j).vec c')) * (if i = j then 1 else 0) := by
    intro i j
    rw [← P.dilationKet_inner i j, bra_mul_ket_eq]
    simp only [Ket.dag_vec, starRingEnd_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [hinner, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hproj : ∀ i : Fin d,
      (P.vec i).vec c * star ((P.vec i).vec c') = (P.vec i * (P.vec i).dag) c c' := by
    intro i
    simp only [ket_mul_bra_apply, Ket.dag_vec, starRingEnd_apply]
  simp_rw [hproj]
  rw [← Matrix.sum_apply, P.complete]

/-!
## The overlap bound `√N_z M_x √N_z ≤ c · 1` (rank-1, `eqn:mo9` input)

The overlap constant `c := max_{x,z} |⟨x|z⟩|²` (`eqn:overlap`; see
arXiv:1504.00233, `apps.tex:174`, `\label{eq:defc}`, rank-1 form) and
the pointwise operator inequality that TR uses to pass from `eqn:mo8` to `eqn:mo9`
(`tr.tex:356–358`).
This is the mathematically load-bearing piece of the `mo8/mo9` step and is proved here in full.
-/

/-- A projector is dominated by the identity in the Löwner order: `|x⟩⟨x| ≤ 1_A`. Proved from
`1 - |x⟩⟨x| = (1 - |x⟩⟨x|)ᴴ (1 - |x⟩⟨x|)` (Hermitian idempotent), hence positive semidefinite. -/
lemma proj_opLe_one (P : RankOneProjectiveBasis d) (x : Fin d) : opLe (P.proj x) 1 := by
  apply opLe_of_posSemidef_sub
  have hH : (P.proj x)ᴴ = P.proj x := P.proj_isHermitian x
  have key : ((1 - P.proj x)ᴴ * (1 - P.proj x)) = 1 - P.proj x := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
    have expand : (1 - P.proj x) * (1 - P.proj x)
        = 1 - P.proj x - P.proj x + P.proj x * P.proj x := by noncomm_ring
    rw [expand, P.proj_idem]; abel
  have psd := Matrix.posSemidef_conjTranspose_mul_self (1 - P.proj x)
  rwa [key] at psd

/-- **Rank-1 collapse of `√N_z M_x √N_z`** (`tr.tex:356–357`, rank-1 form). With `√M_x = M_x`,
`√N_z = N_z`, the triple product collapses to a scalar multiple of the `Z`-projector:
`N_z M_x N_z = |⟨x|z⟩|² · |z⟩⟨z|`. -/
lemma sqrtN_M_sqrtN_eq_normSq_smul (P Q : RankOneProjectiveBasis d) (x z : Fin d) :
    Q.proj z * P.proj x * Q.proj z
      = Complex.ofReal (Complex.normSq ((P.vec x).dag * Q.vec z)) • Q.proj z := by
  have hsym : (Q.vec z).dag * P.vec x = star ((P.vec x).dag * Q.vec z) := by
    have h := Ket.inner_conj (P.vec x) (Q.vec z)
    simp only [Ket.inner] at h
    rw [h, star_star]
  unfold proj
  rw [ketbra_mul_ketbra, smul_mul_assoc, ketbra_mul_ketbra, smul_smul, hsym]
  congr 1
  rw [Complex.star_def, mul_comm]
  exact Complex.mul_conj _

/-- **The overlap constant** `c := max_{x,z} |⟨x|z⟩|²` for a pair of rank-1 projective bases `P`
(the `X`-basis `{|x⟩}`) and `Q` (the `Z`-basis `{|z⟩}`) on the same `d`-dimensional system
(`eqn:overlap`; see arXiv:1504.00233, `apps.tex:174`,
`\label{eq:defc}`; rank-1 form, where `‖√M_x √N_z‖² = |⟨x|z⟩|²`). It always satisfies
`0 < c ≤ 1` (`overlapConst_pos`, `overlapConst_le_one`); for a mutually-unbiased qubit pair it is
`1/2` and for the computational/Walsh–Hadamard pair on `n` qubits it is `2^{-n}`
(`ConcreteMeasurementBases.lean`). Requires `d > 0` for the maximum to range over a nonempty
index set. -/
def overlapConst [NeZero d] (P Q : RankOneProjectiveBasis d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun p : Fin d × Fin d => Complex.normSq ((P.vec p.1).dag * Q.vec p.2))

/-- Every basis overlap is bounded by the overlap constant: `|⟨x|z⟩|² ≤ c`. -/
lemma normSq_overlap_le_overlapConst [NeZero d] (P Q : RankOneProjectiveBasis d) (x z : Fin d) :
    Complex.normSq ((P.vec x).dag * Q.vec z) ≤ overlapConst P Q := by
  unfold overlapConst
  exact Finset.le_sup' (fun p : Fin d × Fin d => Complex.normSq ((P.vec p.1).dag * Q.vec p.2))
    (Finset.mem_univ (x, z))

/-- The overlap constant is nonnegative: `c = max_{x,z} |⟨x|z⟩|² ≥ 0`, since it is a maximum of
squared moduli over a nonempty index set. -/
lemma overlapConst_nonneg [NeZero d] (P Q : RankOneProjectiveBasis d) : 0 ≤ P.overlapConst Q := by
  obtain ⟨p, -⟩ := (Finset.univ_nonempty (α := Fin d × Fin d))
  exact le_trans (Complex.normSq_nonneg _) (P.normSq_overlap_le_overlapConst Q p.1 p.2)

/-- **A single overlap as a projector trace:** `|⟨x|z⟩|² = Tr(M_x N_z)`. The rank-1 collapse
`N_z M_x N_z = |⟨x|z⟩|² · N_z` (`sqrtN_M_sqrtN_eq_normSq_smul`) has trace `|⟨x|z⟩|²` on the right
(`proj_trace`) and `Tr(M_x N_z N_z) = Tr(M_x N_z)` on the left (cyclicity and `proj_idem`). -/
lemma normSq_overlap_eq_trace_proj_mul (P Q : RankOneProjectiveBasis d) (x z : Fin d) :
    (Complex.normSq ((P.vec x).dag * Q.vec z) : ℂ) = (P.proj x * Q.proj z).trace := by
  have h := congrArg Matrix.trace (P.sqrtN_M_sqrtN_eq_normSq_smul Q x z)
  rw [Matrix.trace_smul, smul_eq_mul, Q.proj_trace z, mul_one,
    Matrix.trace_mul_cycle (Q.proj z) (P.proj x) (Q.proj z), Q.proj_idem z,
    Matrix.trace_mul_comm] at h
  exact h.symm

/-- **Parseval for the overlaps:** `Σ_z |⟨x|z⟩|² = 1` for every fixed `x`. Each term is the
projector trace `Tr(M_x N_z)` (`normSq_overlap_eq_trace_proj_mul`), and the `z`-sum of the
`Z`-projectors is the identity (`complete`), leaving `Tr M_x = 1`. -/
lemma sum_normSq_overlap_eq_one (P Q : RankOneProjectiveBasis d) (x : Fin d) :
    ∑ z, Complex.normSq ((P.vec x).dag * Q.vec z) = 1 := by
  have hC : ((∑ z, Complex.normSq ((P.vec x).dag * Q.vec z) : ℝ) : ℂ) = 1 := by
    push_cast
    simp_rw [P.normSq_overlap_eq_trace_proj_mul Q x]
    rw [← Matrix.trace_sum, ← Matrix.mul_sum]
    simp only [proj]
    rw [Q.complete, Matrix.mul_one, P.trace_vec_ketbra x x, ite_eq_left rfl]
  exact_mod_cast hC

/-- **The overlap constant is positive:** `0 < c`. Two orthonormal bases of a nonzero-dimensional
space cannot be pointwise orthogonal: `Σ_z |⟨x|z⟩|² = 1` forces some overlap to be nonzero. -/
lemma overlapConst_pos [NeZero d] (P Q : RankOneProjectiveBasis d) : 0 < P.overlapConst Q := by
  obtain ⟨x⟩ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne d))
  by_contra hle
  push Not at hle
  have hzero : ∀ z : Fin d, Complex.normSq ((P.vec x).dag * Q.vec z) = 0 := fun z =>
    le_antisymm ((P.normSq_overlap_le_overlapConst Q x z).trans hle) (Complex.normSq_nonneg _)
  have := P.sum_normSq_overlap_eq_one Q x
  rw [Finset.sum_congr rfl (fun z _ => hzero z), Finset.sum_const_zero] at this
  exact zero_ne_one this

/-- **The overlap constant is at most one:** `c ≤ 1`. Each `|⟨x|z⟩|²` is one nonnegative term of
the Parseval sum `Σ_z |⟨x|z⟩|² = 1`. -/
lemma overlapConst_le_one [NeZero d] (P Q : RankOneProjectiveBasis d) : P.overlapConst Q ≤ 1 := by
  refine Finset.sup'_le _ _ (fun p _ => ?_)
  rw [← P.sum_normSq_overlap_eq_one Q p.1]
  exact Finset.single_le_sum
    (f := fun z => Complex.normSq ((P.vec p.1).dag * Q.vec z))
    (fun z _ => Complex.normSq_nonneg _) (Finset.mem_univ p.2)

/-- The **preparation quality** `q := −log₂ c = log₂ (1/c)` of an ordered pair of rank-1
projective bases, `c = overlapConst P Q` their overlap
(arXiv:1504.00233, `apps.tex:174`, `\label{eq:defc}`). It is the entropic deficit that
the Maassen–Uffink-type uncertainty relations of the cited textbook subtract on the right-hand side
(`apps.tex:187–189`, `\label{th:ur}`; `apps.tex:198`, `\label{eq:ucr-dual}`). For a
mutually-unbiased qubit pair `c = 1/2` and `q = 1`; more generally
`RankOneProjectiveBasis.overlapConst_computational_walsh` gives `c = 2^{-n}` and `q = n` on `n`
qubits. -/
noncomputable def preparationQuality [NeZero d] (P Q : RankOneProjectiveBasis d) : ℝ :=
  -Real.log (P.overlapConst Q) / Real.log 2

/-- **The preparation quality is nonnegative:** `q = log₂(1/c) ≥ 0`, because `c ≤ 1`
(`overlapConst_le_one`). So the uncertainty relations that subtract `q` never give away
entropy. -/
lemma preparationQuality_nonneg [NeZero d] (P Q : RankOneProjectiveBasis d) :
    0 ≤ P.preparationQuality Q := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine div_nonneg (neg_nonneg.mpr ?_) h2.le
  exact Real.log_nonpos (P.overlapConst_nonneg Q) (P.overlapConst_le_one Q)

/-- **The overlap operator bound** `√N_z M_x √N_z ≤ c · 1_A` (`tr.tex:356–358`, rank-1 form) — the
pointwise inequality behind `eqn:mo9`. Immediate from the rank-1 collapse
`N_z M_x N_z = |⟨x|z⟩|² |z⟩⟨z|`, the projector bound `|z⟩⟨z| ≤ 1`, and `|⟨x|z⟩|² ≤ c`. -/
theorem sqrtN_M_sqrtN_opLe_overlapConst_smul_one [NeZero d]
    (P Q : RankOneProjectiveBasis d) (x z : Fin d) :
    opLe (Q.proj z * P.proj x * Q.proj z)
      (Complex.ofReal (overlapConst P Q) • (1 : Op d)) := by
  rw [sqrtN_M_sqrtN_eq_normSq_smul]
  refine opLe_trans ?_ (opLe_smul_one_mono (normSq_overlap_le_overlapConst P Q x z))
  exact opLe_smul_nonneg (Complex.normSq_nonneg _) (Q.proj_opLe_one z)

end RankOneProjectiveBasis

/-!
## The partial isometry `W := U Vᴴ` and its `Wᴴ W = V Vᴴ` property

`W := U Vᴴ` (`tr.tex:335`), where `U` is the `X`-basis dilation and `V` the `Z`-basis dilation of
the same `d`-dimensional system. TR applies `W` (followed by a partial trace over `X′` and `A`) to
both sides of `eqn:mo6`. The chain consumes the partial-isometry identity `Wᴴ W = V Vᴴ`, which is
`V (Uᴴ U) Vᴴ = V Vᴴ` using the isometry certificate `Uᴴ U = 1`.
-/

namespace RankOneProjectiveBasis

variable {d : ℕ}

/-- **The partial isometry** `W := U Vᴴ` (`tr.tex:335`), mapping the `Z`-dilated register
`Z ⊗ Z′ ⊗ A` to the `X`-dilated register `X ⊗ X′ ⊗ A` (`P` is the `X`-basis, `Q` the `Z`-basis). -/
def partialIsometryW (P Q : RankOneProjectiveBasis d) :
    Matrix (Fin (d * d * d)) (Fin (d * d * d)) ℂ :=
  P.dilationIso * (Q.dilationIso)ᴴ

/-- **Partial-isometry identity** `Wᴴ W = V Vᴴ` (the fact `eqn:mo6`'s conjugation consumes,
`tr.tex:335`): `Wᴴ W = V (Uᴴ U) Vᴴ = V Vᴴ` by the isometry certificate `Uᴴ U = 1`
(`dilationIso_isometry`). -/
theorem partialIsometryW_dagger_mul_self_eq (P Q : RankOneProjectiveBasis d) :
    (P.partialIsometryW Q)ᴴ * (P.partialIsometryW Q) = Q.dilationIso * (Q.dilationIso)ᴴ := by
  unfold partialIsometryW
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (P.dilationIso)ᴴ, P.dilationIso_isometry, Matrix.one_mul]

end RankOneProjectiveBasis

/-!
## The `mo6` feasibility transport (`tr.tex:321–326`)

TR applies the partial isometry `W = U Vᴴ` followed by the partial trace over `X′` and `A` to both
sides of the Löwner inequality (`tr.tex:335–342`); the resulting conjugation-and-partial-trace map
is `measConjTraceMap`. On the dilated global registers `Z ⊗ Z′ ⊗ A ⊗ B` it is a positive,
real-homogeneous map (trap-1: all operators here are on the coherent dilated state), so it
transports the feasibility bound. The remaining computational content — `eqn:mo8/mo9`, the explicit
value of the map on `1_Z ⊗ σ` and its domination by `c · 1_X ⊗ σ_B` — is the single named open leaf
`measConjTraceMap_one_tensor_reference_opLe`.

The map traces out the non-adjacent factors `X′` (2nd) and `A` (3rd) of `X ⊗ X′ ⊗ A ⊗ B`, keeping
`X` (1st) and `B` (4th); `measTraceReindex` reorders to `X ⊗ B ⊗ (X′ ⊗ A)` so that the trailing
`X′ ⊗ A` block is removed by `partialTraceB`.
-/

/-- Quadratic form under a rectangular index reindex: `⟨v | (reindex e e A) | v⟩ = ⟨v∘e | A | v∘e⟩`.
Rectangular counterpart of the square `quadraticForm_reindex` (re-proved locally to avoid importing
the AEP module, a trap-5 dependency). -/
lemma quadraticForm_reindex_rect {n m : ℕ} (e : Fin n ≃ Fin m) (A : Op n) (v : Fin m → ℂ) :
    quadraticForm (Matrix.reindex e e A) v = quadraticForm A (v ∘ e) := by
  unfold quadraticForm
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  rw [dotProduct_comp_equiv_symm]
  rfl

/-- The Löwner order is preserved by a rectangular reindex (via `quadraticForm_reindex_rect`). -/
lemma opLe_reindex_rect {n m : ℕ} (e : Fin n ≃ Fin m) {A B : Op n} (h : opLe A B) :
    opLe (Matrix.reindex e e A) (Matrix.reindex e e B) := by
  intro v
  rw [quadraticForm_reindex_rect, quadraticForm_reindex_rect]
  exact h (v ∘ e)

/-- The reindex equivalence `X ⊗ X′ ⊗ A ⊗ B ≃ X ⊗ B ⊗ (X′ ⊗ A)` realizing the partial trace over
the non-adjacent registers `X′` and `A`: it reassociates the register block `X′ ⊗ A` (dimension
`d·d`) and swaps it past `B` (via `reorderTripartiteACB` on the tripartite `X ⊗ (X′A) ⊗ B`), leaving
`X′ ⊗ A` trailing for `partialTraceB`. -/
def measTraceReindex (d dB : ℕ) : Fin (d * d * d * dB) ≃ Fin (d * dB * (d * d)) :=
  (finCongr (by ring : d * d * d * dB = d * (d * d) * dB)).trans
    (reorderTripartiteACB d (d * d) dB)

/-- **The measurement conjugation-trace map** `Ξ(τ) := Tr_{X′A}( (W ⊗ 1_B) τ (W ⊗ 1_B)ᴴ )`
(`tr.tex:335–342`): conjugate by the partial isometry `W = U Vᴴ` (with the `B` spectator carried
along), then trace out `X′` and `A`. Concretely: conjugate `τ` on `Z ⊗ Z′ ⊗ A ⊗ B`, reorder to
`X ⊗ B ⊗ (X′ ⊗ A)` (`measTraceReindex`), and remove the trailing `X′ ⊗ A` block by `partialTraceB`,
landing on `X ⊗ B`. -/
def measConjTraceMap {d dB : ℕ} (W : Matrix (Fin (d * d * d)) (Fin (d * d * d)) ℂ)
    (τ : Op (d * d * d * dB)) : Op (d * dB) :=
  partialTraceB (Matrix.reindex (measTraceReindex d dB) (measTraceReindex d dB)
    (Op.tensor W (1 : Op dB) * τ * (Op.tensor W (1 : Op dB))ᴴ))

/-- `measConjTraceMap` is real-homogeneous: `Ξ(t • τ) = t • Ξ(τ)`. Each stage — conjugation,
reindex, partial trace — commutes with real scalar multiplication. -/
lemma measConjTraceMap_ofReal_smul {d dB : ℕ}
    (W : Matrix (Fin (d * d * d)) (Fin (d * d * d)) ℂ) (t : ℝ) (τ : Op (d * d * d * dB)) :
    measConjTraceMap W (Complex.ofReal t • τ) = Complex.ofReal t • measConjTraceMap W τ := by
  unfold measConjTraceMap
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.reindex_smul, partialTraceB_smul]

/-- `measConjTraceMap` is order-preserving (a positive map): `τ ≼ τ′ ⟹ Ξ(τ) ≼ Ξ(τ′)`. The
positivity that `eqn:mo6` uses, from composing conjugation monotonicity
(`Quantum.Channels.opLe_kraus_sandwich`),
reindex monotonicity (`opLe_reindex_rect`), and partial-trace monotonicity
(`partialTraceB_opLe_of_opLe`). -/
lemma measConjTraceMap_opLe_mono {d dB : ℕ}
    (W : Matrix (Fin (d * d * d)) (Fin (d * d * d)) ℂ) {τ τ' : Op (d * d * d * dB)}
    (h : opLe τ τ') :
    opLe (measConjTraceMap W τ) (measConjTraceMap W τ') := by
  unfold measConjTraceMap
  exact partialTraceB_opLe_of_opLe
    (opLe_reindex_rect _ (Quantum.Channels.opLe_kraus_sandwich (Op.tensor W (1 : Op dB)) h))

/-- Index action of the tensor-factor swap `reorderTripartiteACB` on a product index:
`(a,b,c) ↦ (a,c,b)`. -/
lemma reorderTripartiteACB_apply (dA dB dC : ℕ) (a : Fin dA) (b : Fin dB) (c : Fin dC) :
    reorderTripartiteACB dA dB dC (finProdFinEquiv (finProdFinEquiv (a, b), c)) =
      finProdFinEquiv (finProdFinEquiv (a, c), b) := by
  simp only [reorderTripartiteACB, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, Equiv.prodAssoc_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.prodAssoc_symm_apply]

/-- Index action of the inverse tensor-factor swap: `(a,c,b) ↦ (a,b,c)`. -/
lemma reorderTripartiteACB_symm_apply (dA dB dC : ℕ) (a : Fin dA) (b : Fin dB) (c : Fin dC) :
    (reorderTripartiteACB dA dB dC).symm (finProdFinEquiv (finProdFinEquiv (a, c), b)) =
      finProdFinEquiv (finProdFinEquiv (a, b), c) := by
  rw [Equiv.symm_apply_eq, reorderTripartiteACB_apply]

/-- **Tracing out the middle factor of a tensor.** Reindexing `A ⊗ B ⊗ C` to `A ⊗ C ⊗ B`
(`reorderTripartiteACB`) and tracing out the trailing `B` factor traces the middle factor,
so on `A' ⊗ M` (with `A'` on `A ⊗ B`, `M` on `C`) it yields `(Tr_B A') ⊗ M`. -/
lemma partialTraceB_reindex_reorderACB_tensor {dA dB dC : ℕ}
    (A' : Op (dA * dB)) (M : Op dC) :
    partialTraceB (Matrix.reindex (reorderTripartiteACB dA dB dC)
        (reorderTripartiteACB dA dB dC) (Op.tensor A' M))
      = Op.tensor (partialTraceB A') M := by
  ext I J
  obtain ⟨⟨a, cc⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨a', cc'⟩, rfl⟩ := finProdFinEquiv.surjective J
  rw [partialTraceB, Matrix.of_apply]
  rw [Op_tensor_apply_finProd]
  simp only [Equiv.symm_apply_apply]
  rw [partialTraceB, Matrix.of_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, reorderTripartiteACB_symm_apply,
    reorderTripartiteACB_symm_apply, Op_tensor_apply_finProd]
  simp only [Equiv.symm_apply_apply]

/-- `Fin.cast` of a product index through a reassociation acting only on the outer factor. -/
lemma finCast_finProd_assoc {d dB : ℕ} (p : Fin (d * (d * d))) (q : Fin dB) :
    Fin.cast (by ring : d * (d * d) * dB = d * d * d * dB) (finProdFinEquiv (p, q)) =
      finProdFinEquiv (Fin.cast (Nat.mul_assoc d d d).symm p, q) := by
  apply Fin.ext
  simp [finProdFinEquiv_apply_val]

/-- Reindexing `(G ⊗ M)` by the outer-factor reassociation regroups only `G`'s factors. -/
lemma reindex_finCongr_tensor {d dB : ℕ} (G : Op (d * d * d)) (M : Op dB) :
    Matrix.reindex (finCongr (by ring : d * d * d * dB = d * (d * d) * dB))
        (finCongr (by ring : d * d * d * dB = d * (d * d) * dB)) (Op.tensor G M)
      = Op.tensor (Op.castDim (Nat.mul_assoc d d d) G) M := by
  ext I J
  obtain ⟨⟨p, q⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨p', q'⟩, rfl⟩ := finProdFinEquiv.surjective J
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Op_tensor_apply_finProd]
  simp only [finCongr_symm, finCongr_apply, finCast_finProd_assoc, Equiv.symm_apply_apply]
  rw [Op_tensor_apply_finProd, Op.castDim]
  simp only [Equiv.symm_apply_apply, matrix_eqRec_apply]

/-- **The trace-out wrapper on a tensor `(G ⊗ M)`.** The measurement conjugation-trace wrapper
`Tr_{X′A}` sends `G ⊗ M` (with `G` on `X ⊗ X′ ⊗ A`, `M` on `B`) to `(Tr_{X′A} G) ⊗ M`, where
`Tr_{X′A} G = Tr_B(Tr_B G)` traces the trailing two `d`-factors of `G`. -/
lemma partialTraceB_reindex_measTraceReindex_tensor {d dB : ℕ}
    (G : Op (d * d * d)) (M : Op dB) :
    partialTraceB (Matrix.reindex (measTraceReindex d dB) (measTraceReindex d dB)
        (Op.tensor G M))
      = Op.tensor (partialTraceB (partialTraceB G)) M := by
  have hcomp : Matrix.reindex (measTraceReindex d dB) (measTraceReindex d dB) (Op.tensor G M)
      = Matrix.reindex (reorderTripartiteACB d (d * d) dB) (reorderTripartiteACB d (d * d) dB)
          (Matrix.reindex (finCongr (by ring : d * d * d * dB = d * (d * d) * dB))
            (finCongr (by ring : d * d * d * dB = d * (d * d) * dB)) (Op.tensor G M)) := by
    simp only [measTraceReindex, Matrix.reindex_apply, Matrix.submatrix_submatrix]
    rfl
  rw [hcomp, reindex_finCongr_tensor, partialTraceB_reindex_reorderACB_tensor]
  congr 1
  rw [partialTraceB_partialTraceB_eq_assoc, Op.castDim]

/-- **`eqn:mo8` per-term trace-out (`B`).** Tracing out `X′` and `A` from the dilation-ket outer
product `|x,x,x⟩⟨x',x',x'|` collapses to the `X`-projector when `x = x'` and vanishes otherwise:
`Tr_{X′A}(|dP x⟩⟨dP x'|) = δ_{x,x'} · |x⟩⟨x'|`. -/
lemma measTraceMid_dilationKet_ketbra {d : ℕ} (P : RankOneProjectiveBasis d) (x x' : Fin d) :
    partialTraceB (partialTraceB (P.dilationKet x * (P.dilationKet x').dag))
      = (if x = x' then (1 : ℂ) else 0) • (P.vec x * (P.vec x').dag) := by
  have hdecomp : P.dilationKet x * (P.dilationKet x').dag
      = Op.tensor (Op.tensor (P.vec x * (P.vec x').dag) (P.vec x * (P.vec x').dag))
          (P.vec x * (P.vec x').dag) := by
    unfold RankOneProjectiveBasis.dilationKet
    rw [ketbra_tensor', ketbra_tensor']
  rw [hdecomp, partialTraceB_tensor_op, partialTraceB_smul, partialTraceB_tensor_op,
    P.trace_vec_ketbra, smul_smul]
  congr 1
  by_cases h : x = x' <;> simp [h]

/-- **Ket-bra form of the partial isometry** `W = U Vᴴ = Σ_{x,z} ⟨x|z⟩ |dP x⟩⟨dQ z|`
(`tr.tex:335`, rank-1 form). Each term is a `d³×d³` outer product of dilation kets weighted by the
basis overlap `⟨x|z⟩ = (P.vec x).dag * Q.vec z`. -/
lemma partialIsometryW_eq_sum_ketbra {d : ℕ} (P Q : RankOneProjectiveBasis d) :
    P.partialIsometryW Q = ∑ x, ∑ z, ((P.vec x).dag * Q.vec z) •
        (P.dilationKet x * (Q.dilationKet z).dag) := by
  ext i j
  rw [RankOneProjectiveBasis.partialIsometryW, Matrix.mul_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, ket_mul_bra_apply, Ket.dag_vec,
    starRingEnd_apply, smul_eq_mul, Matrix.conjTranspose_apply,
    RankOneProjectiveBasis.dilationIso, star_sum, star_mul', star_star, bra_mul_ket_eq]
  -- LHS: ∑ k, (∑ x, (dP x)_i·conj(px_k)) · (∑ z, conj(dQz_j)·qz_k)
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The `B`-register block `⟨b|τ|c⟩_B` of `τ : Op (n ⊗ dB)` between kets `b, c : Ket n` on the
first register: `(⟨b|τ|c⟩_B)_{β,β'} = Σ_{I,J} conj(b_I) τ_{(I,β),(J,β')} c_J`. -/
def braKetBlock {n dB : ℕ} (τ : Op (n * dB)) (b c : Ket n) : Op dB :=
  Matrix.of fun β β' => ∑ I, ∑ J,
    star (b.vec I) * τ (finProdFinEquiv (I, β)) (finProdFinEquiv (J, β')) * c.vec J

/-- **Ket-bra conjugation exposes the `B`-block.** Sandwiching `τ` by `|a⟩⟨b| ⊗ 1_B` on the left and
`|c⟩⟨d| ⊗ 1_B` on the right factors as `|a⟩⟨d| ⊗ ⟨b|τ|c⟩_B`. -/
lemma tensor_ketbra_sandwich {n dB : ℕ} (a b c dd : Ket n) (τ : Op (n * dB)) :
    Op.tensor (a * b.dag) (1 : Op dB) * τ * Op.tensor (c * dd.dag) (1 : Op dB)
      = Op.tensor (a * dd.dag) (braKetBlock τ b c) := by
  ext I J
  obtain ⟨⟨iA, iB⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨jA, jB⟩, rfl⟩ := finProdFinEquiv.surjective J
  rw [Quantum.TensorProducts.tensor_one_mul_mul_tensor_one_apply, Op_tensor_apply_finProd]
  simp only [Equiv.symm_apply_apply, ket_mul_bra_apply, Ket.dag_vec, starRingEnd_apply,
    braKetBlock, Matrix.of_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L _
  ring

/-- `Fin.cast` splitting off the leading `Z`-factor: the `((Z⊗Z′)⊗A)⊗B` index equals the
`Z⊗((Z′⊗A)⊗B)` index after the reassociation cast. -/
lemma finCast_split_leadingZ {d dB : ℕ} (zZ zZ' zA : Fin d) (β : Fin dB) :
    Fin.cast (by ring : d * d * d * dB = d * (d * d * dB))
        (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (zZ, zZ'), zA), β)) =
      finProdFinEquiv (zZ, finProdFinEquiv (finProdFinEquiv (zZ', zA), β)) := by
  apply Fin.ext
  simp [finProdFinEquiv_apply_val]
  ring

/-- Reindexing a sum over `Fin (d*d*d)` into its three factor coordinates. -/
lemma sum_tripleFin {d : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin (d * d * d) → M) :
    ∑ I, f I = ∑ x : Fin d, ∑ x1 : Fin d, ∑ x2 : Fin d,
      f (finProdFinEquiv (finProdFinEquiv (x, x1), x2)) := by
  rw [← Equiv.sum_comp finProdFinEquiv f, Fintype.sum_prod_type,
    ← Equiv.sum_comp finProdFinEquiv (fun p1 => ∑ p2, f (finProdFinEquiv (p1, p2))),
    Fintype.sum_prod_type]

/-- Reindexing a sum over `Fin (d*d)` into its two factor coordinates. -/
lemma sum_doubleFin {d : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin (d * d) → M) :
    ∑ I, f I = ∑ x : Fin d, ∑ x1 : Fin d, f (finProdFinEquiv (x, x1)) := by
  rw [← Equiv.sum_comp finProdFinEquiv f, Fintype.sum_prod_type]

/-- **Delta-collapse of a triple sum against a rank-one weight.** For fixed `x`, summing a product
of a Kronecker-delta weight `A' x3` against an outer function `g x4 x5` collapses the `x3`-sum to
`A' x`, leaving the `(x4, x5)`-sum untouched: this is the finite-sum bookkeeping behind
`⟨z|z'⟩`-factoring in `braKetBlock_castDim_one_tensor`. -/
lemma sum_ite_mul_sum_prod_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι) (A' : ι → ℂ) (g : ι → ι → ℂ) (c : ℂ) :
    ∑ x3 : ι, ∑ x4 : ι, ∑ x5 : ι,
      c * ((if x = x3 then (1 : ℂ) else 0) * g x4 x5) * (A' x3 * A' x4 * A' x5)
      = c * A' x * ∑ x4, ∑ x5, g x4 x5 * (A' x4 * A' x5) := by
  have hpt : ∀ x3 x4 x5 : ι,
      c * ((if x = x3 then (1 : ℂ) else 0) * g x4 x5) * (A' x3 * A' x4 * A' x5)
        = (c * (if x = x3 then A' x3 else 0)) * (g x4 x5 * (A' x4 * A' x5)) := by
    intro x3 x4 x5
    by_cases h : x = x3 <;> simp [h]; ring
  simp only [hpt]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    mul_assoc]

/-- **A single-variable factor splits off a double sum.** -/
lemma sum_mul_sum_two {ι : Type*} [Fintype ι] (f : ι → ℂ) (h : ι → ι → ℂ) :
    ∑ x : ι, ∑ x1 : ι, ∑ x2 : ι, f x * h x1 x2 = (∑ x, f x) * ∑ x1, ∑ x2, h x1 x2 := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- **`eqn:mo8` reference evaluation (`E`).** The `B`-block of the reference `1_Z ⊗ σ` between two
dilation kets `|dQ z⟩, |dQ z'⟩` collapses (via the `Z`-orthonormality of `1_Z`) to `δ_{z,z'}` times
the `B`-block of `σ` between the `Z′ ⊗ A` diagonal vectors `|z⟩⊗|z⟩`:
`⟨dQ z| (1_Z ⊗ σ) |dQ z'⟩_B = δ_{z,z'} · ⟨z,z|σ|z,z⟩_B`. -/
lemma braKetBlock_castDim_one_tensor {d dB : ℕ} (Q : RankOneProjectiveBasis d)
    (σ : Op (d * d * dB)) (z z' : Fin d) :
    braKetBlock (Op.castDim (by ring : d * (d * d * dB) = d * d * d * dB)
        (Op.tensor (1 : Op d) σ)) (Q.dilationKet z) (Q.dilationKet z')
      = (if z = z' then (1 : ℂ) else 0) •
          braKetBlock σ (Q.vec z ⊗ Q.vec z) (Q.vec z ⊗ Q.vec z) := by
  -- `sum_tripleFin`/`sum_doubleFin` reindex the `Fin (d³)` / `Fin (d²)` sums into their factor
  -- tuples; after the cast (`finCast_split_leadingZ`) + `1_Z`-entry rewrites the entrywise goal
  -- becomes a 6-fold sum which `sum_ite_mul_sum_prod_eq` collapses against the `Z`-delta, leaving
  -- a leading `⟨z|z'⟩ = δ_{z,z'}` factor (`sum_mul_sum_two` + the basis orthonormality) times the
  -- reference `B`-block sum, matching the RHS.
  ext β β'
  simp only [braKetBlock, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, sum_tripleFin,
    sum_doubleFin]
  simp only [RankOneProjectiveBasis.dilationKet, Ket.tensor_vec, Equiv.symm_apply_apply,
    Op.castDim, matrix_eqRec_apply, finCast_split_leadingZ, Op_tensor_apply_finProd,
    Matrix.one_apply, star_mul']
  simp only [sum_ite_mul_sum_prod_eq]
  have hpt2 : ∀ x x1 x2 : Fin d,
      star ((Q.vec z).vec x) * star ((Q.vec z).vec x1) * star ((Q.vec z).vec x2) *
          (Q.vec z').vec x *
          ∑ x4, ∑ x5, σ (finProdFinEquiv (finProdFinEquiv (x1, x2), β))
              (finProdFinEquiv (finProdFinEquiv (x4, x5), β')) *
            ((Q.vec z').vec x4 * (Q.vec z').vec x5)
        = (star ((Q.vec z).vec x) * (Q.vec z').vec x) *
            (star ((Q.vec z).vec x1) * star ((Q.vec z).vec x2) *
              ∑ x4, ∑ x5, σ (finProdFinEquiv (finProdFinEquiv (x1, x2), β))
                  (finProdFinEquiv (finProdFinEquiv (x4, x5), β')) *
                ((Q.vec z').vec x4 * (Q.vec z').vec x5)) := by
    intro x x1 x2; ring
  simp only [hpt2, sum_mul_sum_two]
  have hδ : ∑ x, star ((Q.vec z).vec x) * (Q.vec z').vec x
      = if z = z' then (1 : ℂ) else 0 := by
    have h := Q.orthonormal z z'
    rw [bra_mul_ket_eq] at h
    simpa only [Ket.dag_vec, starRingEnd_apply] using h
  rw [hδ]
  simp only [Finset.mul_sum]
  by_cases hzz : z = z'
  · subst hzz; simp only [mul_assoc]
  · simp only [ite_eq_right hzz, zero_mul]

/-- Conjugate transpose of an outer product swaps the ket and bra: `(|ψ⟩⟨φ|)ᴴ = |φ⟩⟨ψ|`. -/
lemma ketbra_conjTranspose {n : ℕ} (ψ φ : Ket n) : (ψ * φ.dag)ᴴ = φ * ψ.dag := by
  ext i j
  simp only [Matrix.conjTranspose_apply, ket_mul_bra_apply, Ket.dag_vec, starRingEnd_apply,
    star_mul', star_star, mul_comm]

/-- A rectangular reindex distributes over finite sums. -/
lemma reindex_finset_sum_rect {n m : ℕ} {ι : Type*} (e : Fin n ≃ Fin m)
    (s : Finset ι) (f : ι → Op n) :
    Matrix.reindex e e (∑ i ∈ s, f i) = ∑ i ∈ s, Matrix.reindex e e (f i) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]

/-- The `Tr_{X′A}`-wrapper `partialTraceB ∘ reindex` distributes over `c • ·`. -/
lemma measTraceWrap_smul {d dB : ℕ} (c : ℂ) (T : Op (d * d * d * dB)) :
    partialTraceB (Matrix.reindex (measTraceReindex d dB) (measTraceReindex d dB) (c • T))
      = c • partialTraceB (Matrix.reindex (measTraceReindex d dB) (measTraceReindex d dB) T) := by
  rw [Matrix.reindex_smul, partialTraceB_smul]

/-- **`eqn:mo8` — the measurement conjugation-trace map on the reference (the identity).** The
`W`-conjugation-and-partial-trace of `1_Z ⊗ σ` evaluates to the block-diagonal double sum
`Σ_{x,z} |⟨x|z⟩|² · |x⟩⟨x| ⊗ ⟨z,z|σ|z,z⟩_B` (`tr.tex:344–354`). -/
theorem measConjTraceMap_one_tensor_reference_eq {d dB : ℕ} [NeZero d]
    (P Q : RankOneProjectiveBasis d) (σ : Op (d * d * dB)) :
    measConjTraceMap (P.partialIsometryW Q)
        (Op.castDim (by ring : d * (d * d * dB) = d * d * d * dB) (Op.tensor (1 : Op d) σ))
      = ∑ x, ∑ z, (Complex.normSq ((P.vec x).dag * Q.vec z) : ℂ) •
          Op.tensor (P.proj x) (braKetBlock σ (Q.vec z ⊗ Q.vec z) (Q.vec z ⊗ Q.vec z)) := by
  set τ : Op (d * d * d * dB) :=
    Op.castDim (by ring : d * (d * d * dB) = d * d * d * dB) (Op.tensor (1 : Op d) σ) with hτ
  -- Ket-bra expansion of `W ⊗ 1` and its adjoint.
  have hW : Op.tensor (P.partialIsometryW Q) (1 : Op dB)
      = ∑ x, ∑ z, ((P.vec x).dag * Q.vec z) •
          Op.tensor (P.dilationKet x * (Q.dilationKet z).dag) (1 : Op dB) := by
    rw [partialIsometryW_eq_sum_ketbra, Op.tensor_finsetSum_left]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Op.tensor_finsetSum_left]
    exact Finset.sum_congr rfl (fun z _ => by rw [Op.tensor_smul_left])
  have hWd : (Op.tensor (P.partialIsometryW Q) (1 : Op dB))ᴴ
      = ∑ x, ∑ z, (star ((P.vec x).dag * Q.vec z)) •
          Op.tensor (Q.dilationKet z * (P.dilationKet x).dag) (1 : Op dB) := by
    rw [hW, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.conjTranspose_smul, Op.tensor_conjTranspose, Matrix.conjTranspose_one,
      ketbra_conjTranspose]
  rw [measConjTraceMap, hWd, hW]
  -- distribute the product of the two double sums over `τ`
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [reindex_finset_sum_rect, partialTraceB_finset_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [reindex_finset_sum_rect, partialTraceB_finset_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  -- per-term evaluation of the conjugation-trace-map on each `|x₁⟩⟨x₂|`-`|z⟩⟨x|` block
  have key : ∀ x1 x2 : Fin d,
      partialTraceB (Matrix.reindex (measTraceReindex d dB) (measTraceReindex d dB)
        (Op.tensor (P.dilationKet x1 * (Q.dilationKet x2).dag) (1 : Op dB) * τ *
          Op.tensor (Q.dilationKet z * (P.dilationKet x).dag) (1 : Op dB)))
        = (if x1 = x then (1 : ℂ) else 0) • (if x2 = z then (1 : ℂ) else 0) •
            Op.tensor (P.vec x1 * (P.vec x).dag)
              (braKetBlock σ (Q.vec x2 ⊗ Q.vec x2) (Q.vec x2 ⊗ Q.vec x2)) := by
    intro x1 x2
    rw [tensor_ketbra_sandwich, partialTraceB_reindex_measTraceReindex_tensor,
      measTraceMid_dilationKet_ketbra, hτ, braKetBlock_castDim_one_tensor,
      Op.tensor_smul_left, Op.tensor_smul_right]
  rw [measTraceWrap_smul]
  simp_rw [reindex_finset_sum_rect, partialTraceB_finset_sum, measTraceWrap_smul, key,
    smul_smul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_one, mul_zero,
    ite_smul, zero_smul]
  rw [smul_smul, ← RankOneProjectiveBasis.proj]
  congr 1
  rw [mul_comm]
  exact Complex.mul_conj _

/-- The projector `M_x = |x⟩⟨x|` is positive semidefinite. -/
lemma RankOneProjectiveBasis.proj_posSemidef {d : ℕ} (P : RankOneProjectiveBasis d) (x : Fin d) :
    (P.proj x).PosSemidef := by
  have h : P.proj x = (P.proj x)ᴴ * P.proj x := by
    rw [P.proj_isHermitian x, P.proj_idem]
  rw [h]; exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **The `B`-block as a quadratic form of `σ`.** The quadratic form of `⟨u|σ|u⟩_B` at `v` equals
the quadratic form of `σ` at the tensor vector `u ⊗ v`. -/
lemma braKetBlock_quadraticForm {n dB : ℕ} (σ : Op (n * dB)) (u : Ket n) (v : Fin dB → ℂ) :
    quadraticForm (braKetBlock σ u u) v = quadraticForm σ (Ket.tensor u ⟨v⟩).vec := by
  have keyσ : quadraticForm σ (Ket.tensor u ⟨v⟩).vec = ∑ I, ∑ β, ∑ J, ∑ β',
      star (u.vec I) * star (v β) *
        (σ (finProdFinEquiv (I, β)) (finProdFinEquiv (J, β')) * (u.vec J * v β')) := by
    simp only [quadraticForm, dotProduct, Pi.star_apply, Matrix.mulVec]
    rw [← Equiv.sum_comp finProdFinEquiv
      (fun P => star ((Ket.tensor u ⟨v⟩).vec P) * ∑ P', σ P P' * (Ket.tensor u ⟨v⟩).vec P')]
    simp_rw [← Equiv.sum_comp finProdFinEquiv
      (fun P' => σ _ P' * (Ket.tensor u ⟨v⟩).vec P'), Fintype.sum_prod_type, Finset.mul_sum,
      Ket.tensor_vec, Equiv.symm_apply_apply, star_mul']
  have keyL : quadraticForm (braKetBlock σ u u) v = ∑ β, ∑ β', ∑ I, ∑ J,
      star (u.vec I) * star (v β) *
        (σ (finProdFinEquiv (I, β)) (finProdFinEquiv (J, β')) * (u.vec J * v β')) := by
    simp only [quadraticForm, dotProduct, Pi.star_apply, Matrix.mulVec, braKetBlock,
      Matrix.of_apply]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β' _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    ring
  rw [keyL, keyσ]
  -- pure reordering of a 4-fold finite sum `(β,β',I,J) ↦ (I,β,J,β')`
  rw [Finset.sum_congr rfl fun β _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun β _ => Finset.sum_comm]

/-- The `B`-block `⟨u|σ|u⟩_B` of a PSD operator is positive semidefinite. -/
lemma braKetBlock_posSemidef {n dB : ℕ} (σ : Op (n * dB)) (hσ : σ.PosSemidef) (u : Ket n) :
    (braKetBlock σ u u).PosSemidef := by
  have hHerm : (braKetBlock σ u u).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext β β'
    simp only [Matrix.conjTranspose_apply, braKetBlock, Matrix.of_apply, star_sum, star_mul',
      star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun I _ => Finset.sum_congr rfl (fun J _ => ?_))
    have := congrFun (congrFun hσ.isHermitian (finProdFinEquiv (I, β))) (finProdFinEquiv (J, β'))
    simp only [Matrix.conjTranspose_apply] at this
    rw [this]; ring
  apply posSemidef_of_isHermitian_of_quadraticForm_re_nonneg hHerm
  intro v
  rw [braKetBlock_quadraticForm]
  exact posSemidef_re_quadraticForm_nonneg hσ _

/-- The quadratic form at `u` is the trace of `|u⟩⟨u| · M`. -/
lemma quadraticForm_eq_trace_ketbra {n : ℕ} (M : Op n) (u : Ket n) :
    quadraticForm M u.vec = ((u * u.dag) * M).trace := by
  simp only [quadraticForm, dotProduct, Pi.star_apply, Matrix.mulVec, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, ket_mul_bra_apply, Ket.dag_vec, starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- `|z,z⟩` orthonormality: `⟨z,z|z',z'⟩ = δ_{z,z'}`. -/
lemma qq_orthonormal {d : ℕ} (Q : RankOneProjectiveBasis d) (z z' : Fin d) :
    (Q.vec z ⊗ Q.vec z).dag * (Q.vec z' ⊗ Q.vec z') = if z = z' then (1 : ℂ) else 0 := by
  rw [Ket.dag_tensor, bra_tensor_mul_ket_tensor, Q.orthonormal z z']
  by_cases h : z = z' <;> simp [h]

/-- `|v⟩⟨v|` is positive semidefinite. -/
lemma ket_ketbra_posSemidef {n : ℕ} (v : Fin n → ℂ) :
    ((⟨v⟩ : Ket n) * (⟨v⟩ : Ket n).dag).PosSemidef := by
  apply posSemidef_of_isHermitian_of_quadraticForm_re_nonneg (ketbra_conjTranspose _ _)
  intro w
  have hqf : quadraticForm ((⟨v⟩ : Ket n) * (⟨v⟩ : Ket n).dag) w
      = (∑ i, star (w i) * v i) * (∑ j, star (v j) * w j) := by
    rw [Finset.sum_mul_sum]
    simp only [quadraticForm, dotProduct, Pi.star_apply, Matrix.mulVec, ket_mul_bra_apply,
      Ket.dag_vec, starRingEnd_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hconj : (∑ i, star (w i) * v i) = (starRingEnd ℂ) (∑ i, star (v i) * w i) := by
    rw [map_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_mul, starRingEnd_apply, star_star]; ring
  rw [hqf, hconj, mul_comm, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- **The `Z′A`-diagonal `B`-blocks sum below the `B`-marginal.** For PSD `σ` on `(Z′⊗A) ⊗ B`, the
sum over `z` of the diagonal `B`-blocks `⟨z,z|σ|z,z⟩_B` is dominated in the Löwner order by the full
`B`-marginal `Tr_{Z′A} σ = partialTraceA σ`. Both sides are traces against `σ`
(`Tr((P_Q ⊗ |v⟩⟨v|) σ)` resp. `Tr((1 ⊗ |v⟩⟨v|) σ)`, `P_Q = Σ_z |z,z⟩⟨z,z|` the diagonal projector);
`1 - P_Q` PSD gives the nonnegative difference by `trace_mul_psd_nonneg`. -/
lemma sum_braKetBlock_qq_opLe {d dB : ℕ} (Q : RankOneProjectiveBasis d) (σ : Op (d * d * dB))
    (hσ : σ.PosSemidef) :
    opLe (∑ z, braKetBlock σ (Q.vec z ⊗ Q.vec z) (Q.vec z ⊗ Q.vec z)) (partialTraceA σ) := by
  intro v
  set Vd : Op dB := (⟨v⟩ : Ket dB) * (⟨v⟩ : Ket dB).dag with hVd
  set PQ : Op (d * d) := ∑ z, (Q.vec z ⊗ Q.vec z) * (Q.vec z ⊗ Q.vec z).dag with hPQ
  have hVdpsd : Vd.PosSemidef := hVd ▸ ket_ketbra_posSemidef v
  have hPQidem : PQ * PQ = PQ := by
    rw [hPQ, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Finset.mul_sum, Finset.sum_eq_single z]
    · rw [ketbra_mul_ketbra, qq_orthonormal, ite_eq_left rfl, one_smul]
    · intro z' _ hz'
      rw [ketbra_mul_ketbra, qq_orthonormal, ite_eq_right (fun h => hz' h.symm), zero_smul]
    · intro h; exact absurd (Finset.mem_univ z) h
  have hPQherm : PQᴴ = PQ := by
    rw [hPQ, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl (fun z _ => ketbra_conjTranspose _ _)
  have hcompl : (1 - PQ).PosSemidef := by
    have hsplit : (1 - PQ) = (1 - PQ)ᴴ * (1 - PQ) := by
      have hexp : (1 - PQ) * (1 - PQ) = 1 - PQ - PQ + PQ * PQ := by noncomm_ring
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPQherm, hexp, hPQidem]; abel
    rw [hsplit]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hLHS : quadraticForm (∑ z, braKetBlock σ (Q.vec z ⊗ Q.vec z) (Q.vec z ⊗ Q.vec z)) v
      = (Op.tensor PQ Vd * σ).trace := by
    rw [quadraticForm_finset_sum]
    have hterm : ∀ z, quadraticForm (braKetBlock σ (Q.vec z ⊗ Q.vec z) (Q.vec z ⊗ Q.vec z)) v
        = (Op.tensor ((Q.vec z ⊗ Q.vec z) * (Q.vec z ⊗ Q.vec z).dag) Vd * σ).trace := fun z => by
      rw [braKetBlock_quadraticForm, quadraticForm_eq_trace_ketbra, hVd, ketbra_tensor']
    simp_rw [hterm]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Op.tensor_finsetSum_left, ← hPQ]
  have hRHS : (quadraticForm (partialTraceA σ) v).re
      = ((Op.tensor (1 : Op (d * d)) Vd * σ).trace).re := by
    rw [quadraticForm_partialTraceA_re_eq_sum]
    have hterm : ∀ k, quadraticForm σ (leftBlockVector k v)
        = (Op.tensor (Quantum.Operators.stdKet (d * d) k *
            (Quantum.Operators.stdKet (d * d) k).dag) Vd * σ).trace := fun k => by
      rw [show leftBlockVector k v
          = (Quantum.Operators.stdKet (d * d) k ⊗ (⟨v⟩ : Ket dB)).vec from ?_,
        quadraticForm_eq_trace_ketbra, hVd, ketbra_tensor']
      funext P
      simp only [leftBlockVector, Ket.tensor_vec, Quantum.Operators.stdKet_apply]
      by_cases h : (finProdFinEquiv.symm P).1 = k
      · rw [ite_eq_left h, ite_eq_left h.symm, one_mul]
      · rw [ite_eq_right h, ite_eq_right (fun he => h he.symm), zero_mul]
    simp_rw [hterm]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, ← Op.tensor_finsetSum_left,
      stdKet_complete]
  rw [hLHS, hRHS]
  have hnn : 0 ≤ ((Op.tensor (1 - PQ) Vd * σ).trace).re :=
    Quantum.Operators.trace_mul_psd_nonneg _ _
      (Quantum.TensorProducts.Op.tensor_posSemidef_mathlib hcompl hVdpsd) hσ
  have hdiff : (Op.tensor (1 - PQ) Vd * σ).trace
      = (Op.tensor (1 : Op (d * d)) Vd * σ).trace - (Op.tensor PQ Vd * σ).trace := by
    rw [Quantum.TensorProducts.Op.tensor_sub_left, Matrix.sub_mul, Matrix.trace_sub]
  rw [hdiff, Complex.sub_re] at hnn
  linarith

/-- **`eqn:mo8/mo9` — the reference bound.** For a reference state `σ` on `Z′ ⊗ A ⊗ B`,
the measurement conjugation-trace map sends `1_Z ⊗ σ` below `c · 1_X ⊗ σ_B`, where
`σ_B = Tr_{Z′A} σ` is the `B`-marginal and `c = overlapConst P Q`:

`Tr_{X′A}( W (1_Z ⊗ σ) Wᴴ ) = Σ_{x,z} |x⟩⟨x| ⊗ ⟨z| Tr_A(√N_z M_x √N_z σ) |z⟩ ≤ c · 1_X ⊗ σ_B`.

This is the conjugation-and-partial-trace computation `eqn:mo8` (`tr.tex:344–354`) followed by the
overlap domination `eqn:mo9` (`tr.tex:350`). Both steps are held in the textbook source: the
displayed chain arXiv:1504.00233, `apps.tex:209–213` is exactly this identity and
domination, in the `M_X ∘ U_Y` notation of that proof. The `eqn:mo9` operator content — the
pointwise bound `√N_z M_x √N_z ≤ c · 1_A` — is `sqrtN_M_sqrtN_opLe_overlapConst_smul_one`; the
`eqn:mo8` evaluation of the non-adjacent partial trace `Tr_{X′A}` of the `W`-conjugation into the
block-diagonal double sum is `measConjTraceMap_one_tensor_reference_eq`.
The `σ`-positivity hypothesis is the state assumption
`σ ∈ S_≤`. -/
theorem measConjTraceMap_one_tensor_reference_opLe {d dB : ℕ} [NeZero d]
    (P Q : RankOneProjectiveBasis d) (σ : Op (d * d * dB)) (_hσ : σ.PosSemidef) :
    opLe
      (measConjTraceMap (P.partialIsometryW Q)
        (Op.castDim (by ring : d * (d * d * dB) = d * d * d * dB) (Op.tensor (1 : Op d) σ)))
      (Complex.ofReal (P.overlapConst Q) • Op.tensor (1 : Op d) (partialTraceA σ)) := by
  rw [measConjTraceMap_one_tensor_reference_eq]
  have hcnn : (0 : ℝ) ≤ P.overlapConst Q := P.overlapConst_nonneg Q
  have hσB : (partialTraceA σ).IsHermitian := partialTraceA_hermitian σ _hσ.isHermitian
  -- LHS grouped by `x`, pulling the projector out of the `z`-sum
  have hLHS : (∑ x, ∑ z, (↑(Complex.normSq ((P.vec x).dag * Q.vec z)) : ℂ) •
        Op.tensor (P.proj x) (braKetBlock σ (Q.vec z ⊗ Q.vec z) (Q.vec z ⊗ Q.vec z)))
      = ∑ x, Op.tensor (P.proj x)
          (∑ z, (↑(Complex.normSq ((P.vec x).dag * Q.vec z)) : ℂ) •
            braKetBlock σ (Q.vec z ⊗ Q.vec z) (Q.vec z ⊗ Q.vec z)) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Op.tensor_finsetSum_right]
    exact Finset.sum_congr rfl (fun z _ => (Op.tensor_smul_right _ _ _).symm)
  have hcomplete : (∑ x, P.proj x) = (1 : Op d) := P.complete
  have hRHS : Complex.ofReal (P.overlapConst Q) • Op.tensor (1 : Op d) (partialTraceA σ)
      = ∑ x, Op.tensor (P.proj x)
          (Complex.ofReal (P.overlapConst Q) • partialTraceA σ) := by
    rw [← Op.tensor_smul_right, ← hcomplete, Op.tensor_finsetSum_left]
  have hD : (Complex.ofReal (P.overlapConst Q) • partialTraceA σ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hσB, Complex.star_def, Complex.conj_ofReal]
  rw [hLHS, hRHS]
  refine opLe_finset_sum _ (fun x _ => ?_)
  refine opLe_tensor_psd (P.proj_isHermitian x) (P.proj_posSemidef x) ?_ hD (opLe_refl _) ?_
  · -- `B_x` PSD: sum of nonneg-scaled PSD blocks
    classical
    refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
    intro z _
    exact (braKetBlock_posSemidef σ _hσ _).smul
      (Complex.zero_le_real.mpr (Complex.normSq_nonneg _))
  · -- the core `eqn:mo9` overlap domination
    refine opLe_trans (opLe_finset_sum _ (fun z _ =>
      opLe_smul_mono_psd (P.normSq_overlap_le_overlapConst Q x z)
        (braKetBlock_posSemidef σ _hσ _))) ?_
    rw [← Finset.smul_sum]
    exact opLe_smul_nonneg hcnn (sum_braKetBlock_qq_opLe Q σ _hσ)

/-- **`eqn:mo6` — the feasibility transport (reduction, proved).** Applying the positive,
real-homogeneous map `Ξ = measConjTraceMap W` to the dominated inequality
`ρ ≼ 2^{-λ} · ref` and combining with the reference bound `Ξ(ref) ≼ c · outRef` gives
`Ξ(ρ) ≼ 2^{-λ}·c · outRef`. TR's `eqn:mo6` (`tr.tex:321–326`) is the instance
`ref = 1_Z ⊗ σ_{Z′AB}`, `outRef = 1_X ⊗ σ_B`, `Ξ(ρ) = ρ_XB` (via `eqn:mo10`, `tr.tex:338–341`, the
`d4` recovery identity), with the reference bound supplied by
`measConjTraceMap_one_tensor_reference_opLe`. Here `s = 2^{-λ} ≥ 0`. -/
theorem measDilation_mo6_transport {d dB : ℕ}
    (W : Matrix (Fin (d * d * d)) (Fin (d * d * d)) ℂ) {s c : ℝ} (hs : 0 ≤ s)
    (ρ ref : Op (d * d * d * dB)) (outRef : Op (d * dB))
    (hdom : opLe ρ (Complex.ofReal s • ref))
    (hbound : opLe (measConjTraceMap W ref) (Complex.ofReal c • outRef)) :
    opLe (measConjTraceMap W ρ) (Complex.ofReal (s * c) • outRef) := by
  have h1 : opLe (measConjTraceMap W ρ) (measConjTraceMap W (Complex.ofReal s • ref)) :=
    measConjTraceMap_opLe_mono W hdom
  rw [measConjTraceMap_ofReal_smul] at h1
  have h2 : opLe (Complex.ofReal s • measConjTraceMap W ref)
      (Complex.ofReal s • (Complex.ofReal c • outRef)) := opLe_smul_nonneg hs hbound
  rw [smul_smul, ← Complex.ofReal_mul] at h2
  exact opLe_trans h1 h2

/-- **`eqn:mo6` for two rank-1 projective bases (the BB84 shape).** The concrete specialization of
`measDilation_mo6_transport` to `ref = 1_Z ⊗ σ`, `outRef = 1_X ⊗ σ_B`, `c = overlapConst P Q`: for
any operator `ρ` dominated by `s · 1_Z ⊗ σ` (with `s = 2^{-λ} ≥ 0`), the measurement
conjugation-trace map sends `ρ` below `(s · c) · 1_X ⊗ σ_B`. Combined in `d4` with the recovery
identity `eqn:mo10` (`Ξ(ρ_ZZ′AB) = ρ_XB`), this is TR's `eqn:mo6` (`tr.tex:321–326`)

`2^{-λ} · 1_Z ⊗ σ_{Z′AB} ≥ ρ_{ZZ′AB}  ⟹  2^{-λ} · c · 1_X ⊗ σ_B ≥ ρ_{XB}` .

The reference bound is discharged by the open leaf `measConjTraceMap_one_tensor_reference_opLe`. -/
theorem measDilation_mo6 {d dB : ℕ} [NeZero d]
    (P Q : RankOneProjectiveBasis d) {s : ℝ} (hs : 0 ≤ s)
    (σ : Op (d * d * dB)) (hσ : σ.PosSemidef) (ρ : Op (d * d * d * dB))
    (hdom : opLe ρ (Complex.ofReal s •
      Op.castDim (by ring : d * (d * d * dB) = d * d * d * dB) (Op.tensor (1 : Op d) σ))) :
    opLe (measConjTraceMap (P.partialIsometryW Q) ρ)
      (Complex.ofReal (s * P.overlapConst Q) • Op.tensor (1 : Op d) (partialTraceA σ)) :=
  measDilation_mo6_transport (P.partialIsometryW Q) hs ρ _ _ hdom
    (measConjTraceMap_one_tensor_reference_opLe P Q σ hσ)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
