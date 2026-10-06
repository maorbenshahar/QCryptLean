import QCryptLean.InfoTheory.BellDiagonal.Entropy
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.ProjectiveDPI

/-!
# Bell-twirl monotonicity of the single-round Devetak–Winter rate

For a two-qubit `AB` density operator `s : DensityOp 4`, the single-round Devetak–Winter
key rate is the entropy-production functional `r(ρ) = S(Δ_A ρ) − S(ρ)`, where `Δ_A` dephases
Alice's qubit in the computational (`Z`) basis. This file proves that the Bell twirl
`T = bellDephasingDensity` does **not increase** this rate:

`A.4-core :  r(T s) ≤ r(s)`,  i.e.  `S(Δ_A (T s)) − S(T s) ≤ S(Δ_A s) − S(s)`.

The proof is a **data-processing** argument (NOT concavity; the naïve concavity argument gives
the wrong direction):

`r(T s) =(K1) Σ_k p_k log(p_k/q_k) ≤(DPI) D(s ‖ Δ_A s) =(E1) r(s)`,

where the middle inequality is the projective-measurement data-processing inequality
`InfoTheory.RelativeEntropy.projective_measurement_dpi_of_ker_sub` applied to the Bell PVM
`{|β_k⟩⟨β_k|}` on the pair `(s, Δ_A s)`. Here `p_k = ⟨β_k|s|β_k⟩`, `q_k = ⟨β_k|Δ_A s|β_k⟩`.

## Main definitions
- `aliceZProj`: the Alice-`Z` block projectors `P₀ = diag(1,1,0,0)`, `P₁ = diag(0,0,1,1)`
- `aliceZDephase`: the Alice-`Z` pinching `Δ_A s = P₀ s P₀ + P₁ s P₁` as a `DensityOp 4`
- `bellProj`: the four Bell rank-one PVM elements `|β_k⟩⟨β_k|`

## Main statements
- `aliceZ_entropyProduction` (E1): `D(s ‖ Δ_A s) = S(Δ_A s) − S(s)`  (entropy-production identity)
- `bellMeas_KL_eq_dephasingRate` (K1): the Bell-measurement KL equals `S(Δ_A (T s)) − S(T s)`
- `aliceZDephase_ker_sub` (support glue): `ker (Δ_A s) ⊆ ker s`
- `aliceZDephasingRate_bellTwirl_monotone` (A.4-core): `r(T s) ≤ r(s)`

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B; Devetak–Winter
2005 (Proc. R. Soc. A 461);
Coles–Colbeck–Yu–Zwolak 2012 (PRL 108, 210405); Lindblad 1975 / Uhlmann 1977 (relative-entropy
monotonicity).
-/

open Quantum.Operators Quantum.TensorProducts
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace QKD.BB84.Engine

open Quantum.Basis.BellStates Math.ClassicalEntropy InfoTheory.VonNeumannEntropy
open QKD.BB84.Model
  InfoTheory.RelativeEntropy QKD.BB84.Engine.BellDephasing Quantum.Metrics

/-! ## The Alice-`Z` block projectors -/

/-- Alice-`Z` computational block projector. Index `i ∈ Fin 4` encodes `|aliceBit bobBit⟩`
as `2·aliceBit + bobBit`, so Alice's bit is `i / 2`. Then `aliceZProj 0 = diag(1,1,0,0)`
(Alice bit `0`) and `aliceZProj 1 = diag(0,0,1,1)` (Alice bit `1`). -/
def aliceZProj (z : Fin 2) : Op 4 :=
  Matrix.diagonal (fun i : Fin 4 => if i.val / 2 = z.val then (1 : ℂ) else 0)

@[simp] lemma aliceZProj_conjTranspose (z : Fin 2) : (aliceZProj z)† = aliceZProj z := by
  unfold aliceZProj
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

lemma aliceZProj_mul_self (z : Fin 2) : aliceZProj z * aliceZProj z = aliceZProj z := by
  unfold aliceZProj
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

lemma aliceZProj_mul_orthogonal {z w : Fin 2} (h : z ≠ w) :
    aliceZProj z * aliceZProj w = 0 := by
  unfold aliceZProj
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun i : Fin 4 => (if i.val / 2 = z.val then (1 : ℂ) else 0) *
      (if i.val / 2 = w.val then (1 : ℂ) else 0)) = (fun _ : Fin 4 => (0 : ℂ)) from ?_]
  · simp
  · funext i
    split_ifs with h1 h2
    · exact absurd (Fin.val_injective (h1 ▸ h2)) h
    · simp
    · simp
    · simp

lemma aliceZProj_sum : aliceZProj 0 + aliceZProj 1 = 1 := by
  unfold aliceZProj
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

/-! ## The Alice-`Z` dephasing (pinching) `Δ_A` -/

/-- The Alice-`Z` pinching operator `Δ_A s = P₀ s P₀ + P₁ s P₁`. -/
def aliceZDephaseOp (s : DensityOp 4) : Op 4 :=
  aliceZProj 0 * s.toOp * aliceZProj 0 + aliceZProj 1 * s.toOp * aliceZProj 1

lemma aliceZDephaseOp_isHermitian (s : DensityOp 4) : (aliceZDephaseOp s).IsHermitian := by
  unfold aliceZDephaseOp IsHermitian
  rw [conjTranspose_add]
  have hcongr : ∀ z : Fin 2, (aliceZProj z * s.toOp * aliceZProj z)† =
      aliceZProj z * s.toOp * aliceZProj z := by
    intro z
    simp only [conjTranspose_mul, aliceZProj_conjTranspose, Matrix.mul_assoc]
    rw [show s.toOpᴴ = s.toOp from s.isHermitian]
  rw [hcongr 0, hcongr 1]

lemma aliceZDephaseOp_posSemidef (s : DensityOp 4) : (aliceZDephaseOp s).PosSemidef := by
  have hs : s.toOp.PosSemidef := posSemidefOp_implies_mathlib s.toPosSemidefOp
  apply Matrix.PosSemidef.add
  · have h := posSemidef_conj_aux s.toOp (aliceZProj 0) hs
    rwa [aliceZProj_conjTranspose] at h
  · have h := posSemidef_conj_aux s.toOp (aliceZProj 1) hs
    rwa [aliceZProj_conjTranspose] at h

lemma aliceZDephaseOp_trace (s : DensityOp 4) : (aliceZDephaseOp s).trace = 1 := by
  unfold aliceZDephaseOp
  rw [Matrix.trace_add]
  have hcyc : ∀ z : Fin 2, (aliceZProj z * s.toOp * aliceZProj z).trace =
      (aliceZProj z * s.toOp).trace := by
    intro z
    rw [Matrix.trace_mul_cycle, aliceZProj_mul_self]
  rw [hcyc 0, hcyc 1, ← Matrix.trace_add, ← Matrix.add_mul, aliceZProj_sum, Matrix.one_mul]
  exact s.trace_one

/-- The Alice-`Z` pinching `Δ_A s = P₀ s P₀ + P₁ s P₁`, packaged as a `DensityOp 4`. -/
def aliceZDephase (s : DensityOp 4) : DensityOp 4 :=
  ⟨⟨⟨aliceZDephaseOp s, aliceZDephaseOp_isHermitian s⟩,
    fun x => posSemidef_re_quadraticForm_nonneg (aliceZDephaseOp_posSemidef s) x⟩,
   aliceZDephaseOp_trace s⟩

@[simp] lemma aliceZDephase_toOp (s : DensityOp 4) :
    (aliceZDephase s).toOp = aliceZDephaseOp s := rfl

/-! ## The Bell PVM -/

/-- The `k`-th Bell rank-one projector `|β_k⟩⟨β_k|`. -/
def bellProj (k : Fin 4) : Op 4 := bellStatesVec k * (bellStatesVec k).dag

lemma bellProj_mul_self (k : Fin 4) : bellProj k * bellProj k = bellProj k :=
  ketbra_idempotent (bellStatesVec k) (bellStatesVec_normalized k)

lemma bellProj_conjTranspose (k : Fin 4) : (bellProj k)† = bellProj k :=
  ketbra_hermitian (bellStatesVec k)

lemma bellProj_orthogonal (k l : Fin 4) (h : k ≠ l) : bellProj k * bellProj l = 0 := by
  apply ketbra_orthogonal_mul_zero
  have hortho := bellStates_orthonormal k l
  simp only [if_neg h] at hortho
  exact hortho

lemma bellProj_complete : ∑ y : Fin 4, bellProj y = 1 := by
  rw [Fin.sum_univ_four]
  change bellState00 * bellState00.dag + bellState01 * bellState01.dag +
      bellState10 * bellState10.dag + bellState11 * bellState11.dag = 1
  exact bell_projectors_sum_identity

/-! ## Support glue: `ker (Δ_A s) ⊆ ker s` -/

/-- Adjoint move for the sesquilinear form: `⟨v, A u⟩ = ⟨Aᴴ v, u⟩`. -/
private lemma star_dotProduct_mulVec_adj {n : ℕ} (A : Op n) (v u : Fin n → ℂ) :
    star v ⬝ᵥ A.mulVec u = star (Aᴴ.mulVec v) ⬝ᵥ u := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, star_sum,
    star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The pinching `Δ_A` spreads support: `ker (Δ_A s) ⊆ ker s`. Equivalently `supp s ⊆ supp (Δ_A s)`,
the support side-condition consumed by the projective-measurement DPI. -/
lemma aliceZDephase_ker_sub (s : DensityOp 4) :
    ∀ v : Fin 4 → ℂ, (aliceZDephase s).toOp.mulVec v = 0 → s.toOp.mulVec v = 0 := by
  intro v hv
  have hs : s.toOp.PosSemidef := posSemidefOp_implies_mathlib s.toPosSemidefOp
  have hkey : star v ⬝ᵥ (aliceZDephaseOp s).mulVec v = 0 := by
    have hΔ : (aliceZDephaseOp s).mulVec v = 0 := by rw [← aliceZDephase_toOp]; exact hv
    rw [hΔ, dotProduct_zero]
  have hterm : ∀ z : Fin 2,
      star v ⬝ᵥ (aliceZProj z * s.toOp * aliceZProj z).mulVec v
        = star ((aliceZProj z).mulVec v) ⬝ᵥ s.toOp.mulVec ((aliceZProj z).mulVec v) := by
    intro z
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      star_dotProduct_mulVec_adj, aliceZProj_conjTranspose]
  have hexpand : star v ⬝ᵥ (aliceZDephaseOp s).mulVec v
      = star ((aliceZProj 0).mulVec v) ⬝ᵥ s.toOp.mulVec ((aliceZProj 0).mulVec v)
        + star ((aliceZProj 1).mulVec v) ⬝ᵥ s.toOp.mulVec ((aliceZProj 1).mulVec v) := by
    unfold aliceZDephaseOp
    rw [Matrix.add_mulVec, dotProduct_add, hterm 0, hterm 1]
  rw [hexpand] at hkey
  have h0 := hs.dotProduct_mulVec_nonneg ((aliceZProj 0).mulVec v)
  have h1 := hs.dotProduct_mulVec_nonneg ((aliceZProj 1).mulVec v)
  obtain ⟨hz0, hz1⟩ := (add_eq_zero_iff_of_nonneg h0 h1).mp hkey
  have hsw0 : s.toOp.mulVec ((aliceZProj 0).mulVec v) = 0 :=
    (hs.dotProduct_mulVec_zero_iff _).mp hz0
  have hsw1 : s.toOp.mulVec ((aliceZProj 1).mulVec v) = 0 :=
    (hs.dotProduct_mulVec_zero_iff _).mp hz1
  have hvsum : (aliceZProj 0).mulVec v + (aliceZProj 1).mulVec v = v := by
    rw [← Matrix.add_mulVec, aliceZProj_sum, Matrix.one_mulVec]
  calc s.toOp.mulVec v
      = s.toOp.mulVec ((aliceZProj 0).mulVec v + (aliceZProj 1).mulVec v) := by rw [hvsum]
    _ = s.toOp.mulVec ((aliceZProj 0).mulVec v) + s.toOp.mulVec ((aliceZProj 1).mulVec v) :=
        Matrix.mulVec_add _ _ _
    _ = 0 := by rw [hsw0, hsw1, add_zero]

/-! ## E1 — the entropy-production identity -/

/-- **(E1)** The relative entropy of `s` against its Alice-`Z` pinching is the
entropy-production of the pinching:

`D(s ‖ Δ_A s) = S(Δ_A s) − S(s)`.

The hard direction is the pinching-trace invariance `Tr(s · log Δ_A s) = Tr(Δ_A s · log Δ_A s)`,
because `log Δ_A s` is block-diagonal in the `Z_A` blocks and `s`, `Δ_A s` share their
block-diagonal part. -/
theorem aliceZ_entropyProduction (s : DensityOp 4) :
    relativeEntropyReal s (aliceZDephase s)
      = vonNeumannEntropy (aliceZDephase s) - vonNeumannEntropy s := by
  haveI : NeZero 4 := ⟨by norm_num⟩
  set σ := aliceZDephase s with hσ
  set V := eigenbasisOf σ with hVdef
  set Λvec : Fin 4 → ℂ := fun i => (eigenvaluesOf σ i : ℂ) with hΛvec
  set dvec : Fin 4 → ℂ := fun i => (Real.log (eigenvaluesOf σ i) : ℂ) with hdvec
  set Lop : Op 4 := Vᴴ * Matrix.diagonal dvec * V with hLop
  have hVl : Vᴴ * V = 1 := eigenbasisOf_unitary_left σ
  have hVr : V * Vᴴ = 1 := eigenbasisOf_unitary_right σ
  have hspec : σ.toOp = Vᴴ * Matrix.diagonal Λvec * V :=
    (Classical.choose_spec (eigenvaluesOf_spec σ).2.2.2).2.2
  -- (claimA) traceProductLogSigma ρ σ = Re Tr(ρ Lop)
  have htrace_diag : ∀ (M : Op 4) (d : Fin 4 → ℂ),
      (M * Matrix.diagonal d).trace = ∑ i, M i i * d i := by
    intro M d
    simp [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  have claimA : ∀ ρ : DensityOp 4,
      traceProductLogSigma ρ σ = ((ρ.toOp * Lop).trace).re := by
    intro ρ
    have htr : (ρ.toOp * Lop).trace = ∑ i, (V * ρ.toOp * Vᴴ) i i * dvec i := by
      have h1 : ρ.toOp * Lop = ρ.toOp * Vᴴ * Matrix.diagonal dvec * V := by
        rw [hLop]; simp only [Matrix.mul_assoc]
      rw [h1, Matrix.trace_mul_comm (ρ.toOp * Vᴴ * Matrix.diagonal dvec) V]
      have h2 : V * (ρ.toOp * Vᴴ * Matrix.diagonal dvec)
          = (V * ρ.toOp * Vᴴ) * Matrix.diagonal dvec := by simp only [Matrix.mul_assoc]
      rw [h2, htrace_diag]
    rw [htr]
    unfold traceProductLogSigma diagonalOfRhoInSigmaBasis
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hdvec, ← hVdef, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  -- (claimB) Lop commutes with each block projector
  have hPσ : aliceZProj 0 * σ.toOp = σ.toOp * aliceZProj 0 := by
    have hL : aliceZProj 0 * σ.toOp = aliceZProj 0 * s.toOp * aliceZProj 0 := by
      rw [hσ, aliceZDephase_toOp]; unfold aliceZDephaseOp
      rw [Matrix.mul_add]
      rw [show aliceZProj 0 * (aliceZProj 0 * s.toOp * aliceZProj 0)
          = (aliceZProj 0 * aliceZProj 0) * s.toOp * aliceZProj 0 by simp only [Matrix.mul_assoc]]
      rw [show aliceZProj 0 * (aliceZProj 1 * s.toOp * aliceZProj 1)
          = (aliceZProj 0 * aliceZProj 1) * s.toOp * aliceZProj 1 by simp only [Matrix.mul_assoc]]
      rw [aliceZProj_mul_self, aliceZProj_mul_orthogonal (by decide : (0 : Fin 2) ≠ 1)]
      simp
    have hR : σ.toOp * aliceZProj 0 = aliceZProj 0 * s.toOp * aliceZProj 0 := by
      rw [hσ, aliceZDephase_toOp]; unfold aliceZDephaseOp
      rw [Matrix.add_mul]
      rw [show aliceZProj 0 * s.toOp * aliceZProj 0 * aliceZProj 0
          = aliceZProj 0 * s.toOp * (aliceZProj 0 * aliceZProj 0) by simp only [Matrix.mul_assoc]]
      rw [show aliceZProj 1 * s.toOp * aliceZProj 1 * aliceZProj 0
          = aliceZProj 1 * s.toOp * (aliceZProj 1 * aliceZProj 0) by simp only [Matrix.mul_assoc]]
      rw [aliceZProj_mul_self, aliceZProj_mul_orthogonal (by decide : (1 : Fin 2) ≠ 0)]
      simp
    rw [hL, hR]
  have hΛeq : V * σ.toOp * Vᴴ = Matrix.diagonal Λvec := by
    rw [hspec]
    rw [show V * (Vᴴ * Matrix.diagonal Λvec * V) * Vᴴ
        = (V * Vᴴ) * Matrix.diagonal Λvec * (V * Vᴴ) by simp only [Matrix.mul_assoc]]
    rw [hVr, Matrix.one_mul, Matrix.mul_one]
  set Q : Op 4 := V * aliceZProj 0 * Vᴴ with hQdef
  have hQΛ : Q * Matrix.diagonal Λvec = Matrix.diagonal Λvec * Q := by
    rw [hQdef, ← hΛeq]
    rw [show (V * aliceZProj 0 * Vᴴ) * (V * σ.toOp * Vᴴ)
        = V * aliceZProj 0 * (Vᴴ * V) * σ.toOp * Vᴴ by simp only [Matrix.mul_assoc]]
    rw [show (V * σ.toOp * Vᴴ) * (V * aliceZProj 0 * Vᴴ)
        = V * σ.toOp * (Vᴴ * V) * aliceZProj 0 * Vᴴ by simp only [Matrix.mul_assoc]]
    rw [hVl, Matrix.mul_one, Matrix.mul_one]
    rw [show V * aliceZProj 0 * σ.toOp * Vᴴ = V * (aliceZProj 0 * σ.toOp) * Vᴴ by
      simp only [Matrix.mul_assoc]]
    rw [hPσ]
    simp only [Matrix.mul_assoc]
  have hQd : Q * Matrix.diagonal dvec = Matrix.diagonal dvec * Q := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hQ0 : Q i j = 0
    · rw [hQ0]; ring
    · have hcomm := congrFun (congrFun hQΛ i) j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hcomm
      have hLamEq : Λvec j = Λvec i := by
        have : Q i j * Λvec j = Q i j * Λvec i := by rw [hcomm]; ring
        exact mul_left_cancel₀ hQ0 this
      have hd : dvec j = dvec i := by
        rw [hdvec]; simp only
        rw [show eigenvaluesOf σ j = eigenvaluesOf σ i from by
          have := hLamEq; rw [hΛvec] at this; simp only at this; exact_mod_cast this]
      rw [hd]; ring
  have claimB : aliceZProj 0 * Lop = Lop * aliceZProj 0 := by
    have hP0 : aliceZProj 0 = Vᴴ * Q * V := by
      rw [hQdef, show Vᴴ * (V * aliceZProj 0 * Vᴴ) * V
          = (Vᴴ * V) * aliceZProj 0 * (Vᴴ * V) by simp only [Matrix.mul_assoc]]
      rw [hVl, Matrix.one_mul, Matrix.mul_one]
    rw [hP0, hLop]
    rw [show (Vᴴ * Q * V) * (Vᴴ * Matrix.diagonal dvec * V)
        = Vᴴ * Q * (V * Vᴴ) * Matrix.diagonal dvec * V by simp only [Matrix.mul_assoc]]
    rw [show (Vᴴ * Matrix.diagonal dvec * V) * (Vᴴ * Q * V)
        = Vᴴ * Matrix.diagonal dvec * (V * Vᴴ) * Q * V by simp only [Matrix.mul_assoc]]
    rw [hVr, Matrix.mul_one, Matrix.mul_one]
    rw [show Vᴴ * Q * Matrix.diagonal dvec * V = Vᴴ * (Q * Matrix.diagonal dvec) * V by
      simp only [Matrix.mul_assoc]]
    rw [hQd]
    simp only [Matrix.mul_assoc]
  have claimB1 : aliceZProj 1 * Lop = Lop * aliceZProj 1 := by
    have h1 : aliceZProj 1 = 1 - aliceZProj 0 := by
      rw [← aliceZProj_sum]; abel
    rw [h1, Matrix.sub_mul, Matrix.mul_sub, claimB, Matrix.one_mul, Matrix.mul_one]
  -- (claimC) Tr(s Lop) = Tr(Δ_A s · Lop)
  have hPLP : ∀ z : Fin 2, aliceZProj z * Lop = Lop * aliceZProj z := by
    intro z; fin_cases z
    · exact claimB
    · exact claimB1
  have etrace : ∀ z : Fin 2, (aliceZProj z * s.toOp * aliceZProj z * Lop).trace
      = (s.toOp * (aliceZProj z * Lop)).trace := by
    intro z
    have hPLPz : aliceZProj z * Lop * aliceZProj z = aliceZProj z * Lop := by
      rw [Matrix.mul_assoc, ← hPLP z, ← Matrix.mul_assoc, aliceZProj_mul_self]
    have h1 : aliceZProj z * s.toOp * aliceZProj z * Lop
        = aliceZProj z * (s.toOp * aliceZProj z * Lop) := by simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm (aliceZProj z) (s.toOp * aliceZProj z * Lop)]
    have h2 : s.toOp * aliceZProj z * Lop * aliceZProj z
        = s.toOp * (aliceZProj z * Lop * aliceZProj z) := by simp only [Matrix.mul_assoc]
    rw [h2, hPLPz]
  have claimC : (s.toOp * Lop).trace = (σ.toOp * Lop).trace := by
    rw [hσ, aliceZDephase_toOp]
    unfold aliceZDephaseOp
    rw [Matrix.add_mul, Matrix.trace_add, etrace 0, etrace 1, ← Matrix.trace_add,
      ← Matrix.mul_add, ← Matrix.add_mul, aliceZProj_sum, Matrix.one_mul]
  -- assemble
  have hcore : traceProductLogSigma s σ = traceProductLogSigma σ σ := by
    rw [claimA s, claimA σ, claimC]
  have hself : traceProductLogSigma σ σ = -vonNeumannEntropy σ := by
    have h := relativeEntropyReal_self σ
    rw [relativeEntropyReal_eq] at h
    linarith
  rw [relativeEntropyReal_eq, hcore, hself]
  ring

/-! ## K1 helpers — explicit Bell / Alice-`Z` matrix identities -/

/-- The Alice-`Z` operator twirl `P₀ M P₀ + P₁ M P₁` (the pinching as a map on operators). -/
private def aliceZTwirl (M : Op 4) : Op 4 :=
  aliceZProj 0 * M * aliceZProj 0 + aliceZProj 1 * M * aliceZProj 1

private lemma aliceZTwirl_add (M N : Op 4) :
    aliceZTwirl (M + N) = aliceZTwirl M + aliceZTwirl N := by
  unfold aliceZTwirl
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

private lemma aliceZTwirl_smul_real (c : ℝ) (M : Op 4) :
    aliceZTwirl (c • M) = c • aliceZTwirl M := by
  unfold aliceZTwirl
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add]

/-- `Δ_A` and trace move: `Tr(B · Δ_A M) = Tr(Δ_A B · M)` (self-adjointness of the pinching). -/
private lemma trace_aliceZTwirl_move (B M : Op 4) :
    (B * aliceZTwirl M).trace = (aliceZTwirl B * M).trace := by
  unfold aliceZTwirl
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add]
  congr 1
  · rw [show B * (aliceZProj 0 * M * aliceZProj 0) = (B * aliceZProj 0 * M) * aliceZProj 0 by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm,
       show aliceZProj 0 * (B * aliceZProj 0 * M) = aliceZProj 0 * B * aliceZProj 0 * M by
        simp only [Matrix.mul_assoc]]
  · rw [show B * (aliceZProj 1 * M * aliceZProj 1) = (B * aliceZProj 1 * M) * aliceZProj 1 by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm,
       show aliceZProj 1 * (B * aliceZProj 1 * M) = aliceZProj 1 * B * aliceZProj 1 * M by
        simp only [Matrix.mul_assoc]]

/-- `bellProj 0` in terms of `bellState00`. -/
private lemma bellProj_zero : bellProj 0 = bellState00 * bellState00.dag := rfl
private lemma bellProj_one : bellProj 1 = bellState01 * bellState01.dag := rfl
private lemma bellProj_two : bellProj 2 = bellState10 * bellState10.dag := rfl
private lemma bellProj_three : bellProj 3 = bellState11 * bellState11.dag := rfl

/-- Entries of a Bell projector from the explicit Bell vector `ψ = (√2)⁻¹ • u`
(`bellState00_vec` …): `(|ψ⟩⟨ψ|)ᵢⱼ = ½ · uᵢ · conj uⱼ`. -/
private lemma bellKet_mul_dag_apply {ψ : Ket 4} {u : Fin 4 → ℂ}
    (h : ψ.vec = (Real.sqrt 2 : ℂ)⁻¹ • u) (i j : Fin 4) :
    (ψ * ψ.dag) i j = 1 / 2 * (u i * conj (u j)) := by
  rw [ket_mul_bra_apply, Ket.dag_vec, h, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    map_mul, ← inv_sqrt_two_sq, one_div]
  ring

/-- Entry formula for the Alice-`Z` twirl: it keeps the entries whose row and column lie in the
same Alice block (`i / 2 = j / 2`) and deletes the coherences between the two blocks. -/
private lemma aliceZTwirl_apply (M : Op 4) (i j : Fin 4) :
    aliceZTwirl M i j = if i.val / 2 = j.val / 2 then M i j else 0 := by
  simp only [aliceZTwirl, aliceZProj, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Fin.val_zero, Fin.val_one]
  have hi : i.val / 2 = 0 ∨ i.val / 2 = 1 := by omega
  have hj : j.val / 2 = 0 ∨ j.val / 2 = 1 := by omega
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> simp [hi, hj]

/-- The `Φ`-pair Bell projectors sum to the `{|00⟩,|11⟩}` block projector. -/
private lemma bellProj_sum_02 : bellProj 0 + bellProj 2 = Matrix.diagonal ![(1:ℂ),0,0,1] := by
  ext i j
  rw [Matrix.add_apply, bellProj_zero, bellProj_two, bellKet_mul_dag_apply bellState00_vec,
    bellKet_mul_dag_apply bellState10_vec, Matrix.diagonal_apply]
  -- each entry is an explicit sum of two terms `±1/2` or `0`
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- The `Ψ`-pair Bell projectors sum to the `{|01⟩,|10⟩}` block projector. -/
private lemma bellProj_sum_13 : bellProj 1 + bellProj 3 = Matrix.diagonal ![0,(1:ℂ),1,0] := by
  ext i j
  rw [Matrix.add_apply, bellProj_one, bellProj_three, bellKet_mul_dag_apply bellState01_vec,
    bellKet_mul_dag_apply bellState11_vec, Matrix.diagonal_apply]
  -- each entry is an explicit sum of two terms `±1/2` or `0`
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- `Δ_A` of each Bell projector is the half-weight block projector of its `Z_A`-pair. -/
private lemma aliceZTwirl_bellProj0 :
    aliceZTwirl (bellProj 0) = (1/2 : ℂ) • (bellProj 0 + bellProj 2) := by
  rw [bellProj_sum_02]
  ext i j
  rw [aliceZTwirl_apply, bellProj_zero, bellKet_mul_dag_apply bellState00_vec,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  -- on each explicit entry both sides are `±1/2` or `0`
  fin_cases i <;> fin_cases j <;> simp

private lemma aliceZTwirl_bellProj2 :
    aliceZTwirl (bellProj 2) = (1/2 : ℂ) • (bellProj 0 + bellProj 2) := by
  rw [bellProj_sum_02]
  ext i j
  rw [aliceZTwirl_apply, bellProj_two, bellKet_mul_dag_apply bellState10_vec,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  -- on each explicit entry both sides are `±1/2` or `0`
  fin_cases i <;> fin_cases j <;> simp

private lemma aliceZTwirl_bellProj1 :
    aliceZTwirl (bellProj 1) = (1/2 : ℂ) • (bellProj 1 + bellProj 3) := by
  rw [bellProj_sum_13]
  ext i j
  rw [aliceZTwirl_apply, bellProj_one, bellKet_mul_dag_apply bellState01_vec,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  -- on each explicit entry both sides are `±1/2` or `0`
  fin_cases i <;> fin_cases j <;> simp

private lemma aliceZTwirl_bellProj3 :
    aliceZTwirl (bellProj 3) = (1/2 : ℂ) • (bellProj 1 + bellProj 3) := by
  rw [bellProj_sum_13]
  ext i j
  rw [aliceZTwirl_apply, bellProj_three, bellKet_mul_dag_apply bellState11_vec,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  -- on each explicit entry both sides are `±1/2` or `0`
  fin_cases i <;> fin_cases j <;> simp

/-- A diagonal density operator has von Neumann entropy equal to the Shannon entropy of its
diagonal (using the identity as the diagonalizing unitary; nonnegativity and normalization of
the diagonal are inherited from the density operator). -/
private lemma vonNeumannEntropy_of_diagonal (ρ : DensityOp 4) (ev : Fin 4 → ℝ)
    (hdiag : ρ.toOp = Matrix.diagonal (fun i => (ev i : ℂ))) :
    vonNeumannEntropy ρ = Math.ClassicalEntropy.shannonEntropy ev := by
  haveI : NeZero 4 := ⟨by norm_num⟩
  have hPSD : ρ.toOp.PosSemidef := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have hnn : ∀ i, 0 ≤ ev i := by
    intro i
    have h := psd_conj_diag_nonneg hPSD (1 : Matrix (Fin 4) (Fin 4) ℂ) i
    simpa [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, hdiag,
      Matrix.diagonal_apply_eq] using h
  have hsum : ∑ i, ev i = 1 := by
    have h1 : ρ.toOp.trace = 1 := ρ.trace_one
    rw [hdiag, Matrix.trace_diagonal] at h1
    have h2 := congrArg Complex.re h1
    simpa [Complex.re_sum] using h2
  have hle : ∀ i, ev i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans_eq hsum
  apply vonNeumannEntropy_eq_shannonEntropy ρ ev
  refine ⟨hnn, hsum, hle, (1 : Op 4), ?_, ?_, ?_⟩
  · simp
  · simp
  · rw [hdiag]; simp

/-- The Bell-dephased state, expressed via the `bellProj` projectors. -/
private lemma bellDephasing_eq_bellProj_sum (s : DensityOp 4) :
    bellDephasing s =
      DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized) • bellProj 0 +
      DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized) • bellProj 1 +
      DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized) • bellProj 2 +
      DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized)
        • bellProj 3 := by
  rw [bellProj_zero, bellProj_one, bellProj_two, bellProj_three]; rfl

/-- The Alice-`Z` dephasing of the Bell-twirled state is the computational-diagonal operator
`diag(a/2, b/2, b/2, a/2)`, with `a` the `Φ`-pair Bell weight and `b` the `Ψ`-pair Bell weight. -/
private lemma aliceZDephase_bellDephasing_toOp_diagonal (s : DensityOp 4) :
    (aliceZDephase (bellDephasingDensity s)).toOp =
      Matrix.diagonal (fun i => ((![
        (DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized)
          + DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized)) / 2,
        (DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized)
          + DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized)) / 2,
        (DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized)
          + DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized)) / 2,
        (DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized)
          + DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized)) / 2]
        : Fin 4 → ℝ) i : ℂ)) := by
  rw [aliceZDephase_toOp]
  change aliceZTwirl ((bellDephasingDensity s).toOp) = _
  rw [bellDephasingDensity_toOp, bellDephasing_eq_bellProj_sum,
      aliceZTwirl_add, aliceZTwirl_add, aliceZTwirl_add,
      aliceZTwirl_smul_real, aliceZTwirl_smul_real, aliceZTwirl_smul_real, aliceZTwirl_smul_real,
      aliceZTwirl_bellProj0, aliceZTwirl_bellProj1, aliceZTwirl_bellProj2, aliceZTwirl_bellProj3,
      bellProj_sum_02, bellProj_sum_13]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul, Fin.ext_iff] <;>
    push_cast <;> ring

/-- The single Kullback–Leibler summand, split using `log(p/q) = log p − log q`. -/
private lemma kl_term_split (p q : ℝ) (hp : 0 ≤ p) (hq : p ≠ 0 → 0 < q) :
    (if p = 0 then 0 else p * Real.log (p / q)) = p * Real.log p - p * Real.log q := by
  split_ifs with h
  · subst h; simp
  · rw [Real.log_div h (hq h).ne']; ring

/-- Real part of the half-sum scalar. -/
private lemma half_add_re (z w : ℂ) : ((1/2 : ℂ) * (z + w)).re = (z.re + w.re) / 2 := by
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im]
  norm_num
  ring

/-- Explicit four-term Shannon entropy in `-(p·log p)` form. -/
private lemma shannonEntropy_four_eq (a b c d : ℝ) :
    Math.ClassicalEntropy.shannonEntropy ![a, b, c, d] =
      -(a * Real.log a) - (b * Real.log b) - (c * Real.log c) - (d * Real.log d) := by
  rw [Math.ClassicalEntropy.shannonEntropy, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, Math.ClassicalEntropy.entropyTerm_eq_neg_mul_log]
  ring

/-! ## The Alice-`Z` pinching entropy of a Bell-diagonal state -/

/-- Shannon entropy of the Alice-`Z`-split pair distribution `(a/2, b/2, b/2, a/2)` of a normalized
pair `a + b = 1`: splitting each of the two weights evenly across the two Alice blocks contributes
exactly one bit, `H(a/2, b/2, b/2, a/2) = log 2 + h(b)`. -/
private lemma shannonEntropy_halfPaired (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Math.ClassicalEntropy.shannonEntropy ![a / 2, b / 2, b / 2, a / 2] =
      Real.log 2 + Math.ClassicalEntropy.binaryEntropy b := by
  have key : ∀ x : ℝ, 0 ≤ x → x * Real.log (x / 2) = x * Real.log x - x * Real.log 2 := by
    intro x hx
    rcases eq_or_lt_of_le hx with h | h
    · simp [← h]
    · rw [Real.log_div (ne_of_gt h) (two_ne_zero)]; ring
  have hsum2 : a * Real.log 2 + b * Real.log 2 = Real.log 2 := by
    rw [← add_mul, hab, one_mul]
  have h1b : (1 : ℝ) - b = a := by linarith
  rw [shannonEntropy_four_eq, Math.ClassicalEntropy.binaryEntropy,
    Math.ClassicalEntropy.entropyTerm_eq_neg_mul_log,
    Math.ClassicalEntropy.entropyTerm_eq_neg_mul_log, h1b]
  linarith [key a ha, key b hb, hsum2]

/-- **The Alice-`Z` pinching entropy of a Bell-twirled state.**  `Δ_A (T s)` is the computational
diagonal `diag(a/2, b/2, b/2, a/2)` with `a` the `Φ`-pair Bell weight and `b = ⟨β₀₁|s|β₀₁⟩ +
⟨β₁₁|s|β₁₁⟩` the `Ψ`-pair (bit-flip) Bell weight, so

`S(Δ_A (T s)) = log 2 + h(b)`.

The `log 2` is Alice's uniform key bit (each Bell state is Alice-balanced) and `h(b)` is the
residual bit-error entropy: the pinching averages the **phase** index of the Bell weights and
leaves the bit index intact.  Together with `bellDephasing_entropy`
(`S(T s) = H(f₀₀,f₀₁,f₁₀,f₁₁)`) and `2×2` subadditivity this yields the **phase-only**
Devetak–Winter floor `1 − h(e_phase)`.

⚠ This identity is **false for a general `s`**: it holds on the Bell-diagonal state `T s` only, and
must be transferred to a general `s` through `aliceZDephasingRate_bellTwirl_monotone`. -/
theorem aliceZDephase_bellDephasing_entropy (s : DensityOp 4) :
    vonNeumannEntropy (aliceZDephase (bellDephasingDensity s)) =
      Real.log 2 + Math.ClassicalEntropy.binaryEntropy
        (DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized) +
          DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized)) := by
  have hn0 : 0 ≤ DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized) :=
    fidelityPureSq_nonneg s bellState00 bellState00_normalized
  have hn1 : 0 ≤ DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized) :=
    fidelityPureSq_nonneg s bellState01 bellState01_normalized
  have hn2 : 0 ≤ DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized) :=
    fidelityPureSq_nonneg s bellState10 bellState10_normalized
  have hn3 : 0 ≤ DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized) :=
    fidelityPureSq_nonneg s bellState11 bellState11_normalized
  have hsum := bell_fidelity_sum_eq_one s
  rw [vonNeumannEntropy_of_diagonal _ _ (aliceZDephase_bellDephasing_toOp_diagonal s)]
  exact shannonEntropy_halfPaired _ _ (by linarith) (by linarith) (by linarith)

/-! ## K1 — the Bell-measurement KL identity -/

/-- **(K1)** The Bell-measurement KL divergence of `(s, Δ_A s)` equals the entropy-production
rate of the Bell-twirled state:

`Σ_k [ p_k log(p_k/q_k) ]  =  S(Δ_A (T s)) − S(T s)`,

with `p_k = ⟨β_k|s|β_k⟩` and `q_k = ⟨β_k|Δ_A s|β_k⟩`. The left side is exactly the left side of the
projective measurement DPI for the Bell PVM `bellProj`; the remaining content is the
explicit `4×4` evaluation:

* `p_k = DensityOp.fidelitySq s (fromPure β_k …)` (Bell fidelity), so `Σ_k entropyTerm p_k = S(T s)`
  via `bellDephasing_eigenvalues`/`bellDephasing_entropy` (`bellProj k`-trace via `trace_ketbra_mul`
  and `fidelitySq_fromPure`);
* `q_k = (s_ee + s_ff)/2` where `|e⟩,|f⟩` are the two computational vectors of `β_k`
  (`q₀ = q₂ = (s₀₀+s₃₃)/2 =: a/2`, `q₁ = q₃ = (s₁₁+s₂₂)/2 =: b/2`, `a+b = 1`), since `Δ_A β_k`
  splits `β_k` into one half-weight vector per Alice block;
* `Δ_A (T s) = diag(a/2, b/2, b/2, a/2)` (each Bell state is Alice-balanced), so
  `S(Δ_A (T s)) = log 2 + H(a, b)`; and the KL algebra
  `Σ_k p_k log(p_k/q_k) = -S(T s) - (a log(a/2) + b log(b/2)) = S(Δ_A (T s)) - S(T s)`. -/
theorem bellMeas_KL_eq_dephasingRate (s : DensityOp 4) :
    (∑ y : Fin 4,
        if ((bellProj y * s.toOp).trace).re = 0 then 0
        else ((bellProj y * s.toOp).trace).re *
          Real.log (((bellProj y * s.toOp).trace).re /
            ((bellProj y * (aliceZDephase s).toOp).trace).re))
      = vonNeumannEntropy (aliceZDephase (bellDephasingDensity s))
          - vonNeumannEntropy (bellDephasingDensity s) := by
  haveI : NeZero 4 := ⟨by norm_num⟩
  -- the four Bell fidelities (eigenvalues of `T s`) are non-negative
  have hn0 : 0 ≤ DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized) :=
    fidelityPureSq_nonneg s bellState00 bellState00_normalized
  have hn1 : 0 ≤ DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized) :=
    fidelityPureSq_nonneg s bellState01 bellState01_normalized
  have hn2 : 0 ≤ DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized) :=
    fidelityPureSq_nonneg s bellState10 bellState10_normalized
  have hn3 : 0 ≤ DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized) :=
    fidelityPureSq_nonneg s bellState11 bellState11_normalized
  -- p_y : the Bell-measurement probabilities are the Bell fidelities
  have hp0 : ((bellProj 0 * s.toOp).trace).re =
      DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized) := by
    rw [bellProj_zero, trace_ketbra_mul, fidelitySq_fromPure]
  have hp1 : ((bellProj 1 * s.toOp).trace).re =
      DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized) := by
    rw [bellProj_one, trace_ketbra_mul, fidelitySq_fromPure]
  have hp2 : ((bellProj 2 * s.toOp).trace).re =
      DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized) := by
    rw [bellProj_two, trace_ketbra_mul, fidelitySq_fromPure]
  have hp3 : ((bellProj 3 * s.toOp).trace).re =
      DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized) := by
    rw [bellProj_three, trace_ketbra_mul, fidelitySq_fromPure]
  -- q_y : the dephased Bell-measurement probabilities are the half block-weights
  have hq0 : ((bellProj 0 * (aliceZDephase s).toOp).trace).re
      = (((bellProj 0 * s.toOp).trace).re + ((bellProj 2 * s.toOp).trace).re) / 2 := by
    have htr : (bellProj 0 * (aliceZDephase s).toOp).trace
        = (1/2 : ℂ) * ((bellProj 0 * s.toOp).trace + (bellProj 2 * s.toOp).trace) := by
      rw [aliceZDephase_toOp]
      change (bellProj 0 * aliceZTwirl s.toOp).trace = _
      rw [trace_aliceZTwirl_move, aliceZTwirl_bellProj0, Matrix.smul_mul, Matrix.trace_smul,
          Matrix.add_mul, Matrix.trace_add, smul_eq_mul]
    rw [htr]; exact half_add_re _ _
  have hq1 : ((bellProj 1 * (aliceZDephase s).toOp).trace).re
      = (((bellProj 1 * s.toOp).trace).re + ((bellProj 3 * s.toOp).trace).re) / 2 := by
    have htr : (bellProj 1 * (aliceZDephase s).toOp).trace
        = (1/2 : ℂ) * ((bellProj 1 * s.toOp).trace + (bellProj 3 * s.toOp).trace) := by
      rw [aliceZDephase_toOp]
      change (bellProj 1 * aliceZTwirl s.toOp).trace = _
      rw [trace_aliceZTwirl_move, aliceZTwirl_bellProj1, Matrix.smul_mul, Matrix.trace_smul,
          Matrix.add_mul, Matrix.trace_add, smul_eq_mul]
    rw [htr]; exact half_add_re _ _
  have hq2 : ((bellProj 2 * (aliceZDephase s).toOp).trace).re
      = (((bellProj 0 * s.toOp).trace).re + ((bellProj 2 * s.toOp).trace).re) / 2 := by
    have htr : (bellProj 2 * (aliceZDephase s).toOp).trace
        = (1/2 : ℂ) * ((bellProj 0 * s.toOp).trace + (bellProj 2 * s.toOp).trace) := by
      rw [aliceZDephase_toOp]
      change (bellProj 2 * aliceZTwirl s.toOp).trace = _
      rw [trace_aliceZTwirl_move, aliceZTwirl_bellProj2, Matrix.smul_mul, Matrix.trace_smul,
          Matrix.add_mul, Matrix.trace_add, smul_eq_mul]
    rw [htr]; exact half_add_re _ _
  have hq3 : ((bellProj 3 * (aliceZDephase s).toOp).trace).re
      = (((bellProj 1 * s.toOp).trace).re + ((bellProj 3 * s.toOp).trace).re) / 2 := by
    have htr : (bellProj 3 * (aliceZDephase s).toOp).trace
        = (1/2 : ℂ) * ((bellProj 1 * s.toOp).trace + (bellProj 3 * s.toOp).trace) := by
      rw [aliceZDephase_toOp]
      change (bellProj 3 * aliceZTwirl s.toOp).trace = _
      rw [trace_aliceZTwirl_move, aliceZTwirl_bellProj3, Matrix.smul_mul, Matrix.trace_smul,
          Matrix.add_mul, Matrix.trace_add, smul_eq_mul]
    rw [htr]; exact half_add_re _ _
  -- S(T s)
  have hSTs : vonNeumannEntropy (bellDephasingDensity s) =
      Math.ClassicalEntropy.shannonEntropy
        ![DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized),
          DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized),
          DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized),
          DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized)] :=
    bellDephasing_entropy s
  -- S(Δ_A (T s))
  have hSDelta : vonNeumannEntropy (aliceZDephase (bellDephasingDensity s)) =
      Math.ClassicalEntropy.shannonEntropy
        ![(DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized)
            + DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized)) / 2,
          (DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized)
            + DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized)) / 2,
          (DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized)
            + DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized)) / 2,
          (DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized)
            + DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized))
            / 2] :=
    vonNeumannEntropy_of_diagonal _ _ (aliceZDephase_bellDephasing_toOp_diagonal s)
  -- positivity of the dephased weights when the fidelity is nonzero
  have hqpos0 : DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized) ≠ 0 →
      0 < (DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized)
        + DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized)) / 2 :=
    fun h => by have := lt_of_le_of_ne hn0 (Ne.symm h); linarith [hn2]
  have hqpos1 : DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized) ≠ 0 →
      0 < (DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized)
        + DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized)) / 2 :=
    fun h => by have := lt_of_le_of_ne hn1 (Ne.symm h); linarith [hn3]
  have hqpos2 : DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized) ≠ 0 →
      0 < (DensityOp.fidelitySq s (DensityOp.fromPure bellState00 bellState00_normalized)
        + DensityOp.fidelitySq s (DensityOp.fromPure bellState10 bellState10_normalized)) / 2 :=
    fun h => by have := lt_of_le_of_ne hn2 (Ne.symm h); linarith [hn0]
  have hqpos3 : DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized) ≠ 0 →
      0 < (DensityOp.fidelitySq s (DensityOp.fromPure bellState01 bellState01_normalized)
        + DensityOp.fidelitySq s (DensityOp.fromPure bellState11 bellState11_normalized)) / 2 :=
    fun h => by have := lt_of_le_of_ne hn3 (Ne.symm h); linarith [hn1]
  -- assemble
  rw [hSDelta, hSTs, shannonEntropy_four_eq, shannonEntropy_four_eq, Fin.sum_univ_four,
      hq0, hq1, hq2, hq3, hp0, hp1, hp2, hp3,
      kl_term_split _ _ hn0 hqpos0, kl_term_split _ _ hn1 hqpos1,
      kl_term_split _ _ hn2 hqpos2, kl_term_split _ _ hn3 hqpos3]
  ring

/-! ## A.4-core — Bell-twirl monotonicity of the entropy-production rate -/

/-- **(A.4-core)** The Bell twirl does not increase the Alice-`Z`
entropy-production rate `r(ρ) = S(Δ_A ρ) − S(ρ)`:

`r(T s) = S(Δ_A (T s)) − S(T s)  ≤  S(Δ_A s) − S(s) = r(s)`.

Proof: the projective-measurement data-processing inequality for the Bell PVM on the
pair `(s, Δ_A s)`, with the left side identified as `r(T s)` (K1) and the right side as `r(s)`
(E1). Tight at Bell-diagonal `s` (where `T s = s`). -/
theorem aliceZDephasingRate_bellTwirl_monotone (s : DensityOp 4) :
    vonNeumannEntropy (aliceZDephase (bellDephasingDensity s))
        - vonNeumannEntropy (bellDephasingDensity s)
      ≤ vonNeumannEntropy (aliceZDephase s) - vonNeumannEntropy s := by
  haveI : NeZero 4 := ⟨by norm_num⟩
  have hdpi := projective_measurement_dpi_of_ker_sub bellProj
    bellProj_mul_self bellProj_conjTranspose bellProj_orthogonal bellProj_complete
    s (aliceZDephase s) (aliceZDephase_ker_sub s)
  rw [bellMeas_KL_eq_dephasingRate s, aliceZ_entropyProduction s] at hdpi
  exact hdpi

end QKD.BB84.Engine

end
