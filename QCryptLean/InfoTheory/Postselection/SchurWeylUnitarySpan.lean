import QCryptLean.Quantum.Symmetry.TensorPowerPolarization
import QCryptLean.InfoTheory.Postselection.SchurWeylTwirl

/-!
# QKD postselection — Schur–Weyl "unitaries suffice" (`SL-Unit`)

The `SL-Unit` sub-lemma of the duality-free route to SP1. It states that, on the pure `R`-side, the
commutant of
the *unitary* tensor-power family coincides with the commutant of the *full matrix* tensor-power
family:

`Com({U^{⊗n} : U ∈ U(dR)}) = Com({A^{⊗n} : A ∈ M_{dR}})`.

This is the "unitaries suffice" step of the classical (character-free, Weyl-module-free) proof of
the Schur–Weyl commutant identity. Composed with `SL-Pol` (polarization, span of tensor powers =
the `Sₙ`-invariant subalgebra) and `SL-Bicom` (finite-dimensional bicommutant), it yields
`commutant_unitaryTensorPow_eq_permSpan`; lifted through `SL-TensorLift`
(`commutant_pairedTensorFamily_eq_tensorCommutantSpan`,
`QCryptLean/Quantum/TensorProducts/PairedTensorCommutant.lean`) it discharges the R-side of
the E2 commutant half,
which E1c (`twirlMap_eq_iff_commute`,
`QCryptLean/InfoTheory/Postselection/SchurWeylTwirlProjection.lean`) consumes.

## Main statement
- `InfoTheory.Postselection.commutant_unitaryTensorPow_eq_commutant_tensorPow` (`SL-Unit`):
  the unitary and full-matrix tensor-power commutants coincide, for all `dR, n`.

## Fidelity / correctness

This commutant identity holds
**unconditionally** for all `dR ≥ 1`, `n ≥ 1` (sampled Haar-unitary rank computations:
`dim Com({U^{⊗n}}) = dim span{P(π)}` matched exactly at `(dR,n) ∈ {(2,2),(2,3),(3,2),(2,4),(4,2)}`,
including the linearly-dependent `dR < n` regime). No `dA ≤ dR` hypothesis and no `A`-register enter
this sub-lemma; only `[NeZero dR]` is carried, purely to match the ambient
`Matrix.unitaryGroup (Fin dR) ℂ` / `Op` API convention (as with `permCommutant`), never as a
mathematical precondition for the equality.

## Proof

The `⊇` inclusion (`RHS ⊆ LHS`: a `T` commuting with every `A^{⊗n}` in particular commutes with
`U^{⊗n}` for unitary `U`, since `Matrix.unitaryGroup (Fin dR) ℂ` coerces into `Op dR`) is proved
directly below.

The load-bearing `⊆` inclusion (`LHS ⊆ RHS`: a `T` commuting with every *unitary* tensor power
commutes with every *matrix* tensor power) is discharged by the classical
character → spectral → polar → finite-root-density chain:

1. **Character step** (`commute_scalar_exp_core`, `commute_diagonal_exp_of_forall`,
   `commute_tensorPow_posDiag`). Because `Op.tensorPow` of a diagonal matrix is diagonal
   (`Op.tensorPow_diagonal`), each off-frequency entry of `Commute (D^{it})^{⊗n} T` is killed by
   evaluating at a single well-chosen `t₀ = π/(a-b)`; no exponential linear-independence lemma is
   needed. This puts every positive-diagonal `^{⊗n}` in the commutant of `T`.
2. **Spectral step** (`commute_tensorPow_posDef`). `Matrix.IsHermitian.spectral_theorem`
   diagonalizes a positive-definite `P = V D₀ Vᴴ` with `V` unitary and `D₀` positive-diagonal;
   `P^{⊗n} = V^{⊗n} D₀^{⊗n} (Vᴴ)^{⊗n}` is a product of three commutants of `T`.
3. **Polar step** (`commute_tensorPow_isUnit`). For invertible `A`, `P := √(AᴴA)` is
   positive-definite (`IsStrictlyPositive.sqrt`) and `U := A P⁻¹` is unitary
   (`Matrix.mem_unitaryGroup_iff'`), giving `A = U P` with both factors already covered.
4. **Density step** (`commute_tensorPow_of_commute_unitaryTensorPow`, the internal theorem
   closing the load-bearing inclusion). For arbitrary `A`, the map
   `z ↦ [Op.tensorPow (A + z•1) n, T]` is continuous in `z ∈ ℂ`, vanishes off the finite root
   set of `(-A).charpoly` (`Matrix.eval_charpoly`, `Polynomial.finite_setOfPred_isRoot`), and that
   complement is dense (`Dense.sdiff_finite`); by `Continuous.ext_on` the map vanishes
   identically, in particular at `z = 0`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.Postselection

section CommuteChain

variable {dR n : ℕ} {T : Op (dR ^ n)}

/-! ## U1 — the scalar/diagonal character step -/

/-- The scalar character core: if `(e^{ita}-e^{itb})c = 0` for all real `t`, then already
`(e^a - e^b) c = 0`. Evaluating at a single `t₀ = π/(a-b)` (`a ≠ b`) makes the exponential
prefactor equal `-2 e^{it₀b} ≠ 0`. -/
private lemma commute_scalar_exp_core {a b : ℝ} {c : ℂ}
    (h : ∀ t : ℝ, (Complex.exp (Complex.I * (t : ℂ) * (a : ℂ))
                    - Complex.exp (Complex.I * (t : ℂ) * (b : ℂ))) * c = 0) :
    (Complex.exp (a : ℂ) - Complex.exp (b : ℂ)) * c = 0 := by
  by_cases hab : a = b
  · subst hab; simp
  · have hδ : a - b ≠ 0 := sub_ne_zero.mpr hab
    set t₀ : ℝ := Real.pi / (a - b) with ht0
    have h0 := h t₀
    have hexp_pi : Complex.I * (t₀ : ℂ) * ((a : ℂ) - (b : ℂ)) = (Real.pi : ℂ) * Complex.I := by
      have hkey : (t₀ : ℂ) * ((a : ℂ) - (b : ℂ)) = (Real.pi : ℂ) := by
        rw [ht0]
        push_cast
        rw [div_mul_cancel₀]
        exact_mod_cast hδ
      calc Complex.I * (t₀ : ℂ) * ((a : ℂ) - (b : ℂ))
          = (t₀ : ℂ) * ((a : ℂ) - (b : ℂ)) * Complex.I := by ring
        _ = (Real.pi : ℂ) * Complex.I := by rw [hkey]
    have hfactor : Complex.exp (Complex.I * (t₀ : ℂ) * (a : ℂ))
          - Complex.exp (Complex.I * (t₀ : ℂ) * (b : ℂ))
        = Complex.exp (Complex.I * (t₀ : ℂ) * (b : ℂ)) *
            (Complex.exp (Complex.I * (t₀ : ℂ) * ((a : ℂ) - (b : ℂ))) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      ring_nf
    rw [hexp_pi, Complex.exp_pi_mul_I] at hfactor
    rw [hfactor] at h0
    have hprefactor_ne : Complex.exp (Complex.I * (t₀ : ℂ) * (b : ℂ)) * (-1 - 1) ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) (by norm_num)
    have hc : c = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hprefactor_ne
      · exact h1
    rw [hc, mul_zero]

/-- Diagonal wrapper for `commute_scalar_exp_core`: if `diagonal (exp(itw))` commutes with `T`
for every real `t`, then `diagonal (exp w)` commutes with `T`. -/
private lemma commute_diagonal_exp_of_forall (w : Fin (dR ^ n) → ℝ)
    (h : ∀ t : ℝ, Commute (Matrix.diagonal
            (fun J => Complex.exp (Complex.I * (t : ℂ) * (w J : ℂ)))) T) :
    Commute (Matrix.diagonal (fun J => Complex.exp ((w J : ℝ) : ℂ))) T := by
  have hstep : ∀ (lam : Fin (dR ^ n) → ℂ), Commute (Matrix.diagonal lam) T ↔
      ∀ p q, lam p * T p q = T p q * lam q := by
    intro lam
    constructor
    · intro hc p q
      have := congrFun (congrFun hc p) q
      simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this
    · intro hc
      ext p q
      simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using hc p q
  rw [hstep]
  intro p q
  have hpq : ∀ t : ℝ, (Complex.exp (Complex.I * (t : ℂ) * (w p : ℂ))
        - Complex.exp (Complex.I * (t : ℂ) * (w q : ℂ))) * T p q = 0 := by
    intro t
    have ht := (hstep (fun J => Complex.exp (Complex.I * (t : ℂ) * (w J : ℂ)))).mp (h t) p q
    have := sub_eq_zero.mpr ht
    linear_combination this
  have := commute_scalar_exp_core hpq
  linear_combination this

/-- **Step 1 (`U2`): positive-diagonal `⊆ S_T`.** For strictly positive `μ : Fin dR → ℝ` and `T`
commuting with every unitary tensor power, `T` commutes with `(diagonal μ)^{⊗n}`. -/
private lemma commute_tensorPow_posDiag {μ : Fin dR → ℝ} (hμ : ∀ k, 0 < μ k)
    (hUnit : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ, Commute (Op.tensorPow (U : Op dR) n) T) :
    Commute (Op.tensorPow (Matrix.diagonal (fun k => (μ k : ℂ))) n) T := by
  set w : Fin (dR ^ n) → ℝ :=
    fun J => ∑ k : Fin n, Real.log (μ ((@finFunctionFinEquiv dR n).symm J k)) with hw
  -- Target rewrite: `(diag μ)^{⊗n} = diag (fun J => exp (w J))`.
  have htarget : Op.tensorPow (Matrix.diagonal (fun k => (μ k : ℂ))) n
      = Matrix.diagonal (fun J => Complex.exp ((w J : ℝ) : ℂ)) := by
    rw [Op.tensorPow_diagonal]
    congr 1
    funext J
    rw [hw]
    have hprod_eq : (∏ k : Fin n, ((μ ((@finFunctionFinEquiv dR n).symm J k) : ℝ) : ℂ))
        = ((∏ k : Fin n, μ ((@finFunctionFinEquiv dR n).symm J k) : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
    rw [hprod_eq]
    have hexp_eq : (∏ k : Fin n, μ ((@finFunctionFinEquiv dR n).symm J k))
        = Real.exp (∑ k : Fin n, Real.log (μ ((@finFunctionFinEquiv dR n).symm J k))) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun k _ => (Real.exp_log (hμ _)).symm
    rw [hexp_eq, Complex.ofReal_exp]
  rw [htarget]
  apply commute_diagonal_exp_of_forall w
  intro t
  have hUt_mem : (Matrix.diagonal (fun k : Fin dR =>
        Complex.exp (Complex.I * (t : ℂ) * (Real.log (μ k) : ℂ))))
      ∈ Matrix.unitaryGroup (Fin dR) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext k
    simp only [Pi.star_apply]
    have hconj : star (Complex.exp (Complex.I * (t : ℂ) * (Real.log (μ k) : ℂ)))
        = Complex.exp (- (Complex.I * (t : ℂ) * (Real.log (μ k) : ℂ))) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      simp
    rw [hconj, ← Complex.exp_add]
    simp
  set U : Matrix.unitaryGroup (Fin dR) ℂ :=
    ⟨Matrix.diagonal (fun k : Fin dR =>
        Complex.exp (Complex.I * (t : ℂ) * (Real.log (μ k) : ℂ))), hUt_mem⟩ with hU
  have hEntry : Op.tensorPow ((U : Matrix.unitaryGroup (Fin dR) ℂ) : Op dR) n
      = Matrix.diagonal (fun J => Complex.exp (Complex.I * (t : ℂ) * (w J : ℂ))) := by
    change Op.tensorPow (Matrix.diagonal (fun k : Fin dR =>
        Complex.exp (Complex.I * (t : ℂ) * (Real.log (μ k) : ℂ)))) n = _
    rw [Op.tensorPow_diagonal]
    congr 1
    funext J
    rw [hw]
    push_cast
    rw [Finset.mul_sum]
    rw [← Complex.exp_sum]
  rw [← hEntry]
  exact hUnit U

/-- **Step 2a (`U3`): positive-definite `⊆ S_T` (spectral theorem). -/
private lemma commute_tensorPow_posDef {P : Op dR} (hP : P.PosDef)
    (hUnit : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ, Commute (Op.tensorPow (U : Op dR) n) T) :
    Commute (Op.tensorPow P n) T := by
  have hH : P.IsHermitian := hP.isHermitian
  set V : Matrix.unitaryGroup (Fin dR) ℂ := hH.eigenvectorUnitary with hV
  have hspec : P = (V : Op dR) * Matrix.diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ))
      * (V : Op dR)ᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, ← hV]
    congr 2
  have hPn : Op.tensorPow P n
      = Op.tensorPow (V : Op dR) n
        * Op.tensorPow (Matrix.diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ))) n
        * Op.tensorPow ((V : Op dR)ᴴ) n := by
    have hcongr := congrArg (Op.tensorPow · n) hspec
    rw [Op.mul_tensorPow, Op.mul_tensorPow] at hcongr
    exact hcongr
  rw [hPn]
  have hc1 : Commute (Op.tensorPow (V : Op dR) n) T := hUnit V
  have hc2 : Commute (Op.tensorPow (Matrix.diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ))) n) T :=
    commute_tensorPow_posDiag (μ := hH.eigenvalues) (fun k => hP.eigenvalues_pos k) hUnit
  have hc3 : Commute (Op.tensorPow ((V : Op dR)ᴴ) n) T := by
    have hstar : (V : Op dR)ᴴ = ((star V : Matrix.unitaryGroup (Fin dR) ℂ) : Op dR) := by
      rw [← Matrix.star_eq_conjTranspose]
      rfl
    rw [hstar]
    exact hUnit (star V)
  exact (hc1.mul_left hc2).mul_left hc3

/-- **Step 2b (`U4`): invertible `⊆ S_T` (polar decomposition `A = U·P`,
`P = √(AᴴA)`, non-deprecated CFC route). -/
private lemma commute_tensorPow_isUnit {A : Op dR} (hA : IsUnit A)
    (hUnit : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ, Commute (Op.tensorPow (U : Op dR) n) T) :
    Commute (Op.tensorPow A n) T := by
  have hAunit : IsUnit (Aᴴ * A) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (isUnit_star.mpr hA).mul hA
  have hAhA : (Aᴴ * A).PosDef :=
    (Matrix.posSemidef_conjTranspose_mul_self A).posDef_iff_isUnit.mpr hAunit
  set P : Op dR := CFC.sqrt (Aᴴ * A) with hPdef
  have hPpd : P.PosDef := hAhA.isStrictlyPositive.sqrt.posDef
  have hPP : P * P = Aᴴ * A := CFC.sqrt_mul_sqrt_self (Aᴴ * A) hAhA.posSemidef.nonneg
  have hPdet : IsUnit P.det := P.isUnit_iff_isUnit_det.mp hPpd.isUnit
  set U : Op dR := A * P⁻¹ with hUdef
  have hstarU : star U = P⁻¹ * Aᴴ := by
    rw [hUdef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv, hPpd.isHermitian]
  have hUmem : U ∈ Matrix.unitaryGroup (Fin dR) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', hstarU, hUdef]
    rw [show P⁻¹ * Aᴴ * (A * P⁻¹) = P⁻¹ * (Aᴴ * A) * P⁻¹ from by noncomm_ring]
    rw [← hPP]
    rw [show P⁻¹ * (P * P) * P⁻¹ = (P⁻¹ * P) * (P * P⁻¹) from by noncomm_ring]
    rw [Matrix.nonsing_inv_mul P hPdet, Matrix.mul_nonsing_inv P hPdet, Matrix.mul_one]
  set Uunit : Matrix.unitaryGroup (Fin dR) ℂ := ⟨U, hUmem⟩ with hUunitdef
  have hAeq : A = U * P := by
    rw [hUdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet, Matrix.mul_one]
  have hAn : Op.tensorPow A n = Op.tensorPow U n * Op.tensorPow P n := by
    rw [hAeq, Op.mul_tensorPow]
  rw [hAn]
  have hc1 : Commute (Op.tensorPow U n) T := hUnit Uunit
  have hc2 : Commute (Op.tensorPow P n) T := commute_tensorPow_posDef hPpd hUnit
  exact hc1.mul_left hc2

end CommuteChain

/-- **Step 3 (`U5`): the density step — closes the load-bearing `⊆` inclusion of `SL-Unit`.**
For arbitrary `A : Op dR`, `A + z • 1` is invertible for cofinitely many `z ∈ ℂ` (the
complement of the finite root set of `(-A).charpoly`), and `z ↦ [Op.tensorPow (A + z•1) n, T]`
is continuous, vanishing on that dense cofinite set (`commute_tensorPow_isUnit`); by
`Continuous.ext_on` it vanishes identically, in particular at `z = 0`, giving
`Commute (Op.tensorPow A n) T`. -/
theorem commute_tensorPow_of_commute_unitaryTensorPow
    (dR n : ℕ) [NeZero dR] (T : Op (dR ^ n))
    (hUnit : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ, Commute (Op.tensorPow (U : Op dR) n) T)
    (A : Op dR) : Commute (Op.tensorPow A n) T := by
  set g : ℂ → Op (dR ^ n) := fun z =>
      Op.tensorPow (A + z • (1 : Op dR)) n * T - T * Op.tensorPow (A + z • (1 : Op dR)) n
      with hgdef
  suffices hgzero : g = fun _ => (0 : Op (dR ^ n)) by
    have h0 : g 0 = 0 := by rw [hgzero]
    simp only [hgdef, zero_smul, add_zero] at h0
    exact sub_eq_zero.mp h0
  -- Continuity of `g`.
  have hpow : Continuous (fun z : ℂ => Op.tensorPow (A + z • (1 : Op dR)) n) :=
    (Op.continuous_tensorPow n).comp (continuous_const.add (continuous_id.smul continuous_const))
  have hcont : Continuous g := by
    simp only [hgdef]
    exact (hpow.mul continuous_const).sub (continuous_const.mul hpow)
  -- The bad set (non-invertible shifts) is finite.
  have hscalar : ∀ z : ℂ, Matrix.scalar (Fin dR) z - (-A) = A + z • (1 : Op dR) := by
    intro z
    have hse : Matrix.scalar (Fin dR) z = z • (1 : Op dR) := by
      rw [Matrix.scalar_apply]
      ext i j
      simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    rw [sub_neg_eq_add, hse, add_comm]
  set bad : Set ℂ := Set.ofPred (fun z : ℂ => ¬ IsUnit (A + z • (1 : Op dR))) with hbaddef
  have hbad_eq : bad = Set.ofPred (fun z : ℂ => ((-A).charpoly).IsRoot z) := by
    ext z
    simp only [hbaddef, Set.mem_ofPred_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly, hscalar z]
    rw [(A + z • (1 : Op dR)).isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  have hbad_finite : bad.Finite := by
    rw [hbad_eq]
    exact Polynomial.finite_setOfPred_isRoot ((Matrix.charpoly_monic (-A)).ne_zero)
  have hdense : Dense badᶜ := by
    have hd : Dense ((Set.univ : Set ℂ) \ bad) := Dense.sdiff_finite dense_univ hbad_finite
    rwa [← Set.compl_eq_univ_sdiff] at hd
  have heq : Set.EqOn g (fun _ => (0 : Op (dR ^ n))) badᶜ := by
    intro z hz
    have hzu : IsUnit (A + z • (1 : Op dR)) := by
      simpa [hbaddef] using hz
    simp only [hgdef]
    exact sub_eq_zero.mpr (commute_tensorPow_isUnit hzu hUnit)
  exact Continuous.ext_on hdense hcont continuous_const heq

/-- **`SL-Unit` (unitaries suffice).** On the pure `R`-side, the commutant of the unitary
tensor-power family equals the commutant of the full matrix tensor-power family:
`Com({U^{⊗n} : U ∈ U(dR)}) = Com({A^{⊗n} : A ∈ M_{dR}})`.

The `⊇` inclusion (`RHS ⊆ LHS`) is immediate from the coercion
`Matrix.unitaryGroup (Fin dR) ℂ → Op dR`. The `⊆` inclusion is proved by the character → spectral
→ polar → finite-root-density chain (module docstring); see
`commute_tensorPow_of_commute_unitaryTensorPow`.

The unitary family is quantified exactly as in the `twirlMap_eq_iff_commute`, so the
paired-register composite (`Op.tensor (1 : Op (dA^n)) ·` via
`commutant_pairedTensorFamily_eq_tensorCommutantSpan`) type-checks against this output directly. -/
theorem commutant_unitaryTensorPow_eq_commutant_tensorPow (dR n : ℕ) [NeZero dR] :
    -- `Set.ofPred` (which delaborates to `{T | …}`) is used instead of the `{T : … | …}`
    -- set-builder notation because `open Quantum.Operators` brings the Dirac ket `|·⟩`
    -- notation, whose `|` token shadows the set-builder separator. The two forms produce
    -- the identical `Set (Op (dR ^ n))`.
    Set.ofPred (fun T : Op (dR ^ n) => ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
        Commute (Op.tensorPow (U : Op dR) n) T)
      = Set.ofPred (fun T : Op (dR ^ n) => ∀ A : Op dR, Commute (Op.tensorPow A n) T) := by
  ext T
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro _hUnit _A
    exact commute_tensorPow_of_commute_unitaryTensorPow dR n T _hUnit _A
  · -- `⊇` (RHS ⊆ LHS): trivial — every unitary coerces to a matrix.
    intro hAll U
    exact hAll (U : Op dR)

end InfoTheory.Postselection
