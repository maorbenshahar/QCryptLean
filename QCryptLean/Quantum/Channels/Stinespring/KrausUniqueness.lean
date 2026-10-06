import QCryptLean.Quantum.Channels.Stinespring.KrausChoi
import QCryptLean.Math.LinearAlgebra.UnitaryExtension

/-!
# Kraus Stinespring Uniqueness — marginal equality and minimal intertwiners

This file packages the generic Kraus-form uniqueness interface used by retained
environment arguments. It relates equality of Bob marginals to an isometric
intertwiner on the combined environment/Kraus index.

## Main statements
- `kraus_unique_partial_isometry_of_partialTraceB_eq`: marginally equal minimal Kraus
representations have a right-isometry intertwiner.
- `choiRank_singleIsometry_eq_one`: a single-isometry Kraus representation has Choi rank one.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- **Stacked-Kraus-matrix right-intertwiner from partial-trace-B equality.**

Let `kr : KrausRepresentation B (B*E)` and `kr' : KrausRepresentation B (B*E')`.
Assume the Bob marginal channels agree (`partialTraceB ∘ krausMapFintype kr = partialTraceB ∘
krausMapFintype kr'`),
and that both Kraus representations are minimal: `E * kr.numOps` and `E' * kr'.numOps` each
equal the Choi rank `r` of the common marginal channel.

Then there exists a partial isometry
`V : Matrix (Fin (E * kr.numOps)) (Fin (E' * kr'.numOps)) ℂ` (`V * Vᴴ * V = V`) on the
combined environment-Kraus index such that
`stackedKrausChoiVec kr = stackedKrausChoiVec kr' * Vᴴ`.

The minimality equalities force `E * kr.numOps = r = E' * kr'.numOps`, so `V` is a unitary.
The right-intertwiner `Vᴴ` relates the stacked Kraus matrices column-wise; by the
Choi-Jamiolkowski correspondence this encodes how the two Kraus representations differ by
a unitary reparametrisation of their combined environment-Kraus index.

An Eve-only intertwiner `V_eve : Fin E → Fin E'` acting via `id_B ⊗ V_eve` on the
`krausMapFintype` output type `Op (B * E)` does NOT exist in general: the output types
`Op (B * E)` and `Op (B * E')` are distinct when `E ≠ E'`, and no single operator
bridges them at the `krausMapFintype` level (the numOps index does not appear in the output
type).
The combined-index form at `stackedKrausChoiVec` level is the correct and always-valid
conclusion of Stinespring uniqueness in this setting.

Proof route:
1. Use `stackedKrausChoiVec_gram_eq_choi_marginal` to identify each row Gram with
   the Choi matrix of the corresponding Bob marginal channel.
2. Use marginal equality and the two minimality equalities to identify the combined
   column dimensions `E * kr.numOps` and `E' * kr'.numOps`.
3. Reindex the columns of `stackedKrausChoiVec kr'` across that equality and apply
   `exists_unitary_right_mul_of_row_gram_eq_full_col_rank`.
4. Convert the resulting square unitary back to the requested rectangular type by
   reindexing its adjoint.

References:
- Watrous (2018) *Theory of Quantum Information*, §2.2, Theorem 2.22.
- Paulsen (2002) *Completely Bounded Maps and Operator Algebras*, Ch. 4. -/
private theorem partialTraceB_krausMapFintype_eq_imp_choi_factorization_eq
    {B E E' : ℕ} [NeZero B] [NeZero E] [NeZero E']
    (kr : KrausRepresentation B (B * E))
    (kr' : KrausRepresentation B (B * E'))
    [NeZero kr.numOps] [NeZero kr'.numOps]
    [NeZero (B * E)] [NeZero (B * E')]
    (h_marginals : ∀ A : Op B,
      partialTraceB (krausMapFintype kr.operators A) =
        partialTraceB (krausMapFintype kr'.operators A))
    (h_min_kr : E * kr.numOps =
      Matrix.rank (ChoiMatrix B B (fun A => partialTraceB (krausMapFintype kr.operators A))))
    (h_min_kr' : E' * kr'.numOps =
      Matrix.rank (ChoiMatrix B B (fun A => partialTraceB (krausMapFintype kr'.operators A)))) :
    ∃ V : Matrix (Fin (E * kr.numOps)) (Fin (E' * kr'.numOps)) ℂ,
      Vᴴ * V = 1 ∧
      stackedKrausChoiVec kr = stackedKrausChoiVec kr' * Vᴴ := by
  classical
  have hfun :
      (fun A : Op B => partialTraceB (krausMapFintype kr.operators A)) =
        (fun A : Op B => partialTraceB (krausMapFintype kr'.operators A)) := by
    funext A
    exact h_marginals A
  have hchoi :
      ChoiMatrix B B (fun A : Op B => partialTraceB (krausMapFintype kr.operators A)) =
        ChoiMatrix B B (fun A : Op B => partialTraceB (krausMapFintype kr'.operators A)) := by
    rw [hfun]
  have hdim : E * kr.numOps = E' * kr'.numOps := by
    calc
      E * kr.numOps =
          Matrix.rank (ChoiMatrix B B
            (fun A : Op B => partialTraceB (krausMapFintype kr.operators A))) := h_min_kr
      _ = Matrix.rank (ChoiMatrix B B
            (fun A : Op B => partialTraceB (krausMapFintype kr'.operators A))) := by
            rw [hchoi]
      _ = E' * kr'.numOps := h_min_kr'.symm
  let e : Fin (E * kr.numOps) ≃ Fin (E' * kr'.numOps) := finCongr hdim
  let S'_cast : Matrix (Fin (B * B)) (Fin (E * kr.numOps)) ℂ :=
    (stackedKrausChoiVec kr').submatrix id e
  have hcast_gram :
      S'_cast * S'_castᴴ =
        (stackedKrausChoiVec kr') * (stackedKrausChoiVec kr')ᴴ := by
    ext i j
    simpa [S'_cast, Matrix.mul_apply, Matrix.conjTranspose_apply] using
      (e.sum_comp (fun k' : Fin (E' * kr'.numOps) =>
        stackedKrausChoiVec kr' i k' * star (stackedKrausChoiVec kr' j k')))
  have hgram :
      S'_cast * S'_castᴴ =
        (stackedKrausChoiVec kr) * (stackedKrausChoiVec kr)ᴴ := by
    rw [hcast_gram]
    exact (stackedKrausChoiVec_gram_eq_of_partialTraceB_krausMapFintype_eq
      kr kr' h_marginals).symm
  have hrank :
      Matrix.rank S'_cast = E * kr.numOps := by
    have hrank_cast :
        Matrix.rank S'_cast = Matrix.rank (stackedKrausChoiVec kr') := by
      simpa [S'_cast] using
        (Matrix.rank_submatrix (A := stackedKrausChoiVec kr')
          (em := Equiv.refl (Fin (B * B))) (en := e))
    calc
      Matrix.rank S'_cast = Matrix.rank (stackedKrausChoiVec kr') := hrank_cast
      _ = E' * kr'.numOps :=
        (stackedKrausChoiVec_rank_eq_choi_marginal_rank kr').trans h_min_kr'.symm
      _ = E * kr.numOps := hdim.symm
  obtain ⟨W, _hW_left, hW_right, hfactor⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_unitary_right_mul_of_row_gram_eq_full_col_rank
      S'_cast (stackedKrausChoiVec kr) hgram hrank
  let V : Matrix (Fin (E * kr.numOps)) (Fin (E' * kr'.numOps)) ℂ :=
    (Wᴴ).submatrix id e.symm
  refine ⟨V, ?_, ?_⟩
  · ext a b
    have hentry := congrFun (congrFun hW_right (e.symm a)) (e.symm b)
    simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using hentry
  · ext i j
    have hentry := congrFun (congrFun hfactor i) j
    rw [hentry]
    simpa [V, S'_cast, Matrix.mul_apply, Matrix.conjTranspose_apply] using
      (e.sum_comp (fun k' : Fin (E' * kr'.numOps) =>
        stackedKrausChoiVec kr' i k' * W (e.symm k') j))

/-- **Stinespring uniqueness up to a unitary on the combined env-Kraus index,
Bob-Eve Kraus form, minimal representations** (Watrous 2018, §2.2, Theorem 2.22).

Let `B`, `E`, `E'` be nonzero finite dimensions and let `kr`, `kr'` be Kraus
representations of CPTP maps `Φ : Op B → Op (B * E)` and `Φ' : Op B → Op (B * E')`.
Assume:
- the Bob marginal channels agree: `partialTraceB ∘ Φ = partialTraceB ∘ Φ'`;
- both representations are minimal: `E * kr.numOps = Choi rank` (`h_min_kr`) and
  `E' * kr'.numOps = Choi rank` (`h_min_kr'`).

Then there exists a matrix `V : Matrix (Fin (E * kr.numOps)) (Fin (E' * kr'.numOps)) ℂ`
satisfying:
- `Vᴴ * V = 1` (V is a right isometry; square unitary when `E * numOps = E' * numOps`);
- `stackedKrausChoiVec kr = stackedKrausChoiVec kr' * Vᴴ`.

Minimality makes the combined-index dimension equal to the shared Choi rank `r`, so the
intertwiner is a square unitary `Fin r → Fin r`. The partial-isometry body condition
`V * Vᴴ * V = V` follows from `Vᴴ * V = 1`.

This is an immediate application of `partialTraceB_krausMapFintype_eq_imp_choi_factorization_eq`.

References:
- Stinespring (1955) "Positive functions on C*-algebras".
- Paulsen (2002) "Completely Bounded Maps and Operator Algebras", Chapter 4.
- Watrous (2018) *Theory of Quantum Information*, §2.2, Theorem 2.22. -/
theorem kraus_unique_partial_isometry_of_partialTraceB_eq
    {B E E' : ℕ} [NeZero B] [NeZero E] [NeZero E']
    (kr : KrausRepresentation B (B * E))
    (kr' : KrausRepresentation B (B * E'))
    [NeZero kr.numOps] [NeZero kr'.numOps]
    [NeZero (B * E)] [NeZero (B * E')]
    (h : ∀ A : Op B,
      partialTraceB (krausMapFintype kr.operators A) =
        partialTraceB (krausMapFintype kr'.operators A))
    (h_min_kr : E * kr.numOps =
      Matrix.rank (ChoiMatrix B B (fun A => partialTraceB (krausMapFintype kr.operators A))))
    (h_min_kr' : E' * kr'.numOps =
      Matrix.rank (ChoiMatrix B B (fun A => partialTraceB (krausMapFintype kr'.operators A)))) :
    ∃ V : Matrix (Fin (E * kr.numOps)) (Fin (E' * kr'.numOps)) ℂ,
      Vᴴ * V = 1 ∧
      stackedKrausChoiVec kr = stackedKrausChoiVec kr' * Vᴴ := by
  exact partialTraceB_krausMapFintype_eq_imp_choi_factorization_eq kr kr' h h_min_kr h_min_kr'

/-- **The Choi rank of a single-isometry Kraus representation is 1.**

For any isometry `V : Matrix (Fin M) (Fin B) ℂ` with `Vᴴ * V = 1`, the single-operator
Kraus representation `{numOps := 1, operators := fun _ => V}` is minimal: the Choi
matrix of the channel `A ↦ V * A * Vᴴ` has rank 1.

Mathematical content: the Choi matrix of a pure quantum channel (single Kraus operator)
equals the outer product `|vec(V)⟩⟨vec(V)|` where `vec(V)` is the column-major
vectorization of V.  When V ≠ 0 (which is guaranteed by `Vᴴ * V = 1` for B ≥ 1),
this outer product has rank 1.  Hence `numOps = 1 = Choi rank`, establishing minimality.

Reference: Paulsen (2002) "Completely Bounded Maps and Operator Algebras", §2. -/
theorem choiRank_singleIsometry_eq_one
    {B M : ℕ} [NeZero B] [NeZero M]
    (V : Matrix (Fin M) (Fin B) ℂ) (hV : Vᴴ * V = 1) :
    (1 : ℕ) = Matrix.rank (ChoiMatrix B M (krausMapFintype (fun _ : Fin 1 => V))) := by
  set w : Fin (B * M) → ℂ := fun α =>
    V (finProdFinEquiv.symm α).2 (finProdFinEquiv.symm α).1 with hw_def
  have hChoi : ChoiMatrix B M (⇑(krausMapFintype (fun _ : Fin 1 => V))) =
      Matrix.vecMulVec w (star w) := by
    ext p q
    simp only [ChoiMatrix, Matrix.of_apply, krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.sum_univ_one, Matrix.vecMulVec, Pi.star_apply, hw_def]
    exact mul_unitMatrix_conjTranspose_apply V _ _ _ _
  have hw : w ≠ 0 := by
    intro heq
    have hV0 : V = 0 := by
      ext a i
      have h := congr_fun heq (finProdFinEquiv (i, a))
      simp only [hw_def, Equiv.symm_apply_apply, Pi.zero_apply] at h
      exact h
    simp [hV0] at hV
  have hstarw : star w ≠ 0 := by
    intro heq
    apply hw
    funext i
    have := congr_fun heq i
    simp only [Pi.star_apply, Pi.zero_apply] at this
    exact star_eq_zero.mp this
  have hMne : Matrix.vecMulVec w (star w) ≠ 0 :=
    Matrix.vecMulVec_ne_zero hw hstarw
  symm
  rw [hChoi]
  apply Nat.le_antisymm (Matrix.rank_vecMulVec_le w (star w))
  rw [Matrix.rank, Nat.one_le_iff_ne_zero]
  intro h0
  apply hMne
  have hml0 : ∀ v, (Matrix.vecMulVec w (star w)) *ᵥ v = 0 := fun v => by
    have := DFunLike.congr_fun
      (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0)) v
    simpa [Matrix.mulVecLin_apply] using this
  exact Matrix.ext_iff_mulVec.mpr fun v => by rw [hml0 v, Matrix.zero_mulVec]

end Quantum.Channels

end -- noncomputable section
