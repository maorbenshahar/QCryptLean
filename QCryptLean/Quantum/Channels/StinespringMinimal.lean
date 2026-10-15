import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.SpectralTheory.PSDDecomposition
import QCryptLean.Quantum.Channels.Stinespring

/-!
# Minimal Stinespring dilations

Let `Φ` be a quantum operation on finite registers and `choiMatrix Φ` its Choi
matrix.  This file proves the three basic size facts about Stinespring
representations of `Φ` (Watrous, *The Theory of Quantum Information*, 2018,
Section 2.2, Theorem 2.22):

* every Stinespring environment of `Φ` has at least `Matrix.rank (choiMatrix Φ)`
  elements (`StinespringRepresentation.rank_choiMatrix_le`): the stacked isometry
  has the Choi rank as its row rank;
* one environment of exactly that size exists
  (`IsChannel.exists_stinespring_fin_rank`): the rank-many rank-one outer
  products of the PSD Choi matrix are exactly a Kraus family for `Φ`;
* a representation whose environment has the Choi rank factors every other
  representation (`StinespringRepresentation.exists_isometry_mul_eq`): the other
  isometry is the minimal one followed by an isometry of the environments, so all
  Stinespring representations are unique up to such an isometry.
-/

noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped ComplexOrder Kronecker MatrixOrder

variable {X Y E F : Type*} [Fintype X] [Fintype Y] [Fintype E] [Fintype F]

/-- The entries of a Stinespring isometry stacked into an input-output-indexed matrix. -/
private def stackedIsometryVec {Φ : Operation X Y} (V : StinespringRepresentation Φ E) :
    Matrix (X × Y) E ℂ :=
  Matrix.of fun p k => V.isometry (p.2, k) p.1

omit [Fintype Y] in
/-- The Choi matrix of a Kraus map is the row Gram of the entry-stacked family. -/
private theorem choiMatrix_eq_stacked_gram (K : E → Matrix Y X ℂ) :
    choiMatrix (krausMap K) =
      (Matrix.of fun (p : X × Y) (k : E) => K k p.2 p.1) *
        (Matrix.of fun (p : X × Y) (k : E) => K k p.2 p.1)ᴴ := by
  rw [choiMatrix_krausMap]
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Matrix.of_apply]

/-- The Choi matrix of the channel of a Stinespring representation is the row Gram of
its stacked isometry. -/
private theorem choiMatrix_eq_stackedIsometryVec_gram {Φ : Operation X Y}
    (V : StinespringRepresentation Φ E) :
    choiMatrix Φ = (stackedIsometryVec V) * (stackedIsometryVec V)ᴴ := by
  have hK : krausMap V.kraus.operators = Φ := V.kraus_toOperation
  have h1 : choiMatrix Φ = choiMatrix (krausMap V.kraus.operators) :=
    congrArg choiMatrix hK.symm
  exact h1.trans (choiMatrix_eq_stacked_gram V.kraus.operators) |>.trans rfl

/-- Every Stinespring environment has at least as many elements as the rank of the Choi
matrix. -/
theorem StinespringRepresentation.rank_choiMatrix_le {Φ : Operation X Y}
    (V : StinespringRepresentation Φ E) :
    (choiMatrix Φ).rank ≤ Fintype.card E := by
  rw [choiMatrix_eq_stackedIsometryVec_gram V, Matrix.rank_self_mul_conjTranspose]
  exact Matrix.rank_le_card_width _

/-- A channel has a Stinespring representation whose environment has exactly the Choi
rank. -/
theorem IsChannel.exists_stinespring_fin_rank {Φ : Operation X Y} (h : IsChannel Φ) :
    Nonempty (StinespringRepresentation Φ (Fin (choiMatrix Φ).rank)) := by
  classical
  have hcp : (choiMatrix Φ).PosSemidef := h.1
  have hkey : ∃ v : Fin (choiMatrix Φ).rank → X × Y → ℂ,
      choiMatrix Φ = ∑ k, Matrix.vecMulVec (v k) (star (v k)) :=
    hcp.exists_eq_sum_vecMulVec
  obtain ⟨v, hv⟩ := hkey
  let K : Fin (choiMatrix Φ).rank → Matrix Y X ℂ := fun k a i => v k (i, a)
  have hKsum : ∑ i, Matrix.vecMulVec (fun p : X × Y => K i p.2 p.1)
      (star (fun p : X × Y => K i p.2 p.1)) =
      ∑ k, Matrix.vecMulVec (v k) (star (v k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    ext p q
    simp only [Matrix.vecMulVec_apply, Pi.star_apply]
    rfl
  have hK : krausMap K = Φ :=
    choiMatrix_injective ((choiMatrix_krausMap K).trans (hKsum.trans hv.symm))
  have htp : IsTracePreserving (krausMap K) := by rw [hK]; exact h.2
  have hcomp : ∑ k, (K k)ᴴ * K k = 1 := (isTracePreserving_krausMap_iff K).mp htp
  have hdil : StinespringRepresentation (krausMap K) (Fin (choiMatrix Φ).rank) :=
    KrausRepresentation.stinespring ⟨K, hcomp⟩
  rw [hK] at hdil
  exact ⟨hdil⟩

/-- A Stinespring representation through an environment of the Choi rank factors every
other one: the other isometry is the first one followed by an isometry of the
environments. -/
theorem StinespringRepresentation.exists_isometry_mul_eq [DecidableEq Y] [DecidableEq E]
    {Φ : Operation X Y} (V : StinespringRepresentation Φ E)
    (hV : Fintype.card E = (choiMatrix Φ).rank) (W : StinespringRepresentation Φ F) :
    ∃ T : Matrix F E ℂ, Tᴴ * T = 1 ∧
      W.isometry = ((1 : Matrix Y Y ℂ) ⊗ₖ T) * V.isometry := by
  have hgram : (stackedIsometryVec V) * (stackedIsometryVec V)ᴴ
      = (stackedIsometryVec W) * (stackedIsometryVec W)ᴴ :=
    (choiMatrix_eq_stackedIsometryVec_gram V).symm.trans
      (choiMatrix_eq_stackedIsometryVec_gram W)
  have hdim : Fintype.card E ≤ Fintype.card F := by
    rw [hV]
    exact W.rank_choiMatrix_le
  obtain ⟨U, hU, hstack⟩ := exists_coisometry_of_rowGram_eq
    (stackedIsometryVec V) (stackedIsometryVec W) hgram hdim
  refine ⟨Uᵀ, ?_, ?_⟩
  · have h1 : (U * Uᴴ)ᵀ = (1 : Matrix E E ℂ) := by
      ext i j
      have hui := congrFun (congrFun hU j) i
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
        Matrix.one_apply] at hui ⊢
      rw [hui]
      by_cases hij : i = j
      · rw [ite_eq_left hij.symm, ite_eq_left hij]
      · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, ← Matrix.transpose_mul]
    exact h1
  · ext p x
    obtain ⟨y, l⟩ := p
    have hentry := congrFun (congrFun hstack (x, y)) l
    simp only [stackedIsometryVec, Matrix.of_apply, Matrix.mul_apply] at hentry
    have hrhs : (((1 : Matrix Y Y ℂ) ⊗ₖ Uᵀ) * V.isometry) (y, l) x
        = ∑ k : E, U k l * V.isometry (y, k) x := by
      simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Matrix.transpose_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single y]
      · simp
      · intro y' _ hy'
        simp [Ne.symm hy']
      · intro h
        exact absurd (Finset.mem_univ y) h
    rw [hentry, hrhs]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end Quantum.Channels
