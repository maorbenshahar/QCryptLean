import QCryptLean.LOCC.Typed.Implementability.Separable
import QCryptLean.LOCC.Typed.Program.Uniform
import QCryptLean.LOCC.Typed.TwoParty
import QCryptLean.Quantum.Channels.Separable
import QCryptLean.Quantum.TensorProducts.ClassicalRegister

/-!
# Complete uniform-output channels are separable

Each complete hidden history of a typed two-party program contributes a product Kraus matrix.
Writing its full public transcript in the output's low tensor factor is a Bob-local isometry.
Consequently the complete channel is separable, with global Kraus completeness retained.
The input and output coordinates are the canonical product equivalences of the typed registers;
the output regrouping is the value-preserving associativity cast.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## Party registers at a uniform boundary

`Boundary.uniformSystemEquiv` identifies the register at a complete exit of a uniform boundary with
the boundary's defining joint register.  The product-Kraus description needs that identification one
party at a time. -/

namespace Boundary

/-- Every complete exit of a uniform boundary carries the defining multipartite system's register at
each party.

Like `Boundary.uniformSystemEquiv` this computes by recursion on the transcript word alone, so it
never transports across `Boundary.uniform_system`. -/
def uniformSystemRegEquiv (S : MultipartiteSystem P) (T : TList) (e : (uniform S T).Exit) (i : P) :
    ((uniform S T).system e).reg i ≃ (S).reg i :=
  match T with
  | .nil => Equiv.refl _
  | @TList.cons _ _ _ T => uniformSystemRegEquiv S T e.2 i

/-- The joint uniform-system identification acts party by party. -/
theorem uniformSystemEquiv_apply (S : MultipartiteSystem P) (T : TList) (e : (uniform S T).Exit)
    (q : ((uniform S T).system e).total) (i : P) :
    uniformSystemEquiv S T e q i = uniformSystemRegEquiv S T e i (q i) :=
  match T with
  | .nil => rfl
  | @TList.cons _ _ _ T => uniformSystemEquiv_apply S T e.2 q i

/-- `Boundary.uniformSystemEquiv` is the product of its party-local components. -/
theorem uniformSystemEquiv_eq_piCongrRight (S : MultipartiteSystem P) (T : TList)
    (e : (uniform S T).Exit) :
    uniformSystemEquiv S T e = Equiv.piCongrRight (uniformSystemRegEquiv S T e) :=
  Equiv.ext fun q => funext fun i => uniformSystemEquiv_apply S T e q i

end Boundary

namespace Program.ExitBranch

/-- The accumulated party factors of one complete hidden history, read at the single final
multipartite system of a uniform output boundary. -/
noncomputable def uniformPartyKraus {R S : MultipartiteSystem P} {T : TList}
    {p : Program R (Boundary.uniform S T)} {t : (Boundary.uniform S T).Exit}
    (b : p.ExitBranch t) (i : P) : Matrix ((S).reg i) ((R).reg i) ℂ :=
  (b.partyKraus i).submatrix (Boundary.uniformSystemRegEquiv S T t i).symm id

/-- Reading the party factors at the defining final multipartite system multiplies out to the
branch's joint product matrix, read at that multipartite system. -/
theorem famKraus_uniformPartyKraus {R S : MultipartiteSystem P} {T : TList}
    {p : Program R (Boundary.uniform S T)} {t : (Boundary.uniform S T).Exit}
    (b : p.ExitBranch t) :
    famKraus b.uniformPartyKraus =
      (famKraus b.partyKraus).submatrix (Boundary.uniformSystemEquiv S T t).symm id := by
  rw [Boundary.uniformSystemEquiv_eq_piCongrRight]
  rfl

end Program.ExitBranch

namespace TwoParty

variable {rA rB sA sB : ℕ} [NeZero rA] [NeZero rB] [NeZero sA] [NeZero sB]

local notation "R" => system (Fin rA) (Fin rB)
local notation "S" => system (Fin sA) (Fin sB)
local notation "rCoord" => Equiv.trans (pairEquiv (Fin rA) (Fin rB)) finProdFinEquiv
local notation "sCoord" => Equiv.trans (pairEquiv (Fin sA) (Fin sB)) finProdFinEquiv
local notation "outCoord(" T ", " e ")" =>
  Equiv.trans (Boundary.uniformSpaceEquiv S T)
    (Equiv.trans (Equiv.prodCongr sCoord e) finProdFinEquiv)

open Quantum.TensorProducts (appendIndexKraus appendIndexKraus_apply
  appendIndexKraus_conjTranspose_mul_self castRect_mul_appendIndexKraus)

private theorem prod_party {M : Type*} [CommMonoid M] (f : Party → M) :
    ∏ i, f i = f Party.alice * f Party.bob := by
  rw [show (Finset.univ : Finset Party) = {Party.alice, Party.bob} from rfl,
    Finset.prod_insert (by decide), Finset.prod_singleton]

/-- Canonical two-party coordinates turn a party-product matrix into a rectangular tensor. -/
theorem reindex_famKraus_eq_tensorRect (K : ∀ i, Matrix ((S).reg i) ((R).reg i) ℂ) :
    Matrix.reindex sCoord rCoord (famKraus K) =
      Quantum.TensorProducts.tensorRect (K Party.alice) (K Party.bob) := by
  ext i j
  let KA : Matrix (Fin sA) (Fin rA) ℂ := K Party.alice
  let KB : Matrix (Fin sB) (Fin rB) ℂ := K Party.bob
  change (∏ p : Party, K p ((sCoord).symm i p) ((rCoord).symm j p)) =
    Quantum.TensorProducts.tensorRect KA KB i j
  rw [Quantum.TensorProducts.tensorRect_apply, prod_party]
  rfl

/-- A complete public exit appends its full transcript label in canonical output coordinates. -/
theorem reindex_exitKraus_uniform {T : TList} {D : ℕ}
    (e : Transcript T ≃ Fin D) (t : (Boundary.uniform S T).Exit) :
    Matrix.reindex outCoord(T, e)
        ((Boundary.uniformSystemEquiv S T t).trans sCoord)
        (Boundary.exitKraus (Boundary.uniform S T) t) =
      appendIndexKraus (sA * sB) (e (Boundary.uniformExitEquiv S T t)) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Boundary.exitKraus_apply,
    appendIndexKraus_apply]
  refine if_congr ?_ rfl rfl
  rw [Equiv.symm_apply_eq]
  have hpair : Boundary.uniformSpaceEquiv S T
        ⟨t, (Boundary.uniformSystemEquiv S T t).symm ((sCoord).symm j)⟩ =
      ((sCoord).symm j, Boundary.uniformExitEquiv S T t) := by
    refine Prod.ext ?_ ?_
    · rw [Boundary.uniformSpaceEquiv_fst, Equiv.apply_symm_apply]
    · rw [Boundary.uniformSpaceEquiv_snd]
  change (i = outCoord(T, e)
    ⟨t, (Boundary.uniformSystemEquiv S T t).symm ((sCoord).symm j)⟩) ↔ _
  rw [show outCoord(T, e)
        ⟨t, (Boundary.uniformSystemEquiv S T t).symm ((sCoord).symm j)⟩ =
      finProdFinEquiv (j, e (Boundary.uniformExitEquiv S T t)) by
    simp only [Equiv.trans_apply, hpair, Equiv.prodCongr_apply,
      Prod.map_apply, Equiv.apply_symm_apply]]

/-- The complete-history Kraus matrix: the two local factors followed by the transcript write. -/
noncomputable def coordinateKraus {T : TList} {D : ℕ}
    (e : Transcript T ≃ Fin D) {p : Program R (Boundary.uniform S T)}
    {t : (Boundary.uniform S T).Exit} (b : p.ExitBranch t) :
    Matrix (Fin ((sA * sB) * D)) (Fin (rA * rB)) ℂ :=
  appendIndexKraus (sA * sB) (e (Boundary.uniformExitEquiv S T t)) *
    Quantum.TensorProducts.tensorRect (b.uniformPartyKraus Party.alice)
      (b.uniformPartyKraus Party.bob)

/-- The accumulated branch factors form the branch matrix in canonical two-party coordinates. -/
theorem reindex_famKraus_partyKraus {T : TList}
    {p : Program R (Boundary.uniform S T)}
    {t : (Boundary.uniform S T).Exit} (b : p.ExitBranch t) :
    Matrix.reindex ((Boundary.uniformSystemEquiv S T t).trans sCoord) rCoord
        (famKraus b.partyKraus) =
      Quantum.TensorProducts.tensorRect (b.uniformPartyKraus Party.alice)
        (b.uniformPartyKraus Party.bob) := by
  rw [← reindex_famKraus_eq_tensorRect, Program.ExitBranch.famKraus_uniformPartyKraus]
  rfl

/-- The native complete-history Kraus matrix has the stated canonical coordinates. -/
theorem reindex_exitKraus_mul_famKraus {T : TList} {D : ℕ}
    (e : Transcript T ≃ Fin D) {p : Program R (Boundary.uniform S T)}
    {t : (Boundary.uniform S T).Exit} (b : p.ExitBranch t) :
    Matrix.reindex outCoord(T, e) rCoord
        (Boundary.exitKraus (Boundary.uniform S T) t * famKraus b.partyKraus) =
      coordinateKraus e b := by
  rw [coordinateKraus, ← reindex_exitKraus_uniform e t, ← reindex_famKraus_partyKraus b]
  simp only [Matrix.reindex_apply]
  exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

/-- The complete channel is the sum of conjugations over every complete hidden history. -/
theorem coordinateDenote_apply_eq_sum {T : TList} {D : ℕ}
    (e : Transcript T ≃ Fin D) (p : Program R (Boundary.uniform S T))
    (ρ : Quantum.Operators.Op (rA * rB)) :
    (coordinateLinear rCoord outCoord(T, e) p.denote) ρ =
      ∑ x : Σ t : (Boundary.uniform S T).Exit, p.ExitBranch t,
        coordinateKraus e x.2 * ρ * (coordinateKraus e x.2)ᴴ := by
  have hsum : (∑ x : Σ t : (Boundary.uniform S T).Exit, p.ExitBranch t,
        matrixConjLinear (Boundary.exitKraus (Boundary.uniform S T) x.1 *
          famKraus x.2.partyKraus)) = p.denote :=
    (Fintype.sum_sigma _).trans p.denote_eq_exitBranchSum.symm
  rw [← hsum, coordinateLinear_sum]
  simp only [coordinateMatrixConj_eq, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [reindex_exitKraus_mul_famKraus]
  rfl

/-- The complete-history Kraus family satisfies the global completeness equation. -/
theorem sum_coordinateKraus_gram {T : TList} {D : ℕ}
    (e : Transcript T ≃ Fin D) (p : Program R (Boundary.uniform S T)) :
    (∑ x : Σ t : (Boundary.uniform S T).Exit, p.ExitBranch t,
      (coordinateKraus e x.2)ᴴ * coordinateKraus e x.2) = 1 := by
  have hgram : (∑ x : Σ t : (Boundary.uniform S T).Exit, p.ExitBranch t,
      (famKraus x.2.partyKraus)ᴴ * famKraus x.2.partyKraus) = 1 :=
    (Fintype.sum_sigma _).trans p.exitBranch_famKraus_gram_sum
  have hterm : ∀ x : Σ t : (Boundary.uniform S T).Exit, p.ExitBranch t,
      (coordinateKraus e x.2)ᴴ * coordinateKraus e x.2 =
        ((famKraus x.2.partyKraus)ᴴ * famKraus x.2.partyKraus).submatrix
          (rCoord).symm (rCoord).symm := by
    rintro ⟨t, b⟩
    rw [coordinateKraus, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (appendIndexKraus (sA * sB) (e (Boundary.uniformExitEquiv S T t)))ᴴ,
      appendIndexKraus_conjTranspose_mul_self, Matrix.one_mul,
      ← reindex_famKraus_partyKraus b]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
    exact Matrix.submatrix_mul_equiv _ _ _ _ _
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.submatrix_apply]
  rw [← Matrix.sum_apply, hgram, Matrix.one_apply, Matrix.one_apply]
  exact if_congr (Equiv.apply_eq_iff_eq _) rfl rfl

/-- Canonical output reassociation places the complete transcript in Bob's local factor. -/
theorem castRect_mul_coordinateKraus {T : TList} {D : ℕ}
    (e : Transcript T ≃ Fin D) {p : Program R (Boundary.uniform S T)}
    {t : (Boundary.uniform S T).Exit} (b : p.ExitBranch t) :
    Quantum.TensorProducts.castRect (sA * sB * D) (sA * (sB * D)) * coordinateKraus e b =
      Quantum.TensorProducts.tensorRect (b.uniformPartyKraus Party.alice)
        (HMul.hMul (β := Matrix (Fin sB) (Fin rB) ℂ)
          (appendIndexKraus sB (e (Boundary.uniformExitEquiv S T t)))
          (b.uniformPartyKraus Party.bob)) := by
  rw [coordinateKraus, ← Matrix.mul_assoc, castRect_mul_appendIndexKraus]
  let KA : Matrix (Fin sA) (Fin rA) ℂ := b.uniformPartyKraus Party.alice
  let KB : Matrix (Fin sB) (Fin rB) ℂ := b.uniformPartyKraus Party.bob
  change Quantum.TensorProducts.tensorRect (1 : Quantum.Operators.Op sA)
    (appendIndexKraus sB (e (Boundary.uniformExitEquiv S T t))) *
      Quantum.TensorProducts.tensorRect KA KB =
    Quantum.TensorProducts.tensorRect KA
      (appendIndexKraus sB (e (Boundary.uniformExitEquiv S T t)) * KB)
  rw [Quantum.TensorProducts.tensorRect_mul]
  exact congrArg (fun M : Matrix (Fin sA) (Fin rA) ℂ =>
    Quantum.TensorProducts.tensorRect M
      (appendIndexKraus sB (e (Boundary.uniformExitEquiv S T t)) *
        (show Matrix (Fin sB) (Fin rB) ℂ from b.uniformPartyKraus Party.bob)))
    (Matrix.one_mul _)

/-- The complete channel has a product-Kraus expansion with the transcript charged to Bob. -/
theorem castDim_coordinateDenote_apply {T : TList} {D : ℕ}
    (e : Transcript T ≃ Fin D) (p : Program R (Boundary.uniform S T))
    (ρ : Quantum.Operators.Op (rA * rB)) :
    Quantum.Operators.Op.castDimLinear (Nat.mul_assoc sA sB D)
      (coordinateLinear rCoord outCoord(T, e) p.denote ρ) =
      ∑ x : Σ t : (Boundary.uniform S T).Exit, p.ExitBranch t,
        Quantum.TensorProducts.tensorRect (x.2.uniformPartyKraus Party.alice)
            (HMul.hMul (β := Matrix (Fin sB) (Fin rB) ℂ)
              (appendIndexKraus sB (e (Boundary.uniformExitEquiv S T x.1)))
              (x.2.uniformPartyKraus Party.bob)) * ρ *
          (Quantum.TensorProducts.tensorRect (x.2.uniformPartyKraus Party.alice)
            (HMul.hMul (β := Matrix (Fin sB) (Fin rB) ℂ)
              (appendIndexKraus sB (e (Boundary.uniformExitEquiv S T x.1)))
              (x.2.uniformPartyKraus Party.bob)))ᴴ := by
  rw [Quantum.TensorProducts.castDimLinear_apply_eq_conj, coordinateDenote_apply_eq_sum,
    Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Quantum.TensorProducts.conj_mul_conj, castRect_mul_coordinateKraus]

/-- The complete uniform-output channel is separable across the two laboratories.

The output regrouping is the canonical associativity cast. Every complete hidden history is
retained, and the Kraus family satisfies global completeness: no exit is selected or erased. -/
theorem coordinateDenote_isSeparable {T : TList} {D : ℕ}
    (e : Transcript T ≃ Fin D) (p : Program R (Boundary.uniform S T)) :
    Quantum.Channels.IsSeparableOperation (rA := rA) (rB := rB)
      (sA := sA) (sB := sB * D)
      ((Quantum.Operators.Op.castDimLinear (Nat.mul_assoc sA sB D)).comp
        ((coordinateLinear rCoord outCoord(T, e) p.denote))) := by
  refine Quantum.Channels.isSeparableOperation_of_fintype
    (ι := Σ t : (Boundary.uniform S T).Exit, p.ExitBranch t) _
    (fun x => x.2.uniformPartyKraus Party.alice)
    (fun x => HMul.hMul (β := Matrix (Fin sB) (Fin rB) ℂ)
      (appendIndexKraus sB (e (Boundary.uniformExitEquiv S T x.1)))
      (x.2.uniformPartyKraus Party.bob))
    (fun ρ => castDim_coordinateDenote_apply e p ρ) ?_
  have hcast : ∀ x : Σ t : (Boundary.uniform S T).Exit, p.ExitBranch t,
      (Quantum.TensorProducts.tensorRect (x.2.uniformPartyKraus Party.alice)
          (HMul.hMul (β := Matrix (Fin sB) (Fin rB) ℂ)
            (appendIndexKraus sB (e (Boundary.uniformExitEquiv S T x.1)))
            (x.2.uniformPartyKraus Party.bob)))ᴴ *
        Quantum.TensorProducts.tensorRect (x.2.uniformPartyKraus Party.alice)
          (HMul.hMul (β := Matrix (Fin sB) (Fin rB) ℂ)
            (appendIndexKraus sB (e (Boundary.uniformExitEquiv S T x.1)))
            (x.2.uniformPartyKraus Party.bob))
        = (coordinateKraus e x.2)ᴴ * coordinateKraus e x.2 := by
    rintro ⟨t, b⟩
    rw [← castRect_mul_coordinateKraus e b, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Quantum.TensorProducts.castRect (sA * sB * D) (sA * (sB * D)))ᴴ,
      Quantum.TensorProducts.castRect_isometry (Nat.mul_assoc sA sB D), Matrix.one_mul]
  rw [Finset.sum_congr rfl fun x _ => hcast x]
  exact sum_coordinateKraus_gram e p

/-- Renumbering the transcript along a dimension equality casts the complete output channel. -/
theorem coordinateDenote_trans_finCongr {T : TList} {D D' : ℕ}
    (e : Transcript T ≃ Fin D) (h : D = D')
    (p : Program R (Boundary.uniform S T)) :
    coordinateLinear rCoord
        ((Boundary.uniformSpaceEquiv S T).trans
          ((Equiv.prodCongr sCoord (e.trans (finCongr h))).trans finProdFinEquiv)) p.denote =
      (Quantum.Operators.Op.castDimLinear (congrArg (fun d => (sA * sB) * d) h)).comp
        ((coordinateLinear rCoord outCoord(T, e) p.denote)) := by
  subst h
  rfl

end TwoParty

end TypedLOCC
