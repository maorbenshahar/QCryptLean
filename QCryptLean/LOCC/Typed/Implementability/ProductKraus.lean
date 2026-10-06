import QCryptLean.LOCC.Typed.LocalAction

/-!
# Product Kraus matrices for typed party registers

This module contains the matrix algebra behind the treewise product-Kraus description of a
finite-round LOCC protocol.  At each node only one party acts, and multiplication along a complete
history composes the local factors party by party.  This is the finite instrument-tree construction
of Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2 and the tree expansion in
Appendix A.
-/

open scoped Matrix BigOperators

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- The joint matrix obtained by multiplying one matrix entry from every party.

This is the typed-coordinate form of a tensor product of party-local Kraus matrices in the
separable-map representation discussed in Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2. -/
def famKraus {R S : MultipartiteSystem P} (K : ∀ i, Matrix (S.reg i) (R.reg i) ℂ) :
    Matrix S.total R.total ℂ :=
  Matrix.of fun a b => ∏ i, K i (a i) (b i)

/-- The family of identity matrices gives the identity joint matrix. -/
@[simp] theorem famKraus_one {R : MultipartiteSystem P} :
    famKraus (R := R) (S := R) (fun _ => 1) = 1 := by
  ext a b
  simp only [famKraus, Matrix.of_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

/-- Products of party-product matrices compose party by party.

This is the algebraic form of accumulating the local Kraus operators along a complete branch of
the LOCC tree in Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Appendix A. -/
theorem famKraus_mul {R M S : MultipartiteSystem P}
    (L : ∀ i, Matrix (S.reg i) (M.reg i) ℂ)
    (K : ∀ i, Matrix (M.reg i) (R.reg i) ℂ) :
    famKraus L * famKraus K = famKraus fun i => L i * K i := by
  ext a b
  simp only [famKraus, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun c _ => Finset.prod_mul_distrib.symm

/-- The local matrix family with `M` at the actor and identities at all spectators. -/
def MultipartiteSystem.localFam (R : MultipartiteSystem P) (i : P) (HH : Type)
    [Nonempty HH] [Fintype HH] [DecidableEq HH]
    (M : Matrix HH (R.reg i) ℂ) (j : P) : Matrix ((R.set i HH).reg j) (R.reg j) ℂ :=
  if hj : j = i then
    M.submatrix (Equiv.cast ((congrArg (R.set i HH).reg hj).trans (R.set_reg_self i HH)))
      (Equiv.cast (congrArg R.reg hj))
  else
    (1 : Matrix (R.reg j) (R.reg j) ℂ).submatrix
      (Equiv.cast (R.set_reg_of_ne i HH hj)) id

/-- The local family at its actor is the supplied matrix with its output index transported. -/
@[simp] theorem MultipartiteSystem.localFam_apply_self (R : MultipartiteSystem P) (i : P)
    (HH : Type) [Nonempty HH] [Fintype HH] [DecidableEq HH]
    (M : Matrix HH (R.reg i) ℂ) (a : (R.set i HH).reg i) (b : R.reg i) :
    R.localFam i HH M i a b = M (cast (R.set_reg_self i HH) a) b := by
  simp [MultipartiteSystem.localFam]

/-- The local family is the transported identity at every spectator. -/
theorem MultipartiteSystem.localFam_apply_of_ne (R : MultipartiteSystem P) (i : P)
    (HH : Type) [Nonempty HH] [Fintype HH] [DecidableEq HH]
    (M : Matrix HH (R.reg i) ℂ) {j : P} (hj : j ≠ i)
    (a : (R.set i HH).reg j) (b : R.reg j) :
    R.localFam i HH M j a b = if cast (R.set_reg_of_ne i HH hj) a = b then 1 else 0 := by
  simp only [MultipartiteSystem.localFam, dite_eq_right hj]
  rfl

/-- Componentwise coordinates for splitting off one party. -/
theorem MultipartiteSystem.splitAt_apply (R : MultipartiteSystem P) (i : P) (b : R.total) :
    R.splitAt i b = (b i, fun j : {j // j ≠ i} => b j) :=
  rfl

/-- A lifted local Kraus matrix is the product matrix with the local action at its actor and
identity factors at every spectator.

This is the single-node product-operator property used in the finite LOCC instrument tree of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2. -/
theorem localKrausLift_eq_famKraus (R : MultipartiteSystem P) (i : P) (HH : Type)
    [Nonempty HH] [Fintype HH] [DecidableEq HH] (M : Matrix HH (R.reg i) ℂ) :
    localKrausLift R i HH M = famKraus (R.localFam i HH M) := by
  ext a b
  have hL : localKrausLift R i HH M a b =
      M (cast (R.set_reg_self i HH) (a i)) (b i) *
        (1 : Matrix (R.rest i) (R.rest i) ℂ)
          (fun j => cast (R.set_reg_of_ne i HH j.2) (a j)) (fun j => b j) := by
    simp only [localKrausLift, Matrix.submatrix_apply, Matrix.kroneckerMap, Matrix.of_apply,
      MultipartiteSystem.splitAt_apply, MultipartiteSystem.splitAtSet_apply]
  rw [hL]
  simp only [famKraus, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), R.localFam_apply_self]
  congr 1
  by_cases hfg : (fun j : {j // j ≠ i} => cast (R.set_reg_of_ne i HH j.2) (a j)) =
      (fun j : {j // j ≠ i} => b j)
  · rw [hfg, Matrix.one_apply_eq]
    refine (Finset.prod_eq_one fun j hj => ?_).symm
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [R.localFam_apply_of_ne _ _ _ hji, ite_eq_left (congrFun hfg ⟨j, hji⟩)]
  · rw [Matrix.one_apply_ne hfg]
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hfg
    refine (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨j0.2, Finset.mem_univ _⟩) ?_).symm
    rw [R.localFam_apply_of_ne _ _ _ j0.2, ite_eq_right hj0]

/-- Every lifted Kraus matrix of an announced local action is a party-product matrix. -/
theorem AnnouncedAction.liftedKraus_eq_famKraus {R : MultipartiteSystem P} {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (A : AnnouncedAction R Y)
    (o : A.Outcome) (r : A.krausIndex o) :
    A.liftedKraus o r =
      famKraus (R.localFam A.actor (A.Output (A.announce o)) (A.kraus o r)) := by
  exact localKrausLift_eq_famKraus R A.actor (A.Output (A.announce o)) (A.kraus o r)

/-- Every lifted Kraus matrix of a private local action is a party-product matrix. -/
theorem PrivateAction.liftedKraus_eq_famKraus {R : MultipartiteSystem P} (A : PrivateAction R)
    (o : A.Outcome) (r : A.instrument.krausIndex o) :
    A.liftedKraus o r =
      famKraus (R.localFam A.actor A.Output (A.instrument.kraus o r)) := by
  exact localKrausLift_eq_famKraus R A.actor A.Output (A.instrument.kraus o r)

end TypedLOCC
