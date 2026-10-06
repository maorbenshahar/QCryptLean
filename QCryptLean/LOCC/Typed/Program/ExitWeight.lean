import QCryptLean.LOCC.Typed.Program.GraftDenotation
import QCryptLean.LOCC.Typed.Instrument.Classical

/-!
# Exit weights of typed program outputs

The output of a typed LOCC program is block diagonal over its complete public exits
(`Program.denote_isExitBlockDiagonal`).  The *exit weight* of a set `E` of complete exits is the
real part of the trace of those blocks; for the output state of a run it is the probability that the
run ends at an exit in `E`.  This module proves the three structural facts every such probability
computation uses:

* a program's denotation preserves the trace (`Program.trace_denote`) and positivity
  (`Program.denote_posSemidef`), so the weights of complementary exit sets add up to the input trace
  (`Boundary.exitWeight_add_exitWeight_not`); register reindexing preserves the trace as well
  (`trace_reindexOp`);
* the exit weight of a grafted program is the sum, over the base program's complete exits, of the
  continuation's exit weight on the extracted base block (`Program.exitWeight_graft_denote`);
* transporting a program along equalities of its input multipartite system and output boundary
  transports its denotation by the corresponding coordinate casts (`Program.denote_cast`).

The public-history-dependent continuation is the finite-round LOCC instrument tree of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II; trace preservation is the
completeness condition of the flattened instrument.
-/

open scoped Matrix BigOperators ComplexOrder

namespace TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Reindexing a register along a bijection preserves the trace. -/
theorem trace_reindexOp {HH HH' : Type} [Fintype HH] [DecidableEq HH] [Fintype HH']
    [DecidableEq HH'] (e : HH ≃ HH') (M : Op HH) : (reindexOp e M).trace = M.trace :=
  Fintype.sum_equiv e.symm _ _ fun _ => rfl

namespace Boundary

/-- **The diagonal mass of a set of complete public exits.**

For an operator `M` on the output space, `B.exitWeight E M` is the real part of the trace of the
blocks of `M` at the complete public exits satisfying `E`.  For the output state of a run it is the
probability that the run ends at an exit in `E`. -/
noncomputable def exitWeight (B : Boundary P) (E : B.Exit → Prop) [DecidablePred E]
    (M : Op B.space) : ℝ :=
  ∑ q : B.space, if E q.1 then (M q q).re else 0

/-- The exit weight only depends on which exits satisfy the predicate. -/
theorem exitWeight_congr (B : Boundary P) {E E' : B.Exit → Prop} [DecidablePred E]
    [DecidablePred E'] (h : ∀ e, E e ↔ E' e) (M : Op B.space) :
    B.exitWeight E M = B.exitWeight E' M := by
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : E q.1
  · rw [if_pos hq, if_pos ((h q.1).mp hq)]
  · rw [if_neg hq, if_neg (fun h' => hq ((h q.1).mpr h'))]

/-- **Complementary exit sets partition the trace.** -/
theorem exitWeight_add_exitWeight_not (B : Boundary P) (E : B.Exit → Prop) [DecidablePred E]
    (M : Op B.space) :
    B.exitWeight E M + B.exitWeight (fun e => ¬ E e) M = (Matrix.trace M).re := by
  simp only [exitWeight, ← Finset.sum_add_distrib, Matrix.trace, Matrix.diag, Complex.re_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : E q.1 <;> simp [hq]

/-- The exit weight of the set of all exits is the real part of the trace. -/
theorem exitWeight_true (B : Boundary P) (M : Op B.space) :
    B.exitWeight (fun _ => True) M = (Matrix.trace M).re := by
  simp [exitWeight, Matrix.trace, Complex.re_sum]

/-- The exit weight of the empty set of exits is zero. -/
theorem exitWeight_false (B : Boundary P) (M : Op B.space) :
    B.exitWeight (fun _ => False) M = 0 := by
  simp [exitWeight]

/-- A positive semidefinite output assigns nonnegative weight to every set of exits. -/
theorem exitWeight_nonneg (B : Boundary P) (E : B.Exit → Prop) [DecidablePred E]
    {M : Op B.space} (hM : M.PosSemidef) : 0 ≤ B.exitWeight E M := by
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · exact (Complex.nonneg_iff.mp hM.diag_nonneg).1
  · exact le_rfl

/-- **The exit weight of a diagonal pushforward.**  If every diagonal entry of `M` collects the
weights `w i` of the indices `i` that `p` sends to it, then the weight of a set of exits collects
the real weights of the indices sent into it. -/
theorem exitWeight_eq_sum_of_diag {ι : Type} [Fintype ι] (B : Boundary P) (E : B.Exit → Prop)
    [DecidablePred E] (M : Op B.space) (p : ι → B.space) (w : ι → ℂ)
    (hM : ∀ q, M q q = ∑ i, if p i = q then w i else 0) :
    B.exitWeight E M = ∑ i, if E (p i).1 then (w i).re else 0 := by
  unfold exitWeight
  simp_rw [hM]
  calc
    _ = ∑ q : B.space, ∑ i, if p i = q then (if E q.1 then (w i).re else 0) else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : E q.1
      · rw [if_pos hq, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      · rw [if_neg hq]
        symm
        exact Finset.sum_eq_zero fun i _ => by split_ifs <;> rfl
    _ = ∑ i, ∑ q : B.space, if p i = q then (if E q.1 then (w i).re else 0) else 0 :=
      Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq]
      simp

/-- The weight of a set of exits is at most the real part of the trace of a positive semidefinite
output. -/
theorem exitWeight_le_trace (B : Boundary P) (E : B.Exit → Prop) [DecidablePred E]
    {M : Op B.space} (hM : M.PosSemidef) : B.exitWeight E M ≤ (Matrix.trace M).re := by
  rw [← B.exitWeight_add_exitWeight_not E M]
  exact le_add_of_nonneg_right (B.exitWeight_nonneg _ hM)

end Boundary

namespace Program

/-- **A typed program preserves the trace of every operator.**  This is the completeness of the
flattened path instrument (`Program.kraus_complete`). -/
theorem trace_denote {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) (ρ : Op R.total)
    :
    (p.denote ρ).trace = ρ.trace :=
  Instrument.channel_trace_eq p.toInstrument ρ

/-- **A typed program maps positive semidefinite operators to positive semidefinite operators.** -/
theorem denote_posSemidef {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B) {ρ : Op
    R.total}
    (hρ : ρ.PosSemidef) : (p.denote ρ).PosSemidef := by
  rw [denote_eq_krausSum, LinearMap.sum_apply]
  exact Matrix.posSemidef_sum _ fun b _ => hρ.mul_mul_conjTranspose_same (p.kraus b)

/-- **Exit weights through a graft.**

The exit weight of `p.graft k` on a set `E` of grafted exits is the sum over the complete exits `e`
of the base program `p` of the weight, on the pulled-back set of continuation exits, of the
continuation `k e` run on the block of `p`'s output extracted at `e`.  No positivity, trace or
reachability premise is used. -/
theorem exitWeight_graft_denote {R : MultipartiteSystem P} {B : Boundary P} (p : Program R B)
    {C : B.Exit → Boundary P} (k : ∀ e : B.Exit, Program (B.system e) (C e))
    (E : (B.graft C).Exit → Prop) [DecidablePred E] (ρ : Op R.total) :
    (B.graft C).exitWeight E ((p.graft k).denote ρ) =
      ∑ e : B.Exit, (C e).exitWeight (fun c => E ((B.graftExitEquiv C).symm ⟨e, c⟩))
        ((k e).denote ((Boundary.exitKraus B e)ᴴ * p.denote ρ * Boundary.exitKraus B e)) := by
  rw [denote_graft]
  unfold Boundary.exitWeight
  rw [← (Boundary.graftSpaceEquiv B C).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun r _ => ?_
  rw [LinearMap.comp_apply, controlledContinuation_sameExit,
    Boundary.graftSpaceEquiv_symm_fst]

/-- **Transport of a program along equalities of its input multipartite system and output
boundary.**

The denotation of the transported program is the original denotation conjugated by the two
coordinate casts. -/
theorem denote_cast {R R' : MultipartiteSystem P} {B B' : Boundary P} (hR : R = R') (hB : B = B')
    (p : Program R' B') (ρ : Op R.total) :
    (cast (by subst hR hB; rfl) p : Program R B).denote ρ =
      reindexOp (Equiv.cast (congrArg Boundary.space hB)).symm
        (p.denote (reindexOp (Equiv.cast (congrArg MultipartiteSystem.total hR)) ρ)) := by
  subst hR hB
  rfl

/-- **Point form of `Program.denote_cast`**: the transported program's denotation applied to two
coordinates is the original denotation applied to the reindexed operator and the coordinate
casts. -/
theorem denote_cast_apply {R R' : MultipartiteSystem P} {B B' : Boundary P}
    (hR : R = R') (hB : B = B') (p : Program R' B')
    (rho : Op R.total) (q q' : B.space) :
    (cast (by cases hR; cases hB; rfl) p : Program R B).denote rho q q' =
      p.denote (Matrix.reindex (Equiv.cast (congrArg MultipartiteSystem.total hR))
          (Equiv.cast (congrArg MultipartiteSystem.total hR)) rho)
        (Equiv.cast (congrArg Boundary.space hB) q)
        (Equiv.cast (congrArg Boundary.space hB) q') := by
  subst hR
  subst hB
  simp [Matrix.reindex_apply]

end Program

end TypedLOCC
