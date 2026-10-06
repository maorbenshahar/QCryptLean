import QCryptLean.LOCC.Typed.Instrument.Classical
import QCryptLean.LOCC.Typed.Program.Denotation

/-!
# Classical private actions on typed programs

Entrywise semantics for deterministic classical functions executed as private typed LOCC
actions. The spectator coordinates remain independent in the output row and column. This is
the tensor-with-identity local operation of Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section II, specialized to deterministic classical postprocessing.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace TypedLOCC

namespace PrivateAction

/-- Entrywise operation of a local `functionAndForget` action on a joint register.

For output rows `q` and `q'`, the acting-party coordinates must both equal `f a` for the same
forgotten input value `a`.  The spectator coordinates of `q` and `q'` remain separate in the two
input indices of `rho`; in particular, this theorem does not discard spectator coherence.  This
is the exact local tensor-with-identity operation of the finite-round LOCC instrument tree in
Chitambar et al., arXiv:1210.4583, Section II, specialized to the deterministic classical
postprocessing used in Nahar et al., arXiv:2403.11851, lines 914--919. -/
theorem liftedOperation_ofInstrument_functionAndForget_apply
    {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P} (i : P) {HH : Type}
    [Nonempty HH] [Fintype HH] [DecidableEq HH]
    (f : R.reg i → HH) (rho : Op R.total) (q q' : (R.set i HH).total) :
    ((PrivateAction.ofInstrument i
        (Instrument.functionAndForget f)).liftedOperation () rho) q q' =
      ∑ a : R.reg i,
        if ((R.splitAtSet i HH) q).1 = f a ∧
            ((R.splitAtSet i HH) q').1 = f a then
          rho
            ((R.splitAt i).symm
              (a, ((R.splitAtSet i HH) q).2))
            ((R.splitAt i).symm
              (a, ((R.splitAtSet i HH) q').2))
        else 0 := by
  classical
  let rhoqq : Op (R.reg i) :=
    rho.submatrix
      (fun x => (R.splitAt i).symm
        (x, ((R.splitAtSet i HH) q).2))
      (fun y => (R.splitAt i).symm
        (y, ((R.splitAtSet i HH) q').2))
  have hsum (g : R.total → ℂ) :
      (∑ x, g x) =
        ∑ p : R.reg i × R.rest i, g ((R.splitAt i).symm p) := by
    exact (Equiv.sum_comp (R.splitAt i).symm g).symm
  have hlift
      (L : Instrument (R.reg i) (HH) Unit) :
      ((PrivateAction.ofInstrument i L).liftedOperation () rho) q q' =
        (L.operation () rhoqq)
          ((R.splitAtSet i HH) q).1
          ((R.splitAtSet i HH) q').1 := by
    change ((L.liftAt R i).operation () rho) q q' = _
    simp only [Instrument.liftAt, Instrument.operation, matrixConjLinear,
      LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
      Matrix.sum_apply, Matrix.mul_apply, localKrausLift_apply, ite_mul, zero_mul,
      Matrix.conjTranspose_apply, RCLike.star_def, rhoqq]
    simp_rw [hsum]
    simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
    simp [apply_ite]
    rfl
  rw [hlift (Instrument.functionAndForget f)]
  simp only [Instrument.functionAndForget_operation_apply, rhoqq,
    Matrix.submatrix_apply]

end PrivateAction

end TypedLOCC

