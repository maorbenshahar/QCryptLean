import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Extending a finite-register equivalence

`Equiv.finProdCongrExt` transports the first factor and leaves the second factor fixed.
-/

namespace Equiv

/-- The "extend by identity on the ancilla `k`" companion of an index equivalence `e`, matching
    the `finProdFinEquiv` splitting used by `mapTensorId` / `partialTraceB`. -/
def finProdCongrExt {b a : ℕ} (e : Fin b ≃ Fin a) (k : ℕ) : Fin (b * k) ≃ Fin (a * k) :=
  finProdFinEquiv.symm.trans
    ((e.prodCongr (Equiv.refl (Fin k))).trans finProdFinEquiv)

@[simp] lemma finProdCongrExt_apply {b a : ℕ} (e : Fin b ≃ Fin a) (k : ℕ) (i : Fin b) (s : Fin k) :
    finProdCongrExt e k (finProdFinEquiv (i, s)) = finProdFinEquiv (e i, s) := by
  simp [finProdCongrExt]

@[simp] lemma finProdCongrExt_symm_apply {b a : ℕ} (e : Fin b ≃ Fin a) (k : ℕ)
    (i : Fin a) (s : Fin k) :
    (finProdCongrExt e k).symm (finProdFinEquiv (i, s)) = finProdFinEquiv (e.symm i, s) := by
  simp [finProdCongrExt]

/-- `finProdCongrExt` commutes with taking the inverse equivalence. -/
lemma finProdCongrExt_symm {b a : ℕ} (e : Fin b ≃ Fin a) (k : ℕ) :
    (finProdCongrExt e k).symm = finProdCongrExt e.symm k := rfl

end Equiv

/-- Reassociate flattened product coordinates while keeping the final block
coordinate separate. -/
def finProdFinEquiv_assoc_right (a b k : ℕ) :
    Fin (a * (b * k)) ≃ Fin (a * b) × Fin k :=
  finProdFinEquiv.symm.trans
    ((Equiv.refl _).prodCongr finProdFinEquiv.symm |>.trans
      (Equiv.prodAssoc _ _ _).symm |>.trans
      (finProdFinEquiv.prodCongr (Equiv.refl _)))
