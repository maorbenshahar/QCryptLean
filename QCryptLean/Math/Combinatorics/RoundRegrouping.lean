import Mathlib.Algebra.BigOperators.Fin

/-!
# Regrouping pairs of finite digit strings

The equivalence takes a sequence of paired digits to a pair of sequences.
-/

namespace Equiv

/-- **Round-regrouping index equivalence** `Fin ((dA·dB)^n) ≃ Fin (dA^n · dB^n)`,
    The first block contains the first component of each pair.

    Takes the interleaved per-round digit tuple `(x₀,b₀,…,x_{n−1},b_{n−1})` on the
    round-grouped register `(dA·dB)^n` to the grouped pair
    `((x₀,…,x_{n−1}),(b₀,…,b_{n−1}))` on `dA^n · dB^n`, by:
    1. `finFunctionFinEquiv.symm` — unpack `Fin ((dA·dB)^n)` to `Fin n → Fin (dA·dB)`;
    2. `Equiv.piCongrRight (fun _ => finProdFinEquiv.symm)` — split each round digit
       into `(xₖ, bₖ) ∈ Fin dA × Fin dB`;
    3. `Equiv.arrowProdEquivProdArrow` — regroup to `(Fin n → Fin dA) × (Fin n → Fin dB)`;
    4. `Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv` — pack each block to
       `Fin (dA^n)`, `Fin (dB^n)`;
    5. `finProdFinEquiv` — pack the pair to `Fin (dA^n · dB^n)`.

    This is the tensor-structure regrouping permutation. A bare linear-index cast
    along `(dA·dB)^n = dA^n·dB^n` is **not** this map: it does not commute the
    interleaved digits into blocks. -/
def roundGroupEquiv (dA dB n : ℕ) :
    Fin ((dA * dB) ^ n) ≃ Fin (dA ^ n * dB ^ n) :=
  (finFunctionFinEquiv (m := dA * dB) (n := n)).symm.trans <|
    (Equiv.piCongrRight (fun _ : Fin n =>
        (finProdFinEquiv (m := dA) (n := dB)).symm)).trans <|
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin dA) (fun _ => Fin dB)).trans <|
    (Equiv.prodCongr
        (finFunctionFinEquiv (m := dA) (n := n))
        (finFunctionFinEquiv (m := dB) (n := n))).trans
      (finProdFinEquiv (m := dA ^ n) (n := dB ^ n))

end Equiv

open Equiv

/-- Decoding a regrouped index pairs the corresponding digits of its two blocks. -/
lemma finFunctionFinEquiv_symm_roundGroupEquiv_symm {dA dB n : ℕ}
    (I : Fin (dA ^ n * dB ^ n)) :
    finFunctionFinEquiv.symm ((roundGroupEquiv dA dB n).symm I) =
      fun k => finProdFinEquiv
        ((finFunctionFinEquiv.symm (finProdFinEquiv.symm I).1 : Fin n → Fin dA) k,
         (finFunctionFinEquiv.symm (finProdFinEquiv.symm I).2 : Fin n → Fin dB) k) := by
  funext k
  simp only [roundGroupEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply, Equiv.piCongrRight_symm_apply, Pi.map_apply,
    Equiv.arrowProdEquivProdArrow_symm_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd]

