import QCryptLean.InfoTheory.QuantumLHL.SeedAvgVarianceCore

/-!
# Scope of single-σ variance bounds

An outer-form universality variance bound is false under Hermitian-only hypotheses:
a rank-one `T` with complex positive semidefinite blocks `R x` gives a counterexample.

The squared-sandwich bound `squared_sandwich_variance_pair_bound` in
`LambdaBoundSquaredCollisionAlgebra.lean` has a direct proof that does not use that bound.
-/
