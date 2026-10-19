import RRDenseCoeffVectorV6

set_option autoImplicit false

namespace AspisWide.GSRootCandidateContract

open Polynomial RRDenseCoeffVector

variable {K : Type} [Field K]

/-- State-free soundness and bounded completeness contract for the coefficient
lists returned by a root finder for one fixed bivariate polynomial. -/
def Candidates (Q : (K[X])[X]) (d : Nat) (cs : List (List K)) : Prop :=
  (∀ candidate ∈ cs, Q.eval (toPolynomial candidate) = 0) ∧
  ∀ f : K[X], Q.eval f = 0 → (f = 0 ∨ f.natDegree < d) →
    ∃ candidate ∈ cs, toPolynomial candidate = f

#print axioms Candidates

end AspisWide.GSRootCandidateContract
