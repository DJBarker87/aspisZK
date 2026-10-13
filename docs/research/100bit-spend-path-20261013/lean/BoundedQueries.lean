import R1MatchingSupport
import R0C.V3.Q22Law

/-! The existing bounded, stopped q22 formal sampler applied to the concrete
two-fold matching support. The law is an unconditional successful-event
bound under independent answers. It does not refine Rust or instantiate the
shared-oracle Fiat--Shamir reduction. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.BoundedQueries

open AspisCircleGroupOrder AspisR1.MatchingSupport
open AspisV8R19.SourceDuplexStep AspisV8R19.CausalFirstHitUnionBound
open R0C.V3.Q22

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

/-- False functional claims give the exact q22 hypergeometric upper bound
for the bounded sampler's successful containment event. Failed scans have
zero event mass; there is no conditioning on successful sampling. -/
theorem no_claims_bounded_q22 (d : Data E) (s : State)
    (hgood : Good d) (haccepted : AcceptedPairing d) (hnot : ¬ Claims d) :
    chainE (fun bs xs => indicator
      ((chalSet (scanOut 8 q0 bs xs s).1).card = 22 ∧
        chalSet (scanOut 8 q0 bs xs s).1 ⊆ matchingSet d)) 8 ≤
      (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ) :=
  q22_bound s (matchingSet d) (no_claims_card_le d hgood haccepted hnot)

#print axioms no_claims_bounded_q22

end AspisR1.BoundedQueries
end
