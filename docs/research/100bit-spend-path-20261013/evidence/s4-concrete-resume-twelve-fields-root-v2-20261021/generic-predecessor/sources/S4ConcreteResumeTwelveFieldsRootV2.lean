import S4FullTx2CandidateFieldsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4ConcreteResumeTwelveFieldsRootV2
open AspisR1Stage2
open AspisR1S4P6PowersQueryJoinV1
open AspisR1FastDotsV10CandidateQueryFullWideBoundsV1

/-- Raw decoder-coordinate bounds imply the exact canonical coefficient
contract already used by the S4 powers and query proofs. The map changes
only type owners; no field operation or decoder is interpreted here. -/
theorem raw_bounds_claim_canonical
    (x : AspisR1Stage2.aspis_core.field.wide_exact.WideExact)
    (h : FullCoordinateBound x) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical (stage2ToClaim x) := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  change ((x.c0.c0.a.val < 2147483647 ∧ x.c0.c0.b.val < 2147483647) ∧
    (x.c0.c1.a.val < 2147483647 ∧ x.c0.c1.b.val < 2147483647)) ∧
    ((x.c1.c0.a.val < 2147483647 ∧ x.c1.c0.b.val < 2147483647) ∧
    (x.c1.c1.a.val < 2147483647 ∧ x.c1.c1.b.val < 2147483647))
  exact ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩

#print axioms raw_bounds_claim_canonical
end AspisR1S4ConcreteResumeTwelveFieldsRootV2
