import S4V10QueryOpsResultTransportV1
import S4ConcreteV10CandidateEndpointV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsV10ConcreteQueryOpsBuilderV1

open AspisR1Stage2
open AspisR1S4FullQueryValuesPrefixV1

open AspisR1FastDotsV10QueryOpsResultTransportV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10LiteralOuterTransferRootV1 (literalV10Outer)
open AspisR1S4FourWrapperCarrierTransportRootV1 (mapArray)
open AspisR1FastDotsV10CarrierMapV1 (wideToEbyK)

/-- QueryOps builder for the selected candidate source: its dots slot is
bound to the fully specified concrete V10 operation record, with the exact
FullWide-to-V10 carrier conversion used by the actual extracted query shape.
All non-dots operations are passed through unchanged. -/
def concreteCandidateQueryOps (rest : QueryOps) : QueryOps :=
  withLiteralDots concreteOps rest

theorem concrete_candidate_dots_is_literal_v10
    (q : Slice U8) (g : Array FullWide 29#usize) :
    (literalDots concreteOps q g) = (do
      let values ← literalV10Outer concreteOps q (fullArrayToV10 g)
      ok (currentArrayToFull (mapArray wideToEbyK values))) := by
  simp only [literalDots, AspisR1FastDotsConcreteKernelOpsRootV1.installed_eq_concrete]

/-- Successful complete candidate query result under the actual fixed concrete
candidate backend transfers to the old P6 callback with the identical query
result. There is no free S4 operation-slot assumption. -/
theorem concrete_candidate_query_refines_old_model
    (aops : AccumulateOps) (rest : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array FullWide 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (out : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
      verifier.Error)
    (h : verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)
      proof p a g obs geometry pending = .ok out) :
    verifier.candidate.queryWithOps aops (withOldModelDots concreteOps rest)
      proof p a g obs geometry pending = .ok out := by
  have hc : verifier.candidate.queryWithOps aops (withLiteralDots concreteOps rest)
      proof p a g obs geometry pending = .ok out := by
    simpa [concreteCandidateQueryOps] using h
  exact successful_query_candidate_refines_old_model
    aops concreteOps rest proof p a g obs geometry pending out hc

#print axioms concrete_candidate_dots_is_literal_v10
#print axioms concrete_candidate_query_refines_old_model

end AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
