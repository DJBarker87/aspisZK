import XRr_EmptySemantic
import XRr_CandidateReject
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_Nonvacuity
theorem emitted_observed {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) :
 r1_semantic.verify_observed D pub XRr_EmptySemantic.empty hash none=ok (.Err (.Length 0#u8)) :=
 XRr_ObservedReject.parse_error D pub _ hash none _ XRr_EmptySemantic.emitted
/-- A stopped source loop is inhabited without any assumed successful child
call. It is not promoted to an accepted transaction or root-game witness. -/
theorem stopped_query (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geo : verifier.QueryGeometry) (b : verifier.BatchedWeights) :
 verifier.candidate.query_loop proof p a g none geo b a.next=ok (.Ok (a,b)) :=
 XRr_QueryStop.stopped proof p a g none geo b a.next (Nat.le_refl _)
#print axioms emitted_observed
#print axioms stopped_query
end XRr_Nonvacuity
