import XRy_QueryEmbedding
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRy_Queries

theorem boundaries : XRy_QueryLaws.rawBoundaries =
 Query31ConcreteMaterializedSchedule.concreteBoundaries
   Query31ConcreteDriverTraceFacts.sourceDefaultState AspisS1M31Embedding.Total.embed := by
 apply congrArg₂ AspisR1PublicPreparation.QueriesModel.Boundaries.mk
 · funext blocks advances
   exact XRy_QueryLaws.decode blocks advances
 · funext x
   exact XRy_QueryEmbedding.embed x

/-- Every eager digest and its failure continuation is retained. -/
theorem queries {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (inner id ce p.1,ct p.2))
   (XRn_Join_Release.transcript.Transcript.queries (ed D) (et t) row payload) =
 XRo_Join_Installed.actual.sampling.queries D t row payload := by
 rw [XRy_QueryTransport.raw,boundaries]
 rfl

#print axioms boundaries
#print axioms queries
end XRy_Queries
