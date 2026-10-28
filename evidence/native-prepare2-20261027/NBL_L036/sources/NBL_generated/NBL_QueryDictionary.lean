import NBA_Scalars
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_QueryDictionary
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
def boundaries : QueriesModel.Boundaries :=
  Query31ConcreteMaterializedSchedule.concreteBoundaries
    Query31ConcreteDriverTraceFacts.sourceDefaultState AspisS1M31Embedding.Total.embed

theorem installed {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    NBA_Installed.actual.sampling.queries D self row payload=
      QueriesModel.queries boundaries D self row payload := by
  rw [NBA_Scalars.sampling]
  simp only [AspisR1ClaimPreparedBridge.withCandidateSamplers,
    AspisR1ClaimPreparedBridge.withCandidateGamma,
    AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary,NBA_Scalars.base,
    AspisR1ClaimPreparedBridge.PreparedFromQmSourceBridge.withSourceFromQm,
    AspisR1ClaimPreparedBridge.CurrentQueryRho.withConcreteQueries,boundaries]


#print axioms installed
end AspisR1.NBL_QueryDictionary
end
