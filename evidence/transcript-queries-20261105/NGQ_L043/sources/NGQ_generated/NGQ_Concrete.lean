import NGQ_TRANSCRIPT
import NGQ_SamplerPacket
import NGQ_Normalize
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_TRANSCRIPT
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Fixed emitted sampler and fixed emitted constructor. No freely selected
successful decode or independently selected challenge list is installed. -/
def boundaries : QueriesModel.Boundaries := NGQ_Embed.boundaries NGQ_SamplerPacket.decode

theorem adopted_boundaries :
    boundaries=Query31ConcreteMaterializedSchedule.concreteBoundaries
      NGQ_SamplerPacket.initial AspisS1M31Embedding.Total.embed := by
  exact congrArg (fun decode : NGQ_Embed.Decode => QueriesModel.Boundaries.mk decode AspisS1M31Embedding.Total.embed)
    (funext fun blocks => funext fun advances => NGQ_SamplerPacket.adopted_decoder blocks advances)
#print axioms adopted_boundaries

/-- Hybrid consumer: the native certificates must construct the chronological
local-edge trace on the SAME input/state. This premise is disclosed, never
reported as discharged by model compilation alone. -/
theorem actual_queries
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
    (observed : NGP_L181.Observation NGQ_Effects.Reply)
    (trace : NGQ_Cuts.Trace hashv
      (NGQ_Normalize.normalize (NGQ_Effects.code boundaries self row payload))
      observed.result observed.attempted) :
    NGP_L181.NativeAssociation hashv (NGQ_Effects.code boundaries self row payload) observed ∧
    observed.result=QueriesModel.queries boundaries (NGQ_Effects.dictionary hashv) self row payload ∧
    positions observed.result=positions (QueriesModel.queries boundaries (NGQ_Effects.dictionary hashv) self row payload) ∧
    observed.attempted=(SdkC_Source.run hashv (NGQ_Effects.code boundaries self row payload) []).2 := by
  have edgeRun := NGQ_Cuts.run trace []
  have normalized := NGQ_Normalize.run hashv (NGQ_Effects.code boundaries self row payload) []
  have native : NGP_L181.NativeAssociation hashv (NGQ_Effects.code boundaries self row payload) observed := by
    simpa only [NGP_L181.NativeAssociation,List.nil_append] using (edgeRun.symm.trans normalized)
  have result := congrArg Prod.fst native
  have events := congrArg Prod.snd native
  dsimp only at result events
  have same := result.trans (NGQ_Effects.model_result hashv boundaries self row payload)
  exact ⟨native,same,congrArg positions same,events⟩

#print axioms actual_queries
end AspisR1.NGQ_TRANSCRIPT
end
