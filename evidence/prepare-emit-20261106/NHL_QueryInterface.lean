import NHL_OpeningPacket
import NGQ_Concrete
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_QueryInterface
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NHL_PreparedScalars

/-- The constructor actually uses the same adopted query dictionary. -/
theorem dictionary {H : Type} (D : aspis_core.Digest32 H)
 (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
 actual.sampling.queries D self row payload=
 QueriesModel.queries NGQ_TRANSCRIPT.boundaries D self row payload := by
 rw [NGQ_TRANSCRIPT.adopted_boundaries]
 simp only [actual,NGT_NBA_Installed.actual,AspisR1ClaimPreparedBridge.concreteBoundaries,
   AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries,
   PreparedFromQmSourceBridge.withSourceFromQm,AspisR1ClaimPreparedBridge.CurrentQueryRho.withConcreteQueries]

/-- Exact NHK export shape, including full reply and attempted-event prefix.
The chronological trace remains the OPEN producer; it is never constructed
from a desired result equation. This is only its direct constructor consumer. -/
theorem result
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (trace : NGQ_Cuts.Trace hashv
   (NGQ_Normalize.normalize (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries self row payload))
   observed.result observed.attempted) :
 NGP_L181.NativeAssociation hashv (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries self row payload) observed ∧
 actual.sampling.queries (NGQ_Effects.dictionary hashv) self row payload=observed.result ∧
 observed.attempted=(SdkC_Source.run hashv (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries self row payload) []).2 := by
 obtain ⟨association,same,_,events⟩ := NGQ_TRANSCRIPT.actual_queries hashv self row payload observed trace
 exact ⟨association,(dictionary _ self row payload).trans same.symm,events⟩
#print axioms dictionary
#print axioms result
end AspisR1.NHL_QueryInterface
