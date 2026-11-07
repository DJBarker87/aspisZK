import NHL_QueryInterface
import NHK_TRANSCRIPT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_QueryPacket
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NHL_PreparedScalars

/-- The chronological producer is consumed, including the complete Result and
state, on the constructor's SAME opening and final_message. -/
theorem source
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (hash : Unit)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem v hash)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv packet.opening.transcript packet.opening.row v.final_message observed) :
 NGP_L181.NativeAssociation hashv
   (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries packet.opening.transcript packet.opening.row v.final_message) observed ∧
 actual.sampling.queries (NGQ_Effects.dictionary hashv) packet.opening.transcript packet.opening.row v.final_message=observed.result ∧
 observed.attempted=(SdkC_Source.run hashv
   (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries packet.opening.transcript packet.opening.row v.final_message) []).2 :=
 NHL_QueryInterface.result hashv _ _ _ observed (NHK_Invocation.producer cuts)

/-- Row30/31 is derived from the actual fold branch, never assumed. -/
theorem domain
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (hash : Unit)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem v hash)
 (width : v.final_message.val.length=2048) :
 NHK_Invocation.Domain packet.opening.row v.final_message := by
 constructor
 · rcases (NHL_OpeningPacket.fold_fields packet.fold).2.2 with h|h <;> rw [h] <;> decide
 · omega
#print axioms source
#print axioms domain
end AspisR1.NHS_QueryPacket
