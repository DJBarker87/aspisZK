import NHS_QueryPacket
import NHL_PreparedFailures
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_QueryFailures
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NFW_PreparedControl
open NHL_PreparedScalars
variable (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (hash : Unit) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem v hash)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv packet.opening.transcript packet.opening.row v.final_message observed)

theorem error (e : verifier.Error) (after : transcript.Transcript Unit)
 (returned : observed.result=ok (.Err e,after)) :
 NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v hash old=ok (.Err e,old) :=
 NHL_PreparedRecompose.query_error _ sem v hash old packet e after
   ((NHS_QueryPacket.source hashv sem v hash packet observed cuts).2.1.trans returned)

theorem fail (e : Error) (returned : observed.result=.fail e) :
 NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v hash old=.fail e :=
 NHL_PreparedFailures.query_fail _ sem v hash old packet e
   ((NHS_QueryPacket.source hashv sem v hash packet observed cuts).2.1.trans returned)

theorem div (returned : observed.result=.div) :
 NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v hash old=.div :=
 NHL_PreparedFailures.query_div _ sem v hash old packet
   ((NHS_QueryPacket.source hashv sem v hash packet observed cuts).2.1.trans returned)
#print axioms error
#print axioms fail
#print axioms div
end AspisR1.NHS_QueryFailures
