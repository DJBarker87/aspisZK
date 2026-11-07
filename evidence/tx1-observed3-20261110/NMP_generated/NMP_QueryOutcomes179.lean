import NHS_QueryPacket
import NHL_PreparedFailures
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_QueryOutcomes179
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NFW_PreparedControl NHL_PreparedScalars
/-- SAME query observation supplies the Err arm and preserves incoming scratch.
This composes existing model companions; it is not the full native179 root or
its combined opening/query effect history. -/
theorem error (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (hash : Unit) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem v hash)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv packet.opening.transcript packet.opening.row v.final_message observed)
 (e : verifier.Error) (after : transcript.Transcript Unit)
 (reply : observed.result=ok (.Err e,after)) :
 NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v hash old=ok (.Err e,old) ∧
 observed.attempted=(SdkC_Source.run hashv
  (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries packet.opening.transcript packet.opening.row v.final_message) []).2 := by
 have q := NHS_QueryPacket.source hashv sem v hash packet observed cuts
 exact ⟨NHL_PreparedRecompose.query_error _ sem v hash old packet e after (q.2.1.trans reply),q.2.2⟩
/-- Outer failure keeps only the attempted query prefix; no post-abort heap. -/
theorem failed (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (hash : Unit) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem v hash)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv packet.opening.transcript packet.opening.row v.final_message observed)
 (e : Error) (reply : observed.result=.fail e) :
 NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v hash old=.fail e ∧
 observed.attempted=(SdkC_Source.run hashv
  (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries packet.opening.transcript packet.opening.row v.final_message) []).2 := by
 have q := NHS_QueryPacket.source hashv sem v hash packet observed cuts
 exact ⟨NHL_PreparedFailures.query_fail _ sem v hash old packet e (q.2.1.trans reply),q.2.2⟩
theorem diverged (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (hash : Unit) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem v hash)
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv packet.opening.transcript packet.opening.row v.final_message observed)
 (reply : observed.result=.div) :
 NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v hash old=.div ∧
 observed.attempted=(SdkC_Source.run hashv
  (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries packet.opening.transcript packet.opening.row v.final_message) []).2 := by
 have q := NHS_QueryPacket.source hashv sem v hash packet observed cuts
 exact ⟨NHL_PreparedFailures.query_div _ sem v hash old packet (q.2.1.trans reply),q.2.2⟩
#print axioms error
#print axioms failed
#print axioms diverged
end AspisR1.NMP_QueryOutcomes179
end
