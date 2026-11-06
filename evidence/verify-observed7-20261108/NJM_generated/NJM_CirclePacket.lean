import NJM_CircleDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_CirclePacket
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_DispatchCut
open PreparedHashCode (run)

def tag : FinishModel.CircleRow → U8 | .First=>25#u8 | .Second=>26#u8

def inputs {Pointer H : Type} (template : Pre Pointer) (record : r1_wire.ValidatedRecord)
 (row : FinishModel.CircleRow) (before after : r1_wire.SemanticTranscript H) (reply : Reply) : Pre Pointer :=
 { template with
   framed := record.framed
   row := tag row
   state := before.state
   next := before.next_row
   newState := after.state
   newNext := after.next_row
   reply := reply
   count := 0 }

theorem valid_tag (row : FinishModel.CircleRow) : valid (tag row)=true := by cases row <;> rfl

theorem row_tag (row : FinishModel.CircleRow) : NJM_CircleNative.row (tag row)=row := by cases row <;> rfl

/-- Dispatch at either real branch is exactly the complete SAME child bind. -/
theorem branch {H : Type} (D : aspis_core.Digest32 H)
 (before : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) (row : FinishModel.CircleRow) :
 run (NJM_CircleCode.dispatch D before record (tag row))=
 NGX_RunBind.appendResult
  (run (S1SemanticCode.sampleBlock D before (tag row) record.framed)).1
  (run (S1SemanticCode.sampleBlock D before (tag row) record.framed)).2
  (NJM_CircleJoin.after row) := by
 cases row <;> exact NGX_RunBind.bind_run _ _

/-- Concrete native-domain installation at the SAME source block reply.
Both returning error and success are established internally; no endpoint
or child-success premise occurs in the positive branch packet below. -/
theorem domain {Pointer H : Type} (D : aspis_core.Digest32 H)
 (template : Pre Pointer) (record : r1_wire.ValidatedRecord) (row : FinishModel.CircleRow)
 (before after : r1_wire.SemanticTranscript H) (reply : Reply)
 (framed : record.framed.val.length≤3717)
 (call : (run (S1SemanticCode.sampleBlock D before (tag row) record.framed)).2=ok (reply,after)) :
 (NJM_CircleNative.install (inputs template record row before after reply)).framed.val.length≤3717 ∧
 (NJM_CircleNative.install (inputs template record row before after reply)).count<254 ∧ childDomain reply :=
 ⟨framed,by change (0:Nat)<254; decide,NJM_CircleDomain.reply D before after (tag row) record.framed reply call⟩

/-- Full returning/error native cut association; child bytes, Result and
post-state are the SAME source child's. The only condition is the reviewed
K049/K050 cut, after concrete CLOSED sampler substitution. -/
theorem returned {Pointer H : Type} (template : Pre Pointer) (record : r1_wire.ValidatedRecord)
 (row : FinishModel.CircleRow) (before after : r1_wire.SemanticTranscript H) (reply : Reply) (post : Post Pointer)
 (certificate : cut (NJM_CircleNative.install (inputs template record row before after reply)) post) :
 run (NJM_CircleJoin.after row (reply,after))=([],ok (post.result,after)) ∧
 post.transcriptState=after.state ∧ post.transcriptNext=after.next_row ∧ post.frame=template.frame := by
 have h:=NJM_CircleNative.returned (inputs template record row before after reply) post after certificate (valid_tag row)
 refine ⟨?_,h.1,h.2.1,h.2.2.1⟩
 simpa only [inputs,row_tag] using h.2.2.2

#print axioms valid_tag
#print axioms row_tag
#print axioms branch
#print axioms domain
#print axioms returned
end AspisR1.NJM_CirclePacket
end
