import NJM_CirclePacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_CircleRoot
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_DispatchCut
open PreparedHashCode (run)

/-- Native branch packet after the CLOSED block/sampler Results are installed.
The only returning-post premise is exactly the reviewed native dispatch cut. -/
def Branch {Pointer H : Type} (D : aspis_core.Digest32 H) (template : Pre Pointer)
 (before : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) (row : FinishModel.CircleRow) : Prop :=
 let child:=run (S1SemanticCode.sampleBlock D before (NJM_CirclePacket.tag row) record.framed)
 let whole:=run (NJM_CircleCode.dispatch D before record (NJM_CirclePacket.tag row))
 match child.2 with
 | .fail e => whole=(child.1,.fail e)
 | .div => whole=(child.1,.div)
 | .ok (reply,after) =>
   childDomain reply ∧
   (NJM_CircleNative.install (NJM_CirclePacket.inputs template record row before after reply)).count<254 ∧
   ∀ post,cut (NJM_CircleNative.install (NJM_CirclePacket.inputs template record row before after reply)) post →
    whole=(child.1,ok (post.result,after)) ∧
    post.transcriptState=after.state ∧ post.transcriptNext=after.next_row ∧ post.frame=template.frame

/-- Both actual dispatch branches, all child replies, all original outer
aborts. No arbitrary operation dictionary, endpoint equation, child-success
or output premise is accepted by this root. -/
theorem branch {Pointer H : Type} (D : aspis_core.Digest32 H) (template : Pre Pointer)
 (before : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord)
 (row : FinishModel.CircleRow) (framed : record.framed.val.length≤3717) :
 Branch D template before record row := by
 unfold Branch
 rw [NJM_CirclePacket.branch]
 generalize call : run (S1SemanticCode.sampleBlock D before (NJM_CirclePacket.tag row) record.framed)=child
 rcases child with ⟨log,reply⟩
 cases reply with
 | fail e => rfl
 | div => rfl
 | ok pair =>
   rcases pair with ⟨reply,after⟩
   have eq : (run (S1SemanticCode.sampleBlock D before (NJM_CirclePacket.tag row) record.framed)).2=ok (reply,after) := congrArg Prod.snd call
   have dom:=NJM_CirclePacket.domain D template record row before after reply framed eq
   refine ⟨dom.2.2,dom.2.1,?_⟩
   intro post certificate
   have assoc:=NJM_CirclePacket.returned template record row before after reply post certificate
   refine ⟨?_,assoc.2⟩
   simp only [NGX_RunBind.appendResult,assoc.1,List.append_nil]

/-- All valid source rows select the native branch proven above. Invalid
rows return immediately and preserve every transcript field. -/
theorem source {Pointer H : Type} (D : aspis_core.Digest32 H) (template : Pre Pointer)
 (before : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord)
 (framed : record.framed.val.length≤3717) :
 (record.row=25#u8 → Branch D template before record .First) ∧
 (record.row=26#u8 → Branch D template before record .Second) ∧
 (record.row≠25#u8 → record.row≠26#u8 →
  run (NJM_CircleCode.source D before record)=([],ok (.Err .InvalidRow,before))) := by
 refine ⟨fun _=>branch D template before record .First framed,fun _=>branch D template before record .Second framed,?_⟩
 intro notFirst notSecond
 unfold NJM_CircleCode.source NJM_CircleCode.dispatch
 split
 · rename_i h
   exact False.elim (notFirst h)
 · rename_i h
   exact False.elim (notSecond h)
 · rfl

#print axioms branch
#print axioms source
end AspisR1.NJM_CircleRoot
end
