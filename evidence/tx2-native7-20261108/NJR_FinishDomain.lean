import NJR_FinishWindows
import NJR_FinishPrepared
import NJJ_QueryOps
set_option autoImplicit false
noncomputable section
namespace NJR_FinishDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Internal reached-branch lemma, NOT a positive root: the successful resume
and query equations are obtained by inverting the caller's binds. All Prepared
and accumulator domain fields are derived from those SAME calls. Only the raw
history remains externally unproved. No finish-success or pair-output premise. -/
theorem reached (reserved : Bool) {H : Type} (d : aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (v : verifier.View)
 (ckSize : ck.val.length=1768)
 (resume : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d ck proof pub .S2 hash=ok (.Ok (p,a)))
 (start : a.next.val=10)
 (query : Port3_NativeQueryBody.verifier.candidate.query_loop
  (NFS_QueryOps.installed NJJ_QueryOps.concrete) proof p a g none geometry
  (NFW_QueryResume.pending a) 22#usize=ok (.Ok (after,pending)))
 (size : 10055≤proof.val.length)
 (round0 : v.round0.val=(proof.val.drop 7527).take 224)
 (round1 : v.round1.val=(proof.val.drop 7783).take 224)
 (finalView : v.final_message.val=(proof.val.drop 8007).take 2048)
 (history : NJR_FinishWindows.History proof) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 NIG_FinishInput.Domain proof v p {after with weights:=⟨out.val,out.property⟩} := by
 have dom:=NID_ResumeFields.returned reserved d ck proof pub hash p a ckSize resume
 have qdom:=NFW_QueryResume.domain p a dom.width
  (NID_ResumeQuery.weights a dom.weights)
  (NID_ResumeCallerDomain.wide a.rhs dom.rhs)
  (NID_ResumeCallerDomain.power a.power dom.power)
  (NID_ResumeCallerDomain.power p.rho dom.rho) start
 obtain ⟨out,flush,acc,_⟩:=NGM_FinishDomain.tx2_writeback NJJ_QueryOps.concrete proof p a after g
  geometry (NFW_QueryResume.pending a) pending qdom start query
 have words:=NJR_FinishWindows.three proof v.round0 v.round1 v.final_message size round0 round1 finalView history
 refine ⟨out,flush,⟨acc,dom.variant,NID_ResumeCallerDomain.wide p.claim dom.claim,?_,
  NID_ResumeCallerDomain.wide p.kappa dom.kappa,?_,?_,round0,round1,finalView,
  words.1,words.2.1,words.2.2⟩⟩
 · intro i _ x hx
   exact NID_ResumeCallerDomain.wide x (dom.alpha x (List.mem_of_getElem? hx))
 · intro q hq
   have h:=dom.semantic q hq
   exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩
 · intro point hp
   have h:=dom.coordinates point hp
   exact ⟨⟨⟨h.1.1,h.1.2.1⟩,h.1.2.2⟩,⟨⟨h.2.1,h.2.2.1⟩,h.2.2.2⟩⟩

#print reached
#print axioms reached
end NJR_FinishDomain
