import NJR_WindowsFromFinish
import NJR_ViewFinish
set_option autoImplicit false
noncomputable section
namespace NJR_AcceptedFinishDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem lengths (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact)
 (size : proof.val.length=57607) :
 (NJR_ViewFinish.view proof inactive).round0.val.length=224 ∧
 (NJR_ViewFinish.view proof inactive).round1.val.length=224 ∧
 (NJR_ViewFinish.view proof inactive).final_message.val.length=2048 := by
 change ((proof.val.drop 7527).take 224).length=224 ∧
  ((proof.val.drop 7783).take 224).length=224 ∧
  ((proof.val.drop 8007).take 2048).length=2048
 simp only [List.length_take,List.length_drop,size]
 decide

/-- Invert the SAME accepted source finish to recover raw-word bounds, including
collision branches where no equality to TX1 proof bytes is available. Every
Prepared and accumulator field still comes from the SAME resume/query/flush.
This is acceptance inversion only: the successful source finish is NOT an
admissible additional premise of the positive native TX2:065 root. In particular
it cannot justify installing the callee on arbitrary rejected finish entries. -/
theorem reached (reserved : Bool) (r : NP6_StdModel.Reservation)
 {H : Type} (d : aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inactive : aspis_core.field.wide_exact.WideExact) (out : Slice aspis_core.field.QM31)
 (ckSize : ck.val.length=1768)
 (resume : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d ck proof pub .S2 hash=ok (.Ok (p,a)))
 (start : a.next.val=10)
 (query : Port3_NativeQueryBody.verifier.candidate.query_loop
  (NFS_QueryOps.installed NJJ_QueryOps.concrete) proof p a g none geometry
  (NFW_QueryResume.pending a) 22#usize=ok (.Ok (after,pending)))
 (flush : Port3_FlushInstall.flush pending after.weights.deref=ok out)
 (size : proof.val.length=57607)
 (accepted : Port4D_FinishInstall.finish (IDa_Deployed.finish r)
  (NJR_ViewFinish.view proof inactive) p {after with weights:=⟨out.val,out.property⟩} none=ok (.Ok ())) :
 NIG_FinishInput.Domain proof (NJR_ViewFinish.view proof inactive) p
  {after with weights:=⟨out.val,out.property⟩} := by
 have dom:=NID_ResumeFields.returned reserved d ck proof pub hash p a ckSize resume
 have qdom:=NFW_QueryResume.domain p a dom.width
  (NID_ResumeQuery.weights a dom.weights)
  (NID_ResumeCallerDomain.wide a.rhs dom.rhs)
  (NID_ResumeCallerDomain.power a.power dom.power)
  (NID_ResumeCallerDomain.power p.rho dom.rho) start
 obtain ⟨actual,actualFlush,acc,_⟩:=NGM_FinishDomain.tx2_writeback NJJ_QueryOps.concrete proof p a after g
  geometry (NFW_QueryResume.pending a) pending qdom start query
 have same : actual=out := by rw [flush] at actualFlush; exact (Result.ok.inj actualFlush).symm
 subst actual
 obtain ⟨r0size,r1size,finalSize⟩:=lengths proof inactive size
 have words:=NJR_WindowsFromFinish.source r (NJR_ViewFinish.view proof inactive) p
  {after with weights:=⟨out.val,out.property⟩} dom.variant acc.width r0size r1size finalSize accepted
 refine ⟨acc,dom.variant,NID_ResumeCallerDomain.wide p.claim dom.claim,?_,
  NID_ResumeCallerDomain.wide p.kappa dom.kappa,?_,?_,rfl,rfl,rfl,
  words.1,words.2.1,words.2.2⟩
 · intro i _ x hx
   exact NID_ResumeCallerDomain.wide x (dom.alpha x (List.mem_of_getElem? hx))
 · intro q hq
   have h:=dom.semantic q hq
   exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩
 · intro point hp
   have h:=dom.coordinates point hp
   exact ⟨⟨⟨h.1.1,h.1.2.1⟩,h.1.2.2⟩,⟨⟨h.2.1,h.2.2.1⟩,h.2.2.2⟩⟩

#print reached
#print axioms lengths
#print axioms reached
end NJR_AcceptedFinishDomain
