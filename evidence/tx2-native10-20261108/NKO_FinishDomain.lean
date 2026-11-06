import NKO_QueryPost
import NJU_FinishInput
import NJU_ViewWindows
set_option autoImplicit false
noncomputable section
namespace NKO_FinishDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- Domain of the actual flush writeback, preserving every other accumulator
field. No raw-word, history, NoBad or successful-finish premise. -/
theorem writeback (proof : Slice U8) (p : verifier.Prepared) (before after : verifier.Accumulator)
 (pending : verifier.BatchedWeights) (out : Slice aspis_core.field.QM31) (v : verifier.View)
 (fields : NID_ResumeFields.Domain p before)
 (post : NFS_QueryInvariant.Domain p 10 22 after pending) (next : after.next.val=22)
 (flush : Port3_FlushInstall.flush pending after.weights.deref=ok out)
 (round0 : v.round0.val=(proof.val.drop 7527).take 224)
 (round1 : v.round1.val=(proof.val.drop 7783).take 224)
 (final : v.final_message.val=(proof.val.drop 8007).take 2048)
 (finalSize : v.final_message.val.length=2048) :
 NJU_FinishInput.Holds proof v p {after with weights:=⟨out.val,out.property⟩} := by
 have rawSize : pending.raw.val.length=64 := post.progress.2.1
 have same : out=NJJ_Flush.output pending :=
  Result.ok.inj (flush.symm.trans (NJJ_Flush.source pending after.weights.deref rawSize post.width))
 have width : out.val.length=64 := by
  rw [same]
  simpa only [NJJ_Flush.output,List.length_map] using rawSize
 have canonical : ∀ q∈out.val,Port3_FlushInstall.Canonical q := by
  rw [same]
  exact NJJ_Flush.canonical pending
 refine ⟨⟨width,canonical,post.rhs,post.power,next⟩,fields.variant,
  NID_ResumeCallerDomain.wide p.claim fields.claim,?_,
  NID_ResumeCallerDomain.wide p.kappa fields.kappa,?_,?_,round0,round1,final,finalSize⟩
 · intro i _ x hx
   exact NID_ResumeCallerDomain.wide x (fields.alpha x (List.mem_of_getElem? hx))
 · intro q hq
   have h:=fields.semantic q hq
   exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩
 · intro point hp
   have h:=fields.coordinates point hp
   exact ⟨⟨⟨h.1.1,h.1.2.1⟩,h.1.2.2⟩,⟨⟨h.2.1,h.2.2.1⟩,h.2.2.2⟩⟩
#print axioms writeback
end NKO_FinishDomain
