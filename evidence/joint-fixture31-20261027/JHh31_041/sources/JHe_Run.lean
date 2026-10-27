import JHc_TX1Candidate
import WAdm_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_Run
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
abbrev query := SAQ_Decoder.install (JFr_TX2_DotsBinding.ops JGp_Seeds.query)
abbrev geometry := SAQ_Constructor.install () JGp_Seeds.geometry
abbrev semantic := toCurrentPublic JFs_PublicSerialization.value
abbrev Run (saved : alloc.vec.Vec U8) := WAdm_Execution.Run installed true query geometry
  digest () semantic JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize saved

theorem inhabited : ∃ saved : alloc.vec.Vec U8,
    verifier.candidate.tx1 installed digest semantic JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved) ∧
    saved.val.length=1768 ∧ Nonempty (Run saved) := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,saved,
    prepare,batch,queryCall,flush,write,returned,length,variant,next,size⟩ := JHc_TX1Candidate.returns
  refine ⟨saved,returned,length,?_⟩
  apply WAdm_Execution.accepted_generic installed true query geometry digest () semantic
    JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize saved
    (WAdm_Execution.actual_slots
      (JGp_Allocation.base (Op5T_Concrete.current JGp_Seeds.base)) true query geometry
      JGe_Boundaries.value (NP6_StdModel.calls (.Ok ()))) returned
#print axioms inhabited
end AspisR1.JHe_Run
end
