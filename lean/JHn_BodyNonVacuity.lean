import JHn_PreparedBody
import JHc_QueryPost
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_BodyNonVacuity
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage
/-- An actual prepare/query/flush witness for the complete body identity.
This is auxiliary fixture non-vacuity, not full deployed-hypothesis inhabitance. -/
theorem source : ∃ (p : verifier.Prepared) (a : verifier.Accumulator),
    (WAdm_SourceBody.body (prepared p) (accumulator a)
      JFq_AuthBytes.proofHash JFq_AuthBytes.publicHash).map CheckpointBytes5Writer.u8=
        JFx_NativeBytes.checkpoint.val.take 1736 := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,init,pend,geo,meaning,entry⟩ :=
    JGr_Geometry.inhabited
  obtain ⟨out,after,flushed,query,flush,next,size,variant,rhs,power⟩ :=
    JHc_QueryPost.source p _ scratch initial pending g prepare queries init pend geo
  exact ⟨p,{out with weights:=⟨flushed.val,flushed.property⟩},
    JHn_PreparedBody.source p _ scratch initial out pending after g flushed
      prepare init pend geo query flush variant next⟩
#print axioms source
end AspisR1.JHn_BodyNonVacuity
end
