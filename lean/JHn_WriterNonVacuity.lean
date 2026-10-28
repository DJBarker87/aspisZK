import JHn_SavedIdentity
import JHc_QueryPost
import JHc_InstalledWriter
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_WriterNonVacuity
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
variable [sha : JHh_SHARealization]
/-- Actual writer non-vacuity on a single reached preparation/query/flush.
Batch acceptance and full headline non-vacuity are separate obligations. -/
theorem source : ∃ (saved : alloc.vec.Vec U8),
    saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator),
      installed.op16 digest p a JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,init,pend,geo,meaning,entry⟩ :=
    JGr_Geometry.inhabited
  obtain ⟨out,after,flushed,query,flush,next,size,variant,rhs,power⟩ :=
    JHc_QueryPost.source p _ scratch initial pending g prepare queries init pend geo
  obtain ⟨saved,write,length⟩ := JHc_InstalledWriter.source p out flushed variant next size
  exact ⟨saved,JHn_SavedIdentity.source p _ scratch initial out pending after g flushed saved
    prepare init pend geo query flush variant next size write,length,
    p,{out with weights:=⟨flushed.val,flushed.property⟩},write⟩
#print axioms source
end AspisR1.JHn_WriterNonVacuity
end
