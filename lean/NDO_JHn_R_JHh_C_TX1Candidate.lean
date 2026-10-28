import NDO_JHc_InstalledWriter
import NDO_JHc_QueryPost
import NDO_JHc_WriterContinuation
import NDO_JHn_R_JHh_PreBatchAssembly
import NDO_JHe_SHARealization
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_TX1Candidate
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

/-- Returning verifier candidate on the retained input under the named SHA equations. The
source query, flush and WAdm writer share the same preparation/accumulator.
This does not claim SDK wrapper accepted1 or retained-checkpoint identity. -/
theorem returns :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
      (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31)
      (saved : alloc.vec.Vec U8),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()) ∧
      installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=ok (.Ok (out,after)) ∧
      installed.op17 after out.weights.deref=ok flushed ∧
      installed.op16 digest p {out with weights:=⟨flushed.val,flushed.property⟩}
        JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved ∧
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved) ∧
      saved.val.length=1768 ∧ p.variant=.S2 ∧ out.next.val=10 ∧ flushed.val.length=64 := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,_roots,init,pend,geo,_meaning,batch,entry⟩ :=
    JHh_C_BatchFrontier.inhabited
  obtain ⟨out,after,flushed,query,flush,next,size,variant,_rhs,_power⟩ :=
    JHc_QueryPost.source p _ scratch initial pending g prepare queries init pend geo
  obtain ⟨saved,write,length⟩ := JHc_InstalledWriter.source p out flushed variant next size
  refine ⟨p,scratch,initial,out,pending,after,g,flushed,saved,prepare,batch,query,flush,write,?_,length,variant,next,size⟩
  calc
    _=JGy_QueryFrontier.afterQuery p scratch initial pending g :=
      entry.trans (JGy_QueryFrontier.source p scratch initial pending g init batch geo pend)
    _=JHc_WriterContinuation.afterFlush p out flushed :=
      JHc_WriterContinuation.source p scratch initial out pending after g flushed query flush
    _=ok (.Ok saved) := by
      simp only [JHc_WriterContinuation.afterFlush,write,bind_tc_ok,verifier.mark]
#print axioms returns
end AspisR1.JHh_C_TX1Candidate
end
end
