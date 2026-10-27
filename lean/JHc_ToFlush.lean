import JHc_BatchFrontier
import JHc_InstalledQuery
import JGy_QueryFrontier
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_ToFlush
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

/-- Closed same-preparation batch/query/flush prefix. This is a composition
of returning source procedures, retaining the actual unexecuted writer. -/
theorem source :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
      (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      installed.op20 .S2=ok (.Ok initial) ∧ installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧
      installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()) ∧
      installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=ok (.Ok (out,after)) ∧
      installed.op17 after out.weights.deref=ok flushed ∧
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=
        JGy_QueryFrontier.afterQuery p scratch initial pending g := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,_roots,init,pend,geo,_meaning,batch,entry⟩ :=
    JHc_BatchFrontier.inhabited
  obtain ⟨out,after,flushed,query,flush⟩ :=
    JHc_InstalledQuery.source p _ scratch initial pending g prepare queries init pend geo
  exact ⟨p,scratch,initial,out,pending,after,g,flushed,prepare,init,pend,geo,batch,query,flush,
    entry.trans (JGy_QueryFrontier.source p scratch initial pending g init batch geo pend)⟩
#print axioms source
end AspisR1.JHc_ToFlush
end
