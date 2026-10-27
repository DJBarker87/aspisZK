import JHc_BatchFrontier
import JGy_QueryFrontier
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_TX1
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

/-- Closed actual TX1 prefix through batch0 to the SAME query continuation.
This does not assert query, flush or writer success, nor accepted1. -/
theorem toQuery :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      p.queries=JFq_Queries.value ∧ p.roots=JFo_Prepared.value.roots ∧
      installed.op20 .S2=ok (.Ok initial) ∧ installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧ JGp_Loop.Meaning (Tx1Q_Carriers.geometry g) ∧
      installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()) ∧
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=
        JGy_QueryFrontier.afterQuery p scratch initial pending g := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,roots,init,pend,geo,meaning,batch,entry⟩ :=
    JHc_BatchFrontier.inhabited
  exact ⟨p,scratch,initial,pending,g,prepare,queries,roots,init,pend,geo,meaning,batch,
    entry.trans (JGy_QueryFrontier.source p scratch initial pending g init batch geo pend)⟩
#print axioms toQuery
end AspisR1.JHc_TX1
end
