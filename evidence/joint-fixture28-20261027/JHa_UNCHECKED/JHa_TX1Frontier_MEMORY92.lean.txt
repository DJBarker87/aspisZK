import JGy_TX1
import JHa_CurrentFields
import JHa_CurrentRho
import JGy_BatchFrontier
import JGy_QueryFrontier
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_TX1Frontier
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
      Tx1Q_Carriers.e p.gamma=JFq_Gamma.scalar ∧
      Tx1Q_Carriers.k p.kappa=JFq_Kappa.scalar ∧
      Tx1Q_Carriers.arr Tx1Q_Carriers.e p.alpha=JFo_Prepared.value.alpha ∧
      Tx1Q_Carriers.k p.rho=JFq_Rho.scalar ∧ p.variant=.S2 ∧
      Tx1Q_Carriers.arr Tx1Q_Carriers.e scratch=JFr_TX2_Powers.value ∧
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=
        JGy_QueryFrontier.afterQuery p scratch initial pending g := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,roots,init,pend,geo,meaning,batch,entry⟩ :=
    JGy_TX1.toQuery
  have fields := JHa_CurrentFields.source _ _ _ JGn_TerminalIdentified.shaDictionary () p _ scratch prepare
  have rho := JHa_CurrentRho.source _ _ _ JGn_TerminalIdentified.shaDictionary () p _ scratch prepare
  have powers := JHa_Powers.source p _ scratch prepare
  exact ⟨p,scratch,initial,pending,g,prepare,queries,roots,init,pend,geo,meaning,batch,
    fields.1,fields.2.1,fields.2.2,rho.1,rho.2.1,powers.2,entry⟩
#print axioms toQuery
end AspisR1.JHa_TX1Frontier
end
