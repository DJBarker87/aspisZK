import NDO_JGr_Geometry
import NDO_JGp_BatchInput
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGr_PreBatchFixture
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

/-- The exact unconstructed TX1 suffix at these fixed physical bytes. This
proposition is recorded as OPEN; it is not an assumption of inhabited below. -/
def Remaining (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry) : Prop :=
  ∃ (out : verifier.Accumulator) (after : verifier.BatchedWeights)
    (flushed : Slice aspis_core.field.QM31) (saved : alloc.vec.Vec U8),
    installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()) ∧
    installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=ok (.Ok (out,after)) ∧
    installed.op17 after out.weights.deref=ok flushed ∧
    installed.op16 digest p {out with weights:=⟨flushed.val,flushed.property⟩}
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved ∧
    saved.val=JFx_NativeBytes.checkpoint.val

/-- Closed real-byte local fixture through preparation, initial allocation,
pending allocation and geometry, with source-identified queries AND roots.
This deliberately does not assert Remaining or either accepted wrapper. -/
theorem inhabited :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      p.queries=JFq_Queries.value ∧ p.roots=JFo_Prepared.value.roots ∧
      installed.op20 .S2=ok (.Ok initial) ∧ installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧ JGp_Loop.Meaning (Tx1Q_Carriers.geometry g) ∧
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=
        Tx1Reachability.afterPrepare installed digest JFx_NativeBytes.publicInput JFx_NativeBytes.proof
          10#usize () none p scratch := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,init,pend,geometry,meaning,entry⟩ := JGr_Geometry.inhabited
  have roots := JGp_CurrentRoots.source _ _ _ JGn_TerminalIdentified.shaDictionary () p _ scratch prepare
  exact ⟨p,scratch,initial,pending,g,prepare,queries,roots,init,pend,geometry,meaning,entry⟩
#print axioms inhabited
#print Remaining
end AspisR1.JGr_PreBatchFixture
end
