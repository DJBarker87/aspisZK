import PV_LIB_A_LoopBackedge13
import PV_LIB_A_RangeIteration13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_NextIteration13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Exact post3519 storage suffix and3530 backedge, followed by the next WHOLE
target-prefix iteration. The input is explicitly AFTER the earlier handles push:
its callee/internal frame is not assumed closed by this theorem. Iterator is the
induction facet to derive there, not an extra row/endpoint premise. -/
theorem history (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (start finish : Nat) (iterator : PV_LIB_A_RangeInvariant12.Iterator s a start finish) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let t := PV_LIB_A_LoopBackedge13.stored s a
    let u := PV_LIB_A_RangeInvariant12.post t a parents start finish
    let site := PV_LIB_A_RangePoll11.site t a
    let r := H site.waiting.request w
    let q := PV_LIB_A_RangeReply12.after B K t u a parents es stack r
    PV_LIB_A_PrefixMachine11.advance B K (PV_LIB_A_SpawnEnter12.enter270Programs P) resources encode H values
      (8 + ((6+1) + PV_LIB_A_RangeReply12.steps B K t u a parents r + PV_LIB_A_Post93Prefix12.steps B H q))
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 24,loops := PV_LIB_A_RangeMatch12.loops},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      PV_LIB_A_Post93Prefix12.after B H q := by
  intro B t u site r q
  rw [advance_add,PV_LIB_A_LoopBackedge13.run B K
    (PV_LIB_A_SpawnEnter12.enter270Programs P) resources encode H values s a parents w es stack]
  exact PV_LIB_A_RangeIteration13.history C K P resources encode H values t a parents b w es stack
    start finish (PV_LIB_A_LoopBackedge13.keeps_iterator s a start finish iterator)

#print axioms history
end PV_LIB_A_NextIteration13
