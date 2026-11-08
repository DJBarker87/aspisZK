import PV_LIB_A_RangeReply12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeHistory12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Continuous3400..3471 corrected history: actual165 move, actual93 write and
full reply, Some captures or None break. No local-cell/read/write-definedness
premise. This still starts after the handles child, not original OwnInit entry. -/
theorem history (C : Carrier OWNER Data) (D : Effects) (H : Backend PV_RJ4IDB.NativeEvent)
    (semantics : PV_LIB_A_Range165.PV_THR2_LibrarySemantics_RangeIntoIter165 C D H)
    (K : Control) (P : Data → Option PV_STX2_SliceSyntax.Program)
    (resources : Resources) (encode : Encode) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (value : Data)
    (returned : (PV_THR2_Source15RangeToLoop.reply
      (PV_THR2_OwnUniformResourceHandler.lift H) s w).answer = .returned (.ok value)) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let handler := PV_THR2_OwnUniformResourceHandler.lift H
    let first := PV_THR2_Source15RangeToLoop.reply handler s w
    let iterator := PV_LIB_A_RangeHistoryV2.iteratorStore s a value
    let t := (PV_LIB_A_RangeFirst11.afterWrite s a parents value).store
    let site := PV_LIB_A_RangePoll11.site iterator a
    let r := handler site.waiting.request first.world
    advance B K (PV_LIB_A_RangePoll11.programs P) resources encode handler values
      (((PV_THR2_Source15RangeToLoop.steps handler s w + 7) + 1) +
        PV_LIB_A_RangeReply12.steps B K iterator t a parents r)
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      PV_LIB_A_RangeReply12.after B K iterator t a parents (es ++ first.events) stack r := by
  intro B handler first iterator t site r
  rw [advance_add,PV_LIB_A_RangeFirst11.history C D H semantics K P resources encode values
    s a parents b w es stack value returned]
  exact PV_LIB_A_RangeReply12.run B K (PV_LIB_A_RangePoll11.programs P) resources encode
    handler values iterator t a parents (es ++ first.events) stack r

/-- The delivered Some/None payload cannot erase the increment already derived
from actual165 and93; no activation-counter identity crosses the child. -/
theorem iterator (s : Store Data) (a : Nat) (parents : List Frame) (value v : Data) :
    (PV_LIB_A_RangeReply12.deliveredStore (PV_LIB_A_RangeHistoryV2.iteratorStore s a value)
      (PV_LIB_A_RangeFirst11.afterWrite s a parents value).store a parents v).cells ⟨a,7,[]⟩ =
      some (PV_LIB_A_Range165.sourceRange 2 16) := by
  rw [PV_LIB_A_RangeReply12.iterator]
  exact PV_LIB_A_RangeFirst11.written s a parents value

#print axioms history
#print axioms iterator
end PV_LIB_A_RangeHistory12
