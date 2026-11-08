import PV_LIB_A_CallbackTail14
import PV_LIB_A_F219Issue31813
import PV_LIB_A_IntrinsicInvoke13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F219Selected14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11

def parent (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame) :=
  PV_THR2_IntrinsicFrameEnter.pending
    (PV_THR2_Catch219Call318.moved (PV_LIB_A_CallbackTail14.stored s a) a) a parents loops
    (PV_THR2_F219.live.body.drop 17) PV_THR2_Catch219Call318.fn (PV_THR2_Catch219Call318.args a) 5

theorem operands (C : Carrier OWNER Data) (s : Store Data) (a : Nat) (w : OWNER) :
    PV_STX2_Store.operands C w a [.move (.local 6),.move (.local 7),.move (.local 8)]
      (PV_LIB_A_CallbackTail14.stored s a) =
    some (PV_THR2_Catch219Call318.args a,
      PV_THR2_Catch219Call318.moved (PV_LIB_A_CallbackTail14.stored s a) a) := by
  rcases PV_LIB_A_CallbackTail14.cells s a with ⟨c6,c7,c8⟩
  simp [PV_STX2_Store.operands,operand,PV_STX2_Store.read,locate,writeAddress,write,c6,c7,c8,
    PV_THR2_Catch219Call318.args,PV_THR2_Catch219Call318.moved]

/-- At the actual issued request, the selector follows from generated source
stores. No callback selector, readback, native success or callee counter is a premise. -/
theorem selected (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame) :
    PV_THR2_Catch316Segment.select (parent s a parents loops) =
      some (PV_THR2_CallbackSegment.enter (parent s a parents loops) PV_THR2_F316.live
        [PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null]) := by
  simp [parent,PV_THR2_Catch316Segment.select,PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticReply.wait,
    PV_THR2_Catch219Call318.args]

theorem issue (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_PrefixMachine11.advance C K (PV_THR2_CatchChildren.table P) resources encode H values 1
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 16,loops := loops},
        parents,PV_LIB_A_CallbackTail14.stored s a⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (parent s a parents loops),w,es⟩,stack⟩,none⟩ := by
  have h := PV_LIB_A_F219Issue31813.run C K P resources encode H values
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 16,loops := loops},
      parents,PV_LIB_A_CallbackTail14.stored s a⟩,w,es⟩,stack⟩
  have ready : PV_THR2_IntrinsicAtContinuation.Ready
      (PV_LIB_A_StructuredFrontier13.node PV_LIB_A_F219Issue31813.src :: PV_LIB_A_F219Issue31813.rest)
      ⟨{activation := a,remaining := PV_THR2_F219.live.body.drop 16,loops := loops},
        parents,PV_LIB_A_CallbackTail14.stored s a⟩ := ⟨rfl,rfl,rfl,rfl⟩
  simp only [PV_LIB_A_F219Issue31813.steps,PV_LIB_A_F219Issue31813.after,
    PV_LIB_A_CallIssue13.steps,PV_LIB_A_CallIssue13.after,PV_THR2_IntrinsicAtContinuation.steps,
    PV_THR2_IntrinsicAtContinuation.after,if_pos ready,PV_LIB_A_CallIssue13.finish,
    PV_THR2_IntrinsicFrameCall.after,show PV_LIB_A_F219Issue31813.src.2.2.2.1 =
      [.move (.local 6),.move (.local 7),.move (.local 8)] from rfl,operands] at h
  exact h

theorem invoke (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_LIB_A_DeferredActions.step C K P resources encode H values
      ⟨⟨⟨.running (parent s a parents loops),w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (PV_THR2_CallbackSegment.enter (parent s a parents loops) PV_THR2_F316.live
        [PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null]).callback,w,es⟩,
        parent s a parents loops :: stack⟩,none⟩ :=
  PV_LIB_A_IntrinsicInvoke13.run C K P resources encode H values _ a parents loops _ 5 w es stack _
    (selected s a parents loops)

#print axioms operands
#print axioms selected
#print axioms issue
#print axioms invoke
end PV_LIB_A_F219Selected14
