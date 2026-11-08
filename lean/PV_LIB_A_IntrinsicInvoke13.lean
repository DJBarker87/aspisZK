import PV_LIB_A_PrefixMachine11
import PV_THR2_IntrinsicScopeEntry
import PV_THR2_IntrinsicFrameEnter
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_IntrinsicInvoke13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

def rest := PV_THR2_F219.live.body.drop 17

theorem quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (args : List Data) (dest : Nat)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest
      PV_THR2_Catch219Call318.fn args dest),w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc
    unfold sourceSelect
    change (match P PV_THR2_Catch219Call318.fn with | some _ => none | none => none) = none
    cases P PV_THR2_Catch219Call318.fn <;> rfl
  · intro c hc; cases hc
    cases args with
    | nil => exact ⟨rfl,rfl,True.intro⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩

/-- The source-selected callback is entered exactly once, with the COMPLETE
parent and actual post-issuance store retained. `selected` is a source syntax
certificate; the exact emitted request discharges it in `actual` below. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (args : List Data) (dest : Nat)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (segment : PV_THR2_CallbackSegment.Segment)
    (selected : PV_THR2_Catch316Segment.select (PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest
      PV_THR2_Catch219Call318.fn args dest) = some segment) :
    PV_LIB_A_DeferredActions.step C K P resources encode H values
      ⟨⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest
        PV_THR2_Catch219Call318.fn args dest),w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running segment.callback,w,es⟩,segment.suspended :: stack⟩,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.step C K P resources encode H values _
    (quiet P s a parents loops args dest w es stack)]
  apply congrArg (fun q => (⟨q,none⟩ : SourceState))
  simp only [PV_THR2_IntrinsicState.step,selected,PV_THR2_IntrinsicState.invoke]

/-- Actual9196 argument order and source Data address select316 by the pinned
provider theorem, not by an invented callback address or a native returned arm. -/
theorem actual (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let parent := PV_THR2_Catch219Call318.pending s a parents
    let segment := PV_THR2_CallbackSegment.enter parent PV_THR2_F316.live
      [PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null]
    PV_LIB_A_DeferredActions.step C K P resources encode H values
      ⟨⟨⟨.running parent,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running segment.callback,w,es⟩,parent :: stack⟩,none⟩ := by
  exact run C K P resources encode H values (PV_THR2_Catch219Call318.moved s a) a parents []
    (PV_THR2_Catch219Call318.args a) 5 w es stack _
    (PV_THR2_Catch316Segment.selected s a parents)

#print axioms quiet
#print axioms run
#print axioms actual
end PV_LIB_A_IntrinsicInvoke13
