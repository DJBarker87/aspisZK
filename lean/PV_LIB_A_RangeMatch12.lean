import PV_LIB_A_ChainTrace11
import PV_THR2_Source15LiveCaptures
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeMatch12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_PrefixMachine11 PV_LIB_A_RangeStartTrace11

def loops : List LoopFrame := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]

/-- Only the actual post93 instruction shape is inspected. -/
theorem quiet6 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 6,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc
    exact ⟨rfl,rfl,by change ¬ ((15 : Nat) = 361 ∧ _); simp⟩

theorem quiet7 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 7,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Trace C K P H 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 6,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  apply cons_run C K P H 1 _ _ (quiet6 P s a parents w es stack)
    (PV_THR2_IntrinsicFrameSteps.storage C K P H s a parents loops
      (PV_THR2_F15.block47.drop 7)
      ⟨15,3448,.array [.atom "body",.atom "statements",.number 12,.atom "kind",.atom "Loop",.atom "statements",.number 6]⟩ false 9 w es stack)
  exact ⟨quiet7 P _ a parents w es stack,True.intro⟩

/-- Actual3448/3460 on the corrected machine. All discriminant/read failures
and both Option arms are retained; the iterator is the incoming written store. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance C K P resources encode H values 2
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 6,loops := loops},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨PV_THR2_Source15LoopMatch.after C K s a parents w es stack,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values 2 _
    (trace C K P H s a parents w es stack)]
  exact congrArg (fun q => (⟨q,none⟩ : PV_LIB_StoreActionTable.SourceState))
    (PV_THR2_Source15LoopMatch.run C K P H s a parents w es stack)

#print axioms quiet6
#print axioms quiet7
#print axioms trace
#print axioms run
end PV_LIB_A_RangeMatch12
