import PV_LIB_A_RangeStartTrace11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeTailTrace11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine
open PV_LIB_A_PrefixMachine11 PV_LIB_A_RangeQuiet11 PV_LIB_A_RangeStartTrace11

theorem move3 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Trace C K P H 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 9},parents,s⟩,w,es⟩,stack⟩ := by
  apply cons_run C K P H 2 _ _ (main9 P s a parents [] w es stack)
    (PV_THR2_IntrinsicStorage.run C K P H s a parents (PV_THR2_F15.live.body.drop 10)
      ⟨15,3421,.array [.atom "body",.atom "statements",.number 9]⟩ false 6 w es stack)
  apply cons_run C K P H 1 _ _ (main10 P _ a parents [] w es stack)
    (PV_THR2_IntrinsicStorage.run C K P H _ a parents (PV_THR2_F15.live.body.drop 11)
      ⟨15,3422,.array [.atom "body",.atom "statements",.number 10]⟩ true 7 w es stack)
  exact ⟨main11 P _ a parents [] w es stack,True.intro⟩

/-- Only control and the self-created local10 reference are inspected.
The iterator local7 and all lower-frame/OWNER data remain symbolic. -/
theorem loop6 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Trace (PV_THR2_EntryDynamic.carrier C b) K P H 6
      ⟨⟨.running (PV_THR2_Source15LoopEnter.after s a parents),w,es⟩,stack⟩ := by
  let B := PV_THR2_EntryDynamic.carrier C b
  let loops : List LoopFrame := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]
  apply cons_run B K P H 5 _ _ (loop0 P s a parents loops w es stack)
    (PV_THR2_IntrinsicFrameSteps.storage B K P H s a parents loops
      (PV_THR2_F15.block47.drop 1)
      ⟨15,3425,.array [.atom "body",.atom "statements",.number 12,.atom "kind",.atom "Loop",.atom "statements",.number 0]⟩ true 8 w es stack)
  apply cons_run B K P H 4 _ _ (loop1 P _ a parents loops w es stack)
    (PV_THR2_IntrinsicFrameSteps.storage B K P H _ a parents loops
      (PV_THR2_F15.block47.drop 2)
      ⟨15,3426,.array [.atom "body",.atom "statements",.number 12,.atom "kind",.atom "Loop",.atom "statements",.number 1]⟩ true 9 w es stack)
  apply cons_run B K P H 3 _ _ (loop2 P _ a parents loops w es stack)
    (PV_THR2_IntrinsicFrameSteps.storage B K P H _ a parents loops
      (PV_THR2_F15.block47.drop 3)
      ⟨15,3427,.array [.atom "body",.atom "statements",.number 12,.atom "kind",.atom "Loop",.atom "statements",.number 2]⟩ true 10 w es stack)
  apply cons_run B K P H 2 _ _ (loop3 P _ a parents loops w es stack)
    (PV_THR2_IntrinsicFrameSteps.localRef C K P H _ a 7 10 parents loops
      (PV_THR2_F15.block47.drop 4)
      ⟨15,3428,.array [.atom "body",.atom "statements",.number 12,.atom "kind",.atom "Loop",.atom "statements",.number 3]⟩ b w es stack)
  apply cons_run B K P H 1 _ _ (loop4 P _ a parents loops w es stack)
    (PV_THR2_IntrinsicFrameSteps.derefRef C K P H _ a 10 9 ⟨a,7,[]⟩ parents loops
      (PV_THR2_F15.block47.drop 5)
      ⟨15,3429,.array [.atom "body",.atom "statements",.number 12,.atom "kind",.atom "Loop",.atom "statements",.number 4]⟩ b w es stack (write_same _ _ _))
  exact ⟨loop5 P _ a parents loops w es stack,True.intro⟩

/-- The actual loop entry plus request prefix, with its saved loop stack. -/
theorem enter7 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Trace (PV_THR2_EntryDynamic.carrier C b) K P H 7
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 12},parents,s⟩,w,es⟩,stack⟩ :=
  cons_run _ K P H 6 _ _ (main12 P s a parents [] w es stack)
    (PV_THR2_Source15LoopEnter.run _ K P H s a parents w es stack)
    (loop6 C K P H s a parents b w es stack)

#print axioms move3
#print axioms loop6
#print axioms enter7
end PV_LIB_A_RangeTailTrace11
