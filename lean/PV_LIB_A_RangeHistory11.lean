import PV_LIB_A_RangeTailTrace11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeHistory11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_PrefixMachine11

/-- Complete3400..3423 finite certificate, with all165 answers retained.
The only nonzero continuation is the actual returned iterator move. -/
theorem prefix_trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Trace (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (PV_LIB_A_RangePoll11.programs P) H (PV_THR2_Source15RangeToLoop.steps H s w)
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩ := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  let T := PV_LIB_A_RangePoll11.programs P
  unfold PV_THR2_Source15RangeToLoop.steps
  apply append B K T H 5 _ _ (PV_LIB_A_RangeStartTrace11.prefix5 C K P H s a parents b w es stack)
  have initial := PV_THR2_Source15To165.run C K P H s a parents b w es stack
  change PV_THR2_IntrinsicState.advance B K T H 5 _ = _ at initial
  rw [initial]
  change Trace B K T H
    (PV_THR2_Source15Continue165.steps (PV_THR2_Source15RangeToLoop.reply H s w))
    (PV_THR2_IntrinsicFullLocal.received B (PV_LIB_A_RangeHistoryV2.issued165 s a)
      a parents (PV_THR2_F15.live.body.drop 9) PV_THR2_Source15RangeChild.fn165
      [PV_THR2_Source15RangeAggregate.value] 5 (PV_THR2_Source15RangeToLoop.reply H s w) es stack)
  generalize PV_THR2_Source15RangeToLoop.reply H s w = r
  rcases r with ⟨answer,world,events⟩
  cases answer with
  | pending => trivial
  | fault f => trivial
  | returned result =>
    cases result with
    | fail e => trivial
    | div => trivial
    | ok v =>
      rw [PV_THR2_IntrinsicFullLocal.returned]
      exact PV_LIB_A_RangeTailTrace11.move3 B K T H _ a parents world (es ++ events) stack

/-- All-answer corrected-machine prefix, reusing the SAME provider run through
one proved control trace. No trace or local-cell premise escapes this theorem. -/
theorem corrected_prefix (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (PV_LIB_A_RangePoll11.programs P) resources encode H values
      (PV_THR2_Source15RangeToLoop.steps H s w)
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨PV_THR2_Source15RangeToLoop.after C b H s a parents w es stack,none⟩ := by
  rw [run _ K _ resources encode H values _ _ (prefix_trace C K P H s a parents b w es stack)]
  exact congrArg (fun q => (⟨q,none⟩ : PV_LIB_StoreActionTable.SourceState))
    (PV_LIB_A_RangeHistoryV2.original_prefix C K P H s a parents b w es stack)

/-- Same prefix, returned165 branch, through the ACTUAL3447 request. The
named returned case selects a conclusion branch;93's answer remains arbitrary. -/
theorem poll (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (value : Data)
    (returned : (PV_THR2_Source15RangeToLoop.reply H s w).answer = .returned (.ok value)) :
    advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (PV_LIB_A_RangePoll11.programs P) resources encode H values
      (PV_THR2_Source15RangeToLoop.steps H s w + 7)
      ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (PV_THR2_Source15Loop93Issue.pending
        (PV_LIB_A_RangeHistoryV2.iteratorStore s a value) a parents),
        (PV_THR2_Source15RangeToLoop.reply H s w).world,
        es ++ (PV_THR2_Source15RangeToLoop.reply H s w).events⟩,stack⟩,none⟩ := by
  apply Eq.trans (run _ K _ resources encode H values _ _ ?_) _
  · apply append _ K _ H _ 7 _ (prefix_trace C K P H s a parents b w es stack)
    dsimp only [PV_LIB_A_RangePoll11.programs]
    rw [PV_LIB_A_RangeHistoryV2.original_prefix C K P H s a parents b w es stack,
      PV_LIB_A_RangeTraceV2.after165_returned C b H s a parents w es stack value returned]
    exact PV_LIB_A_RangeTailTrace11.enter7 _ K _ H _ a parents b _ _ stack
  · exact congrArg (fun q => (⟨q,none⟩ : PV_LIB_StoreActionTable.SourceState))
      (PV_LIB_A_RangeTraceV2.original_poll C K P H s a parents b w es stack value returned)

#print axioms prefix_trace
#print axioms corrected_prefix
#print axioms poll
end PV_LIB_A_RangeHistory11
