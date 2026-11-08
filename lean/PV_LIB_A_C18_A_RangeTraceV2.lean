import PV_LIB_A_RangeHistoryV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeTraceV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine

/-- Identify the SAME165 prefix's returned continuation with the named source
iterator store. This is return-branch composition, not a success-only row Pre. -/
theorem after165_returned {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List E) (stack : List Config) (value : Data)
    (returned : (PV_THR2_Source15RangeToLoop.reply H s w).answer = .returned (.ok value)) :
    PV_THR2_Source15RangeToLoop.after C b H s a parents w es stack =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 12},parents,
        PV_LIB_A_RangeHistoryV2.iteratorStore s a value⟩,
        (PV_THR2_Source15RangeToLoop.reply H s w).world,
        es ++ (PV_THR2_Source15RangeToLoop.reply H s w).events⟩,stack⟩ := by
  unfold PV_THR2_Source15RangeToLoop.after PV_THR2_Source15Continue165.after
  rw [returned]
  rfl

/-- Continuous ORIGINAL-interpreter history from source3400 through the issued
3447/93 request. Compose the existing segment theorems by name; no site is
simulated again and no large concrete store is normalized. Failure/pending165
stays at the previously proved original_prefix boundary. D984/OWNER transport
of this segment is still a separate obligation, explicitly not asserted here. -/
theorem original_poll {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config) (value : Data)
    (returned : (PV_THR2_Source15RangeToLoop.reply H s w).answer = .returned (.ok value)) :
    PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve P)))
      H (PV_THR2_Source15RangeToLoop.steps H s w + (1+6))
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_THR2_Source15Loop93Issue.pending
        (PV_LIB_A_RangeHistoryV2.iteratorStore s a value) a parents),
        (PV_THR2_Source15RangeToLoop.reply H s w).world,
        es ++ (PV_THR2_Source15RangeToLoop.reply H s w).events⟩,stack⟩ := by
  rw [PV_THR2_IntrinsicComposition.advance_add,
    PV_LIB_A_RangeHistoryV2.original_prefix C K P H s a parents b w es stack,
    after165_returned C b H s a parents w es stack value returned,
    PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source15LoopEnter.run]
  exact PV_THR2_Source15Loop93Issue.run _ K _ H _ a parents b _ _ stack

#print axioms after165_returned
#print axioms original_poll
end PV_LIB_A_RangeTraceV2
