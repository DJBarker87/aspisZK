import PV_LIB_A_FrontierRun14
import PV_LIB_A_StructuredFrontier13
import PV_THR2_IntrinsicChildCall
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_NativeFull14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_StructuredFrontier13

/-- Full native child at its emitted source call, under any ONE fixed table
that leaves that named child opaque. Source gaps and every answer remain. The
quiet/ordinary/lookup inputs are source/table certificates, discharged at each
actual use, and are never row Pre or MachineSpec fields. -/
theorem exact_call (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (src : Source) (rest : List PV_STX2_SliceSyntax.Node)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (off : src.1.function ≠ 361)
    (stable : operands (PV_THR2_AggregateCompletion.carrier C) w a src.2.2.2.1 s = operands C w a src.2.2.2.1 s)
    (waiting : ∀ t vs, Quiet P ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest
      (fn src) vs src.2.2.2.2),w,es⟩,stack⟩)
    (ordinary : ∀ t vs, PV_THR2_Catch316Segment.select (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest
      (fn src) vs src.2.2.2.2) = none) (child : P (fn src) = none) :
    advance C K P resources encode H values (PV_THR2_IntrinsicChildCall.steps C s a src.2.2.2.1 w)
      ⟨⟨⟨.running ⟨{activation := a,remaining := node src :: rest,loops := loops},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨PV_THR2_IntrinsicChildCall.after C H s a parents loops rest src.1 (fn src) src.2.2.2.1 src.2.2.2.2 w es stack,none⟩ := by
  have trace : Trace C K P H (PV_THR2_IntrinsicChildCall.steps C s a src.2.2.2.1 w)
      ⟨⟨.running ⟨{activation := a,remaining := node src :: rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
    simp only [node,fn]
    unfold PV_THR2_IntrinsicChildCall.steps
    apply append C K P H 1 _ _
      ⟨PV_LIB_A_StructuredTrace12.issue_quiet P s a parents loops rest src.1 (fn src) src.2.2.2.1 src.2.2.2.2 off w es stack,True.intro⟩
    simp only [fn]
    rw [PV_THR2_IntrinsicFrameCall.run C K P H s a parents loops rest src.1 src.2.1 src.2.2.1
      src.2.2.2.1 src.2.2.2.2 w es stack stable]
    unfold PV_THR2_IntrinsicFrameCall.after
    cases evaluated : operands C w a src.2.2.2.1 s with
    | none => trivial
    | some pair =>
      rcases pair with ⟨vs,t⟩
      exact ⟨waiting t vs,True.intro⟩
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values _ _ trace]
  exact congrArg (fun q => (⟨q,none⟩ : SourceState))
    (PV_THR2_IntrinsicChildCall.run C K P H s a parents loops rest src.1 src.2.1 src.2.2.1
      src.2.2.2.1 src.2.2.2.2 w es stack stable ordinary child)

#print axioms exact_call
end PV_LIB_A_NativeFull14
