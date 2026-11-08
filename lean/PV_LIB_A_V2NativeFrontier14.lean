import PV_LIB_A_V2Frontiers14
import PV_LIB_A_NativeFrontier14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2NativeFrontier14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_PrefixMachine11 PV_LIB_A_StructuredFrontier13

/-- Finite trace certificate for the named existing FULL child contract. No
callee body is expanded, and no reply arm is excluded. -/
theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler)
    (src : Source) (rest : List PV_STX2_SliceSyntax.Node)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (off : src.1.function ≠ 361)
    (stable : operands (PV_THR2_AggregateCompletion.carrier C) w a src.2.2.2.1 s = operands C w a src.2.2.2.1 s)
    (waiting : ∀ t vs, Quiet P ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest
      (fn src) vs src.2.2.2.2),w,es⟩,stack⟩) :
    Trace C K P H (PV_THR2_IntrinsicChildCall.steps C s a src.2.2.2.1 w)
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
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (src : Source) (rest : List PV_STX2_SliceSyntax.Node) (off : src.1.function ≠ 361)
    (stable : ∀ s a w, operands (PV_THR2_AggregateCompletion.carrier C) w a src.2.2.2.1 s = operands C w a src.2.2.2.1 s)
    (waiting : ∀ t a parents loops vs w es stack,
      Quiet P ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest
        (fn src) vs src.2.2.2.2),w,es⟩,stack⟩)
    (ordinary : ∀ t a parents loops vs, PV_THR2_Catch316Segment.select
      (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest (fn src) vs src.2.2.2.2) = none)
    (child : P (fn src) = none) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (PV_LIB_A_NativeFrontier14.steps C src rest q) q = PV_LIB_A_NativeFrontier14.after C H src rest q := by
  apply PV_LIB_A_V2Frontiers14.run
  · intro c w es stack ready
    rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
    rcases ready with ⟨rfl,rfl,rfl,rfl⟩
    exact trace C K P H src rest s a parents loops w es stack off (stable s a w)
      (fun t vs => waiting t a parents loops vs w es stack)
  · intro c w es stack ready
    rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
    rcases ready with ⟨rfl,rfl,rfl,rfl⟩
    exact PV_THR2_IntrinsicChildCall.run C K P H s a parents loops rest src.1 src.2.1 src.2.2.1
      src.2.2.2.1 src.2.2.2.2 w es stack (stable s a w)
      (fun t vs => ordinary t a parents loops vs) child

#print axioms trace
#print axioms run
end PV_LIB_A_V2NativeFrontier14
