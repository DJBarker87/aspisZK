import PV_LIB_A_C18_A_StructuredFrontier13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CallIssue13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11
open PV_LIB_A_StructuredFrontier13

def steps (src : Source) (rest : List PV_STX2_SliceSyntax.Node) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.steps (node src :: rest) (fun _ _ => 1) q

def finish (C : Carrier OWNER Data) (src : Source) (rest : List PV_STX2_SliceSyntax.Node)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_THR2_IntrinsicFrameCall.after C c.store c.frame.activation c.callers c.frame.loops rest
    src.1 src.2.1 src.2.2.1 src.2.2.2.1 src.2.2.2.2 w es stack

def after (C : Carrier OWNER Data) (src : Source) (rest : List PV_STX2_SliceSyntax.Node) :=
  PV_THR2_IntrinsicAtContinuation.after (node src :: rest) (finish C src rest)

/-- Issue the exact call, without treating an intrinsic as a native full reply
or prematurely entering a structured callee. Failed operands keep their source gap. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (src : Source) (rest : List PV_STX2_SliceSyntax.Node) (off : src.1.function ≠ 361)
    (stable : ∀ s a w, operands (PV_THR2_AggregateCompletion.carrier C) w a src.2.2.2.1 s = operands C w a src.2.2.2.1 s)
    (q : State) :
    PV_LIB_A_PrefixMachine11.advance C K P resources encode H values (steps src rest q) ⟨q,none⟩ =
      ⟨after C src rest q,none⟩ := by
  apply PV_LIB_A_Continuation12.run
  · intro c w es stack h
    rw [PV_THR2_IntrinsicAtContinuation.frame c h]
    exact ⟨PV_LIB_A_StructuredTrace12.issue_quiet P c.store c.frame.activation c.callers c.frame.loops rest src.1
      (fn src) src.2.2.2.1 src.2.2.2.2 off w es stack,True.intro⟩
  · intro c w es stack h
    rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
    rcases h with ⟨rfl,rfl,rfl,rfl⟩
    exact PV_THR2_IntrinsicFrameCall.run C K P H s a parents loops rest src.1 src.2.1 src.2.2.1
      src.2.2.2.1 src.2.2.2.2 w es stack (stable s a w)

#print axioms steps
#print axioms finish
#print axioms after
#print axioms run
end PV_LIB_A_CallIssue13
