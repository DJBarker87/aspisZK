import PV_LIB_A_NativeFull14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_NativeFrontier14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_StructuredFrontier13

def cost (C : Carrier OWNER Data) (src : Source) (c : Config) (w : OWNER) :=
  PV_THR2_IntrinsicChildCall.steps C c.store c.frame.activation src.2.2.2.1 w
def finish (C : Carrier OWNER Data) (H : Handler) (src : Source) (rest : List PV_STX2_SliceSyntax.Node)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_THR2_IntrinsicChildCall.after C H c.store c.frame.activation c.callers c.frame.loops rest
    src.1 (fn src) src.2.2.2.1 src.2.2.2.2 w es stack

def steps (C : Carrier OWNER Data) (src : Source) (rest : List PV_STX2_SliceSyntax.Node) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.steps (node src :: rest) (cost C src) q
def after (C : Carrier OWNER Data) (H : Handler) (src : Source) (rest : List PV_STX2_SliceSyntax.Node) :=
  PV_THR2_IntrinsicAtContinuation.after (node src :: rest) (finish C H src rest)

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
    advance C K P resources encode H values (steps C src rest q) ⟨q,none⟩ = ⟨after C H src rest q,none⟩ := by
  apply PV_LIB_A_FrontierRun14.run
  intro c w es stack h
  rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  exact PV_LIB_A_NativeFull14.exact_call C K P resources encode H values src rest s a parents loops w es stack
    off (stable s a w) (fun t vs => waiting t a parents loops vs w es stack)
    (fun t vs => ordinary t a parents loops vs) child

#print axioms steps
#print axioms after
#print axioms run
end PV_LIB_A_NativeFrontier14
