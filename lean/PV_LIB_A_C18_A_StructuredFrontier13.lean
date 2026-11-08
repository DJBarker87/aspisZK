import PV_LIB_A_C18_A_StructuredTrace12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_StructuredFrontier13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Exact emitted descriptor components; malformed nodes are excluded by each
actual caller's shape theorem, never interpreted as a successful call. -/
abbrev Source := PV_STX2_Syntax.Site × Data × Data × List Operand × Nat

def source (node : PV_STX2_SliceSyntax.Node) : Source := match node with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) =>
      (site,kind,generics,args,dest)
  | _ => (⟨0,0,.null⟩,.null,.null,[],0)

def fn (src : Source) : Data := .object [("Regular",.object [("kind",src.2.1),("generics",src.2.2.1)])]
def node (src : Source) : PV_STX2_SliceSyntax.Node :=
  .leaf (.call src.1 (fn src) src.2.2.2.1 (.local src.2.2.2.2) [])

def cost (C : Carrier OWNER Data) (src : Source) (c : Config) (w : OWNER) :=
  PV_THR2_IntrinsicStructuredCall.steps C c.store c.frame.activation src.2.2.2.1 w

def finish (C : Carrier OWNER Data) (src : Source) (rest : List PV_STX2_SliceSyntax.Node)
    (body : PV_STX2_SliceSyntax.Program) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_THR2_IntrinsicStructuredCall.after C c.store c.frame.activation c.callers c.frame.loops rest
    src.1 (fn src) src.2.2.2.1 src.2.2.2.2 body w es stack

def steps (C : Carrier OWNER Data) (src : Source) (rest : List PV_STX2_SliceSyntax.Node) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.steps (node src :: rest) (cost C src) q
def after (C : Carrier OWNER Data) (src : Source) (rest : List PV_STX2_SliceSyntax.Node)
    (body : PV_STX2_SliceSyntax.Program) :=
  PV_THR2_IntrinsicAtContinuation.after (node src :: rest) (finish C src rest body)

/-- Per-site hypotheses here are syntax/table certificates, not return-value or
source-write assumptions. Actual callers discharge every one on emitted DATA. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (src : Source) (rest : List PV_STX2_SliceSyntax.Node) (body : PV_STX2_SliceSyntax.Program)
    (off : src.1.function ≠ 361)
    (quiet : ∀ (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame) (vs : List Data),
      PV_THR2_OwnInitAction.selected (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest (fn src) vs src.2.2.2.2) = false ∧
      PV_THR2_OperatorAction.selected (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest (fn src) vs src.2.2.2.2) = none)
    (ordinary : ∀ (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame) (vs : List Data),
      PV_THR2_Catch316Segment.select (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest (fn src) vs src.2.2.2.2) = none)
    (stable : ∀ s a w, operands (PV_THR2_AggregateCompletion.carrier C) w a src.2.2.2.1 s = operands C w a src.2.2.2.1 s)
    (resolved : P (fn src) = some body) (q : State) :
    advance C K P resources encode H values (steps C src rest q) ⟨q,none⟩ =
      ⟨after C src rest body q,none⟩ := by
  apply PV_LIB_A_Continuation12.run
  · intro c w es stack h
    rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
    rcases h with ⟨rfl,rfl,rfl,rfl⟩
    exact PV_LIB_A_StructuredTrace12.trace C K P H s a parents loops rest src.1 src.2.1 src.2.2.1
      src.2.2.2.1 src.2.2.2.2 body off
      (fun t vs => (quiet t a parents loops vs).1)
      (fun t vs => (quiet t a parents loops vs).2) w es stack (stable s a w) resolved
  · intro c w es stack h
    rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
    rcases h with ⟨rfl,rfl,rfl,rfl⟩
    exact PV_THR2_IntrinsicStructuredCall.run C K P H s a parents loops rest src.1 src.2.1 src.2.2.1
      src.2.2.2.1 src.2.2.2.2 body w es stack (stable s a w)
      (fun t vs => ordinary t a parents loops vs) resolved

#print axioms source
#print axioms fn
#print axioms node
#print axioms cost
#print axioms finish
#print axioms steps
#print axioms after
#print axioms run
end PV_LIB_A_StructuredFrontier13
