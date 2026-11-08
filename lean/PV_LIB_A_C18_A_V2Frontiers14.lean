import PV_LIB_A_C18_A_V2TraceTransport14
import PV_LIB_A_C18_A_SequenceFrontier13
import PV_LIB_A_C18_A_StructuredFrontier13
import PV_LIB_A_C18_A_CallIssue13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2Frontiers14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_PrefixMachine11 PV_LIB_A_StructuredFrontier13

/-- Contract-first frontier lift on ORIGINAL v2 using the existing named source
contract and a per-step neutrality certificate. No source-phase projection. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (nodes : List PV_STX2_SliceSyntax.Node) (cost : Config → OWNER → Nat)
    (finish : Config → OWNER → List PV_RJ4IDB.NativeEvent → List Config → State)
    (quiet : ∀ c w es stack, PV_THR2_IntrinsicAtContinuation.Ready nodes c →
      Trace C K P H (cost c w) ⟨⟨.running c,w,es⟩,stack⟩)
    (existing : ∀ c w es stack, PV_THR2_IntrinsicAtContinuation.Ready nodes c →
      PV_THR2_IntrinsicState.advance C K P H (cost c w) ⟨⟨.running c,w,es⟩,stack⟩ = finish c w es stack)
    (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values
      (PV_THR2_IntrinsicAtContinuation.steps nodes cost q) q =
      PV_THR2_IntrinsicAtContinuation.after nodes finish q := by
  rw [PV_LIB_A_V2TraceTransport14.run C K P resources encode H values _ _
    (PV_LIB_A_Continuation12.trace C K P H nodes cost quiet q)]
  exact PV_THR2_IntrinsicAtContinuation.run C K P H nodes cost finish existing q

theorem sequence (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (seq : PV_LIB_A_SourceSequence13.Seq) (rest : List PV_STX2_SliceSyntax.Node)
    (off : PV_LIB_A_SourceSequence13.sites seq) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values
      (PV_LIB_A_SequenceFrontier13.steps C seq rest q) q = PV_LIB_A_SequenceFrontier13.after C seq rest q := by
  apply run
  · intro c w es stack ready
    rw [PV_THR2_IntrinsicAtContinuation.frame c ready]
    exact (PV_LIB_A_SourceSequence13.certified C K P H seq c.store c.frame.activation c.callers c.frame.loops rest w es stack off).1
  · intro c w es stack ready
    rw [PV_THR2_IntrinsicAtContinuation.frame c ready]
    exact (PV_LIB_A_SourceSequence13.certified C K P H seq c.store c.frame.activation c.callers c.frame.loops rest w es stack off).2

theorem issue (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (src : Source) (rest : List PV_STX2_SliceSyntax.Node) (off : src.1.function ≠ 361)
    (stable : ∀ s a w, operands (PV_THR2_AggregateCompletion.carrier C) w a src.2.2.2.1 s = operands C w a src.2.2.2.1 s)
    (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (PV_LIB_A_CallIssue13.steps src rest q) q =
      PV_LIB_A_CallIssue13.after C src rest q := by
  apply run
  · intro c w es stack ready
    rw [PV_THR2_IntrinsicAtContinuation.frame c ready]
    exact ⟨PV_LIB_A_StructuredTrace12.issue_quiet P c.store c.frame.activation c.callers c.frame.loops rest src.1
      (fn src) src.2.2.2.1 src.2.2.2.2 off w es stack,True.intro⟩
  · intro c w es stack ready
    rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
    rcases ready with ⟨rfl,rfl,rfl,rfl⟩
    exact PV_THR2_IntrinsicFrameCall.run C K P H s a parents loops rest src.1 src.2.1 src.2.2.1
      src.2.2.2.1 src.2.2.2.2 w es stack (stable s a w)

theorem structured (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (src : Source) (rest : List PV_STX2_SliceSyntax.Node) (body : PV_STX2_SliceSyntax.Program)
    (off : src.1.function ≠ 361)
    (quiet : ∀ t a parents loops vs,
      PV_THR2_OwnInitAction.selected (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest (fn src) vs src.2.2.2.2) = false ∧
      PV_THR2_OperatorAction.selected (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest (fn src) vs src.2.2.2.2) = none)
    (ordinary : ∀ t a parents loops vs, PV_THR2_Catch316Segment.select
      (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest (fn src) vs src.2.2.2.2) = none)
    (stable : ∀ s a w, operands (PV_THR2_AggregateCompletion.carrier C) w a src.2.2.2.1 s = operands C w a src.2.2.2.1 s)
    (resolved : P (fn src) = some body) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values
      (PV_LIB_A_StructuredFrontier13.steps C src rest q) q = PV_LIB_A_StructuredFrontier13.after C src rest body q := by
  apply run
  · intro c w es stack ready
    rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
    rcases ready with ⟨rfl,rfl,rfl,rfl⟩
    exact PV_LIB_A_StructuredTrace12.trace C K P H s a parents loops rest src.1 src.2.1 src.2.2.1
      src.2.2.2.1 src.2.2.2.2 body off (fun t vs => (quiet t a parents loops vs).1)
      (fun t vs => (quiet t a parents loops vs).2) w es stack (stable s a w) resolved
  · intro c w es stack ready
    rcases c with ⟨⟨a,remaining,loops,wait,unwind,done⟩,parents,s⟩
    rcases ready with ⟨rfl,rfl,rfl,rfl⟩
    exact PV_THR2_IntrinsicStructuredCall.run C K P H s a parents loops rest src.1 src.2.1 src.2.2.1
      src.2.2.2.1 src.2.2.2.2 body w es stack (stable s a w) (fun t vs => ordinary t a parents loops vs) resolved

#print axioms run
#print axioms sequence
#print axioms issue
#print axioms structured
end PV_LIB_A_V2Frontiers14
