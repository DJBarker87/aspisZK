import PV_LIB_SPEC_TlsAt68
import PV_THR2_RunTlsMatch
import PV_THR2_RunTlsForward
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsForward16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem trace (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) (value pointer : Data)
    (cell : s.cells ⟨a,4,[]⟩ = some value)
    (variant : (runtime p).control.variant value = some 0)
    (field : (runtime p).carrier.field value 0 = some pointer) :
    PV_LIB_SPEC_SourceTransport15.Trace cut p H 7
      (stage s a parents (PV_THR2_F170.live.body.drop 24) w es issued consumed) := by
  simp [PV_LIB_SPEC_SourceTransport15.Trace,PV_LIB_SPEC_SourceTransport15.sourceStep,
    PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_SPEC_ControlRuntime.ordinary,
    PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
    PV_THR2_OwnUniformNeutral.instruction,PV_THR2_InterpreterAgreement.NativeAgree,
    PV_THR2_HandlerExecutionAgreement.Agree,stage,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,
    PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
    PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
    PV_STX2_SliceMachine.step,PV_THR2_F170.live,PV_THR2_F170.block66,
    PV_THR2_F170.node24,PV_THR2_F170.node41,PV_THR2_F170.block25,
    PV_THR2_F170.node42,PV_THR2_F170.node43,PV_THR2_F170.node44,PV_THR2_F170.node45,PV_THR2_F170.node46,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,PV_STX2_Store.write,cell,variant,field,selectVariant]

def prepared (s : Store Data) (a : Nat) (pointer : Data) : Store Data :=
  PV_THR2_RunTlsForward.prepared (write s ⟨a,5,[]⟩ none) a pointer

theorem source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (value pointer : Data) (w : OWNER) (es : List Event)
    (cell : s.cells ⟨a,4,[]⟩ = some value)
    (variant : (runtime p).control.variant value = some 0)
    (field : (runtime p).carrier.field value 0 = some pointer) :
    PV_THR2_Execution.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H 7
      ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 24},parents,s⟩,w,es⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 31},parents,
        prepared s a pointer⟩,w,es⟩ := by
  rw [show 7=2+5 from rfl,PV_THR2_Execution.advance_add,
    PV_THR2_RunTlsMatch.success _ _ _ _ _ _ _ value _ _ cell variant]
  rw [PV_THR2_RunTlsForward.forward _ _ _ _ _ _ _ value _ _
    (by simpa [write] using cell),field]
  rfl

#print axioms trace
#print axioms prepared
#print axioms source
end PV_LIB_SPEC_TlsForward16
