import PV_LIB_A_F170Return16
import PV_THR2_RunWithReturn
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F17Value16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem trace (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (v : Data)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,3,[]⟩ = some (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [v])) :
    PV_LIB_SPEC_SourceTransport15.Trace cut p H 8
      (stage s a parents (PV_THR2_F17.live.body.drop 7) w es issued consumed) := by
  have shape : PV_THR2_F17.live.body.drop 7 =
      [PV_THR2_F17.node7,PV_THR2_F17.node8,PV_THR2_F17.node23,
       PV_THR2_F17.node24,PV_THR2_F17.node25,PV_THR2_F17.node26,
       PV_THR2_F17.node27,PV_THR2_F17.node37] ++ PV_THR2_F17.live.body.drop 15 := rfl
  rw [shape]
  generalize hrest : PV_THR2_F17.live.body.drop 15 = rest
  have tag : (runtime p).control.variant (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [v]) = some 0 := rfl
  have field : (runtime p).carrier.field (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [v]) 0 = some v := rfl
  have moved : (runtime p).carrier.replaceField (PV_THR2_KeyValues.pack PV_THR2_RunTlsReturn.kind [v]) 0 none =
      some PV_THR2_RunWithValue.emptied := rfl
  have emptyTag : (runtime p).control.variant PV_THR2_RunWithValue.emptied = some 0 := rfl
  simp only [PV_THR2_RunWithValue.emptied] at moved emptyTag
  simp [PV_LIB_SPEC_SourceTransport15.Trace,PV_LIB_SPEC_SourceTransport15.sourceStep,
    PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_SPEC_ControlRuntime.ordinary,
    PV_LIB_StoreActionTable.Neutral,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
    PV_THR2_OwnUniformNeutral.instruction,PV_THR2_InterpreterAgreement.NativeAgree,
    PV_THR2_HandlerExecutionAgreement.Agree,stage,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,
    PV_THR2_Dynamic.active,PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_THR2_AggregateCompletion.carrier,PV_STX2_SliceMachine.step,
    PV_THR2_F17.node7,PV_THR2_F17.node8,PV_THR2_F17.node23,PV_THR2_F17.node24,
    PV_THR2_F17.node25,PV_THR2_F17.node26,PV_THR2_F17.node27,PV_THR2_F17.node37,
    PV_THR2_F17.block9,PV_THR2_F17.block28,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operand,PV_STX2_Store.read,locate,writeAddress,
    readAddress,readFields,replaceFields,write,cell,tag,field,moved,emptyTag,selectVariant]

#print axioms trace
end PV_LIB_A_F17Value16
