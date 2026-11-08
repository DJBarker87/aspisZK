import PV_LIB_A_F2History16
import PV_THR2_RunActiveEntry
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_A_F5Entry16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def site : Site := match PV_THR2_F1.node53 with | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩
def branchStore (s : Store Data) (a : Nat) : Store Data := write s ⟨a,9,[]⟩ none

def after (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) : Execution :=
  stage (PV_THR2_RunActiveEntry.issued (branchStore s a) a) s.nextActivation
    (PV_THR2_RunActiveEntry.parent (branchStore s a) a :: parents) PV_THR2_F5.live.body w es
    (⟨site,a,.child PV_THR2_ActiveTable.callee s.nextActivation []⟩::issued) consumed

theorem lookup : PV_LIB_SPEC_Full.programs PV_THR2_ActiveTable.callee = some PV_THR2_F5.live := rfl

theorem run (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,9,[]⟩ = some (.boolean false)) :
    PV_LIB_SPEC_ReachedNative14.run cut p 7
      (stage s a parents (PV_THR2_F1.live.body.drop 12) w es issued consumed) =
      after s a parents w es issued consumed := by
  have shape : PV_THR2_F1.live.body.drop 12 = PV_THR2_F1.node166 :: PV_THR2_F1.live.body.drop 13 := rfl
  rw [shape]
  unfold after PV_THR2_RunActiveEntry.parent
  generalize hrest : PV_THR2_F1.live.body.drop 13 = rest
  generalize htail : PV_THR2_F1.block165.drop 5 = tail
  have block : PV_THR2_F1.block165 =
      [PV_THR2_F1.node49,PV_THR2_F1.node50,PV_THR2_F1.node51,PV_THR2_F1.node52,PV_THR2_F1.node53] ++ tail := by
    rw [← htail]; rfl
  have tailHead : tail = PV_THR2_F1.node54 :: PV_THR2_F1.block165.drop 6 := by
    rw [← htail]; rfl
  generalize hrestTail : PV_THR2_F1.block165.drop 6 = tail2 at tailHead
  have truth : (runtime p).carrier.truth (.boolean false) = some false := rfl
  have resolved := lookup
  simp only [PV_THR2_ActiveTable.callee,PV_THR2_F1.node53] at resolved
  simp [stage,site,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_ReachedNative14.run,PV_LIB_SPEC_ReachedNative14.step,
    PV_LIB_SPEC_ReachedNative14.control,PV_LIB_SPEC_ReachedNative14.transition,
    PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,PV_STX2_SliceMachine.step,
    PV_THR2_F1.node166,block,tailHead,PV_THR2_F1.node54,PV_THR2_F1.node49,PV_THR2_F1.node50,PV_THR2_F1.node51,
    PV_THR2_F1.node52,PV_THR2_F1.node53,native,adopt,PV_STX2_Native.step,
    PV_STX2_Native.arguments,operands,operand,PV_STX2_Store.read,locate,writeAddress,write,
    cell,truth,resolved,branchStore,PV_THR2_RunActiveEntry.issued,PV_THR2_ActiveTable.callee]

#print axioms lookup
#print axioms run
end PV_LIB_A_F5Entry16
