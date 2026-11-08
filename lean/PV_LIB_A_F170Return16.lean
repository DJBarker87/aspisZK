import PV_LIB_A_Return16
import PV_LIB_A_F170History16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F170Return16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem execution_ext (x y : Execution) (state : x.state=y.state)
    (issued : x.issued=y.issued) (consumed : x.consumed=y.consumed) : x=y := by
  cases x; cases y; cases state; cases issued; cases consumed; rfl

def store : Store Data := PV_LIB_A_F170Result16.stored PV_LIB_SPEC_Tls85Data16.store85 5 (.boolean false)
def value : Data := PV_THR2_KeyValues.pack PV_LIB_A_F170Result16.kind [.boolean false]
def saved : Frame := PV_THR2_F17Call.parent PV_LIB_SPEC_TlsOriginal14.withStore 4 ⟨3,2,[]⟩ PV_THR2_F2Call.descriptors.2
def wait : PV_STX2_Native.Waiting Data :=
  ⟨.child PV_THR2_F17Call.callee 5 [PV_STX2_TypedReferences.reference ⟨3,2,[]⟩ .null,PV_THR2_F2Call.descriptors.2],.child 5 (.local 3),[]⟩
def site : Site := match PV_THR2_F170.node65 with | .leaf (.ret site _) => site | _ => ⟨0,0,.null⟩
def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (PV_LIB_A_Return16.delivered store 5 3 saved PV_LIB_SPEC_TlsOriginal14.withParents value e.world [] [] []).state

theorem cell : store.cells ⟨5,0,[]⟩ = some value := by
  simp [store,value,PV_LIB_A_F170Result16.stored,write]

theorem original96 (e : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) :
    (PV_LIB_SPEC_LaneAJoins18.history e activation 96).state = after e := by
  let cut := PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e activation)
  let H : Handler := fun _ w => ⟨.pending,w,[]⟩
  let q := PV_LIB_SPEC_LaneAJoins18.history e activation 94
  have shape : PV_THR2_F170.live.body.drop 49 = [.leaf (.ret site (.local 0))] := rfl
  have hq : q = stage store 5 (saved::PV_LIB_SPEC_TlsOriginal14.withParents)
      [.leaf (.ret site (.local 0))] e.world [] q.issued q.consumed := by
    apply execution_ext
    · have hs := PV_LIB_A_F170History16.original94 e activation
      change q.state = _ at hs
      dsimp only [PV_LIB_A_F170History16.after,store,saved,PV_LIB_SPEC_TlsOriginal15.parents,stage] at hs ⊢
      rw [shape] at hs
      exact hs
    · simp only [stage]
    · simp only [stage]
  have returned := PV_LIB_A_Return16.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters H
    store 5 3 saved PV_LIB_SPEC_TlsOriginal14.withParents site wait value e.world []
    q.issued q.consumed cell (show saved.waiting = some wait from rfl) rfl
  change (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 96
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))).state = _
  rw [show 96=94+2 from rfl,PV_LIB_SPEC_Original14.run_add]
  change (PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 2 q).state = _
  rw [hq]
  simpa only [after,PV_LIB_A_Return16.delivered] using congrArg Execution.state returned

#print axioms execution_ext
#print axioms cell
#print axioms original96
end PV_LIB_A_F170Return16
