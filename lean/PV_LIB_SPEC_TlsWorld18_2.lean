import PV_LIB_SPEC_TlsWorld18_1
import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section

namespace PV_LIB_SPEC_World18_TlsAt58

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_TlsNative15 (cut reference)

open PV_LIB_SPEC_TlsAt58
def at58 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := PV_LIB_SPEC_Tls277Request15.after PV_LIB_SPEC_TlsDelivery15.store55 5
  PV_LIB_SPEC_TlsNative15.reference PV_LIB_SPEC_TlsOriginal15.parents e.world []
  (PV_LIB_SPEC_World18_TlsAt54.at54 e).issued [PV_LIB_SPEC_TlsAt55.origin]

#print axioms at58

theorem original58 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 58
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_TlsAt58.at58 e) := by
  rw [show 58=55+3 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_World18_TlsAt55.original55 e)]
  apply PV_LIB_SPEC_Tls277Request15.request
  simp [PV_LIB_SPEC_TlsDelivery15.store55,PV_STX2_Store.write]

#print axioms original58

theorem first_native (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    (PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 58
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))).consumed = [PV_LIB_SPEC_TlsAt55.origin] := by
  rw [(PV_LIB_SPEC_World18_TlsAt58.original58 e)]; rfl

#print axioms first_native

theorem world58 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    (PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 58
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))).state.current.world = e.world := by
  rw [(PV_LIB_SPEC_World18_TlsAt58.original58 e)]; rfl

#print axioms world58

end PV_LIB_SPEC_World18_TlsAt58

namespace PV_LIB_SPEC_World18_Tls59Data15

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_TlsNative15 (reference)

open PV_LIB_SPEC_Tls59Data15
def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (PV_LIB_SPEC_F1Arithmetic14.stage PV_LIB_SPEC_Tls59Data15.store59 5 PV_LIB_SPEC_TlsOriginal15.parents
    (PV_THR2_F170.live.body.drop 17) e.world [] [] []).state

#print axioms after

def at59 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := ⟨(PV_LIB_SPEC_World18_Tls59Data15.after e),(PV_LIB_SPEC_World18_TlsAt58.at58 e).issued,
  [PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin]⟩

#print axioms at59

theorem nonnative (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ControlRuntime.ordinary (PV_LIB_SPEC_World18_TlsAt58.at58 e).state = some (PV_LIB_SPEC_Tls59Data15.config,PV_LIB_SPEC_Tls59Data15.wait) := by
  have lookup : PV_LIB_SPEC_Full.programs PV_LIB_SPEC_Tls59Data15.token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_SPEC_World18_TlsAt58.at58,
    PV_LIB_SPEC_Tls277Request15.after,PV_LIB_SPEC_Tls59Data15.config,PV_LIB_SPEC_Tls59Data15.wait,PV_LIB_SPEC_Tls59Data15.request,
    PV_THR2_RunTlsNext.pending,PV_THR2_RunTlsNext.callee,
    PV_THR2_Catch316Segment.select,lookup,PV_LIB_SPEC_Tls59Data15.token,PV_LIB_SPEC_Tls277Native15.token,
    show PV_LIB_SPEC_TlsDelivery15.store55.nextActivation=7 from rfl]
  exact lookup

#print axioms nonnative

end PV_LIB_SPEC_World18_Tls59Data15

namespace PV_LIB_SPEC_World18_Tls277Delivery15

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_Tls59Data15
open PV_LIB_SPEC_TlsNative15 (cut reference)

open PV_LIB_SPEC_Tls277Delivery15
theorem transition (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      PV_LIB_SPEC_Tls59Data15.config (PV_LIB_SPEC_World18_TlsAt58.at58 e).state = (PV_LIB_SPEC_World18_Tls59Data15.after e) := by
  have lookup : PV_LIB_SPEC_Full.programs PV_LIB_SPEC_Tls59Data15.token = none := rfl
  have table : PV_LIB_StoreActionTable.v2 PV_LIB_SPEC_Tls59Data15.token = none := rfl
  change PV_LIB_SPEC_Full.programs PV_THR2_RunTlsNext.callee = none at lookup
  change PV_LIB_StoreActionTable.v2 PV_THR2_RunTlsNext.callee = none at table
  change PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
    (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls59Data15.config
    ⟨⟨.running PV_LIB_SPEC_Tls59Data15.config,e.world,[]⟩,[]⟩ = _
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running PV_LIB_SPEC_Tls59Data15.config,e.world,[]⟩,[]⟩ := by
    simp [lookup,table,PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node17,
      PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,PV_LIB_SPEC_Tls59Data15.config,PV_THR2_RunTlsNext.pending,PV_LIB_SPEC_Tls59Data15.wait,
      PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
      PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
      PV_THR2_OwnUniformNeutral.instruction]
  rw [PV_LIB_SPEC_NativeDelivery16.full (PV_LIB_SPEC_TlsNative15.cut stack)
    (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls59Data15.config e.world [] []
    PV_LIB_SPEC_Tls59Data15.wait PV_LIB_SPEC_Tls59Data15.token 7 6 [PV_LIB_SPEC_TlsNative15.reference]
    quiet (by rfl) rfl rfl (by rfl) rfl lookup]
  have reply := PV_LIB_SPEC_Tls277Bound15.answer (PV_LIB_SPEC_TlsNative15.cut stack) resources PV_LIB_SPEC_Tls59Data15.config e.world 7 PV_LIB_SPEC_Entry13.slot.source PV_LIB_SPEC_Tls59Data15.wait PV_LIB_SPEC_Tls59Data15.waiting rfl
  change PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
    (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls59Data15.config
    PV_LIB_SPEC_Tls59Data15.request e.world =
      some ⟨.returned (.ok PV_LIB_SPEC_Tls59Data15.result),e.world,[]⟩ at reply
  simp only [PV_LIB_SPEC_ReachedNative14.handler,
    show PV_LIB_SPEC_Tls59Data15.wait.request = PV_LIB_SPEC_Tls59Data15.request from rfl,reply,Option.getD_some]
  rfl

#print axioms transition

end PV_LIB_SPEC_World18_Tls277Delivery15

namespace PV_LIB_SPEC_World18_TlsAt59

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_Tls59Data15 (token config request wait origin at59)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_TlsAt58 (at58)

open PV_LIB_SPEC_TlsAt59
theorem context (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.context (PV_LIB_SPEC_World18_TlsAt58.at58 e) PV_LIB_SPEC_Tls59Data15.config PV_LIB_SPEC_Tls59Data15.wait = some PV_LIB_SPEC_Tls59Data15.origin := by
  classical
  simp [PV_LIB_SPEC_ResourceHistory.context,PV_LIB_SPEC_World18_TlsAt58.at58,PV_LIB_SPEC_Tls277Request15.after,
    PV_LIB_SPEC_Tls59Data15.wait,PV_LIB_SPEC_Tls59Data15.request,
    PV_LIB_SPEC_Tls59Data15.config,PV_LIB_SPEC_Tls59Data15.origin,
    PV_THR2_RunTlsNext.pending,PV_LIB_SPEC_ResourceHistory.arguments,
    PV_LIB_SPEC_Tls59Data15.token,PV_LIB_SPEC_Tls277Native15.token,
    show PV_LIB_SPEC_TlsDelivery15.store55.nextActivation=7 from rfl,
    PV_LIB_SPEC_TlsAt55.origin,PV_LIB_SPEC_Tls277Request15.site,PV_LIB_SPEC_TlsRequest15.site,PV_THR2_F170.node13,PV_THR2_F170.node16]

#print axioms context

theorem consume (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters (PV_LIB_SPEC_World18_TlsAt58.at58 e) = (PV_LIB_SPEC_World18_Tls59Data15.at59 e) := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [(PV_LIB_SPEC_World18_Tls59Data15.nonnative e)]
  rw [(PV_LIB_SPEC_World18_TlsAt59.context e)]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment PV_LIB_SPEC_Tls59Data15.origin
  have result := PV_LIB_SPEC_Tls277Bound15.answer (PV_LIB_SPEC_TlsNative15.cut stack) resources PV_LIB_SPEC_Tls59Data15.config
    e.world 7 PV_LIB_SPEC_Entry13.slot.source PV_LIB_SPEC_Tls59Data15.wait PV_LIB_SPEC_Tls59Data15.waiting rfl
  change (match PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls59Data15.config PV_LIB_SPEC_Tls59Data15.request e.world with
    | none => _ | some _ => _) = (PV_LIB_SPEC_World18_Tls59Data15.at59 e)
  change PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_Tls59Data15.config PV_LIB_SPEC_Tls59Data15.request e.world = some ⟨.returned (.ok PV_LIB_SPEC_Tls59Data15.result),e.world,[]⟩ at result
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls59Data15.config (PV_LIB_SPEC_World18_TlsAt58.at58 e).state,
      PV_LIB_SPEC_ControlRuntime.recordIssue (PV_LIB_SPEC_World18_TlsAt58.at58 e).state
        (PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls59Data15.config (PV_LIB_SPEC_World18_TlsAt58.at58 e).state) (PV_LIB_SPEC_World18_TlsAt58.at58 e).issued,
      [PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin]⟩ : PV_LIB_SPEC_ResourceHistory.Execution) = (PV_LIB_SPEC_World18_Tls59Data15.at59 e)
  rw [(PV_LIB_SPEC_World18_Tls277Delivery15.transition e)]
  simp [PV_LIB_SPEC_World18_Tls59Data15.at59,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_World18_TlsAt58.at58,PV_LIB_SPEC_Tls277Request15.after,PV_THR2_RunTlsNext.pending]

#print axioms consume

theorem original59 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 59
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_Tls59Data15.at59 e) := by
  rw [show 59=58+1 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_World18_TlsAt58.original58 e)]
  exact (PV_LIB_SPEC_World18_TlsAt59.consume e) stack

#print axioms original59

end PV_LIB_SPEC_World18_TlsAt59
