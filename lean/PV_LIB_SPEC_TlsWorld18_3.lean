import PV_LIB_SPEC_TlsWorld18_2
import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section

namespace PV_LIB_SPEC_World18_TlsAt63

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context initial)
open PV_LIB_SPEC_Tls59Data15 (at59 store59 result)
open PV_LIB_SPEC_TlsNative15 (cut)

open PV_LIB_SPEC_TlsAt63
def at63 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := PV_LIB_SPEC_SourceTransport15.advance
  PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_TlsAt63.handler 4 (PV_LIB_SPEC_World18_Tls59Data15.at59 e)

#print axioms at63

theorem original63 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 63
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_TlsAt63.at63 e) := by
  rw [show 63=59+4 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_World18_TlsAt59.original59 e)]
  exact PV_LIB_SPEC_SourceTransport15.run _ _ PV_LIB_SPEC_TlsAt63.handler _ _
    (PV_LIB_SPEC_Tls278Trace15.trace _ _ _ PV_LIB_SPEC_Tls59Data15.store59 5 PV_LIB_SPEC_TlsOriginal15.parents
      e.world [] (PV_LIB_SPEC_World18_TlsAt58.at58 e).issued
      [PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin])

#print axioms original63

theorem state63 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt63.at63 e).state =
    ⟨⟨.running (PV_LIB_SPEC_Tls278Lift15.config PV_LIB_SPEC_Tls59Data15.store59 5 PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Tls59Data15.result),
      e.world,[]⟩,[]⟩ := by
  unfold PV_LIB_SPEC_World18_TlsAt63.at63
  rw [PV_LIB_SPEC_SourceProjection15.state]
  exact PV_LIB_SPEC_Tls278Lift15.source _ PV_LIB_SPEC_TlsAt63.handler PV_LIB_SPEC_Tls59Data15.store59 5
    PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Tls59Data15.result e.world [] PV_LIB_SPEC_TlsAt63.result_bound

#print axioms state63

theorem issued63 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt63.at63 e).issued =
    (⟨PV_LIB_SPEC_Tls278History15.site,5,
      .child PV_THR2_RunTlsErrorCompleted.callee 8 [PV_LIB_SPEC_Tls59Data15.result,PV_LIB_SPEC_Tls278Lift15.error]⟩ : PV_LIB_SPEC_ResourceHistory.Issued) :: (PV_LIB_SPEC_World18_Tls59Data15.at59 e).issued :=
  PV_LIB_SPEC_Tls278History15.issued _ PV_LIB_SPEC_TlsAt63.handler PV_LIB_SPEC_Tls59Data15.store59 5 PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Tls59Data15.result
    e.world [] (PV_LIB_SPEC_World18_Tls59Data15.at59 e).issued (PV_LIB_SPEC_World18_Tls59Data15.at59 e).consumed PV_LIB_SPEC_TlsAt63.result_bound

#print axioms issued63

theorem consumed63 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt63.at63 e).consumed =
    [PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin] :=
  PV_LIB_SPEC_Tls278History15.consumed _ PV_LIB_SPEC_TlsAt63.handler 4 (PV_LIB_SPEC_World18_Tls59Data15.at59 e)

#print axioms consumed63

theorem world63 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt63.at63 e).state.current.world = e.world := by
  rw [(PV_LIB_SPEC_World18_TlsAt63.state63 e)]

#print axioms world63

theorem entry (e : PV_LIB_SPEC_EntryWorld18.Entry) : OwnInit.Pre PV_LIB_SPEC_ReachedEnvironment14.parameters (PV_LIB_SPEC_EntryWorld18.input e.world) := e.pre

#print axioms entry

end PV_LIB_SPEC_World18_TlsAt63

namespace PV_LIB_SPEC_World18_Tls64Data16

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_TlsNative15 (reference)

open PV_LIB_SPEC_Tls64Data16
def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (PV_LIB_SPEC_F1Arithmetic14.stage PV_LIB_SPEC_Tls64Data16.store64 5 PV_LIB_SPEC_TlsOriginal15.parents
    (PV_THR2_F170.live.body.drop 21) e.world [] [] []).state

#print axioms after

def at64 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := ⟨(PV_LIB_SPEC_World18_Tls64Data16.after e),(PV_LIB_SPEC_World18_TlsAt63.at63 e).issued,
  PV_LIB_SPEC_Tls64Data16.origin :: (PV_LIB_SPEC_World18_TlsAt63.at63 e).consumed⟩

#print axioms at64

theorem nonnative (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ControlRuntime.ordinary (PV_LIB_SPEC_World18_TlsAt63.at63 e).state = some (PV_LIB_SPEC_Tls64Data16.config,PV_LIB_SPEC_Tls64Data16.wait) := by
  rw [(PV_LIB_SPEC_World18_TlsAt63.state63 e)]
  have lookup : PV_LIB_SPEC_Full.programs PV_LIB_SPEC_Tls64Data16.token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_SPEC_Tls64Data16.config,PV_LIB_SPEC_Tls64Data16.wait,PV_LIB_SPEC_Tls64Data16.request,
    PV_LIB_SPEC_Tls278Reached15.config,PV_LIB_SPEC_Tls278Reached15.wait,
    PV_LIB_SPEC_Tls278Reached15.request,PV_LIB_SPEC_Tls278Lift15.config,
    PV_THR2_Catch316Segment.select,PV_LIB_SPEC_Tls64Data16.token,PV_LIB_SPEC_Tls278Values15.token,
    show PV_LIB_SPEC_Tls59Data15.store59.nextActivation=8 from rfl]
  exact lookup

#print axioms nonnative

end PV_LIB_SPEC_World18_Tls64Data16

namespace PV_LIB_SPEC_World18_Tls278Delivery16

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Tls64Data16
open PV_LIB_SPEC_TlsNative15 (cut)

open PV_LIB_SPEC_Tls278Delivery16
theorem transition (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      PV_LIB_SPEC_Tls64Data16.config (PV_LIB_SPEC_World18_TlsAt63.at63 e).state = (PV_LIB_SPEC_World18_Tls64Data16.after e) := by
  rw [(PV_LIB_SPEC_World18_TlsAt63.state63 e)]
  change PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_Tls64Data16.config ⟨⟨.running PV_LIB_SPEC_Tls64Data16.config,e.world,[]⟩,[]⟩ = (PV_LIB_SPEC_World18_Tls64Data16.after e)
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet
      ⟨⟨.running PV_LIB_SPEC_Tls64Data16.config,e.world,[]⟩,[]⟩ := by
    have lookup : PV_LIB_SPEC_Full.programs PV_THR2_RunTlsErrorCompleted.callee = none := rfl
    have table : PV_LIB_StoreActionTable.v2 PV_THR2_RunTlsErrorCompleted.callee = none := rfl
    simp [lookup,table,PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node21,
      PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,PV_LIB_SPEC_Tls64Data16.config,PV_LIB_SPEC_Tls278Reached15.config,
      PV_LIB_SPEC_Tls278Lift15.config,PV_THR2_OwnInitAction.selected,
      PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
      PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction]
  rw [PV_LIB_SPEC_NativeDelivery16.full (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_Tls64Data16.config e.world [] [] PV_LIB_SPEC_Tls64Data16.wait PV_LIB_SPEC_Tls64Data16.token 8 5
    [PV_LIB_SPEC_Tls59Data15.result,PV_LIB_SPEC_Tls278Lift15.error]
    quiet (by rfl) rfl rfl PV_LIB_SPEC_Tls64Data16.waiting rfl (by rfl)]
  have reply := PV_LIB_SPEC_Tls278Bound15.answer (PV_LIB_SPEC_TlsNative15.cut stack) resources PV_LIB_SPEC_Tls64Data16.config
    e.world 8 PV_LIB_SPEC_Entry13.slot.source PV_LIB_SPEC_Tls64Data16.wait PV_LIB_SPEC_Tls64Data16.waiting rfl
  change PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_Tls64Data16.config PV_LIB_SPEC_Tls64Data16.request e.world = some ⟨.returned (.ok PV_LIB_SPEC_Tls64Data16.result),e.world,[]⟩ at reply
  simp only [PV_LIB_SPEC_ReachedNative14.handler,show PV_LIB_SPEC_Tls64Data16.wait.request=PV_LIB_SPEC_Tls64Data16.request from rfl,reply,Option.getD_some]
  rfl

#print axioms transition

end PV_LIB_SPEC_World18_Tls278Delivery16

namespace PV_LIB_SPEC_World18_TlsAt64

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_Tls64Data16 (token config request wait origin at64)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_TlsAt63 (at63)

open PV_LIB_SPEC_TlsAt64
theorem context (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.context (PV_LIB_SPEC_World18_TlsAt63.at63 e) PV_LIB_SPEC_Tls64Data16.config PV_LIB_SPEC_Tls64Data16.wait = some PV_LIB_SPEC_Tls64Data16.origin := by
  rw [PV_LIB_SPEC_ResourceHistory.context,(PV_LIB_SPEC_World18_TlsAt63.issued63 e),
    (PV_LIB_SPEC_World18_TlsAt63.consumed63 e)]
  simp [PV_LIB_SPEC_Tls278Values15.token,PV_LIB_SPEC_Tls64Data16.config,PV_LIB_SPEC_Tls278Reached15.config,
    PV_LIB_SPEC_Tls278Lift15.config,PV_LIB_SPEC_Tls64Data16.wait,
    PV_LIB_SPEC_Tls278Reached15.wait,PV_LIB_SPEC_Tls278Reached15.request,
    PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls64Data16.request,
    PV_LIB_SPEC_ResourceHistory.arguments,PV_LIB_SPEC_TlsAt55.origin,
    PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_Tls277Request15.site,
    PV_LIB_SPEC_Tls278History15.site,PV_LIB_SPEC_TlsRequest15.site,
    PV_THR2_F170.node13,PV_THR2_F170.node16,PV_THR2_F170.node20,
    show PV_LIB_SPEC_Tls59Data15.store59.nextActivation=8 from rfl]

#print axioms context

theorem consume (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters (PV_LIB_SPEC_World18_TlsAt63.at63 e) = (PV_LIB_SPEC_World18_Tls64Data16.at64 e) := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [(PV_LIB_SPEC_World18_Tls64Data16.nonnative e)]
  rw [(PV_LIB_SPEC_World18_TlsAt64.context e)]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment PV_LIB_SPEC_Tls64Data16.origin
  have result := PV_LIB_SPEC_Tls278Bound15.answer (PV_LIB_SPEC_TlsNative15.cut stack) resources PV_LIB_SPEC_Tls64Data16.config
    e.world 8 PV_LIB_SPEC_Entry13.slot.source PV_LIB_SPEC_Tls64Data16.wait PV_LIB_SPEC_Tls64Data16.waiting rfl
  change (match PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls64Data16.config PV_LIB_SPEC_Tls64Data16.request e.world with
    | none => _ | some _ => _) = (PV_LIB_SPEC_World18_Tls64Data16.at64 e)
  change PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_Tls64Data16.config PV_LIB_SPEC_Tls64Data16.request e.world = some ⟨.returned (.ok PV_LIB_SPEC_Tls64Data16.result),e.world,[]⟩ at result
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls64Data16.config (PV_LIB_SPEC_World18_TlsAt63.at63 e).state,
      PV_LIB_SPEC_ControlRuntime.recordIssue (PV_LIB_SPEC_World18_TlsAt63.at63 e).state
        (PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls64Data16.config (PV_LIB_SPEC_World18_TlsAt63.at63 e).state) (PV_LIB_SPEC_World18_TlsAt63.at63 e).issued,
      PV_LIB_SPEC_Tls64Data16.origin :: (PV_LIB_SPEC_World18_TlsAt63.at63 e).consumed⟩ : PV_LIB_SPEC_ResourceHistory.Execution) = (PV_LIB_SPEC_World18_Tls64Data16.at64 e)
  rw [(PV_LIB_SPEC_World18_Tls278Delivery16.transition e)]
  simp only [PV_LIB_SPEC_World18_Tls64Data16.at64]
  rw [(PV_LIB_SPEC_World18_TlsAt63.state63 e)]
  rfl

#print axioms consume

theorem original64 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 64
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_Tls64Data16.at64 e) := by
  rw [show 64=63+1 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_World18_TlsAt63.original63 e)]
  exact (PV_LIB_SPEC_World18_TlsAt64.consume e) stack

#print axioms original64

end PV_LIB_SPEC_World18_TlsAt64
