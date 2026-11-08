import PV_LIB_SPEC_TlsWorld18_3
import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section

namespace PV_LIB_SPEC_World18_TlsAt67

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context initial)
open PV_LIB_SPEC_Tls64Data16 (at64 store64 result)
open PV_LIB_SPEC_TlsNative15 (cut)

open PV_LIB_SPEC_TlsAt67
def at67 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := PV_LIB_SPEC_SourceTransport15.advance
  PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_TlsAt67.handler 3 (PV_LIB_SPEC_World18_Tls64Data16.at64 e)

#print axioms at67

theorem original67 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 67
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_TlsAt67.at67 e) := by
  rw [show 67=64+3 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_World18_TlsAt64.original64 e)]
  exact PV_LIB_SPEC_SourceTransport15.run _ _ PV_LIB_SPEC_TlsAt67.handler _ _
    (PV_LIB_SPEC_Tls279Request16.trace _ _ _ PV_LIB_SPEC_Tls64Data16.store64 5 PV_LIB_SPEC_TlsOriginal15.parents
      e.world [] (PV_LIB_SPEC_World18_Tls64Data16.at64 e).issued (PV_LIB_SPEC_World18_Tls64Data16.at64 e).consumed)

#print axioms original67

theorem state67 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt67.at67 e).state =
    ⟨⟨.running (PV_LIB_SPEC_Tls279Request16.config PV_LIB_SPEC_Tls64Data16.store64 5 PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Tls64Data16.result),
      e.world,[]⟩,[]⟩ := by
  unfold PV_LIB_SPEC_World18_TlsAt67.at67
  rw [PV_LIB_SPEC_SourceProjection15.state]
  exact PV_LIB_SPEC_Tls279Request16.source _ PV_LIB_SPEC_TlsAt67.handler PV_LIB_SPEC_Tls64Data16.store64 5
    PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Tls64Data16.result e.world [] PV_LIB_SPEC_TlsAt67.result_bound

#print axioms state67

theorem issued67 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt67.at67 e).issued =
    (⟨PV_LIB_SPEC_Tls279History16.site,5,
      .child PV_THR2_RunTlsBranchRequest.callee 9 [PV_LIB_SPEC_Tls64Data16.result]⟩ : PV_LIB_SPEC_ResourceHistory.Issued) :: (PV_LIB_SPEC_World18_Tls64Data16.at64 e).issued :=
  PV_LIB_SPEC_Tls279History16.issued _ PV_LIB_SPEC_TlsAt67.handler PV_LIB_SPEC_Tls64Data16.store64 5 PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Tls64Data16.result
    e.world [] (PV_LIB_SPEC_World18_Tls64Data16.at64 e).issued (PV_LIB_SPEC_World18_Tls64Data16.at64 e).consumed PV_LIB_SPEC_TlsAt67.result_bound

#print axioms issued67

theorem consumed67 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt67.at67 e).consumed =
    [PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin] :=
  PV_LIB_SPEC_Tls279History16.consumed _ PV_LIB_SPEC_TlsAt67.handler 3 (PV_LIB_SPEC_World18_Tls64Data16.at64 e)

#print axioms consumed67

theorem world67 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt67.at67 e).state.current.world = e.world := by
  rw [(PV_LIB_SPEC_World18_TlsAt67.state67 e)]

#print axioms world67

theorem entry (e : PV_LIB_SPEC_EntryWorld18.Entry) : OwnInit.Pre PV_LIB_SPEC_ReachedEnvironment14.parameters (PV_LIB_SPEC_EntryWorld18.input e.world) := e.pre

#print axioms entry

end PV_LIB_SPEC_World18_TlsAt67

namespace PV_LIB_SPEC_World18_Tls68Data16

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_TlsNative15 (reference)

open PV_LIB_SPEC_Tls68Data16
def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (PV_LIB_SPEC_F1Arithmetic14.stage PV_LIB_SPEC_Tls68Data16.store68 5 PV_LIB_SPEC_TlsOriginal15.parents
    (PV_THR2_F170.live.body.drop 24) e.world [] [] []).state

#print axioms after

def at68 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := ⟨(PV_LIB_SPEC_World18_Tls68Data16.after e),(PV_LIB_SPEC_World18_TlsAt67.at67 e).issued,
  PV_LIB_SPEC_Tls68Data16.origin :: (PV_LIB_SPEC_World18_TlsAt67.at67 e).consumed⟩

#print axioms at68

theorem nonnative (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ControlRuntime.ordinary (PV_LIB_SPEC_World18_TlsAt67.at67 e).state = some (PV_LIB_SPEC_Tls68Data16.config,PV_LIB_SPEC_Tls68Data16.wait) := by
  rw [(PV_LIB_SPEC_World18_TlsAt67.state67 e)]
  have lookup : PV_LIB_SPEC_Full.programs PV_LIB_SPEC_Tls68Data16.token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_SPEC_Tls68Data16.config,PV_LIB_SPEC_Tls68Data16.wait,PV_LIB_SPEC_Tls68Data16.request,
    PV_LIB_SPEC_Tls279Request16.config,PV_THR2_RunTlsBranchRequest.pending,
    PV_THR2_Catch316Segment.select,PV_LIB_SPEC_Tls68Data16.token,PV_LIB_SPEC_Tls279Values16.token,
    show PV_LIB_SPEC_Tls64Data16.store64.nextActivation=9 from rfl]

  exact lookup

#print axioms nonnative

end PV_LIB_SPEC_World18_Tls68Data16

namespace PV_LIB_SPEC_World18_Tls279Delivery16

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Tls68Data16
open PV_LIB_SPEC_TlsNative15 (cut)

open PV_LIB_SPEC_Tls279Delivery16
theorem transition (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      PV_LIB_SPEC_Tls68Data16.config (PV_LIB_SPEC_World18_TlsAt67.at67 e).state = (PV_LIB_SPEC_World18_Tls68Data16.after e) := by
  rw [(PV_LIB_SPEC_World18_TlsAt67.state67 e)]
  change PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_Tls68Data16.config ⟨⟨.running PV_LIB_SPEC_Tls68Data16.config,e.world,[]⟩,[]⟩ = (PV_LIB_SPEC_World18_Tls68Data16.after e)
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet
      ⟨⟨.running PV_LIB_SPEC_Tls68Data16.config,e.world,[]⟩,[]⟩ := by
    have lookup : PV_LIB_SPEC_Full.programs PV_THR2_RunTlsBranchRequest.callee = none := rfl
    have table : PV_LIB_StoreActionTable.v2 PV_THR2_RunTlsBranchRequest.callee = none := rfl
    simp [lookup,table,PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node24,
      PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,PV_LIB_SPEC_Tls68Data16.config,PV_LIB_SPEC_Tls279Request16.config,
      PV_THR2_RunTlsBranchRequest.pending,PV_THR2_OwnInitAction.selected,
      PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
      PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction]
  rw [PV_LIB_SPEC_NativeDelivery16.full (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_Tls68Data16.config e.world [] [] PV_LIB_SPEC_Tls68Data16.wait PV_LIB_SPEC_Tls68Data16.token 9 4
    [PV_LIB_SPEC_Tls64Data16.result]
    quiet (by rfl) rfl rfl PV_LIB_SPEC_Tls68Data16.waiting rfl (by rfl)]
  have reply := PV_LIB_SPEC_Tls279Bound16.answer (PV_LIB_SPEC_TlsNative15.cut stack) resources PV_LIB_SPEC_Tls68Data16.config
    e.world 9 PV_LIB_SPEC_Entry13.slot.source PV_LIB_SPEC_Tls68Data16.wait PV_LIB_SPEC_Tls68Data16.waiting rfl
  change PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_Tls68Data16.config PV_LIB_SPEC_Tls68Data16.request e.world = some ⟨.returned (.ok PV_LIB_SPEC_Tls68Data16.result),e.world,[]⟩ at reply
  simp only [PV_LIB_SPEC_ReachedNative14.handler,show PV_LIB_SPEC_Tls68Data16.wait.request=PV_LIB_SPEC_Tls68Data16.request from rfl,reply,Option.getD_some]
  rfl

#print axioms transition

end PV_LIB_SPEC_World18_Tls279Delivery16

namespace PV_LIB_SPEC_World18_TlsAt68

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_Tls68Data16 (token config request wait origin at68)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_TlsAt67 (at67)

open PV_LIB_SPEC_TlsAt68
theorem context (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.context (PV_LIB_SPEC_World18_TlsAt67.at67 e) PV_LIB_SPEC_Tls68Data16.config PV_LIB_SPEC_Tls68Data16.wait = some PV_LIB_SPEC_Tls68Data16.origin := by
  rw [PV_LIB_SPEC_ResourceHistory.context,(PV_LIB_SPEC_World18_TlsAt67.issued67 e),
    (PV_LIB_SPEC_World18_TlsAt67.consumed67 e)]
  simp [PV_LIB_SPEC_Tls68Data16.token,PV_LIB_SPEC_Tls279Values16.token,PV_LIB_SPEC_Tls68Data16.config,
    PV_LIB_SPEC_Tls279Request16.config,PV_THR2_RunTlsBranchRequest.pending,
    PV_LIB_SPEC_Tls68Data16.wait,PV_LIB_SPEC_Tls68Data16.request,
    PV_LIB_SPEC_Tls68Data16.origin,PV_LIB_SPEC_ResourceHistory.arguments,
    PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls59Data15.origin,
    PV_LIB_SPEC_TlsAt55.origin,PV_LIB_SPEC_Tls279History16.site,
    PV_LIB_SPEC_Tls278History15.site,PV_LIB_SPEC_Tls277Request15.site,
    PV_LIB_SPEC_TlsRequest15.site,PV_THR2_F170.node13,PV_THR2_F170.node16,
    PV_THR2_F170.node20,PV_THR2_F170.node23,
    show PV_LIB_SPEC_Tls64Data16.store64.nextActivation=9 from rfl]

#print axioms context

theorem consume (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters (PV_LIB_SPEC_World18_TlsAt67.at67 e) = (PV_LIB_SPEC_World18_Tls68Data16.at68 e) := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [(PV_LIB_SPEC_World18_Tls68Data16.nonnative e)]
  rw [(PV_LIB_SPEC_World18_TlsAt68.context e)]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment PV_LIB_SPEC_Tls68Data16.origin
  have result := PV_LIB_SPEC_Tls279Bound16.answer (PV_LIB_SPEC_TlsNative15.cut stack) resources PV_LIB_SPEC_Tls68Data16.config
    e.world 9 PV_LIB_SPEC_Entry13.slot.source PV_LIB_SPEC_Tls68Data16.wait PV_LIB_SPEC_Tls68Data16.waiting rfl
  change (match PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls68Data16.config PV_LIB_SPEC_Tls68Data16.request e.world with
    | none => _ | some _ => _) = (PV_LIB_SPEC_World18_Tls68Data16.at68 e)
  change PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_Tls68Data16.config PV_LIB_SPEC_Tls68Data16.request e.world = some ⟨.returned (.ok PV_LIB_SPEC_Tls68Data16.result),e.world,[]⟩ at result
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls68Data16.config (PV_LIB_SPEC_World18_TlsAt67.at67 e).state,
      PV_LIB_SPEC_ControlRuntime.recordIssue (PV_LIB_SPEC_World18_TlsAt67.at67 e).state
        (PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_Tls68Data16.config (PV_LIB_SPEC_World18_TlsAt67.at67 e).state) (PV_LIB_SPEC_World18_TlsAt67.at67 e).issued,
      PV_LIB_SPEC_Tls68Data16.origin :: (PV_LIB_SPEC_World18_TlsAt67.at67 e).consumed⟩ : PV_LIB_SPEC_ResourceHistory.Execution) = (PV_LIB_SPEC_World18_Tls68Data16.at68 e)
  rw [(PV_LIB_SPEC_World18_Tls279Delivery16.transition e)]
  simp only [PV_LIB_SPEC_World18_Tls68Data16.at68]
  rw [(PV_LIB_SPEC_World18_TlsAt67.state67 e)]
  rfl

#print axioms consume

theorem original68 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 68
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_Tls68Data16.at68 e) := by
  rw [show 68=67+1 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_World18_TlsAt67.original67 e)]
  exact (PV_LIB_SPEC_World18_TlsAt68.consume e) stack

#print axioms original68

end PV_LIB_SPEC_World18_TlsAt68
