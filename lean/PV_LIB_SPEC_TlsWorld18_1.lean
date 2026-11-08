import PV_LIB_SPEC_Prefix54World18
import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section

namespace PV_LIB_SPEC_World18_TlsAt54

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_TlsOriginal15

open PV_LIB_SPEC_TlsAt54
def at54 (e : PV_LIB_SPEC_EntryWorld18.Entry) : Execution := PV_LIB_SPEC_TlsRequest15.after PV_LIB_SPEC_TlsAt54.store53 5 PV_LIB_SPEC_TlsAt54.token PV_LIB_SPEC_TlsAt54.initValue PV_LIB_SPEC_TlsOriginal15.parents
  e.world [] PV_LIB_SPEC_TlsOriginal15.issued []

#print axioms at54

end PV_LIB_SPEC_World18_TlsAt54

namespace PV_LIB_SPEC_World18_TlsNative15

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_TlsAt54

open PV_LIB_SPEC_TlsNative15
theorem physical (e : PV_LIB_SPEC_EntryWorld18.Entry) : e.world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 := e.active

#print axioms physical

theorem active (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
    PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_TlsAt54.config e.world = some false := by
  unfold PV_LIB_SPEC_TlsBindings13.read
  have address : readAddress (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier
      PV_LIB_SPEC_TlsAt54.config.store PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
    unfold readAddress
    simp only [PV_LIB_SPEC_Entry13.slot,List.foldl_nil]
    exact PV_LIB_SPEC_TlsNative15.source
  rw [address]
  change (if e.world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 then some false else none) = _
  rw [(PV_LIB_SPEC_World18_TlsNative15.physical e)]; rfl

#print axioms active

theorem value (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_TlsBindings13.value PV_LIB_SPEC_Entry13.slot
    PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_TlsAt54.config e.world PV_LIB_SPEC_TlsNative15.request = some PV_LIB_SPEC_TlsNative15.reference := by
  unfold PV_LIB_SPEC_TlsBindings13.value
  simp only [PV_LIB_SPEC_TlsNative15.request,PV_LIB_SPEC_TlsAt54.token,PV_THR2_FnOnceDispatch.request,ite_true]
  have initializer : (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).control.variant PV_LIB_SPEC_TlsAt54.initValue = some 0 := rfl
  rw [initializer]
  change (do let _ ← PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
               PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_TlsAt54.config e.world
             pure PV_LIB_SPEC_TlsNative15.reference) = _
  rw [(PV_LIB_SPEC_World18_TlsNative15.active e)]; rfl

#print axioms value

end PV_LIB_SPEC_World18_TlsNative15

namespace PV_LIB_SPEC_World18_TlsBound15

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_EVHB_OwnerHeap
open PV_LIB_SPEC_TlsAt54 (token initValue config)
open PV_LIB_SPEC_TlsNative15 (cut request reference)

open PV_LIB_SPEC_TlsBound15
theorem answer (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt54.config PV_LIB_SPEC_TlsNative15.request
      e.world =
    some ⟨.returned (.ok PV_LIB_SPEC_TlsNative15.reference),e.world,[]⟩ := by
  classical
  have n268 := PV_LIB_SPEC_TlsBound15.different PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have n164 := PV_LIB_SPEC_TlsBound15.different PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have n165 := PV_LIB_SPEC_TlsBound15.different PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have n93 := PV_LIB_SPEC_TlsBound15.different PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  have n295 := PV_LIB_SPEC_TlsBound15.different PV_LIB_SPEC_StackSize14.token 295 rfl (by decide)
  have n453 := PV_LIB_SPEC_TlsBound15.different PV_THR2_Source361HookChildren.fnTrueFull 453 rfl (by decide)
  have n454 := PV_LIB_SPEC_TlsBound15.different PV_THR2_Source361HookChildren.fnFalseFull 454 rfl (by decide)
  have id : PV_THR2_OffPath.functionId PV_LIB_SPEC_TlsAt54.token = some 469 := rfl
  simp only [PV_LIB_SPEC_ReachedNative14.answer,PV_LIB_SPEC_ReachedNative14.core,
    PV_LIB_SPEC_TlsNative15.request,if_neg n268,PV_LIB_SPEC_Assembly14.answer,PV_LIB_SPEC_Assembly14.core,
    if_neg n164,if_neg n165,if_neg n93,PV_LIB_SPEC_PrefixNative14.answer,
    PV_LIB_SPEC_PrefixNative14.core,if_neg n295,if_neg n454,if_neg n453,
    PV_LIB_SPEC_PrefixNative13.answer,PV_LIB_SPEC_PrefixNative13.core,id,
    show ¬(some 469 = (some 269 : Option Nat)) from by decide,ite_false,PV_LIB_SPEC_BoundNative13.answer,PV_LIB_SPEC_BoundNative13.core,
    PV_LIB_SPEC_Native13.answer,PV_LIB_SPEC_Native13.core,
    show PV_LIB_SPEC_TlsBindings13.selected (.child PV_LIB_SPEC_TlsAt54.token 6 [PV_LIB_SPEC_TlsAt54.initValue]) = true from PV_LIB_SPEC_TlsBound15.selected,
    Bool.true_eq,ite_true,PV_LIB_SPEC_TlsNative15.cut]
  have bound : PV_LIB_SPEC_TlsBindings13.reply PV_LIB_SPEC_Entry13.slot
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt54.config e.world PV_LIB_SPEC_TlsNative15.request
      (PV_THR2_OwnUniformResourceHandler.lift (PV_LIB_SPEC_TlsBound15.parameters resources).environment.native PV_LIB_SPEC_TlsNative15.request
        e.world) =
      some ⟨.returned (.ok PV_LIB_SPEC_TlsNative15.reference),e.world,[]⟩ := by
    rw [PV_LIB_SPEC_TlsBound15.trigger]
    unfold PV_LIB_SPEC_TlsBindings13.reply
    have value : PV_LIB_SPEC_TlsBindings13.value PV_LIB_SPEC_Entry13.slot
        (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt54.config e.world PV_LIB_SPEC_TlsNative15.request = some PV_LIB_SPEC_TlsNative15.reference :=
      (PV_LIB_SPEC_World18_TlsNative15.value e)
    rw [value]
    rfl
  simp only [PV_LIB_SPEC_TlsNative15.request] at bound
  rw [bound]
  cases marked : PV_LIB_SPEC_BoundRuntime.allocationToken PV_LIB_SPEC_TlsNative15.request <;>
    simp only [PV_LIB_SPEC_TlsNative15.request] at marked <;>
    simp only [Option.map_some,PV_LIB_SPEC_BoundRuntime.frameReply,marked,
      Bool.false_eq_true,ite_false,ite_true] <;> rfl

#print axioms answer

end PV_LIB_SPEC_World18_TlsBound15

namespace PV_LIB_SPEC_World18_TlsDelivery15

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_F1Arithmetic14 (stage)
open PV_LIB_SPEC_TlsAt54 (token initValue config)
open PV_LIB_SPEC_TlsNative15 (cut request reference)

open PV_LIB_SPEC_TlsDelivery15
def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State :=
  (PV_LIB_SPEC_F1Arithmetic14.stage PV_LIB_SPEC_TlsDelivery15.store55 5 PV_LIB_SPEC_TlsOriginal15.parents (PV_THR2_F170.live.body.drop 14)
    e.world [] [] []).state

#print axioms after

theorem transition (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      PV_LIB_SPEC_TlsAt54.config (PV_LIB_SPEC_World18_TlsAt54.at54 e).state = (PV_LIB_SPEC_World18_TlsDelivery15.after e) := by
  have lookup : PV_LIB_SPEC_Full.programs PV_LIB_SPEC_TlsAt54.token = none := rfl
  have table : PV_LIB_StoreActionTable.v2 PV_LIB_SPEC_TlsAt54.token = none := rfl
  change PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
    (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt54.config
    ⟨⟨.running PV_LIB_SPEC_TlsAt54.config,e.world,[]⟩,[]⟩ = _
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running PV_LIB_SPEC_TlsAt54.config,e.world,[]⟩,[]⟩ := by
    simp [lookup,table,PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node14,
      PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,PV_LIB_SPEC_TlsAt54.config,PV_LIB_SPEC_TlsAt55.wait,
      PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
      PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
      PV_THR2_OwnUniformNeutral.instruction]
  rw [PV_LIB_SPEC_NativeDelivery16.full (PV_LIB_SPEC_TlsNative15.cut stack)
    (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt54.config e.world [] []
    PV_LIB_SPEC_TlsAt55.wait PV_LIB_SPEC_TlsAt54.token 6 7 [PV_LIB_SPEC_TlsAt54.initValue]
    quiet (by rfl) rfl rfl (by rfl) rfl lookup]
  have reply := PV_LIB_SPEC_World18_TlsBound15.answer e stack resources
  simp only [PV_LIB_SPEC_ReachedNative14.handler,
    show PV_LIB_SPEC_TlsAt55.wait.request = PV_LIB_SPEC_TlsNative15.request from rfl,reply,Option.getD_some]
  rfl

#print axioms transition

end PV_LIB_SPEC_World18_TlsDelivery15

namespace PV_LIB_SPEC_World18_TlsAt55

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_TlsAt54 (token initValue config at54)
open PV_LIB_SPEC_TlsNative15 (cut request reference)

open PV_LIB_SPEC_TlsAt55
def at55 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := ⟨(PV_LIB_SPEC_World18_TlsDelivery15.after e),(PV_LIB_SPEC_World18_TlsAt54.at54 e).issued,[PV_LIB_SPEC_TlsAt55.origin]⟩

#print axioms at55

theorem ordinary (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ControlRuntime.ordinary (PV_LIB_SPEC_World18_TlsAt54.at54 e).state = some (PV_LIB_SPEC_TlsAt54.config,PV_LIB_SPEC_TlsAt55.wait) := by
  have lookup : PV_LIB_SPEC_Full.programs PV_LIB_SPEC_TlsAt54.token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_SPEC_World18_TlsAt54.at54,PV_LIB_SPEC_TlsRequest15.after,
    PV_THR2_Catch316Segment.select,lookup,PV_LIB_SPEC_TlsAt55.wait,PV_LIB_SPEC_TlsNative15.request,PV_LIB_SPEC_TlsAt54.config,
    show PV_LIB_SPEC_TlsAt54.store53.nextActivation=6 from rfl]

#print axioms ordinary

theorem context (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.context (PV_LIB_SPEC_World18_TlsAt54.at54 e) PV_LIB_SPEC_TlsAt54.config PV_LIB_SPEC_TlsAt55.wait = some PV_LIB_SPEC_TlsAt55.origin := by
  classical
  simp [PV_LIB_SPEC_ResourceHistory.context,PV_LIB_SPEC_World18_TlsAt54.at54,PV_LIB_SPEC_TlsRequest15.after,
    PV_LIB_SPEC_TlsAt55.wait,PV_LIB_SPEC_TlsNative15.request,PV_LIB_SPEC_TlsAt54.config,PV_LIB_SPEC_TlsAt55.origin,PV_LIB_SPEC_ResourceHistory.arguments,
    show PV_LIB_SPEC_TlsAt54.store53.nextActivation=6 from rfl]

#print axioms context

theorem consume (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters (PV_LIB_SPEC_World18_TlsAt54.at54 e) = (PV_LIB_SPEC_World18_TlsAt55.at55 e) := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [(PV_LIB_SPEC_World18_TlsAt55.ordinary e)]
  rw [(PV_LIB_SPEC_World18_TlsAt55.context e)]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment PV_LIB_SPEC_TlsAt55.origin
  have result := (PV_LIB_SPEC_World18_TlsBound15.answer e) stack resources
  change (match PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt54.config PV_LIB_SPEC_TlsNative15.request e.world with
    | none => _ | some _ => _) = (PV_LIB_SPEC_World18_TlsAt55.at55 e)
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt54.config (PV_LIB_SPEC_World18_TlsAt54.at54 e).state,
      PV_LIB_SPEC_ControlRuntime.recordIssue (PV_LIB_SPEC_World18_TlsAt54.at54 e).state
        (PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt54.config (PV_LIB_SPEC_World18_TlsAt54.at54 e).state) (PV_LIB_SPEC_World18_TlsAt54.at54 e).issued,
      [PV_LIB_SPEC_TlsAt55.origin]⟩ : PV_LIB_SPEC_ResourceHistory.Execution) = (PV_LIB_SPEC_World18_TlsAt55.at55 e)
  rw [(PV_LIB_SPEC_World18_TlsDelivery15.transition e)]
  simp [PV_LIB_SPEC_World18_TlsAt55.at55,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_World18_TlsAt54.at54,PV_LIB_SPEC_TlsRequest15.after]

#print axioms consume

theorem original55 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 55
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_TlsAt55.at55 e) := by
  rw [show 55=54+1 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_Prefix54World18.original54 e.world)]
  exact (PV_LIB_SPEC_World18_TlsAt55.consume e) stack

#print axioms original55

end PV_LIB_SPEC_World18_TlsAt55
