import PV_LIB_SPEC_TlsWorld18_4
import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section

namespace PV_LIB_SPEC_World18_TlsAt75

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution initial)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_Tls68Data16 (at68 store68 result)

open PV_LIB_SPEC_TlsAt75
def at75 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := PV_LIB_SPEC_SourceTransport15.advance
  PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_TlsAt75.handler 7 (PV_LIB_SPEC_World18_Tls68Data16.at68 e)

#print axioms at75

theorem original75 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 75
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_TlsAt75.at75 e) := by
  rw [show 75=68+7 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_World18_TlsAt68.original68 e)]
  exact PV_LIB_SPEC_SourceTransport15.run _ _ PV_LIB_SPEC_TlsAt75.handler _ _
    (PV_LIB_SPEC_TlsForward16.trace _ _ _ PV_LIB_SPEC_Tls68Data16.store68 5 PV_LIB_SPEC_TlsOriginal15.parents
      e.world [] (PV_LIB_SPEC_World18_Tls68Data16.at68 e).issued (PV_LIB_SPEC_World18_Tls68Data16.at68 e).consumed PV_LIB_SPEC_Tls68Data16.result PV_LIB_SPEC_TlsNative15.reference PV_LIB_SPEC_TlsAt75.cell rfl rfl)

#print axioms original75

theorem state75 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt75.at75 e).state =
    ⟨⟨.running ⟨{activation := 5,remaining := PV_THR2_F170.live.body.drop 31},
      PV_LIB_SPEC_TlsOriginal15.parents,PV_LIB_SPEC_TlsAt75.store75⟩,e.world,[]⟩,[]⟩ := by
  unfold PV_LIB_SPEC_World18_TlsAt75.at75
  rw [PV_LIB_SPEC_SourceProjection15.state]
  exact PV_LIB_SPEC_TlsForwardLift16.source _ PV_LIB_SPEC_TlsAt75.handler PV_LIB_SPEC_Tls68Data16.store68 5
    PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Tls68Data16.result PV_LIB_SPEC_TlsNative15.reference e.world [] PV_LIB_SPEC_TlsAt75.cell rfl rfl

#print axioms state75

theorem consumed75 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt75.at75 e).consumed = (PV_LIB_SPEC_World18_Tls68Data16.at68 e).consumed :=
  PV_LIB_SPEC_Tls279History16.consumed _ PV_LIB_SPEC_TlsAt75.handler 7 (PV_LIB_SPEC_World18_Tls68Data16.at68 e)

#print axioms consumed75

end PV_LIB_SPEC_World18_TlsAt75

namespace PV_LIB_SPEC_World18_TlsAt84

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context initial)
open PV_LIB_SPEC_TlsAt75 (at75 store75 handler)
open PV_LIB_SPEC_TlsNative15 (cut reference)
open PV_LIB_SPEC_Tls75Cells16 (callable pointer)

open PV_LIB_SPEC_TlsAt84
def at84 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := PV_LIB_SPEC_SourceTransport15.advance
  PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_TlsAt75.handler 9 (PV_LIB_SPEC_World18_TlsAt75.at75 e)

#print axioms at84

theorem stage75 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt75.at75 e) = PV_LIB_SPEC_F1Arithmetic14.stage PV_LIB_SPEC_TlsAt75.store75 5
    PV_LIB_SPEC_TlsOriginal15.parents (PV_THR2_F170.live.body.drop 31)
    e.world [] (PV_LIB_SPEC_World18_TlsAt75.at75 e).issued (PV_LIB_SPEC_World18_TlsAt75.at75 e).consumed := by
  calc (PV_LIB_SPEC_World18_TlsAt75.at75 e) = ⟨(PV_LIB_SPEC_World18_TlsAt75.at75 e).state,(PV_LIB_SPEC_World18_TlsAt75.at75 e).issued,(PV_LIB_SPEC_World18_TlsAt75.at75 e).consumed⟩ := rfl
       _ = _ := by rw [(PV_LIB_SPEC_World18_TlsAt75.state75 e)]; rfl

#print axioms stage75

theorem dereference (e : PV_LIB_SPEC_EntryWorld18.Entry) :
    (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier.dereference
      e.world PV_LIB_SPEC_TlsNative15.reference = some PV_LIB_SPEC_Entry13.slot.source := by
  simp only [PV_LIB_SPEC_TlsNative15.reference,runtime,PV_THR2_OwnInitExactReturnedCases.carrier,
    PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
    PV_STX2_TypedReferences.carrier,PV_STX2_TypedReferences.roundtrip]

#print axioms dereference

theorem original84 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 84
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_TlsAt84.at84 e) := by
  rw [show 84=75+9 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_World18_TlsAt75.original75 e)]
  unfold PV_LIB_SPEC_World18_TlsAt84.at84
  rw [(PV_LIB_SPEC_World18_TlsAt84.stage75 e)]
  exact PV_LIB_SPEC_SourceTransport15.run _ _ PV_LIB_SPEC_TlsAt75.handler _ _
    (PV_LIB_SPEC_TlsCallable16.trace _ _ _ PV_LIB_SPEC_TlsAt75.store75 5 PV_LIB_SPEC_TlsOriginal15.parents
      e.world [] (PV_LIB_SPEC_World18_TlsAt75.at75 e).issued (PV_LIB_SPEC_World18_TlsAt75.at75 e).consumed _ PV_LIB_SPEC_TlsNative15.reference _ PV_LIB_SPEC_Tls75Cells16.callable PV_LIB_SPEC_Tls75Cells16.pointer (PV_LIB_SPEC_World18_TlsAt84.dereference e))

#print axioms original84

theorem state84 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt84.at84 e).state = ⟨⟨.running PV_LIB_SPEC_TlsAt84.config,e.world,[]⟩,[]⟩ := by
  unfold PV_LIB_SPEC_World18_TlsAt84.at84
  rw [PV_LIB_SPEC_SourceProjection15.state,(PV_LIB_SPEC_World18_TlsAt75.state75 e)]
  exact PV_LIB_SPEC_TlsCallableLift16.source _ PV_LIB_SPEC_TlsAt75.handler PV_LIB_SPEC_TlsAt75.store75 5
    PV_LIB_SPEC_TlsOriginal15.parents _ PV_LIB_SPEC_TlsNative15.reference _ e.world [] PV_LIB_SPEC_Tls75Cells16.callable PV_LIB_SPEC_Tls75Cells16.pointer (PV_LIB_SPEC_World18_TlsAt84.dereference e)

#print axioms state84

theorem issued84 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt84.at84 e).issued =
    (⟨PV_LIB_SPEC_TlsCallableHistory16.site,5,
      .child PV_THR2_RunTlsCallable.descriptors.1 10
        [PV_THR2_F2Call.descriptors.2,PV_THR2_KeyValues.pack PV_THR2_RunTlsCallable.descriptors.2
          [PV_LIB_SPEC_TlsNative15.reference]]⟩ : PV_LIB_SPEC_ResourceHistory.Issued) :: (PV_LIB_SPEC_World18_TlsAt75.at75 e).issued := by
  unfold PV_LIB_SPEC_World18_TlsAt84.at84
  rw [(PV_LIB_SPEC_World18_TlsAt84.stage75 e)]
  exact PV_LIB_SPEC_TlsCallableHistory16.issued (PV_LIB_SPEC_TlsNative15.cut ⟨0,0,⟨0,0,[]⟩,0⟩) _ PV_LIB_SPEC_TlsAt75.handler PV_LIB_SPEC_TlsAt75.store75 5
    PV_LIB_SPEC_TlsOriginal15.parents e.world [] (PV_LIB_SPEC_World18_TlsAt75.at75 e).issued (PV_LIB_SPEC_World18_TlsAt75.at75 e).consumed
    _ PV_LIB_SPEC_TlsNative15.reference _ PV_LIB_SPEC_Tls75Cells16.callable PV_LIB_SPEC_Tls75Cells16.pointer (PV_LIB_SPEC_World18_TlsAt84.dereference e)

#print axioms issued84

theorem consumed84 (e : PV_LIB_SPEC_EntryWorld18.Entry) : (PV_LIB_SPEC_World18_TlsAt84.at84 e).consumed = (PV_LIB_SPEC_World18_TlsAt75.at75 e).consumed :=
  PV_LIB_SPEC_Tls279History16.consumed _ PV_LIB_SPEC_TlsAt75.handler 9 (PV_LIB_SPEC_World18_TlsAt75.at75 e)

#print axioms consumed84

end PV_LIB_SPEC_World18_TlsAt84

namespace PV_LIB_SPEC_World18_Tls18Reached16

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_TlsAt75 (store75)
open PV_LIB_SPEC_TlsAt84 (config)
open PV_LIB_SPEC_TlsNative15 (cut)

open PV_LIB_SPEC_Tls18Reached16
theorem active (e : PV_LIB_SPEC_EntryWorld18.Entry) (resources : PV_EVHB_OwnerHeap.Resources) :
    PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt84.config e.world = some false := by
  unfold PV_LIB_SPEC_TlsBindings13.read
  have read : readAddress (runtime (PV_LIB_SPEC_TlsBound15.parameters resources)).carrier
      PV_LIB_SPEC_TlsAt84.config.store PV_LIB_SPEC_Entry13.slot.source = some (.boolean false) := by
    change readAddress _ PV_LIB_SPEC_TlsAt84.config.store ⟨0,20,[]⟩ = _
    rw [PV_LIB_SPEC_Tls18Reached16.read_nil]
    exact PV_LIB_SPEC_Tls18Reached16.source
  rw [read]
  change (if e.world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0 then some false else none) = _
  rw [(PV_LIB_SPEC_World18_TlsNative15.physical e)]
  rfl

#print axioms active

end PV_LIB_SPEC_World18_Tls18Reached16

namespace PV_LIB_SPEC_World18_Tls85Data16

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_TlsAt84 (config at84)
open PV_LIB_SPEC_Tls18Bound16 (token arguments request)

open PV_LIB_SPEC_Tls85Data16
def after (e : PV_LIB_SPEC_EntryWorld18.Entry) : State := (PV_LIB_SPEC_F1Arithmetic14.stage PV_LIB_SPEC_Tls85Data16.store85 5
  PV_LIB_SPEC_TlsOriginal15.parents (PV_THR2_F170.live.body.drop 40)
  e.world [] [] []).state

#print axioms after

def at85 (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.Execution := ⟨(PV_LIB_SPEC_World18_Tls85Data16.after e),(PV_LIB_SPEC_World18_TlsAt84.at84 e).issued,PV_LIB_SPEC_Tls85Data16.origin :: (PV_LIB_SPEC_World18_TlsAt84.at84 e).consumed⟩

#print axioms at85

theorem ordinary (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ControlRuntime.ordinary (PV_LIB_SPEC_World18_TlsAt84.at84 e).state = some (PV_LIB_SPEC_TlsAt84.config,PV_LIB_SPEC_Tls85Data16.wait) := by
  rw [(PV_LIB_SPEC_World18_TlsAt84.state84 e)]
  have lookup : PV_LIB_SPEC_Full.programs PV_LIB_SPEC_Tls18Bound16.token = none := by
    have ne : PV_LIB_SPEC_Tls18Bound16.token ≠ PV_THR2_Catch208Invoke.fn := by
      intro eq
      have same := congrArg PV_THR2_SourceTraitDispatch.source eq
      cases same
    change PV_THR2_Source208Table.table _ PV_LIB_SPEC_Tls18Bound16.token = none
    rw [PV_THR2_Source208Table.away _ _ ne]
    rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,PV_LIB_SPEC_TlsAt84.config,PV_LIB_SPEC_TlsCallable16.config,
    PV_THR2_Catch316Segment.select,PV_LIB_SPEC_Tls85Data16.wait,PV_LIB_SPEC_Tls18Bound16.request,PV_LIB_SPEC_Tls18Bound16.arguments,PV_LIB_SPEC_Tls18Bound16.token,
    show PV_LIB_SPEC_TlsAt75.store75.nextActivation=10 from rfl]
  exact ⟨lookup,rfl⟩

#print axioms ordinary

end PV_LIB_SPEC_World18_Tls85Data16

namespace PV_LIB_SPEC_World18_Tls18Delivery16

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Tls85Data16
open PV_LIB_SPEC_TlsAt84 (config at84)
open PV_LIB_SPEC_Tls18Bound16 (token arguments request)
open PV_LIB_SPEC_TlsNative15 (cut)

open PV_LIB_SPEC_Tls18Delivery16
theorem transition (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      PV_LIB_SPEC_TlsAt84.config (PV_LIB_SPEC_World18_TlsAt84.at84 e).state = (PV_LIB_SPEC_World18_Tls85Data16.after e) := by
  rw [(PV_LIB_SPEC_World18_TlsAt84.state84 e)]
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet
      ⟨⟨.running PV_LIB_SPEC_TlsAt84.config,e.world,[]⟩,[]⟩ := by
    have table : PV_LIB_StoreActionTable.v2 PV_LIB_SPEC_Tls18Bound16.token = none := rfl
    simp [PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,PV_LIB_SPEC_TlsAt84.config,PV_LIB_SPEC_TlsCallable16.config,
      PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
      PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
      PV_THR2_OwnUniformNeutral.instruction,PV_THR2_F170.live,PV_THR2_F170.block66,
      PV_THR2_F170.node56,← show PV_LIB_SPEC_Tls18Bound16.token=PV_THR2_RunTlsCallable.descriptors.1 from rfl,
      PV_LIB_SPEC_Tls18Delivery16.lookup,table]
  rw [PV_LIB_SPEC_NativeDelivery16.full (PV_LIB_SPEC_TlsNative15.cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
    PV_LIB_SPEC_TlsAt84.config e.world [] [] PV_LIB_SPEC_Tls85Data16.wait PV_LIB_SPEC_Tls18Bound16.token 10 14 PV_LIB_SPEC_Tls18Bound16.arguments
    quiet (by rfl) rfl rfl PV_LIB_SPEC_Tls85Data16.waiting rfl PV_LIB_SPEC_Tls18Delivery16.lookup]
  have reply := PV_LIB_SPEC_Tls18Bound16.answer stack resources PV_LIB_SPEC_TlsAt84.config
    e.world 10 ((PV_LIB_SPEC_World18_Tls18Reached16.active e) resources)
  simp only [PV_LIB_SPEC_ReachedNative14.handler,show PV_LIB_SPEC_Tls85Data16.wait.request=PV_LIB_SPEC_Tls18Bound16.request 10 from rfl,
    reply,Option.getD_some]
  rfl

#print axioms transition

end PV_LIB_SPEC_World18_Tls18Delivery16

namespace PV_LIB_SPEC_World18_TlsAt85

open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_TlsAt84 (config at84)
open PV_LIB_SPEC_Tls85Data16 (wait origin at85)
open PV_LIB_SPEC_Tls18Bound16 (request)
open PV_LIB_SPEC_TlsNative15 (cut)

open PV_LIB_SPEC_TlsAt85
theorem context (e : PV_LIB_SPEC_EntryWorld18.Entry) : PV_LIB_SPEC_ResourceHistory.context (PV_LIB_SPEC_World18_TlsAt84.at84 e) PV_LIB_SPEC_TlsAt84.config PV_LIB_SPEC_Tls85Data16.wait = some PV_LIB_SPEC_Tls85Data16.origin := by
  rw [PV_LIB_SPEC_ResourceHistory.context,(PV_LIB_SPEC_World18_TlsAt84.issued84 e),
    (PV_LIB_SPEC_World18_TlsAt84.consumed84 e),(PV_LIB_SPEC_World18_TlsAt75.consumed75 e)]
  change _ = some PV_LIB_SPEC_Tls85Data16.origin
  simp [PV_LIB_SPEC_TlsAt84.config,PV_LIB_SPEC_TlsCallable16.config,PV_LIB_SPEC_Tls85Data16.wait,PV_LIB_SPEC_Tls85Data16.origin,PV_LIB_SPEC_Tls18Bound16.request,
    PV_LIB_SPEC_Tls18Bound16.arguments,PV_LIB_SPEC_Tls18Bound16.token,
    PV_LIB_SPEC_ResourceHistory.arguments,PV_LIB_SPEC_World18_Tls68Data16.at68,
    (PV_LIB_SPEC_World18_TlsAt67.consumed67 e),PV_LIB_SPEC_Tls68Data16.origin,
    PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls59Data15.origin,
    PV_LIB_SPEC_TlsAt55.origin,PV_LIB_SPEC_TlsCallableHistory16.site,
    PV_LIB_SPEC_Tls279History16.site,PV_LIB_SPEC_Tls278History15.site,
    PV_LIB_SPEC_Tls277Request15.site,PV_LIB_SPEC_TlsRequest15.site,
    PV_THR2_F170.node13,PV_THR2_F170.node16,PV_THR2_F170.node20,
    PV_THR2_F170.node23,PV_THR2_F170.node55,
    show PV_LIB_SPEC_TlsAt75.store75.nextActivation=10 from rfl]

#print axioms context

theorem consume (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.step (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters (PV_LIB_SPEC_World18_TlsAt84.at84 e) = (PV_LIB_SPEC_World18_Tls85Data16.at85 e) := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [(PV_LIB_SPEC_World18_Tls85Data16.ordinary e)]
  rw [(PV_LIB_SPEC_World18_TlsAt85.context e)]
  simp only []
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment PV_LIB_SPEC_Tls85Data16.origin
  have result := PV_LIB_SPEC_Tls18Bound16.answer stack resources PV_LIB_SPEC_TlsAt84.config
    e.world 10 ((PV_LIB_SPEC_World18_Tls18Reached16.active e) resources)
  change (match PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt84.config (PV_LIB_SPEC_Tls18Bound16.request 10) e.world with
    | none => _ | some _ => _) = (PV_LIB_SPEC_World18_Tls85Data16.at85 e)
  rw [result]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt84.config (PV_LIB_SPEC_World18_TlsAt84.at84 e).state,
      PV_LIB_SPEC_ControlRuntime.recordIssue (PV_LIB_SPEC_World18_TlsAt84.at84 e).state
        (PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
          (PV_LIB_SPEC_TlsBound15.parameters resources) PV_LIB_SPEC_TlsAt84.config (PV_LIB_SPEC_World18_TlsAt84.at84 e).state) (PV_LIB_SPEC_World18_TlsAt84.at84 e).issued,
      PV_LIB_SPEC_Tls85Data16.origin :: (PV_LIB_SPEC_World18_TlsAt84.at84 e).consumed⟩ : PV_LIB_SPEC_ResourceHistory.Execution) = (PV_LIB_SPEC_World18_Tls85Data16.at85 e)
  rw [(PV_LIB_SPEC_World18_Tls18Delivery16.transition e)]
  simp only [PV_LIB_SPEC_World18_Tls85Data16.at85]
  rw [(PV_LIB_SPEC_World18_TlsAt84.state84 e)]
  rfl

#print axioms consume

theorem original85 (e : PV_LIB_SPEC_EntryWorld18.Entry) (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 85
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world)) = (PV_LIB_SPEC_World18_Tls85Data16.at85 e) := by
  rw [show 85=84+1 from rfl,PV_LIB_SPEC_Original14.run_add,(PV_LIB_SPEC_World18_TlsAt84.original84 e)]
  exact (PV_LIB_SPEC_World18_TlsAt85.consume e) stack

#print axioms original85

end PV_LIB_SPEC_World18_TlsAt85
