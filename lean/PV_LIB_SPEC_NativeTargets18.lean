import PV_LIB_SPEC_LaneAJoins18
import PV_LIB_SPEC_ContextContracts18
import PV_LIB_SPEC_OriginalStackGap17
import PV_LIB_SPEC_UnitReserve17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativeTargets18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_LaneAJoins18 (history)

/-- Exact original poll and origin. These predicates below are OPEN proof
obligations, not new assumptions of a row, endpoint, or Joins. -/
def AtNative (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) (n : Nat)
    (c : Config) (wait : PV_STX2_Native.Waiting Data) (ctx : Context) : Prop :=
  (history entry activation n).state.current.status = .running c ∧
  PV_LIB_SPEC_ControlRuntime.ordinary (history entry activation n).state = some (c,wait) ∧
  PV_LIB_SPEC_ResourceHistory.context (history entry activation n) c wait = some ctx

def bound (ctx : Context) : Parameters :=
  let p := PV_LIB_SPEC_ReachedEnvironment14.parameters
  {p with resources := PV_LIB_SPEC_ResourceHistory.allocationResources p.environment ctx}

/-- Paired, granted stack on the selected complete entry, replacing the
refuted fixed112 fixture. This is now inhabited for every Entry by construction. -/
def OriginalStack (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) : Prop :=
  let stack := PV_LIB_SPEC_EntryWorld18.frame entry activation
  PV_LIB_SPEC_OriginalStackGap17.NativePair entry.scopeEntryRsp stack.runPointer ∧
  entry.stackGrant.base ≤ stack.rsp ∧
  stack.runPointer+16 ≤ entry.stackGrant.base+entry.stackGrant.size ∧
  ∃ id h, PV_EVHB_OwnerMachine.receiver entry.world PV_LIB_SPEC_ConcreteCaptures.places.run = some (id,h) ∧
    h.pointer = stack.runPointer

theorem original_stack (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) :
    OriginalStack entry activation := by
  obtain ⟨id,h,receiver,pointer⟩ := entry.run
  exact ⟨PV_LIB_SPEC_EntryWorld18.paired entry activation,
    (PV_LIB_SPEC_EntryWorld18.stack_contains entry activation).1,
    (PV_LIB_SPEC_EntryWorld18.stack_contains entry activation).2.1,id,h,receiver,pointer⟩

/-- Actual future source-frame/initialized-run association is a separate OPEN
conclusion. A finite entry frame alone does not establish this reached fact. -/
def StackAtCallback (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation callbackN : Nat) : Prop :=
  ∃ c value id h,
    (history entry activation callbackN).state.current.status = .running c ∧
    c.frame.activation = activation ∧
    readAddress (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier c.store
      (PV_LIB_SPEC_EntryWorld18.frame entry activation).runSource = some value ∧
    PV_EVHB_OwnerMachine.receiver (history entry activation callbackN).state.current.world
      PV_LIB_SPEC_ConcreteCaptures.places.run = some (id,h) ∧
    h.pointer = (PV_LIB_SPEC_EntryWorld18.frame entry activation).runPointer

/-- Native ACTIVE obligation before lane A's EXHIBITED n6. No extension of
its original-to-f6 BODY history is implemented here. Actual8248, its full
computed answer, source write, physical write and consumed origin are required. -/
def ActiveBeforeF6 (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) (n6 : Nat) : Prop :=
  ∃ n c wait ctx fn a,
    85 ≤ n ∧ n < n6 ∧ AtNative entry activation n c wait ctx ∧
    ctx.site.function = 207 ∧ ctx.site.statement = 8248 ∧
    PV_THR2_OffPath.functionId fn = some 289 ∧
    wait.request = .child fn a [PV_LIB_SPEC_TlsNative15.reference,.boolean true] ∧
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation)) (bound ctx)
      c wait.request (history entry activation n).state.current.world =
      some ⟨.returned (.ok (.boolean false)),
        PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot
          (history entry activation n).state.current.world true,[]⟩ ∧
    (history entry activation (n+1)).consumed = ctx :: (history entry activation n).consumed ∧
    (PV_W1_LeafBoundary.statusStore (history entry activation (n+1)).state.current.status).cells
      PV_LIB_SPEC_Entry13.slot.source = some (.boolean true) ∧
    (history entry activation (n+1)).state.current.world.world.memory
      PV_LIB_SPEC_Entry13.slot.physical = some 1

/--295 must be reached inside lane A's actual f361 interval. Context, actual
arguments, cached byte reads, full native reply and consumption all share the
same history. This is not a successful-reply hypothesis of any contract. -/
def StackSize (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) (n361 callbackN : Nat) : Prop :=
  ∃ n c wait ctx a args,
    n361 ≤ n ∧ n < callbackN ∧ AtNative entry activation n c wait ctx ∧
    ctx.site.function = 361 ∧
    wait.request = .child PV_LIB_SPEC_StackSize14.token a args ∧
    PV_LIB_SPEC_StackSize14.value (bound ctx) (history entry activation n).state.current.world args =
      some (.number 2097152) ∧
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation)) (bound ctx)
      c wait.request (history entry activation n).state.current.world =
      some ⟨.returned (.ok (.number 2097152)),(history entry activation n).state.current.world,[]⟩ ∧
    (history entry activation (n+1)).consumed = ctx :: (history entry activation n).consumed

/--454 additionally requires its ACTUAL source Thread pointer and initialized
empty TLS, then the adopted32 stack stores. A local fixture cannot discharge it. -/
def Hooks (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat) (n361 callbackN : Nat) : Prop :=
  ∃ n c wait ctx a args threadPointer,
    n361 ≤ n ∧ n < callbackN ∧ AtNative entry activation n c wait ctx ∧
    ctx.site.function = 361 ∧
    wait.request = .child PV_THR2_Source361HookChildren.fnFalseFull a args ∧
    PV_LIB_SPEC_SpawnHooks14.thread (bound ctx) c (history entry activation n).state.current.world args =
      some threadPointer ∧
    PV_LIB_SPEC_SpawnHooks14.empty PV_LIB_SPEC_Entry14.hooksSlot
      (history entry activation n).state.current.world = some () ∧
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation)) (bound ctx)
      c wait.request (history entry activation n).state.current.world =
      some ⟨.returned (.ok PV_LIB_SPEC_SpawnHooks14.value),
        PV_LIB_SPEC_PhysicalStack12.installDefault (PV_LIB_SPEC_EntryWorld18.frame entry activation) (history entry activation n).state.current.world,[]⟩ ∧
    (history entry activation (n+1)).consumed = ctx :: (history entry activation n).consumed

#print axioms AtNative
#print axioms bound
#print axioms OriginalStack
#print axioms original_stack
#print axioms StackAtCallback
#print axioms ActiveBeforeF6
#print axioms StackSize
#print axioms Hooks
end PV_LIB_SPEC_NativeTargets18
