import PV_LIB_SPEC_LaneAJoins16
import PV_LIB_SPEC_OriginalStackGap17
import PV_LIB_SPEC_UnitReserve17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativeObligations17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_LaneAJoins16 (history)

/-- Exact original poll and origin. These predicates below are OPEN proof
obligations, not new assumptions of a row, endpoint, or Joins. -/
def AtNative (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (n : Nat)
    (c : Config) (wait : PV_STX2_Native.Waiting Data) (ctx : Context) : Prop :=
  (history stack n).state.current.status = .running c ∧
  PV_LIB_SPEC_ControlRuntime.ordinary (history stack n).state = some (c,wait) ∧
  PV_LIB_SPEC_ResourceHistory.context (history stack n) c wait = some ctx

def bound (ctx : Context) : Parameters :=
  let p := PV_LIB_SPEC_ReachedEnvironment14.parameters
  {p with resources := PV_LIB_SPEC_ResourceHistory.allocationResources p.environment ctx}

/-- Same-input finite native stack target. The final equality is the actual
registered run capture112, not an independently chosen physical address. The
required no-wrap stack grant would in particular imply the360-byte bound.
There is no inhabited proof of this target for the retained fixture. -/
def OriginalStack (stack : PV_LIB_SPEC_PhysicalStack12.Frame) : Prop :=
  ∃ entryRsp, PV_LIB_SPEC_OriginalStackGap17.NativePair entryRsp stack.runPointer ∧
    stack.rsp = PV_LIB_SPEC_BinaryStack16.spawnRsp entryRsp ∧
    stack.runSource = ⟨0,12,[]⟩ ∧
    stack.runPointer = PV_LIB_SPEC_ConcreteCaptures.runHeader.pointer

theorem no_original_stack (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    ¬ OriginalStack stack := by
  rintro ⟨entryRsp,pair,_,_,run⟩
  rw [run,PV_LIB_SPEC_OriginalStackGap17.original_run_base] at pair
  exact PV_LIB_SPEC_OriginalStackGap17.original_pair_impossible entryRsp pair

/-- Native ACTIVE obligation before lane A's EXHIBITED n6. No extension of
its original-to-f6 BODY history is implemented here. Actual8248, its full
computed answer, source write, physical write and consumed origin are required. -/
def ActiveBeforeF6 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (n6 : Nat) : Prop :=
  ∃ n c wait ctx fn a,
    85 ≤ n ∧ n < n6 ∧ AtNative stack n c wait ctx ∧
    ctx.site.function = 207 ∧ ctx.site.statement = 8248 ∧
    PV_THR2_OffPath.functionId fn = some 289 ∧
    wait.request = .child fn a [PV_LIB_SPEC_TlsNative15.reference,.boolean true] ∧
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack) (bound ctx)
      c wait.request (history stack n).state.current.world =
      some ⟨.returned (.ok (.boolean false)),
        PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot
          (history stack n).state.current.world true,[]⟩ ∧
    (history stack (n+1)).consumed = ctx :: (history stack n).consumed ∧
    (PV_W1_LeafBoundary.statusStore (history stack (n+1)).state.current.status).cells
      PV_LIB_SPEC_Entry13.slot.source = some (.boolean true) ∧
    (history stack (n+1)).state.current.world.world.memory
      PV_LIB_SPEC_Entry13.slot.physical = some 1

/--295 must be reached inside lane A's actual f361 interval. Context, actual
arguments, cached byte reads, full native reply and consumption all share the
same history. This is not a successful-reply hypothesis of any contract. -/
def StackSize (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (n361 callbackN : Nat) : Prop :=
  ∃ n c wait ctx a args,
    n361 ≤ n ∧ n < callbackN ∧ AtNative stack n c wait ctx ∧
    ctx.site.function = 361 ∧
    wait.request = .child PV_LIB_SPEC_StackSize14.token a args ∧
    PV_LIB_SPEC_StackSize14.value (bound ctx) (history stack n).state.current.world args =
      some (.number 2097152) ∧
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack) (bound ctx)
      c wait.request (history stack n).state.current.world =
      some ⟨.returned (.ok (.number 2097152)),(history stack n).state.current.world,[]⟩ ∧
    (history stack (n+1)).consumed = ctx :: (history stack n).consumed

/--454 additionally requires its ACTUAL source Thread pointer and initialized
empty TLS, then the adopted32 stack stores. A local fixture cannot discharge it. -/
def Hooks (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (n361 callbackN : Nat) : Prop :=
  ∃ n c wait ctx a args threadPointer,
    n361 ≤ n ∧ n < callbackN ∧ AtNative stack n c wait ctx ∧
    ctx.site.function = 361 ∧
    wait.request = .child PV_THR2_Source361HookChildren.fnFalseFull a args ∧
    PV_LIB_SPEC_SpawnHooks14.thread (bound ctx) c (history stack n).state.current.world args =
      some threadPointer ∧
    PV_LIB_SPEC_SpawnHooks14.empty PV_LIB_SPEC_Entry14.hooksSlot
      (history stack n).state.current.world = some () ∧
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack) (bound ctx)
      c wait.request (history stack n).state.current.world =
      some ⟨.returned (.ok PV_LIB_SPEC_SpawnHooks14.value),
        PV_LIB_SPEC_PhysicalStack12.installDefault stack (history stack n).state.current.world,[]⟩ ∧
    (history stack (n+1)).consumed = ctx :: (history stack n).consumed

#print axioms AtNative
#print axioms bound
#print axioms OriginalStack
#print axioms no_original_stack
#print axioms ActiveBeforeF6
#print axioms StackSize
#print axioms Hooks
end PV_LIB_SPEC_NativeObligations17
