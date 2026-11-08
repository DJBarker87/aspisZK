import PV_LIB_SPEC_PrefixNative14
import PV_LIB_SPEC_PrefixEnvironment13
import PV_LIB_SPEC_EntryPre14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_PrefixEnvironment14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_EntryPre14
local instance : DecidableEq Data := Classical.decEq _
open PV_LIB_SPEC_ConcreteCaptures (captures)

/-- Exact295/453/454 successful triggers supplement the retained13 native
schedule. Each adapter computes its source value and byte effects from the
actual pre-state. Unbound requests still remain pending. -/
def native (request : PV_STX2_Native.Request Data) (w : PV_STX_World.World) :
    Reply PV_STX_World.World Event Data :=
  match request with
  | .child fn _ _ =>
    if fn=PV_LIB_SPEC_StackSize14.token ∨
        fn=PV_THR2_Source361HookChildren.fnTrueFull ∨
        fn=PV_THR2_Source361HookChildren.fnFalseFull then
      ⟨.returned (.ok .null),w,[]⟩
    else PV_LIB_SPEC_PrefixEnvironment13.native request w
  | _ => PV_LIB_SPEC_PrefixEnvironment13.native request w

def environment : Environment :=
  {PV_LIB_SPEC_SuccessSchedule12.environment with native := native}
def parameters : Parameters :=
  {PV_LIB_SPEC_SuccessSchedule12.parameters with environment := environment}

/-- Same complete entry Pre; no environment identification is assumed. -/
theorem pre : OwnInit.Pre parameters PV_LIB_SPEC_Entry14.input := by
  refine ⟨rfl,rfl,owner 2 (by decide),
    owner 1 (by decide),PV_LIB_SPEC_ConcreteEntry.validity,
    ?_,?_,?_⟩
  · constructor
    · intro c eq
      cases eq
      exact ⟨by decide,True.intro,True.intro⟩
    · intro c member; cases member
  · intro v address reached deref
    have valid : PV_LIB_SPEC_ConcreteEntry.Value v := by
      clear deref
      induction reached with
      | argument member =>
        change _ ∈ [.number 1,PV_LIB_SPEC_ConcreteCaptures.closure] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact .count
        · rcases List.mem_singleton.mp member with rfl; exact .closure
      | field n _ selected ih => exact PV_LIB_SPEC_ConcreteEntry.fields _ _ n ih selected
      | pointee _ selected read ih =>
        have eq := PV_LIB_SPEC_ConcreteEntry.dereference _ _ ih selected
        subst eq
        change some Data.null = some _ at read
        cases read
        exact .unit
    have eq := PV_LIB_SPEC_ConcreteEntry.dereference v address valid deref
    subst address
    exact ⟨.null,rfl⟩
  · exact ⟨Unit,Unit,captures,rfl,captured⟩


/-- The binding at an issued poll still constructs its full resource request
from the real origin/occurrence/operands and pre-world. It never accepts a
caller-supplied allocation index. The existing five sparse size/site replies
are reused unchanged. -/
theorem allocations {A : Type} (ctx : PV_LIB_SPEC_ResourceHistory.Context)
    (operation : PV_EVHB_GlobalSystem.Primitive A) (before : PV_STX_World.World) :
    PV_LIB_SPEC_ResourceHistory.allocationResources environment ctx operation before =
      PV_LIB_SPEC_SuccessSchedule12.allocation
        ⟨ctx.site,ctx.occurrence,ctx.arguments,operation,before⟩ := rfl

#print axioms native
#print axioms environment
#print axioms parameters
#print axioms pre
#print axioms allocations
end PV_LIB_SPEC_PrefixEnvironment14
