import PV_LIB_SPEC_ThreadNewNative
import PV_LIB_SPEC_ConcreteEntry
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SuccessSchedule12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen PV_LIB_SPEC_D984
/-- One finite successful malloc schedule, source-site AND size bound.
ScopeData and Packet share erased source4963, but have distinct sizes/images.
The implicit213 allocation is attached to its actual source12290 request.
Unknown operations remain pending. This is concrete data, not reachability. -/
def pointer (statement size : Nat) : Option Nat :=
  if statement=4963 ∧ size=40 then some 2048
  else if statement=4963 ∧ size=48 then some 4096
  else if statement=12290 ∧ size=48 then some 6144
  else if statement=13923 ∧ size=56 then some 8192
  else if statement=14756 ∧ size=24 then some 12288
  else none

def allocation {A : Type} (req : ResourceRequest A) : ResourceReply A :=
  match req.operation with
  | .malloc size =>
    ⟨match pointer req.site.statement size with
      | some p => .returned (.ok p) | none => .pending,
      req.before.allocator,req.before.errno⟩
  | _ => ⟨.pending,req.before.allocator,req.before.errno⟩

def native (req : PV_STX2_Native.Request Data) (w : PV_STX_World.World) :
    Reply PV_STX_World.World Event Data :=
  match req with
  | .child fn _ _ =>
    match PV_THR2_OffPath.functionId fn with
    | some 122 => ⟨.returned (.ok (.number 16384)),w,[]⟩
    | some 452 => ⟨.returned (.ok (.number 2)),w,[]⟩
    | some 121 | some 123 | some 455 | some 456 => ⟨.returned (.ok .null),w,[]⟩
    | _ => ⟨.pending,w,[]⟩
  | _ => ⟨.pending,w,[]⟩
def environment : Environment :=
  ⟨allocation,fun req => ⟨.pending,req.before.allocator,req.before.errno⟩,native⟩
def parameters : Parameters :=
  {PV_LIB_SPEC_ConcreteEntry.parameters with environment := environment}

theorem replies :
    pointer 4963 40 = some 2048 ∧ pointer 4963 48 = some 4096 ∧
    pointer 12290 48 = some 6144 ∧ pointer 13923 56 = some 8192 ∧
    pointer 14756 24 = some 12288 := by decide

theorem allocation_reply (site : Site) (n : Nat) (args : List Data)
    (before : PV_STX_World.World) (size address : Nat)
    (selected : pointer site.statement size = some address) :
    (allocation (⟨site,n,args,.malloc size,before⟩ : ResourceRequest Nat)).answer =
      .returned (.ok address) := by
  simp only [allocation,selected]

/-- The same complete entry Pre survives this environment choice: entry
reference/capture validity depends on the initialized input, not future replies.
It earns ENTRY credit only, not TLS validity or successful reachability. -/
theorem entry : OwnInit.Pre parameters PV_LIB_SPEC_ConcreteEntry.input := by
  refine ⟨rfl,rfl,PV_LIB_SPEC_ConcreteEntry.owner 2 (by decide),
    PV_LIB_SPEC_ConcreteEntry.owner 1 (by decide),PV_LIB_SPEC_ConcreteEntry.validity,
    PV_LIB_SPEC_ConcreteEntry.numbered,?_,?_⟩
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
  · exact ⟨Unit,Unit,PV_LIB_SPEC_ConcreteCaptures.captures,rfl,
      PV_LIB_SPEC_ConcreteCaptures.entry_nonempty⟩

#print axioms pointer
#print axioms allocation
#print axioms native
#print axioms environment
#print axioms parameters
#print axioms replies
#print axioms allocation_reply
#print axioms entry
end PV_LIB_SPEC_SuccessSchedule12
