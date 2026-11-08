import PV_LIB_SPEC_NativeRuntime
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ResourceHistory
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984
open PV_LIB_SPEC_NativeRuntime PV_LIB_SPEC_Frozen
local instance : DecidableEq Site := Classical.decEq Site
local instance : DecidableEq (PV_STX2_Native.Request Data) := Classical.decEq _

structure Issued where
  site : Site
  caller : Nat
  request : PV_STX2_Native.Request Data
structure Context where
  site : Site
  occurrence : Nat
  arguments : List Data
  caller : Nat
  request : PV_STX2_Native.Request Data
structure Execution where
  state : State
  issued : List Issued
  consumed : List Context

def arguments : PV_STX2_Native.Request Data → List Data
  | .child _ _ args => args
  | .drop _ value => [value]
  | .copy source destination count => [source,destination,count]

/-- The source instruction supplies the Site BEFORE operand evaluation.
Only a newly issued waiting request is recorded; retries use that same origin.
No caller-supplied request-index function is accepted. -/
def issuing (q : State) : Option (Site × Nat) := do
  let c ← match q.current.status with | .running c => some c | _ => none
  if c.frame.waiting.isSome || c.frame.completed.isSome || c.frame.unwinding.isSome then none else
    match c.frame.remaining with
    | .leaf (.call site _ _ _ _) :: _ | .leaf (.drop site _ _ _ _) :: _ |
        .leaf (.copy site _ _ _) :: _ => some (site,c.frame.activation)
    | _ => none

def recordIssue (before after : State) (old : List Issued) : List Issued :=
  match issuing before,after.current.status with
  | some (site,caller),.running c =>
    match c.frame.waiting with
    | some wait => {site := site,caller := caller,request := wait.request} :: old
    | none => old
  | _,_ => old

/-- Only requests actually polled by this transition get an allocation context.
BODY pushes and intrinsic callbacks do not call the native fallback. -/
def ordinary (q : State) : Option (Config × PV_STX2_Native.Waiting Data) := do
  let c ← match q.current.status with | .running c => some c | _ => none
  if c.frame.completed.isSome || c.frame.unwinding.isSome then none else do
    match PV_THR2_Catch316Segment.select c with
    | some _ => none
    | none =>
      let wait ← c.frame.waiting
      match wait.request with
      | .child fn _ _ => if (PV_LIB_SPEC_Full.programs fn).isSome then none else some (c,wait)
      | _ => some (c,wait)

def context (x : Execution) (c : Config) (wait : PV_STX2_Native.Waiting Data) : Option Context := do
  let origin ← x.issued.find? (fun issued => decide
    (issued.caller = c.frame.activation ∧ issued.request = wait.request))
  pure {site := origin.site
        occurrence := (x.consumed.filter (fun old => decide (old.site = origin.site))).length
        arguments := arguments wait.request
        caller := c.frame.activation,request := wait.request}

/-- Every primitive query is constructed AT the reached native call. Its
operation and pre-backend world come from the named allocation handler's
actual invocation of Resources, not from a guessed operation trace. -/
def request {A : Type} (ctx : Context)
    (op : PV_EVHB_GlobalSystem.Primitive A) (before : PV_STX_World.World) : ResourceRequest A :=
  ⟨ctx.site,ctx.occurrence,ctx.arguments,op,before⟩

def allocationResources (environment : Environment) (ctx : Context) : Resources :=
  fun op before => environment.allocation (request ctx op before)
def reservationResources (environment : Environment) (ctx : Context) : Resources :=
  fun op before => environment.reservation (request ctx op before)

theorem allocation_binding (environment : Environment) (ctx : Context)
    {A : Type} (op : PV_EVHB_GlobalSystem.Primitive A) (before : PV_STX_World.World) :
    allocationResources environment ctx op before =
      environment.allocation ⟨ctx.site,ctx.occurrence,ctx.arguments,op,before⟩ := rfl
theorem reservation_binding (environment : Environment) (ctx : Context)
    {A : Type} (op : PV_EVHB_GlobalSystem.Primitive A) (before : PV_STX_World.World) :
    reservationResources environment ctx op before =
      environment.reservation ⟨ctx.site,ctx.occurrence,ctx.arguments,op,before⟩ := rfl

/-- Named Packet4963, callback13923 and ThreadInit14756 are allocations.
A future reservation handler must use reservationResources, never this path.
Absent source origins become undefined, not an arbitrary channel index. -/
def step (table : FullStoreActionTable) (p : Parameters) (abi : ABI) (x : Execution) : Execution :=
  match ordinary x.state with
  | none =>
    let out := PV_LIB_SPEC_NativeRuntime.step table p abi x.state
    {x with state := out,issued := recordIssue x.state out x.issued}
  | some (c,wait) =>
    match context x c wait with
    | none => {x with state :=
        ⟨⟨.undefined none c.store,x.state.current.world,x.state.current.events⟩,x.state.suspended⟩}
    | some ctx =>
      let bound := {p with resources := allocationResources p.environment ctx}
      let out := PV_LIB_SPEC_NativeRuntime.step table bound abi x.state
      {state := out,issued := recordIssue x.state out x.issued,consumed := ctx :: x.consumed}

def run (table : FullStoreActionTable) (p : Parameters) (abi : ABI) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => run table p abi n (step table p abi x)

def initial (i : PV_LIB_SPEC_F0Full.Original) : Execution :=
  ⟨PV_LIB_SPEC_F0Full.rootEntry i,[],[]⟩

/-- Actual-history association, not a request-index assumption in MachineSpec.
Each consumed context has a real emitted origin with the same caller/request.
The operand list is projected from THAT issued request. Statement only. -/
def HistoryAdequacy (table : FullStoreActionTable) (p : Parameters) (abi : ABI)
    (i : PV_LIB_SPEC_F0Full.Original) : Prop :=
  ∀ n ctx, ctx ∈ (run table p abi n (initial i)).consumed →
    ctx.arguments = arguments ctx.request ∧
    ∃ origin ∈ (run table p abi n (initial i)).issued,
      origin.site = ctx.site ∧ origin.caller = ctx.caller ∧ origin.request = ctx.request

#print axioms Issued
#print axioms Context
#print axioms Execution
#print axioms arguments
#print axioms issuing
#print axioms recordIssue
#print axioms ordinary
#print axioms context
#print axioms request
#print axioms allocationResources
#print axioms reservationResources
#print axioms allocation_binding
#print axioms reservation_binding
#print axioms step
#print axioms run
#print axioms initial
#print axioms HistoryAdequacy
end PV_LIB_SPEC_ResourceHistory
