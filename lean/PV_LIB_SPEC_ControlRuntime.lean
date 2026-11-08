import PV_LIB_SPEC_BoundRuntime
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ControlRuntime
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_NativeRuntime PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
open PV_LIB_SPEC_BoundRuntime (answer handler)

/-- Match the actual interpreter's priority: a waiting native request is
polled even during unwinding. Completion and catch/BODY entry take priority.
This corrects the earlier ResourceHistory.ordinary prefilter; old evidence
is retained. No source outcome is removed. -/
def ordinary (q : State) : Option (Config × PV_STX2_Native.Waiting Data) := do
  let c ← match q.current.status with | .running c => some c | _ => none
  if c.frame.completed.isSome then none else do
    match PV_THR2_Catch316Segment.select c with
    | some _ => none
    | none =>
      let wait ← c.frame.waiting
      match wait.request with
      | .child fn _ _ => if (PV_LIB_SPEC_Full.programs fn).isSome then none else some (c,wait)
      | _ => some (c,wait)

def issuing (q : State) : Option (Site × Nat) := do
  let c ← match q.current.status with | .running c => some c | _ => none
  if c.frame.waiting.isSome || c.frame.completed.isSome then none else
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

/-- Nonpolling transitions must never test a native value decoder. In
particular a completed frame with a stale waiting slot still returns through
the base's completion administration. Named OWNER actions are retained. -/
def controlStep (table : FullStoreActionTable) (p : Parameters) (abi : ABI) (q : State) : State :=
  match q.current.status with
  | .running c => PV_LIB_SPEC_D984.step (machineAt table p abi c) q
  | _ => PV_LIB_SPEC_D984.step (PV_LIB_SPEC_Frozen.source table p) q

/-- Resources are selected from the actual emitted origin BEFORE invoking
any of the three named allocation models. Every ordinary native answer is
framed; invalid value decoding is undefined. BODY/catch/control steps retain
the OWNER-aware base. No desired store, defined write, or successful decoder
is a machine premise. -/
def step (table : FullStoreActionTable) (p : Parameters) (abi : ABI) (x : Execution) : Execution :=
  match ordinary x.state with
  | none =>
    let out := controlStep table p abi x.state
    {x with state := out,issued := recordIssue x.state out x.issued}
  | some (c,wait) =>
    match context x c wait with
    | none => {x with state :=
        ⟨⟨.undefined none c.store,x.state.current.world,x.state.current.events⟩,x.state.suspended⟩}
    | some ctx =>
      let bound := {p with resources := allocationResources p.environment ctx}
      match answer bound abi c wait.request x.state.current.world with
      | none =>
        let r := PV_THR2_OwnUniformResourceHandler.lift p.environment.native wait.request x.state.current.world
        {x with
          state := ⟨⟨.undefined none c.store,r.world,x.state.current.events ++ r.events⟩,x.state.suspended⟩
          consumed := ctx :: x.consumed}
      | some _ =>
        let m := {PV_LIB_SPEC_Frozen.source table bound with handler := handler bound abi c}
        let out := PV_LIB_SPEC_D984.step m x.state
        {state := out,issued := recordIssue x.state out x.issued,consumed := ctx :: x.consumed}

def run (table : FullStoreActionTable) (p : Parameters) (abi : ABI) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => run table p abi n (step table p abi x)

/-- An arbitrary machine satisfying these equations uses the named semantics
at the reached requests. This is an operational specification, not a source
adequacy theorem. Lane A supplies the full table independently. -/
structure Machine where
  transition : Execution → Execution

def source (table : FullStoreActionTable) (p : Parameters) (abi : ABI) : Machine :=
  ⟨step table p abi⟩
def MachineSpec (table : FullStoreActionTable) (p : Parameters) (abi : ABI) (m : Machine) : Prop :=
  m.transition = step table p abi

def execute (m : Machine) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => execute m n (m.transition x)

#print axioms ordinary
#print axioms issuing
#print axioms recordIssue
#print axioms controlStep
#print axioms step
#print axioms run
#print axioms Machine
#print axioms source
#print axioms MachineSpec
#print axioms execute
end PV_LIB_SPEC_ControlRuntime
