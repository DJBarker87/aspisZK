import PV_LIB_SPEC_LaneAJoins18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextMachine18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)

/-- SPEC-C14 successor: the machine carries origin/consumption history as well
as the complete intrinsic state. The transition is the retained v2 operation,
including its source-derived native and resource context. -/
structure Machine where
  next : Execution → Execution

def MachineSpec (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (m : Machine) : Prop :=
  m.next = PV_LIB_SPEC_ReachedNative14.step cut p

def source (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) : Machine :=
  ⟨PV_LIB_SPEC_ReachedNative14.step cut p⟩

def run (m : Machine) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => run m n (m.next x)

def start (q : State) (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨q,issued,consumed⟩

/-- Pending is recognized from the ACTUAL context transition. Intrinsic calls
and BODY pushes are excluded, as in the corrected frozen frontier. -/
def Pending (m : Machine) (x : Execution) : Prop :=
  ∃ c wait after, x.state.current.status = .running c ∧
    c.frame.completed = none ∧ c.frame.unwinding = none ∧
    c.frame.waiting = some wait ∧ PV_THR2_Catch316Segment.select c = none ∧
    (match wait.request with | .child fn _ _ => PV_LIB_SPEC_Full.programs fn = none | _ => True) ∧
    (m.next x).state.current.status = .running after ∧
    after.frame.activation = c.frame.activation ∧ after.frame.completed = none ∧
    after.frame.waiting = some wait

abbrev Finish := State → State → Prop

def Boundary (m : Machine) (finish : Finish) (entry : Execution)
    (trace : Nat → Execution) (n : Nat) : Prop :=
  finish entry.state (trace n).state ∨ Terminal entry.state (trace n).state ∨
    ∃ k, n=k+1 ∧ Pending m (trace k) ∧ trace n = m.next (trace k)

def First (m : Machine) (finish : Finish) (entry : Execution)
    (trace : Nat → Execution) (n : Nat) : Prop :=
  Boundary m finish entry trace n ∧ ∀ k, k<n → ¬ Boundary m finish entry trace k

/-- Abort observation retains only events; every other arm retains the full
state and both origin lists. No successful-only projection is used. -/
inductive Observation where
  | abort : List Event → Observation
  | state : Execution → Observation

def observe (x : Execution) : Observation :=
  match x.state.current.status with
  | .fault .abort _ | .fault .panic _ => .abort x.state.current.events
  | _ => .state x

def Behavior (m : Machine) (finish : Finish) (entry : Execution)
    (candidate : Nat → Execution) : Prop :=
  let ref := fun n => run m n entry
  (∃ n k, First m finish entry ref n ∧ First m finish entry candidate k ∧
    observe (candidate k) = observe (ref n)) ∨
  ((∀ n, ¬ Boundary m finish entry ref n) ∧ (∀ k, ¬ Boundary m finish entry candidate k) ∧
    (∀ n, ∃ k, (ref n).state.current.events = (candidate k).state.current.events) ∧
    (∀ k, ∃ n, (ref n).state.current.events = (candidate k).state.current.events))

/-- At each real issued native poll, the resource adapter is constructed
from that SAME execution's origin and operands. No external request index. -/
def bound (p : Parameters) (x : Execution) (c : Config)
    (wait : PV_STX2_Native.Waiting Data) : Option Parameters :=
  match PV_LIB_SPEC_ResourceHistory.context x c wait with
  | none => none
  | some ctx => some {p with resources := PV_LIB_SPEC_ResourceHistory.allocationResources p.environment ctx}

theorem source_spec (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) :
    MachineSpec cut p (source cut p) := rfl

theorem run_same (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (n : Nat) (x : Execution) :
    run (source cut p) n x = PV_LIB_SPEC_ReachedNative14.run cut p n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih _

#print axioms Machine
#print axioms MachineSpec
#print axioms source
#print axioms run
#print axioms start
#print axioms Pending
#print axioms Finish
#print axioms Boundary
#print axioms First
#print axioms Observation
#print axioms observe
#print axioms Behavior
#print axioms bound
#print axioms source_spec
#print axioms run_same
end PV_LIB_SPEC_ContextMachine18
