import PV_LIB_SPEC_ThreadMachine
import PV_STX2_LiveNumbering
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ThreadContract
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_ThreadMachine

/-- Administrative projection only. Source cells, control, world and events
are retained. A callee interface never exports the unused counter. -/
def storeView (s : Store Data) : Store Data := {s with nextActivation := 0}
def configView (c : Config) : Config := {c with store := storeView c.store}
def statusView : Status → Status
  | .running c => .running (configView c)
  | .returned r s => .returned r (storeView s)
  | .fault f s => .fault f (storeView s)
  | .undefined a s => .undefined a (storeView s)

inductive Observation where
  | state : State → Observation
  | abort : List Event → Observation

def observe (q : State) : Observation :=
  match q.current.status with
  | .fault .abort _ => .abort q.current.events
  | _ => .state ⟨{q.current with status := statusView q.current.status},
      q.suspended.map configView⟩

def Numbered (q : State) : Prop :=
  (∀ c, q.current.status = .running c → PV_STX2_LiveNumbering.Numbered c) ∧
    ∀ c ∈ q.suspended, PV_STX2_LiveNumbering.Numbered c

def OwnComplete (entry out : State) : Prop :=
  ∃ before after result, entry.current.status = .running before ∧
    out.current.status = .running after ∧
    after.frame.activation = before.frame.activation ∧
    after.callers = before.callers ∧ out.suspended = entry.suspended ∧
    after.frame.completed = some result

/-- A nested callback's normal return is administrative; failures and aborts
are delivered at their own frontier without executing a lower caller suffix. -/
def Terminal (entry out : State) : Prop :=
  (∃ value store, out.current.status = .returned (.ok value) store ∧
    out.suspended = entry.suspended) ∨
  (∃ error store, out.current.status = .returned (.fail error) store) ∨
  (∃ store, out.current.status = .returned .div store) ∨
  (∃ fault store, out.current.status = .fault fault store) ∨
  ∃ address store, out.current.status = .undefined address store

def ConsumedPending (m : Machine) (q : State) : Prop :=
  ∃ c wait, q.current.status = .running c ∧ c.frame.completed = none ∧
    c.frame.waiting = some wait ∧ PV_THR2_Catch316Segment.select c = none ∧
    (match wait.request with
      | .child fn _ _ => m.programs fn = none
      | _ => True) ∧
    (m.handler wait.request q.current.world).answer = .pending ∧
    ∃ after, (step m q).current.status = .running after ∧
      after.frame.completed = none ∧ after.frame.waiting = some wait

/-- A finite boundary is indexed by the trace, allowing a D877 caller and an
expanded execution to use different numbers of administrative transitions. -/
def Boundary (m : Machine) (entry : State) (trace : Nat → State) (n : Nat) : Prop :=
  OwnComplete entry (trace n) ∨ Terminal entry (trace n) ∨
    ∃ k, n = k+1 ∧ ConsumedPending m (trace k) ∧ trace n = step m (trace k)

def First (m : Machine) (entry : State) (trace : Nat → State) (n : Nat) : Prop :=
  Boundary m entry trace n ∧ ∀ k, k < n → ¬ Boundary m entry trace k

def Diverges (m : Machine) (entry : State) (trace : Nat → State) : Prop :=
  ∀ n, ¬ Boundary m entry trace n

/-- The immutable source reference is independent of the candidate trace.
Machine/leaf adequacy is a separate specification, never a desired Post field. -/
def reference (m : Machine) (entry : State) : Nat → State :=
  fun n => run m n entry

/-- All finite answers compare exact source status/value, cells, backend,
ownership and events, erasing abort state and administrative counters. Infinite
executions compare every observable event prefix in both directions. Frame
and typed row-value clauses are additional row-specific conjuncts. -/
def BehavioralPost (m : Machine) (entry : State) (candidate : Nat → State) : Prop :=
  (∃ n k, First m entry (reference m entry) n ∧ First m entry candidate k ∧
    observe (candidate k) = observe (reference m entry n)) ∨
  (Diverges m entry (reference m entry) ∧ Diverges m entry candidate ∧
    (∀ n, ∃ k, (candidate n).current.events = (reference m entry k).current.events) ∧
    (∀ k, ∃ n, (reference m entry k).current.events = (candidate n).current.events))

/-- Exact target for a source implementation's trace projection. No equality
is presumed merely because the reference interpreter has been defined. -/
def SourceAdequacy (m : Machine) (entry : State) (sourceTrace : Nat → State) : Prop :=
  BehavioralPost m entry sourceTrace

theorem abort_prefix (s : Store Data) (w : PV_EVHB_OwnerMachine.OWNER)
    (es : List Event) (stack : List Config) :
    observe ⟨⟨.fault .abort s,w,es⟩,stack⟩ = .abort es := rfl

theorem counter_irrelevant (s : Store Data) (n : Nat) :
    storeView {s with nextActivation := n} = storeView s := rfl

#print axioms storeView
#print axioms configView
#print axioms statusView
#print axioms Observation
#print axioms observe
#print axioms Numbered
#print axioms OwnComplete
#print axioms Terminal
#print axioms ConsumedPending
#print axioms Boundary
#print axioms First
#print axioms Diverges
#print axioms reference
#print axioms BehavioralPost
#print axioms SourceAdequacy
#print axioms abort_prefix
#print axioms counter_irrelevant
end PV_LIB_SPEC_ThreadContract
