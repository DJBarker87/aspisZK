import PV_FN_THREAD_f6Interfaces
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Joins
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces

/-- Delivery to the actual immediate caller. Non-success adoption retains the
saved request and marks that caller completed; successful adoption clears it.
Terminal outcomes retain their exact status, store, world and events in q.
No instruction of the resumed caller belongs to this row. -/
def Delivered {E : Type} (x : Entry E)
    (q : PV_THR2_IntrinsicState.State OWNER E) : Prop :=
  Returned x q ∨
  (∃ c outcome, q.current.status = .running c ∧
    c.frame = {x.parent with completed := some outcome} ∧
    c.callers = x.parents ∧ q.suspended = x.suspended) ∨
  (match q.current.status with
    | .returned (.ok _) _ => q.suspended = x.suspended
    | .returned _ _ => True
    | .fault _ _ => True
    | _ => False)

/-- A pending answer ends obligations AFTER its actual step, retaining the
answer's world/events. A structured call and the higher-order catch dispatch
are not native replies. The preceding configuration must issue this request;
no restriction on the reply domain is imposed. -/
def PendingDelivery {E : Type} (M : Machine E) (x : Entry E) (n : Nat) : Prop :=
  ∃ k c wait, n = k+1 ∧ (run M x k).current.status = .running c ∧
    c.frame.completed = none ∧ c.frame.waiting = some wait ∧
    PV_THR2_Catch316Segment.select c = none ∧
    (match wait.request with
      | .child fn _ _ => M.programs fn = none
      | _ => True) ∧
    (M.handler wait.request (run M x k).current.world).answer = .pending

/-- Includes the first delivery/pending prefix; excludes every later prefix. -/
def BeforeDelivery {E : Type} (M : Machine E) (x : Entry E) (n : Nat) : Prop :=
  ∀ m, m < n → ¬ (Delivered x (run M x m) ∨ PendingDelivery M x m)

/-- Full status/store/world/events are the actual run at the selected prefix,
including the first outcome delivery or post-pending state. No success-only
reply restriction, lower-stack validity or eventual loop exit is assumed.
The historical BeforeReturn/FullPost remain unchanged for the checked D933
counterexample and already-audited provider interfaces. -/
def FullPost {E : Type} (M : Machine E) (x : Entry E)
    (valuePost : Store Data → OWNER → Data → Prop) : Prop :=
  ∀ n, BeforeDelivery M x n →
    let q := run M x n
    let s := statusStore q.current.status
    Defined q.current.status ∧ StoreFrame M x s ∧ OwnerFrame M x q.current.world ∧
    OwnerWellFormed q.current.world s.nextActivation ∧
    (∃ suffix, q.current.events = x.events ++ suffix) ∧
    (∀ v c, q.current.status = .running c →
      c.frame.activation = x.activation → c.frame.completed = some (.ok v) →
      valuePost s q.current.world v) ∧
    (∀ v c, q.current.status = .running c → c.frame = {x.parent with waiting := none} →
      c.callers = x.parents → s.cells ⟨x.parent.activation,x.dest,[]⟩ = some v →
      q.suspended = x.suspended → valuePost s q.current.world v)

/-- f6's revised value statement, over the same original run and callback. -/
def Post {E : Type} (M : Machine E) (x : Entry E) : Prop :=
  FullPost M x (fun _ _ value =>
    ∃ n c result, BeforeDelivery M x n ∧ (run M x n).current.status = .running c ∧
      c.frame.activation = x.activation ∧ c.frame.remaining = PV_THR2_F6.live.body.drop 46 ∧
      c.store.cells ⟨x.activation,10,[]⟩ = some result ∧
      M.control.variant result = some 0 ∧ M.carrier.field result 0 = some value)

/-- Boundary monotonicity used in prefix induction. -/
theorem before_delivery_mono {E : Type} (M : Machine E) (x : Entry E)
    (n k : Nat) (before : BeforeDelivery M x n) (le : k ≤ n) :
    BeforeDelivery M x k := by
  intro m lt
  exact before m (Nat.lt_of_lt_of_le lt le)

/-- The first delivered state itself is included, and its successor is excluded.
This concerns only the boundary; it asserts no unproved frame or row contract. -/
theorem delivery_stops {E : Type} (M : Machine E) (x : Entry E) (n : Nat)
    (delivered : Delivered x (run M x n)) : ¬ BeforeDelivery M x (n+1) := by
  intro before
  exact before n (Nat.lt_succ_self n) (Or.inl delivered)

#print axioms Delivered
#print axioms PendingDelivery
#print axioms BeforeDelivery
#print axioms FullPost
#print axioms Post
#print axioms before_delivery_mono
#print axioms delivery_stops
end PV_FN_THREAD_f6Joins
