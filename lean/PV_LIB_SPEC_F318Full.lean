import PV_LIB_SPEC_F316Full
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F318Full
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- An intrinsic has no fabricated emitted frame. Its entry is its immediate
caller's ACTUAL318 waiting configuration; the reserved activation is in the
issued request, not a supplied callback-result state. -/
def entry (i : Input) : State :=
  ⟨⟨.running ⟨i.parent,i.parents,i.store⟩,i.world,i.events⟩,i.suspended⟩
def Pre (r : Runtime) (i : Input) : Prop :=
  (∃ data, i.arguments = [(PV_THR2_Catch219Callbacks.token false).2,data,
    (PV_THR2_Catch219Callbacks.token true).2]) ∧
  i.parent.waiting = some i.waiting ∧
  i.waiting.request = .child PV_THR2_Catch219Call318.fn i.activation i.arguments ∧
  i.waiting.action = .child i.activation (.local i.destination) ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.store.nextActivation ∧
  RegisteredValidity i.world ∧ Numbered (entry i) ∧ ReferenceEntry r i
/-- Delivery to THIS intrinsic's caller; never continue through the caller's
remaining source instructions. Nested316 completion is not318 completion. -/
def Delivered (i : Input) (q : State) : Prop :=
  ∃ s, q.current.status = .running
    ⟨{i.parent with waiting := none},i.parents,s⟩ ∧ q.suspended = i.suspended

def Boundary (m : Machine) (i : Input) (trace : Nat → State) (n : Nat) : Prop :=
  Delivered i (trace n) ∨ Terminal (entry i) (trace n) ∨
    ∃ k, n = k+1 ∧ ConsumedPending m (trace k) ∧ trace n = step m (trace k)
def First (m : Machine) (i : Input) (trace : Nat → State) (n : Nat) : Prop :=
  Boundary m i trace n ∧ ∀ k, k < n → ¬ Boundary m i trace k
/-- Run do_call316 ONCE under the OWNER-aware intrinsic interception. Compare
its real output cell/success code and full world/events; retain all stopped
branches, panic=abort and actual pending inside the callback. Abort exposes
only its prefix; an infinite execution compares every observable finite prefix. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  let m := PV_LIB_SPEC_Full.source table r
  let ref := fun n => run m n (entry i)
  ((∃ n k, First m i ref n ∧ First m i candidate k ∧
      observe (candidate k) = observe (ref n)) ∨
    ((∀ n, ¬ Boundary m i ref n) ∧ (∀ k, ¬ Boundary m i candidate k) ∧
      (∀ n, ∃ k, (ref n).current.events = (candidate k).current.events) ∧
      (∀ k, ∃ n, (ref n).current.events = (candidate k).current.events))) ∧
  ∀ k, (∀ j, j < k → ¬ Boundary m i candidate j) →
    match (candidate k).current.status with
    | .fault .abort _ => True
    | _ => PV_LIB_SPEC_ThreadRow.Frame r i (candidate k)
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)
/-- The package has a callback-selection statement, not a full intrinsic
contract. Retain that exact proposition separately from the new whole Post. -/
def PackageStatement : Prop := ∀ (s : Store Data) (a : Nat) (parents : List Frame),
  PV_THR2_Catch316Segment.select (PV_THR2_Catch219Call318.pending s a parents) =
    some (PV_THR2_CallbackSegment.enter (PV_THR2_Catch219Call318.pending s a parents)
      PV_THR2_F316.live [PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null])
def Comparison (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  PackageStatement ∧ Contract table r implementation
#print axioms MachineSpec
#print axioms entry
#print axioms Pre
#print axioms Delivered
#print axioms Boundary
#print axioms First
#print axioms Post
#print axioms Contract
#print axioms PackageStatement
#print axioms Comparison
end PV_LIB_SPEC_F318Full
