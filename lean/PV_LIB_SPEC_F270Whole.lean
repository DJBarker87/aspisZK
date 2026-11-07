import PV_LIB_SPEC_F361Whole
import PV_FN_THREAD_f270SummaryRun
import PV_THR2_TypedRepresentation_Builder
set_option autoImplicit false
noncomputable section

namespace PV_LIB_SPEC_Row
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984
/-- Source-model data, fixed before a row is invoked. The fallback is the
library's emitted-body/native table; its source association is an adequacy
obligation, not an arbitrary replacement at a call. -/
structure Runtime where
  carrier : Carrier OWNER Data
  control : Control
  fallback : Data → Option PV_STX2_SliceSyntax.Program
  native : Handler
  resources : Resources
  encode : Encode

structure Input where
  store : Store Data
  activation : Nat
  arguments : List Data
  parent : Frame
  parents : List Frame
  destination : Nat
  waiting : PV_STX2_Native.Waiting Data
  world : OWNER
  events : List Event
  suspended : List Config

def entry (body : PV_STX2_SliceSyntax.Program) (i : Input) : State :=
  ⟨⟨.running ⟨{activation := i.activation,remaining := body.body},
    i.parent :: i.parents,i.store⟩,i.world,i.events⟩,i.suspended⟩

def source (table : FullStoreActionTable) (r : Runtime) : Machine :=
  ⟨r.carrier,r.control,programs r.fallback,r.native,r.resources,r.encode,table⟩

def MachineSpec (table : FullStoreActionTable) (r : Runtime) (m : Machine) : Prop :=
  m.carrier = r.carrier ∧ m.control = r.control ∧ m.programs = programs r.fallback ∧
  m.handler = r.native ∧ @m.resources = @r.resources ∧ @m.encode = @r.encode ∧
  m.storeActions = table

/-- Entry argument/field/pointee reachability, never a set chosen from a
future return. Includes references inside moved closure captures. -/
inductive Reachable (r : Runtime) (i : Input) : Data → Prop where
  | argument {v} : v ∈ i.arguments → Reachable r i v
  | field {v child} (n : Nat) : Reachable r i v →
      r.carrier.field v n = some child → Reachable r i child
  | pointee {v p child} : Reachable r i v →
      r.carrier.dereference i.world v = some p →
      readAddress r.carrier i.store p = some child → Reachable r i child

/-- Every represented source reference has initialized source contents and an
entry-selected registered region covering its path. Physical non-null,
alignment and extent are checked against the actual registered descriptor,
including references to empty regions. No writable/disjointness is invented
for shared references; exact writes are in the source body/action table. -/
def ReferenceEntry (r : Runtime) (i : Input) : Prop :=
  ∀ v p, Reachable r i v → r.carrier.dereference i.world v = some p →
    (∃ value, readAddress r.carrier i.store p = some value) ∧
    ∃ (place : PV_EVHB_SourceLifetimes.Place) (id : Nat)
      (header : PV_EVHB_RawVecOwner.Header) (suffix : List Nat),
      p.activation = place.activation ∧ p.localIndex :: p.fields = place.fields ++ suffix ∧
      receiver i.world place = some (id,header) ∧
      header.pointer ≠ 0 ∧
      header.pointer % PV_EVHB_OwnerReserve.alignment header.shape.align = 0 ∧
      header.len ≤ header.cap ∧ header.pointer + header.cap*header.shape.width ≤ 2^64

/-- Whole own-entry invariant, with no constraints on the CODE of lower
continuations and no success/read/decode/callee-Post premise. nextActivation
is bounded, never equated across a callee boundary. -/
def Pre (body : PV_STX2_SliceSyntax.Program) (arity : Nat) (r : Runtime) (i : Input) : Prop :=
  i.arguments.length = arity ∧
  (∀ n v, i.arguments[n]? = some v → i.store.cells ⟨i.activation,n+1,[]⟩ = some v) ∧
  i.parent.waiting = some i.waiting ∧
  i.waiting.action = .child i.activation (.local i.destination) ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.store.nextActivation ∧
  RegisteredValidity i.world ∧ Numbered (entry body i) ∧ ReferenceEntry r i

def leafEntry (i : Input) : PV_W1_LeafBoundary.Entry :=
  ⟨i.store,i.activation,i.parent :: i.parents,[],[],.null,
    i.arguments,i.destination,i.suspended⟩

/-- Source-cell frame on the actual argument footprint. Exact byte/header,
OWNER, backend and result fields are additionally compared by Behavior.
Lower continuations are retained without inspecting their source code. -/
def Frame (r : Runtime) (i : Input) (q : State) : Prop :=
  let s := PV_W1_LeafBoundary.statusStore q.current.status
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed q.current.world s.nextActivation ∧
  Numbered q ∧ q.suspended = i.suspended ∧
  (∃ suffix, q.current.events = i.events ++ suffix) ∧
  ∀ p : Address, p.activation < i.activation →
    p ≠ ⟨i.parent.activation,i.destination,[]⟩ →
    ¬ PV_W1_ArgumentEffects.Writable r.carrier (leafEntry i) i.world p →
      s.cells p = i.store.cells p

/-- All prefixes through FIRST own completion/delivery/consumed pending, with
no post-abort state. Divergence retains every observable finite prefix. -/
def Post (table : FullStoreActionTable) (r : Runtime)
    (body : PV_STX2_SliceSyntax.Program) (i : Input) (candidate : Nat → State) : Prop :=
  Behavior (source table r) (entry body i) candidate ∧
  ∀ k, (∀ j, j < k → ¬ Boundary (source table r) (entry body i) candidate j) →
    match (candidate k).current.status with
    | .fault .abort _ => True
    | _ => Frame r i (candidate k)

/-- Actual source/runtime adequacy remains separate from every row's Pre.
The endpoint may not acquire this as a new trust item. -/
def SourceAdequacy (table : FullStoreActionTable) (r : Runtime)
    (body : PV_STX2_SliceSyntax.Program) (arity : Nat)
    (actual : Input → Nat → State) : Prop :=
  ∀ i, Pre body arity r i → Post table r body i (actual i)

#print axioms Runtime
#print axioms Input
#print axioms entry
#print axioms source
#print axioms MachineSpec
#print axioms Reachable
#print axioms ReferenceEntry
#print axioms Pre
#print axioms Frame
#print axioms Post
#print axioms SourceAdequacy
end PV_LIB_SPEC_Row

namespace PV_LIB_SPEC_F270Whole
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Row.MachineSpec

def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F270.live 3 r i ∧
  ∃ builder scope closure, i.arguments = [builder,scope,closure] ∧
    PV_THR2_TypedRepresentation_Builder.Shape builder ∧
    ∃ threadName stackSize noHooks,
      r.carrier.field builder 0 = some threadName ∧
      r.carrier.field builder 1 = some stackSize ∧
      r.carrier.field builder 2 = some noHooks

/-- Entire spawn_scoped body: Builder fields, actual Scope Arc clone, moved
closure, full f361 Result and source handle construction, all earlier stops. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Row.Post table r PV_THR2_F270.live i candidate

def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

/-- Literal existing package statement. It is only a caller-prefix theorem
through f361's summary, not a full row Post. No implication from it to Contract
is asserted. Comparison keeps both complete formulas with the SAME entry. -/
def PackageStatement (r : Runtime) (i : Input) : Prop :=
  PV_THR2_IntrinsicState.advance r.carrier r.control PV_FN_THREAD_f270SummaryRun.programs
    r.native (PV_FN_THREAD_f270SummaryRun.steps r.carrier r.native
      (PV_LIB_SPEC_Row.entry PV_THR2_F270.live i))
    (PV_LIB_SPEC_Row.entry PV_THR2_F270.live i) =
    PV_FN_THREAD_f270SummaryRun.after r.carrier r.native
      (PV_LIB_SPEC_Row.entry PV_THR2_F270.live i)

def Comparison (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  (∀ i, PackageStatement r i) ∧ Contract table r implementation

#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms PackageStatement
#print axioms Comparison
end PV_LIB_SPEC_F270Whole
