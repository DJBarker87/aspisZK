import PV_LIB_SLICE_Spec_f21
import PV_STX2_Source7LoopInvariant
set_option autoImplicit false
noncomputable section
/-! Frozen SLICE-PATH statements. No Contract inhabitant is asserted.
All source interpretation remains conditional on the recorded translator patch.
The same named OWNER/copy/set_len machine is used for every row. -/
namespace PV_LIB_SLICE_Statements
open scoped Classical
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
abbrev Machine := PV_LIB_SLICE_Spec_f21.Machine
abbrev Environment := PV_LIB_SLICE_Spec_f21.Environment
abbrev MachineSpec := PV_LIB_SLICE_Spec_f21.MachineSpec
abbrev Outcome := PV_LIB_SLICE_Spec_f21.Outcome
abbrev Event := PV_LIB_SLICE_Spec_f21.Event

structure Entry where
  store : Store Data
  parents : List Frame
  owner : OWNER
  prior : List Event
  suspended : List Config

/-- Arguments are constructed by each row from its entry-selected operands.
Only the new own activation is allocated; lower code is arbitrary. -/
def start (p : PV_STX2_SliceSyntax.Program) (args : List Data) (e : Entry) : Config :=
  {enter p args e.store with callers := e.parents}

def execution (r : Resources) (enc : Encode) (m : Machine) (c : Config) (e : Entry)
    (n : Nat) : Prefix OWNER Event :=
  PV_STX2_ToVecZeroAdvance.advance r enc m.carrier m.control m.programs m.handler n
    ⟨.running c,e.owner,e.prior⟩

structure Pre (c : Config) (e : Entry) : Prop where
  numbered : PV_STX2_LiveNumbering.Numbered c
  suspended : ∀ q ∈ e.suspended, PV_STX2_LiveNumbering.Numbered q
  owner : PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed e.owner c.store.nextActivation

/-- Fixed before execution, including the actual descriptor address and id. -/
structure Source where
  descriptor : Address
  region : Vec PV_OWN2_Codec.M31
  identity : Nat
  header : Header

def vector (h : Header) : Data :=
  PV_STX2_SliceToVecFinish.vector
    (PV_STX2_Aggregates.pack PV_STX2_Source7QHeaderStep.kind
      [PV_STX2_Source7QHeaderOperands.pointerValue h.pointer,.number h.cap,
        PV_STX2_Source7GlobalClone.value]) (.number h.len)

def Source.Valid (m : Machine) (c : Config) (e : Entry) (s : Source) : Prop :=
  PV_STX2_ToVecCallReferenceEntry.Pre e.owner c.store ⟨0,s.header.pointer,[]⟩
    s.region.values.length s.region s.identity s.header ∧
  readAddress m.carrier c.store s.descriptor = some (vector s.header) ∧
  s.descriptor.activation < c.frame.activation ∧
  s.region.values.length < PV_STX2_Source7CapacityScalars.modulus

/-- Actual post-set_len representation and fresh, disjoint provider ownership. -/
def Clone (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (e : Entry) (s : Source) (out : Prefix OWNER Event) (v : Data) : Prop :=
  ∃ q id h, e.owner.next ≤ id ∧ receiver out.world q = some (id,h) ∧
    h.len = s.region.values.length ∧ h.cap = s.region.values.length ∧ v = vector h ∧
    (h.len = 0 → h.pointer = 4 ∧ h.dangling = true) ∧
    PV_OWN2_ExportContracts.VecOwnership (Attr := Unit) (Data := Data) (Native := Unit)
      (IoError := Unit) (OsString := Unit) (Scope := Unit) r enc g out.world
      s.region q s.identity id s.header h ∧
    (∀ offset, offset < h.len*4 → out.world.world.memory (h.pointer+offset) =
      e.owner.world.memory (s.header.pointer+offset))

def Pending (r : Resources) (enc : Encode) (m : Machine) (c0 : Config) (e : Entry)
    (n : Nat) : Prop :=
  ∃ k c w events wait, n = k+1 ∧ execution r enc m c0 e k = ⟨.running c,w,events⟩ ∧
    c.frame.completed = none ∧ c.frame.waiting = some wait ∧
    (match wait.request with | .child f _ _ => m.programs f = none | _ => True) ∧
    (PV_STX2_Source7IterationHandler.handler r enc c m.handler wait.request w).answer = .pending

def Boundary (r : Resources) (enc : Encode) (m : Machine) (c0 : Config) (e : Entry)
    (n : Nat) : Prop :=
  match (execution r enc m c0 e n).status with
  | .fault _ _ => True
  | .running c =>
      (c.frame.activation = c0.frame.activation ∧ c.callers = c0.callers ∧
        ∃ result, c.frame.completed = some result) ∨ Pending r enc m c0 e n
  | _ => False

def First (r : Resources) (enc : Encode) (m : Machine) (c : Config) (e : Entry)
    (n : Nat) : Prop :=
  Boundary r enc m c e n ∧ ∀ k, k < n → ¬ Boundary r enc m c e k

def reference (r : Resources) (enc : Encode) (m : Machine) (c : Config) (e : Entry) : Outcome :=
  if h : ∃ n, Boundary r enc m c e n then
    .finite (PV_LIB_SLICE_Spec_f21.observe e.suspended (execution r enc m c e (Nat.find h)))
  else .infinite (fun n => PV_LIB_SLICE_Spec_f21.observe e.suspended (execution r enc m c e n))

/-- Mutable footprint is the row's actual capture/buffer root, selected by its
entry reference. Address roots, rather than whole Store/counter equality. -/
def inRoot (root q : Address) : Prop :=
  q.activation = root.activation ∧ q.localIndex = root.localIndex

def freshByte (r : Resources) (enc : Encode) (m : Machine) (c : Config) (e : Entry)
    (n address : Nat) : Prop :=
  ∃ k, k ≤ n ∧ ∃ pointer allocation,
    e.owner.world.allocator.metadata pointer = none ∧
    (execution r enc m c e k).world.world.allocator.metadata pointer = some allocation ∧
    pointer ≤ address ∧ address < pointer + allocation.bytes

/-- Complete non-abort frame, including old heap, registry, descriptors,
shared bytes and lower/suspended continuations (the latter in observation).
Fresh cells are restricted by activation; mutations by actual argument roots. -/
def Frame (r : Resources) (enc : Encode) (m : Machine) (c0 : Config) (e : Entry)
    (sources : List Source) (mutable : List Address) (n : Nat) : Prop :=
  let out := execution r enc m c0 e n
  match out.status with
  | .fault .abort _ => True
  | _ =>
    let s := PV_STX2_ToVecCallCallerPost.statusStore out.status
    (∀ q : Address, q.activation < c0.frame.activation →
      (∀ root ∈ mutable, ¬ inRoot root q) →
      s.cells q = c0.store.cells q) ∧
    (∀ address, ¬ freshByte r enc m c0 e n address →
      out.world.world.memory address = e.owner.world.memory address) ∧
    (∀ q id, e.owner.places q = some id → out.world.places q = some id) ∧
    (∀ id h, lookup e.owner.world id = some h → lookup out.world.world id = some h) ∧
    (∀ src ∈ sources,
      readAddress m.carrier s src.descriptor = readAddress m.carrier c0.store src.descriptor ∧
      ∀ offset, offset < src.region.values.length*4 →
        out.world.world.memory (src.header.pointer+offset) =
          e.owner.world.memory (src.header.pointer+offset)) ∧
    PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed out.world s.nextActivation ∧
    (∀ c, out.status = .running c → PV_STX2_LiveNumbering.Numbered c ∧
      ∃ upper, c.callers = upper ++ c0.callers)

/-- All Result payloads and every effect are fixed by the reference; the
additional value clause is only for returned Ok. No error is dropped or reset.
Undefined representations are adequacy failures. Abort has only events. -/
def Post (r : Resources) (enc : Encode) (m : Machine) (c : Config) (e : Entry)
    (sources : List Source) (mutable : List Address)
    (success : Prefix OWNER Event → Data → Prop) (impl : Outcome) : Prop :=
  impl = reference r enc m c e ∧
  (∀ n, (∀ k, k < n → ¬ Boundary r enc m c e k) →
    ¬ ∃ a s, (execution r enc m c e n).status = .undefined a s) ∧
  (∀ n, First r enc m c e n →
    let out := execution r enc m c e n
    (∃ suffix, out.events = e.prior ++ suffix) ∧ Frame r enc m c e sources mutable n ∧
    (∀ d v, out.status = .running d → d.frame.completed = some (.ok v) → success out v))

#print axioms Source.Valid
#print axioms Clone
#print axioms Pending
#print axioms Boundary
#print axioms reference
#print axioms Frame
#print axioms Post
end PV_LIB_SLICE_Statements

namespace PV_LIB_SLICE_Spec_f13
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
open PV_LIB_SLICE_Statements
structure Entry extends PV_LIB_SLICE_Statements.Entry where
  source : Source
abbrev MachineSpec := PV_LIB_SLICE_Statements.MachineSpec
abbrev start (e : Entry) := PV_LIB_SLICE_Statements.start PV_STX2_SliceF13.program
  [PV_STX2_TypedReferences.reference e.source.descriptor .null] e.toEntry

def Pre (m : Machine) (e : Entry) : Prop :=
  PV_LIB_SLICE_Statements.Pre (start e) e.toEntry ∧ e.source.Valid m (start e) e.toEntry

def Post (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (m : Machine) (e : Entry) (impl : Outcome) : Prop :=
  PV_LIB_SLICE_Statements.Post r enc m (start e) e.toEntry [e.source] []
    (Clone r enc g e.toEntry e.source) impl

def Contract (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (env : Environment) (impl : Machine → Entry → Outcome) : Prop :=
  ∀ m, MachineSpec m base ctrl external backend r enc env → ∀ e, Pre m e → Post r enc g m e (impl m e)
#print axioms Pre
#print axioms MachineSpec
#print axioms Post
#print axioms Contract
end PV_LIB_SLICE_Spec_f13
