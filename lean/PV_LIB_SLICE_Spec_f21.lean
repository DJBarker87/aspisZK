import PV_STX2_ToVecCallPendingDiagnostic
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_Spec_f21
open scoped Classical
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
namespace Old
abbrev Machine := PV_STX2_ToVecCallSummary.Machine
abbrev Entry := PV_STX2_ToVecCallSummary.Entry
end Old
abbrev Event := PV_RJ4IDB.NativeEvent
abbrev Machine := Old.Machine
/-- The suspended context is an entry component, independent of ordinary callers. -/
structure Entry extends Old.Entry where
  suspended : List Config

instance : Coe Entry Old.Entry := ⟨Entry.toEntry⟩

abbrev start (e : Entry) := PV_STX2_ToVecCallSummary.start e.toEntry
abbrev execution (resources : Resources) (encode : Encode) (m : Machine) (e : Entry) :=
  PV_STX2_ToVecCallSummary.execution resources encode m e.toEntry

/-- All package validity clauses at the SAME selected source header, plus
numbering of every suspended live configuration. -/
structure Pre (e : Entry) : Prop extends PV_STX2_ToVecCallSummary.Pre e.toEntry where
  suspended : ∀ c ∈ e.suspended, PV_STX2_LiveNumbering.Numbered c

/-- Source site, occurrence, exact request arguments and pre-world. f21 has one
infallible allocation path through f59/s1683; reservation is a distinct channel
and has no reached site in this closure. Neither channel selects success. -/
structure ResourceRequest where
  function : Nat
  statement : Nat
  occurrence : Nat
  identity : Nat
  arguments : List Data
  before : OWNER

structure Environment where
  allocation : ResourceRequest → Reply OWNER Event Nat
  reservation : ResourceRequest → Reply OWNER Event Data

/-- Literal provider equations plus the explicit binding of the actual counted
malloc primitive to its source-associated environment channel. This is an
interpretation equation for ALL replies, not a successful allocation premise. -/
structure MachineSpec (m : Machine) (base : Carrier PV_STX_World.World Data)
    (ctrl : Control) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (resources : Resources) (encode : Encode)
    (env : Environment) : Prop extends
    PV_STX2_ToVecCallSummary.MachineSpec m base ctrl external backend where
  allocation : ∀ id bytes w,
    PV_EVHB_AttemptAccounting.primitive resources encode id (.malloc bytes) w =
      env.allocation ⟨59,1683,0,id,[.number bytes,.number 4],w⟩

/-- The actual consumed reply: a completed frame is administered without
polling; a structured child is pushed without consuming the fallback reply. -/
def Pending (resources : Resources) (encode : Encode) (m : Machine) (e : Entry)
    (fuel : Nat) (out : Prefix OWNER Event) : Prop :=
  ∃ k c w events waiting,
    fuel = k+1 ∧ execution resources encode m e k = ⟨.running c,w,events⟩ ∧
    c.frame.completed = none ∧ c.frame.waiting = some waiting ∧
    (match waiting.request with
      | .child callee _ _ => m.programs callee = none
      | _ => True) ∧
    (PV_STX2_Source7IterationHandler.handler resources encode c m.handler
      waiting.request w).answer = .pending ∧
    out = execution resources encode m e (k+1)

def Boundary (resources : Resources) (encode : Encode) (m : Machine) (e : Entry)
    (fuel : Nat) (out : Prefix OWNER Event) : Prop :=
  match out.status with
  | .undefined _ _ | .returned _ _ => False
  | .fault _ _ => True
  | .running c =>
    (c.frame.activation = (start e).frame.activation ∧ c.callers = (start e).callers ∧
      ∃ result, c.frame.completed = some result) ∨
    Pending resources encode m e fuel out

def First (resources : Resources) (encode : Encode) (m : Machine) (e : Entry)
    (fuel : Nat) : Prop :=
  Boundary resources encode m e fuel (execution resources encode m e fuel) ∧
    ∀ k, k < fuel → ¬ Boundary resources encode m e k (execution resources encode m e k)

/-- Counter abstraction is observational only; raw runs retain live numbering. -/
def storeView (s : Store Data) : Store Data := {s with nextActivation := 0}
def statusView : Status → Status
  | .running c => .running {c with store := storeView c.store}
  | .returned r s => .returned r (storeView s)
  | .fault f s => .fault f (storeView s)
  | .undefined a s => .undefined a (storeView s)
inductive Observation where
  | state : Prefix OWNER Event → List Config → Observation
  | abort : List Event → Observation

def observe (suspended : List Config) (q : Prefix OWNER Event) : Observation :=
  match q.status with
  | .fault .abort _ => .abort q.events
  | _ => .state {q with status := statusView q.status}
      (suspended.map (fun c => {c with store := storeView c.store}))

/-- Includes exact every-prefix behavior when there is no finite boundary. -/
inductive Outcome where
  | finite : Observation → Outcome
  | infinite : (Nat → Observation) → Outcome

/-- A deterministic reference, independent of the candidate implementation.
No successful allocation, finite-fuel, or future-read assumption is used. -/
def reference (resources : Resources) (encode : Encode) (m : Machine) (e : Entry) : Outcome :=
  if h : ∃ n, Boundary resources encode m e n (execution resources encode m e n) then
    .finite (observe e.suspended (execution resources encode m e (Nat.find h)))
  else .infinite (fun n => observe e.suspended (execution resources encode m e n))

/-- Abort has no post-state frame. All other finite arms use the provider's
literal cells, registry, header, validity, numbering and source-byte clauses. -/
def Frame (e : Entry) (out : Prefix OWNER Event) : Prop :=
  match out.status with
  | .fault .abort _ => True
  | _ =>
    (∀ q : Address, q.activation < (start e).frame.activation →
      (PV_STX2_ToVecCallCallerPost.statusStore out.status).cells q = (start e).store.cells q) ∧
    (∀ q id, e.owner.places q = some id → out.world.places q = e.owner.places q) ∧
    (∀ q id, e.owner.places q = some id → lookup out.world.world id = lookup e.owner.world id) ∧
    PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed out.world
      (PV_STX2_ToVecCallCallerPost.statusStore out.status).nextActivation ∧
    (∀ c, out.status = .running c → PV_STX2_LiveNumbering.Numbered c)

/-- Exact source-encoded final value, tied to the SAME fresh header and
entry-selected source region. Unlike the package Success.vector, the final
Vec contains the post-set_len length rather than construction-time zero. -/
def Success (resources : Resources) (encode : Encode)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions) (e : Entry)
    (out : Prefix OWNER Event) (value : Data) : Prop :=
  ∃ id h,
    e.owner.next ≤ id ∧
    receiver out.world (PV_STX2_Source7QBinding.ownerPlace
      ⟨(start e).frame.activation,0,[]⟩) = some (id,h) ∧
    h.len = e.length ∧ h.cap = e.length ∧
    value = PV_STX2_SliceToVecFinish.vector
      (PV_STX2_Aggregates.pack PV_STX2_Source7QHeaderStep.kind
        [PV_STX2_Source7QHeaderOperands.pointerValue h.pointer,.number h.cap,
          PV_STX2_Source7GlobalClone.value]) (.number e.length) ∧
    (e.length = 0 → h.pointer = 4 ∧ h.dangling = true) ∧
    PV_OWN2_ExportContracts.VecOwnership (Attr := Unit) (Data := Data) (Native := Unit)
      (IoError := Unit) (OsString := Unit) (Scope := Unit) resources encode granted out.world
      e.region (PV_STX2_Source7QBinding.ownerPlace ⟨(start e).frame.activation,0,[]⟩)
      e.sourceId id e.sourceHeader h ∧
    (∀ offset, offset < e.length*4 →
      out.world.world.memory (h.pointer+offset) =
        e.owner.world.memory (e.sourceHeader.pointer+offset))

/-- The M31 source is shared, including on all non-success outcomes. -/
def SourceFrame (e : Entry) (out : Prefix OWNER Event) : Prop :=
  match out.status with
  | .fault .abort _ => True
  | _ => ∀ offset, offset < e.length*4 →
      out.world.world.memory (e.sourceHeader.pointer+offset) =
        e.owner.world.memory (e.sourceHeader.pointer+offset)

/-- Decode only the final Vec length slot, retaining the provider's pack
representation. Used to compare actual statement syntax, not a new codec. -/
def encodedLength : Data → Option Nat
  | .object [("aggregate-kind",_),("aggregate-slots",.array [_,.array [.number n]])] => some n
  | _ => none

theorem final_length (inner : Data) (n : Nat) :
    encodedLength (PV_STX2_SliceToVecFinish.vector inner (.number n)) = some n := rfl

theorem construction_length (inner : Data) :
    encodedLength (PV_STX2_SliceToVecConstruct.vector inner) = some 0 := rfl

/-- Literal checked defect in the package statement: its successful-value
shape forces construction-time length zero, even after a positive set_len. -/
theorem package_success_forces_zero (resources : Resources) (encode : Encode)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions) (e : Entry)
    (out : Prefix OWNER Event) (inner : Data) (n : Nat)
    (h : PV_STX2_ToVecCallSummary.Success resources encode granted e out
      (PV_STX2_SliceToVecFinish.vector inner (.number n))) : n = 0 := by
  obtain ⟨other,eqn⟩ := h.vector
  exact Option.some.inj (congrArg encodedLength eqn)

/-- Full heap frame: only a source-defined fresh allocation reached in this
invocation may receive writes. The trace uses allocator metadata, never a
caller-supplied footprint or a desired memory-equality premise. -/
def FreshByte (resources : Resources) (encode : Encode) (m : Machine) (e : Entry)
    (fuel address : Nat) : Prop :=
  ∃ k, k ≤ fuel ∧ ∃ pointer allocation,
    e.owner.world.allocator.metadata pointer = none ∧
    (execution resources encode m e k).world.world.allocator.metadata pointer = some allocation ∧
    pointer ≤ address ∧ address < pointer + allocation.bytes

/-- No post-abort heap or continuation is observable. At an own completion
or nested pending poll, the original lower callers remain an exact suffix. -/
def FullFrame (resources : Resources) (encode : Encode) (m : Machine) (e : Entry)
    (fuel : Nat) (out : Prefix OWNER Event) : Prop :=
  match out.status with
  | .fault .abort _ => True
  | _ =>
    (∀ address, ¬ FreshByte resources encode m e fuel address →
      out.world.world.memory address = e.owner.world.memory address) ∧
    (∀ c, out.status = .running c → ∃ upper, c.callers = upper ++ (start e).callers)

/-- Complete statement only. Primitive adequacy, D877 summary transport and
all frame preservation proofs are obligations of a future Contract proof. -/
def Post (resources : Resources) (encode : Encode)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions) (m : Machine) (e : Entry)
    (impl : Outcome) : Prop :=
  impl = reference resources encode m e ∧
  (∀ n, (∀ k, k < n → ¬ Boundary resources encode m e k (execution resources encode m e k)) →
    ¬ ∃ a s, (execution resources encode m e n).status = .undefined a s) ∧
  (∀ n, First resources encode m e n →
    let out := execution resources encode m e n
    (∃ suffix, out.events = e.prior ++ suffix) ∧ Frame e out ∧ SourceFrame e out ∧ FullFrame resources encode m e n out ∧
    (∀ c value, out.status = .running c → c.frame.completed = some (.ok value) →
      Success resources encode granted e out value))

/-- This is the all-entry contract target, with machine and entry conditions
outside the conclusion; no inhabitant or row closure is asserted here. -/
def Contract (resources : Resources) (encode : Encode)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (env : Environment) (impl : Machine → Entry → Outcome) : Prop :=
  ∀ m, MachineSpec m base ctrl external backend resources encode env → ∀ e, Pre e →
    Post resources encode granted m e (impl m e)

/-- Exact comparison with the actual package predicates, not restated carriers. -/
theorem pre_comparison (e : Entry) : Pre e ↔
    PV_STX2_ToVecCallSummary.Pre e.toEntry ∧
      (∀ c ∈ e.suspended, PV_STX2_LiveNumbering.Numbered c) :=
  ⟨fun h => ⟨h.toPre,h.suspended⟩,fun h => ⟨h.1,h.2⟩⟩

theorem machine_implies_package (m : Machine) (base : Carrier PV_STX_World.World Data)
    (ctrl : Control) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) (resources : Resources) (encode : Encode)
    (env : Environment) (h : MachineSpec m base ctrl external backend resources encode env) :
    PV_STX2_ToVecCallSummary.MachineSpec m base ctrl external backend := h.toMachineSpec

theorem pending_implies_old (resources : Resources) (encode : Encode) (m : Machine)
    (e : Entry) (n : Nat) (out : Prefix OWNER Event)
    (h : Pending resources encode m e n out) :
    PV_STX2_ToVecCallSummary.Pending resources encode m e n out := by
  obtain ⟨k,c,w,events,waiting,hn,hr,_,hw,_,ha,ho⟩ := h
  exact ⟨k,c,w,events,waiting,hn,hr,hw,ha,ho⟩

/-- Compiled strict comparison at the actual f21/s581 entry. The package's
old diagnostic establishes Old.Pending here for an always-pending backend;
this predicate rejects the same prefix independently of the backend answer. -/
theorem no_false_pending11 (resources : Resources) (encode : Encode)
    (m : Machine) (e : Entry) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (machine : PV_STX2_ToVecCallSummary.MachineSpec m base ctrl external backend) :
    ¬ Pending resources encode m e 11 (execution resources encode m e 11) := by
  rintro ⟨k,c,w,events,waiting,fuel,reached,_,hw,dispatch,_,_⟩
  have k10 : k = 10 := by omega
  subst k
  have actual := PV_STX2_ToVecCallSummary.entry10 resources encode m e base ctrl external backend machine
  change PV_STX2_ToVecCallSummary.execution resources encode m e 10 = _ at reached
  rw [actual] at reached
  have configs := congrArg (fun q : Prefix OWNER Event => q.status) reached
  have cc := Status.running.inj configs
  subst c
  have req : waiting.request = PV_STX2_SliceToVecEntry.request
      (PV_STX2_SliceToVecEntry.prepared (start e).store (start e).frame.activation (.number e.length))
      (.number e.length) PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value :=
    congrArg (fun wait : PV_STX2_Native.Waiting Data => wait.request) (Option.some.inj hw).symm
  rw [req,machine.programs] at dispatch
  change (some PV_STX2_Source7CtorF31.program : Option PV_STX2_SliceSyntax.Program) = none at dispatch
  cases dispatch

theorem first_unique (resources : Resources) (encode : Encode) (m : Machine) (e : Entry)
    (a b : Nat) (ha : First resources encode m e a) (hb : First resources encode m e b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact False.elim (hb.2 a h ha.1)
  · exact h
  · exact False.elim (ha.2 b h hb.1)

theorem abort_prefix (s : Store Data) (w : OWNER) (es : List Event) :
    observe [] ⟨.fault .abort s,w,es⟩ = .abort es := rfl

#print axioms Pre
#print axioms MachineSpec
#print axioms Success
#print axioms SourceFrame
#print axioms final_length
#print axioms construction_length
#print axioms package_success_forces_zero
#print axioms FreshByte
#print axioms FullFrame
#print axioms Post
#print axioms Contract
#print axioms pre_comparison
#print axioms machine_implies_package
#print axioms pending_implies_old
#print axioms no_false_pending11
#print axioms first_unique
#print axioms abort_prefix
end PV_LIB_SLICE_Spec_f21
