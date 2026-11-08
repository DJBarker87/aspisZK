import PV_FN_THREAD_f6PostStore
import PV_THR2_Packet124ReturnData
import PV_THR2_OrderedFamiliesEntryRefined
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Interfaces
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine

/-- Environment of the ORIGINAL interpreter. Neither resolver nor handler is
replaced when specializing a dependency. -/
structure Machine (E : Type) where
  carrier : Carrier OWNER Data
  control : Control
  programs : Data → Option PV_STX2_SliceSyntax.Program
  handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data

/-- Own call entry, after argument binding, with the actual saved return action.
The caller suffix, loops, event prefix and intrinsic stack are arbitrary. -/
structure Entry (E : Type) where
  activation : Nat
  body : PV_STX2_SliceSyntax.Program
  store : Store Data
  parent : Frame
  parents : List Frame
  wait : PV_STX2_Native.Waiting Data
  dest : Nat
  args : List Data
  world : OWNER
  events : List E
  suspended : List Config

def entry {E : Type} (x : Entry E) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨{activation := x.activation,remaining := x.body.body},
    x.parent :: x.parents,x.store⟩,x.world,x.events⟩,x.suspended⟩

def run {E : Type} (M : Machine E) (x : Entry E) (n : Nat) :=
  PV_THR2_IntrinsicState.advance M.carrier M.control M.programs M.handler n (entry x)

def statusStore : Status → Store Data
  | .running c => c.store
  | .returned _ s => s
  | .fault _ s => s
  | .undefined _ s => s

/-- Slice-5 and slice-9 invariant, definitionally the provider invariant. -/
def OwnerWellFormed (w : OWNER) (counter : Nat) : Prop :=
  PV_EVHB_SourceLifetimes.Fresh w ∧
    ∀ p id, w.places p = some id → p.activation < counter

/-- Only entry data and the saved call are constrained. No future read, run,
termination, callee contract or callee returned case is an entry premise. -/
def EntryValid {E : Type} (x : Entry E) : Prop :=
  x.store.nextActivation = x.activation + 1 ∧
  x.parent.activation < x.activation ∧
  x.parent.waiting = some x.wait ∧
  x.wait.action = .child x.activation (.local x.dest) ∧
  (∃ fn, x.wait.request = .child fn x.activation x.args) ∧
  OwnerWellFormed x.world x.activation ∧
  ∀ i v, x.args[i]? = some v → x.store.cells ⟨x.activation,i+1,[]⟩ = some v

/-- Values embedded in an argument, including aggregate captures. -/
inductive Contains : Data → Data → Prop
  | self (v) : Contains v v
  | array {v xs z} : v ∈ xs → Contains v z → Contains (.array xs) z
  | object {k v xs z} : (k,v) ∈ xs → Contains v z → Contains (.object xs) z

/-- Transitive argument footprint, including referenced cells and subplaces.
This is computed from ENTRY arguments and storage; it is not a free mask. -/
inductive Reach {E : Type} (M : Machine E) (x : Entry E) : Address → Prop
  | argument {arg v p} : arg ∈ x.args → Contains arg v →
      M.carrier.dereference x.world v = some p → Reach M x p
  | field {p} (suffix : List Nat) : Reach M x p →
      Reach M x {p with fields := p.fields ++ suffix}
  | reference {p root v q} : Reach M x p →
      x.store.cells ⟨p.activation,p.localIndex,[]⟩ = some root → Contains root v →
      M.carrier.dereference x.world v = some q → Reach M x q

/-- The callee may allocate fresh activations. Only argument-reachable OLD
cells and the actual return destination may change. -/
def StoreFrame {E : Type} (M : Machine E) (x : Entry E) (s : Store Data) : Prop :=
  x.store.nextActivation ≤ s.nextActivation ∧
  ∀ p, p.activation < x.activation → ¬ Reach M x p →
    p ≠ (⟨x.parent.activation,x.dest,[]⟩ : Address) → s.cells p = x.store.cells p

/-- A read-only callee also frames argument-reachable caller cells. -/
def ReadOnlyFrame {E : Type} (x : Entry E) (s : Store Data) : Prop :=
  ∀ p, p.activation < x.activation →
    p ≠ (⟨x.parent.activation,x.dest,[]⟩ : Address) → s.cells p = x.store.cells p

/-- Ghost bindings and owned headers outside the declared argument footprint.
No global backend-world identity is asserted for world/OS children. -/
def OwnerFrame {E : Type} (M : Machine E) (x : Entry E) (w : OWNER) : Prop :=
  ∀ p, p.activation < x.activation →
    (∀ localIndex fields, p.fields = localIndex :: fields →
      ¬ Reach M x (⟨p.activation,localIndex,fields⟩ : Address)) →
    w.places p = x.world.places p ∧
    PV_EVHB_SourceLifetimes.headerAt w p = PV_EVHB_SourceLifetimes.headerAt x.world p ∧
    (∀ h, PV_EVHB_SourceLifetimes.headerAt x.world p = some h →
      w.world.live h.pointer = x.world.world.live h.pointer ∧
      w.world.allocator.metadata h.pointer = x.world.world.allocator.metadata h.pointer ∧
      ∀ offset, offset < h.cap * h.shape.width →
        w.world.memory (h.pointer + offset) = x.world.world.memory (h.pointer + offset))

/-- First restoration of this exact saved caller. The intrinsic suffix is
part of its identity, so an unrelated suspended caller cannot extend the row. -/
def Returned {E : Type} (x : Entry E) (q : PV_THR2_IntrinsicState.State OWNER E) : Prop :=
  ∃ c, q.current.status = .running c ∧
    c.frame = {x.parent with waiting := none} ∧ c.callers = x.parents ∧
    q.suspended = x.suspended

def BeforeReturn {E : Type} (M : Machine E) (x : Entry E) (n : Nat) : Prop :=
  ∀ m, m < n → ¬ Returned x (run M x m)

/-- A model-stuck state is not a source fault, pending answer or divergence. -/
def Defined (status : Status) : Prop :=
  match status with
  | .undefined _ _ => False
  | _ => True

/-- Full branch contract as a prefix property up to and INCLUDING the first
return. Finite cutoffs and pending remain running; infinite executions retain
all finite observable prefixes. Fault, fail and div keep their actual store,
world and events. There is no finite-termination or loop-exit premise. -/
def FullPost {E : Type} (M : Machine E) (x : Entry E)
    (valuePost : Store Data → OWNER → Data → Prop) : Prop :=
  ∀ n, BeforeReturn M x n →
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

def fields (B : Carrier OWNER Data) : Data → List Nat → Option Data
  | v,[] => some v
  | v,i::is => (B.field v i).bind fun next => fields B next is

def At (B : Carrier OWNER Data) (s : Store Data) (p : Address) (v : Data) : Prop :=
  ∃ root, s.cells ⟨p.activation,p.localIndex,[]⟩ = some root ∧ fields B root p.fields = some v

/-- Emitted Arc and ArcInner layout; T is entirely arbitrary (in particular,
ScopeData and Packet use the same predicate). Counts are not fixed after clone. -/
def ArcAt (B : Carrier OWNER Data) (s : Store Data) (arc payload : Data) : Prop :=
  ∃ p strong weak, arc = PV_THR2_Packet124ReturnData.value
      (PV_STX2_TypedReferences.reference p .null) ∧
    At B s p (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
      [strong,weak,payload])

/-- Allocation provenance is a callee Post, never a caller alias hypothesis.
The actual BoxNew creates the backing activation inside this function's run. -/
def NewArcAt (B : Carrier OWNER Data) (s : Store Data) (freshFrom : Nat) (arc payload : Data) : Prop :=
  ∃ p strong weak, freshFrom ≤ p.activation ∧ p.activation < s.nextActivation ∧ arc = PV_THR2_Packet124ReturnData.value
      (PV_STX2_TypedReferences.reference p .null) ∧
    B.field strong 0 = some (.number 1) ∧ B.field weak 0 = some (.number 1) ∧
    At B s p (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
      [strong,weak,payload])

/-- W2 dependency, generic in T, caller, world and both saved stacks.
No fixed Packet value, root, handler or resolver is admitted. -/
def f124 {E : Type} (M : Machine E) : Prop :=
  ∀ (x : Entry E) payload, x.body = PV_THR2_F124.live → x.args = [payload] →
    EntryValid x → FullPost M x (fun s _ arc =>
      NewArcAt M.carrier s x.activation arc payload ∧ ReadOnlyFrame x s)

/-- f126 reads the Arc supplied by its ACTUAL reference argument, and returns
the data-field address of that same ArcInner. Generic in payload and metadata. -/
def f126 {E : Type} (M : Machine E) : Prop :=
  ∀ (x : Entry E) (arcPlace : Address) (arc payload metadata : Data),
    x.body = PV_THR2_F126.live →
    x.args = [PV_STX2_TypedReferences.reference arcPlace metadata] →
    EntryValid x → At M.carrier x.store arcPlace arc →
    ArcAt M.carrier x.store arc payload →
    FullPost M x (fun s _ result => ReadOnlyFrame x s ∧
      ∃ p strong weak, arc = PV_THR2_Packet124ReturnData.value
          (PV_STX2_TypedReferences.reference p .null) ∧
        At M.carrier s p (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
          [strong,weak,payload]) ∧
        result = PV_STX2_TypedReferences.reference {p with fields := p.fields ++ [2]} .null)

/-- W4 dependency at1989. Scope and the user's closure are the SOURCE captures.
The catch Result may be Ok OR Err; source2525 and2935 remain in f6. -/
def f125 {E : Type} (M : Machine E) : Prop :=
  ∀ (x : Entry E) (a : Nat) (capture arc payload : Data),
    x.body = PV_THR2_F125.live →
    x.args = [PV_THR2_ScopeCaptureWrap.value a capture] → EntryValid x →
    At M.carrier x.store ⟨a,2,[0]⟩ arc → ArcAt M.carrier x.store arc payload →
    FullPost M x (fun s _ result =>
      At M.carrier s ⟨a,2,[0]⟩ arc ∧ ArcAt M.carrier s arc payload ∧
      (M.control.variant result = some 0 ∨ M.control.variant result = some 1))

end PV_FN_THREAD_f6Interfaces

namespace PV_FN_THREAD_f6
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces

/-- Original-entry callback ownership, not a future ScopeData/Packet read. -/
def Pre {E F Task : Type} (x : Entry E) (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task)
    (callback : Data) : Prop :=
  x.body = PV_THR2_F6.live ∧ x.args = [callback] ∧ EntryValid x ∧
  PV_THR2_OrderedFamiliesEntryRefined.OrderedFamiliesEntryOwned' x.world captures callback

/-- A successful f6 return is the payload of the actual1989 Ok result observed
on the same original execution. Err, panic, resource failure, pending and
nontermination are preserved by FullPost; none is converted into success. -/
def Post {E : Type} (M : Machine E) (x : Entry E) : Prop :=
  FullPost M x (fun _ _ value =>
    ∃ n c result, BeforeReturn M x n ∧ (run M x n).current.status = .running c ∧
      c.frame.activation = x.activation ∧ c.frame.remaining = PV_THR2_F6.live.body.drop 46 ∧
      c.store.cells ⟨x.activation,10,[]⟩ = some result ∧
      M.control.variant result = some 0 ∧ M.carrier.field result 0 = some value)

#print axioms PV_FN_THREAD_f6Interfaces.f124
#print axioms PV_FN_THREAD_f6Interfaces.f125
#print axioms PV_FN_THREAD_f6Interfaces.f126
#print axioms Pre
#print axioms Post
end PV_FN_THREAD_f6
