import PV_FN_THREAD_f6Provider124Dispatch
import PV_FN_THREAD_f6Provider126CallJoin
import PV_FN_THREAD_f6ProviderInterfaces
import PV_FN_THREAD_f6PrefixTransport
import PV_FN_THREAD_f6LoopContinuation
import PV_FN_THREAD_f6Return
import PV_FN_THREAD_f6DeliveryInterfaces
set_option autoImplicit false
noncomputable section

/-! Session112 statement milestone. These are propositions to prove, NOT
contracts assumed at the privacy endpoint. In particular no inhabitant of
GlobalOriginalTransport, LoopInduction, ReturnAndFrame or Contract is asserted
by compiling this file. M is ONE fixed original interpreter throughout.
Provider definitions are imported literally; the obsolete consumer124/126
representation interfaces are not dependencies of any statement below. -/
namespace PV_FN_THREAD_f6Joins
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_FN_THREAD_f6Interfaces
open PV_FN_THREAD_f6LoopIteration
abbrev Event := PV_RJ4IDB.NativeEvent
abbrev Backend := PV_W1_OwnerNativeFrame.Backend

/-- Exact local interpreter used by provider124, not a proposed global table. -/
def local124 (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend Event)
    (resources : Resources) (encode : Encode)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (y : Entry Event) (payload : Data) : Machine Event :=
  let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H y payload
  ⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,K,
    PV_FN_THREAD_f124_Continuation.programs x,
    (PV_FN_THREAD_f124_Interface.installed x H resources encode shape).H⟩

/-- Exact local interpreter used by CLOSED126 at each source Scope call. -/
def local126 (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend Event)
    (y : Entry Event) (arcPlace : Address) : Machine Event :=
  let x := PV_FN_THREAD_f6Provider126Entry.convert C b K P H y
  ⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,K,
    PV_FN_THREAD_f126_ReturnedStage.programs x,
    (PV_FN_THREAD_f126.installed x H arcPlace).H⟩

/-- Transport must hold at EVERY prefix through first outcome delivery, including
callee interiors and failure/pending prefixes. Endpoint Reached is insufficient.
The original machine is fixed OUTSIDE the call-entry quantifiers. This does not
assert global equality of the different provider and source resolver tables. -/
def PrefixIdentity (M N : Machine Event) (y : Entry Event) : Prop :=
  M.carrier = N.carrier ∧ M.control = N.control ∧
  ∀ n, BeforeDelivery N y n → run M y n = run N y n

/-- A child entry on this ONE original run. Restricting the transport target
here is essential: native320 uses the current source store, so a fixed handler
cannot be required to interpret unrelated stores with the same request token.
This is an internal reachability projection to derive, not a new row Pre. -/
def AtOriginalEntry (M : Machine Event) (root child : Entry Event) : Prop :=
  ∃ n, BeforeDelivery M root n ∧ run M root n = entry child

/-- Concrete global join targets at1916 and2097/2306/2659. Entry validity,
stack bounds and owned Arc are entry conditions, not future reads. The theorem
proving this statement must derive instruction agreement; agreement is NOT an
argument of this proposition or of the final Contract. -/
def GlobalOriginalTransport (M : Machine Event) (root : Entry Event) (C : Carrier OWNER Data)
    (b : Bool) (K : Control) (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : Backend Event) (resources : Resources) (encode : Encode)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape) : Prop :=
  (∀ (s : Store Data) (a : Nat) (parents : List Frame)
      (counter thread panicked : Data) (w : OWNER) (es : List Event) (stack : List Config),
    let y := PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack
    AtOriginalEntry M root y → EntryValid y → PV_FN_THREAD_f6Provider124Entry.StackBounded y →
    PrefixIdentity M (local124 C b K P H resources encode shape y
      (PV_THR2_ScopeData.value counter thread panicked)) y) ∧
  (∀ (site : PV_FN_THREAD_f6DerefInterfaces.Site) (s : Store Data) (a : Nat)
      (parents : List Frame) (saved : List LoopFrame) (w : OWNER)
      (es : List Event) (stack : List Config) (p : Address),
    let y := PV_FN_THREAD_f6DerefInterfaces.input site s a parents saved w es stack
    AtOriginalEntry M root y → EntryValid y → At M.carrier y.store ⟨a,2,[0]⟩ (PV_FN_THREAD_f222_EntryOwned.root p) →
    PrefixIdentity M (local126 C b K P H y ⟨a,2,[0]⟩) y)

/-- The125 Ok/Err value is witnessed on the SAME original f6 run, immediately
before its completion loop; it is never a successful endpoint premise. -/
def Saved125 (M : Machine Event) (root : Entry Event) (result : Data) : Prop :=
  ∃ n c, BeforeDelivery M root n ∧ (run M root n).current.status = .running c ∧
    c.frame.activation = root.activation ∧
    c.frame.remaining = PV_THR2_F6.live.body.drop 46 ∧
    c.store.cells ⟨root.activation,10,[]⟩ = some result ∧
    (M.control.variant result = some 0 ∨ M.control.variant result = some 1)

/-- Prefix safety relative to the ORIGINAL entry, with its computed argument
footprint, explicit store, OWNER registry/header/bytes, and prior events. -/
def PrefixFrame (M : Machine Event) (root : Entry Event)
    (q : PV_THR2_IntrinsicState.State OWNER Event) : Prop :=
  Defined q.current.status ∧ StoreFrame M root (statusStore q.current.status) ∧
  OwnerFrame M root q.current.world ∧
  OwnerWellFormed q.current.world (statusStore q.current.status).nextActivation ∧
  (∃ suffix, q.current.events = root.events ++ suffix)

/-- Invariant at a COMPLETE iteration boundary. The Arc layout is the provider's
NonNull representation, and the original returned125 value is preserved.
Reachability and stack bounds are conclusions to establish from original entry,
not new row Pre clauses. No counter bound or eventual-zero assertion occurs. -/
def LoopInvariant (M : Machine Event) (root : Entry Event)
    (k : Context OWNER Event) (x : Cursor OWNER Event) (p : Address)
    (payload result : Data) : Prop :=
  k.activation = root.activation ∧ k.parents = root.parent :: root.parents ∧
  k.suspended = root.suspended ∧ carrier k = M.carrier ∧ k.ctl = M.control ∧
  k.programs = M.programs ∧ k.handler = M.handler ∧
  Saved125 M root result ∧ x.store.cells ⟨k.activation,10,[]⟩ = some result ∧
  At M.carrier x.store ⟨k.activation,2,[0]⟩ (PV_FN_THREAD_f222_EntryOwned.root p) ∧
  (∃ strong weak, At M.carrier x.store p (PV_THR2_KeyValues.pack
    PV_THR2_Packet124Aggregate13.source.2.2.1 [strong,weak,payload])) ∧
  k.activation < x.store.nextActivation ∧
  (∀ f ∈ k.parents, f.activation < x.store.nextActivation) ∧
  (∀ c ∈ k.suspended, ∀ f ∈ c.frame :: c.callers, f.activation < x.store.nextActivation) ∧
  PrefixFrame M root (sourceState k PV_THR2_F6.block86 x) ∧
  (∃ n, BeforeDelivery M root n ∧ run M root n = sourceState k PV_THR2_F6.block86 x)

/-- Exact induction target for any number of complete iterations. C consists
of actual callee-contract applications at2097,2197,2306,2404, with their full
Post stores; deriving those applications and frames from providers is separate.
The invariant at the updated cursor is required, not just a finite Trace. -/
def LoopInduction (M : Machine Event) (C : Nat → PV_FN_THREAD_f6SummaryTrace.CallPost OWNER Event) : Prop :=
  ∀ (root : Entry Event) (k : Context OWNER Event) (x : Cursor OWNER Event)
    (p : Address) (payload result : Data) (rs : List (Iteration OWNER Event)),
    LoopInvariant M root k x p payload result →
    PV_FN_THREAD_f6LoopInduction.Dependencies C k x rs →
    LoopInvariant M root k (PV_FN_THREAD_f6LoopInduction.finish k x rs) p payload result

/-- Zero is a branch of the actual127 reply. Exit must retain original-entry
frames and the saved125 value, with exact store/world/events and lower stacks. -/
def ZeroExit (M : Machine Event) (C : Nat → PV_FN_THREAD_f6SummaryTrace.CallPost OWNER Event) : Prop :=
  ∀ (root : Entry Event) (k : Context OWNER Event) (x : Cursor OWNER Event)
    (p : Address) (payload result : Data) (r : Iteration OWNER Event),
    LoopInvariant M root k x p payload result → r.load.value = 0 →
    C 2097 (firstCall k x) x.world r.first.store
      ⟨.returned (.ok (ref r.first.value)),r.first.world,r.first.events⟩ →
    C 2197 (loadCall k x r) (afterFirst k x r).world r.load.store
      ⟨.returned (.ok (.number r.load.value)),r.load.world,r.load.events⟩ →
    let z := PV_FN_THREAD_f6LoopInduction.zeroCursor k x r
    PrefixFrame M root (PV_FN_THREAD_f6LoopInduction.exited k z) ∧
    z.store.cells ⟨k.activation,10,[]⟩ = some result ∧
    (∃ n, BeforeDelivery M root n ∧ run M root n = PV_FN_THREAD_f6LoopInduction.exited k z)

/-- Remaining exhaustive return/frame target, including cutoffs INSIDE calls,
nonzero iterations, zero exit, Ok/Err continuation, drop and saved-parent return.
The final two clauses are the value clauses of the existing FullPost verbatim.
There is no return, zero-exit, Reached, agreement or future-store premise. -/
def ReturnAndFrame (M : Machine Event) : Prop :=
  ∀ (thread_f124 : PV_FN_THREAD_f6Provider124Entry.Contract)
    (thread_f125 : PV_FN_THREAD_f6DeliveryInterfaces.f125 M)
    (F Task : Type) (root : Entry Event)
    (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task) (callback : Data),
    PV_FN_THREAD_f6.Pre root captures callback →
    ∀ n, BeforeDelivery M root n →
      let q := run M root n
      PrefixFrame M root q ∧
      (∀ v c, q.current.status = .running c → c.frame.activation = root.activation →
        c.frame.completed = some (.ok v) →
        ∃ m d result, BeforeDelivery M root m ∧ (run M root m).current.status = .running d ∧
          d.frame.activation = root.activation ∧ d.frame.remaining = PV_THR2_F6.live.body.drop 46 ∧
          d.store.cells ⟨root.activation,10,[]⟩ = some result ∧
          M.control.variant result = some 0 ∧ M.carrier.field result 0 = some v) ∧
      (∀ v c, q.current.status = .running c → c.frame = {root.parent with waiting := none} →
        c.callers = root.parents → (statusStore q.current.status).cells ⟨root.parent.activation,root.dest,[]⟩ = some v →
        q.suspended = root.suspended →
        ∃ m d result, BeforeDelivery M root m ∧ (run M root m).current.status = .running d ∧
          d.frame.activation = root.activation ∧ d.frame.remaining = PV_THR2_F6.live.body.drop 46 ∧
          d.store.cells ⟨root.activation,10,[]⟩ = some result ∧
          M.control.variant result = some 0 ∧ M.carrier.field result 0 = some v)

end PV_FN_THREAD_f6Joins

namespace PV_FN_THREAD_f6
open PV_FN_THREAD_f6Interfaces
/-- Statement reserved for theorem contract in a subsequent proof module.
M is the selected original interpreter, not a claim for every arbitrary M.
Only125 remains a BODY dependency argument. CLOSED124 is instantiated
by PV_FN_THREAD_f6Provider124Entry.exact_provider_type in the assembly proof.
Neither transport, loop invariant, return/frame, endpoint or extra T field is
an argument. CLOSED dependencies must be instantiated in the proof by name. -/
def Contract (M : Machine PV_FN_THREAD_f6Joins.Event) : Prop :=
  ∀ (thread_f125 : PV_FN_THREAD_f6DeliveryInterfaces.f125 M)
    (F Task : Type) (x : Entry PV_FN_THREAD_f6Joins.Event)
    (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task) (callback : PV_STX2_Syntax.Data),
    Pre x captures callback → PV_FN_THREAD_f6Joins.Post M x
end PV_FN_THREAD_f6

#print axioms PV_FN_THREAD_f6Joins.local124
#print axioms PV_FN_THREAD_f6Joins.local126
#print axioms PV_FN_THREAD_f6Joins.PrefixIdentity
#print axioms PV_FN_THREAD_f6Joins.AtOriginalEntry
#print axioms PV_FN_THREAD_f6Joins.GlobalOriginalTransport
#print axioms PV_FN_THREAD_f6Joins.Saved125
#print axioms PV_FN_THREAD_f6Joins.PrefixFrame
#print axioms PV_FN_THREAD_f6Joins.LoopInvariant
#print axioms PV_FN_THREAD_f6Joins.LoopInduction
#print axioms PV_FN_THREAD_f6Joins.ZeroExit
#print axioms PV_FN_THREAD_f6Joins.ReturnAndFrame
#print axioms PV_FN_THREAD_f6.Contract
