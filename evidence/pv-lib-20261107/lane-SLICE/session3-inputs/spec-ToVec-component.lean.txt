import PV_STX2_ToVecCallPendingDiagnostic
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ToVec
open scoped Classical
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
namespace Old
abbrev Machine := PV_STX2_ToVecCallSummary.Machine
abbrev Entry := PV_STX2_ToVecCallSummary.Entry
end Old
abbrev Event := PV_RJ4IDB.NativeEvent
abbrev Machine := Old.Machine
abbrev Entry := Old.Entry
abbrev Pre := PV_STX2_ToVecCallSummary.Pre
abbrev MachineSpec := PV_STX2_ToVecCallSummary.MachineSpec
abbrev execution := PV_STX2_ToVecCallSummary.execution
abbrev start := PV_STX2_ToVecCallSummary.start

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
  | state : Prefix OWNER Event → Observation
  | abort : List Event → Observation

def observe (q : Prefix OWNER Event) : Observation :=
  match q.status with
  | .fault .abort _ => .abort q.events
  | _ => .state {q with status := statusView q.status}

/-- Includes exact every-prefix behavior when there is no finite boundary. -/
inductive Outcome where
  | finite : Observation → Outcome
  | infinite : (Nat → Observation) → Outcome

/-- A deterministic reference, independent of the candidate implementation.
No successful allocation, finite-fuel, or future-read assumption is used. -/
def reference (resources : Resources) (encode : Encode) (m : Machine) (e : Entry) : Outcome :=
  if h : ∃ n, Boundary resources encode m e n (execution resources encode m e n) then
    .finite (observe (execution resources encode m e (Nat.find h)))
  else .infinite (fun n => observe (execution resources encode m e n))

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

/-- Statement only. Source decoding gaps are excluded by a proof obligation,
not by accepting an undefined configuration as divergence. No row is proved. -/
def Post (resources : Resources) (encode : Encode)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions) (m : Machine) (e : Entry)
    (impl : Outcome) : Prop :=
  impl = reference resources encode m e ∧
  (∀ n, (∀ k, k < n → ¬ Boundary resources encode m e k (execution resources encode m e k)) →
    ¬ ∃ a s, (execution resources encode m e n).status = .undefined a s) ∧
  (∀ n, First resources encode m e n →
    let out := execution resources encode m e n
    (∃ suffix, out.events = e.prior ++ suffix) ∧ Frame e out ∧
    (∀ c value, out.status = .running c → c.frame.completed = some (.ok value) →
      PV_STX2_ToVecCallSummary.Success resources encode granted e out value))

/-- This is the all-entry contract target, with machine and entry conditions
outside the conclusion; no inhabitant or row closure is asserted here. -/
def Contract (resources : Resources) (encode : Encode)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (impl : Machine → Entry → Outcome) : Prop :=
  ∀ m, MachineSpec m base ctrl external backend → ∀ e, Pre e →
    Post resources encode granted m e (impl m e)

/-- Exact comparison with the actual package predicates, not restated carriers. -/
theorem pre_same (e : Entry) : Pre e ↔ PV_STX2_ToVecCallSummary.Pre e := Iff.rfl

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
    (machine : MachineSpec m base ctrl external backend) :
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
    observe ⟨.fault .abort s,w,es⟩ = .abort es := rfl

#print axioms Pre
#print axioms MachineSpec
#print axioms Post
#print axioms Contract
#print axioms pre_same
#print axioms pending_implies_old
#print axioms no_false_pending11
#print axioms first_unique
#print axioms abort_prefix
end PV_LIB_SPEC_ToVec
