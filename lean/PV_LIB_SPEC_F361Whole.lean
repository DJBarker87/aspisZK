import PV_LIB_SPEC_F361Contract
import PV_THR2_Source270Table
import PV_THR2_Source361Children
import PV_THR2_Source361HookChildren
import PV_THR2_Source361PacketChildren
import PV_THR2_Source361ScopeChildren
import PV_THR2_Source361BoxTable
import PV_THR2_BoxFromTable
import PV_THR2_Source361InitChildren
set_option autoImplicit false
noncomputable section

/-! D984 statement interface. `FullStoreActionTable` is ONE explicit parameter
shared by every row. Lane A supplies its completed, named documented meanings;
the obsolete five-writer table is NEVER chosen as a default. The parameter is
not an identity delta, a write-definedness hypothesis or a proof of adequacy.
No row contract in this file is proved. -/
namespace PV_LIB_SPEC_D984
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
abbrev Event := PV_RJ4IDB.NativeEvent
abbrev State := PV_THR2_IntrinsicState.State OWNER Event
abbrev Handler := PV_STX2_Native.Request Data → OWNER → Reply OWNER Event Data
/-- Each table entry names ONE emitted function's documented source-store
meaning. It receives the actual store/arguments and FULL resource answer;
none means invalid representation, never a neutral write. Arc/Box backing
cells, atomics and native drop requests are included by D984's criterion. -/
structure Writer where
  function : Data
  documentedName : String
  sourcePin : String
  interpret : Carrier OWNER Data → List Data → Store Data → OWNER →
    Reply OWNER Event Data → Option (Store Data)
/-- Completed by lane A. No default, finite five-writer enumeration or success
assumption is built into the statement. Duplicate keys use the first entry;
uniqueness and inventory/source completeness are separate adequacy targets. -/
abbrev FullStoreActionTable := List Writer
local instance : DecidableEq Data := Classical.decEq Data

def lookup (table : FullStoreActionTable) (fn : Data) : Option Writer :=
  table.find? (fun row => decide (row.function = fn))

structure Machine where
  carrier : Carrier OWNER Data
  control : Control
  programs : Data → Option PV_STX2_SliceSyntax.Program
  handler : Handler
  resources : Resources
  encode : Encode
  storeActions : FullStoreActionTable

/-- OWNER-aware base, including storage registration, all operator actions,
bridged allocation and intrinsic callback priority. -/
def ownerStep (m : Machine) : State → State :=
  PV_THR2_OwnInitInterpreterBridged.step m.carrier m.control m.programs
    m.resources m.encode m.handler

/-- Recognize actual ordinary native polls, including Drop. BODY entry is not
an answer. The table is keyed by the COMPLETE issued function descriptor. -/
def selected (m : Machine) (c : Config) : Option (Writer × PV_STX2_Native.Waiting Data × List Data) := do
  if c.frame.completed.isSome then none else do
    let wait ← c.frame.waiting
    let (fn,args) ← match wait.request with
      | .child fn _ args => some (fn,args)
      | .drop fn value => some (fn,[value])
      | _ => none
    if (m.programs fn).isSome then none else do
      let writer ← lookup m.storeActions fn
      pure (writer,wait,args)

/-- The corrected machine NAMED by all session5 contracts. Every full answer
is administered after its documented source write; undecodable representations
are explicit undefined states. No backend/store effect is fabricated. -/
def step (m : Machine) (q : State) : State :=
  match q.current.status with
  | .running c =>
    match PV_THR2_Catch316Segment.select c with
    | some _ => ownerStep m q
    | none => match selected m c with
      | none => ownerStep m q
      | some (writer,wait,args) =>
        let r := m.handler wait.request q.current.world
        match writer.interpret m.carrier args c.store q.current.world r with
        | none => ⟨⟨.undefined none c.store,r.world,q.current.events ++ r.events⟩,q.suspended⟩
        | some store =>
          let out := PV_THR2_ChildBoundary.delivered m.carrier {c with store := store} wait r
          ⟨⟨out.status,out.world,q.current.events ++ out.events⟩,q.suspended⟩
  | _ => ownerStep m q

def run (m : Machine) : Nat → State → State
  | 0,q => q
  | n+1,q => run m n (step m q)

/-- Exact table audit to instantiate after lane A's re-inventory. `sourceWrites`
is the independently inventoried set, NOT a premise of any row contract. -/
def TableAdequacy (table : FullStoreActionTable) (sourceWrites : Data → Prop) : Prop :=
  (table.map Writer.function).Nodup ∧
  (∀ fn, sourceWrites fn ↔ ∃ writer ∈ table, writer.function = fn) ∧
  ∀ writer ∈ table, writer.documentedName ≠ "" ∧ writer.sourcePin ≠ ""

/-- One agreement obligation for the completed machine, against the OWNER
base, away from ALL completed table entries; statement only. -/
def AwayAgreement : Prop := ∀ m q,
  (∀ c, q.current.status = .running c → selected m c = none) →
    step m q = ownerStep m q

abbrev observe := PV_LIB_SPEC_ThreadContract.observe
abbrev Numbered := PV_LIB_SPEC_ThreadContract.Numbered
abbrev OwnComplete := PV_LIB_SPEC_ThreadContract.OwnComplete
abbrev Terminal := PV_LIB_SPEC_ThreadContract.Terminal

def ConsumedPending (m : Machine) (q : State) : Prop :=
  ∃ c wait, q.current.status = .running c ∧ c.frame.completed = none ∧
    c.frame.waiting = some wait ∧ PV_THR2_Catch316Segment.select c = none ∧
    (match wait.request with | .child fn _ _ => m.programs fn = none | _ => True) ∧
    (m.handler wait.request q.current.world).answer = .pending ∧
    ∃ after, (step m q).current.status = .running after ∧
      after.frame.completed = none ∧ after.frame.waiting = some wait

def Boundary (m : Machine) (entry : State) (trace : Nat → State) (n : Nat) : Prop :=
  OwnComplete entry (trace n) ∨ Terminal entry (trace n) ∨
    ∃ k, n = k+1 ∧ ConsumedPending m (trace k) ∧ trace n = step m (trace k)

def First (m : Machine) (entry : State) (trace : Nat → State) (n : Nat) : Prop :=
  Boundary m entry trace n ∧ ∀ k, k < n → ¬ Boundary m entry trace k

def Diverges (m : Machine) (entry : State) (trace : Nat → State) : Prop :=
  ∀ n, ¬ Boundary m entry trace n

/-- Independent frozen-source execution, not the candidate's own trace.
Every exact Result constructor/payload is retained by observe; abort erases
all state; the counter alone is abstracted at row boundaries. -/
def Behavior (m : Machine) (entry : State) (candidate : Nat → State) : Prop :=
  (∃ n k, First m entry (fun i => run m i entry) n ∧ First m entry candidate k ∧
    observe (candidate k) = observe (run m n entry)) ∨
  (Diverges m entry (fun i => run m i entry) ∧ Diverges m entry candidate ∧
    (∀ n, ∃ k, (candidate n).current.events = (run m k entry).current.events) ∧
    (∀ k, ∃ n, (run m k entry).current.events = (candidate n).current.events))

/-- Full transitive emitted resolver used throughout the thread chain. The
fallback remains an explicit source library parameter (CLOSED bodies and
named native models), never an installed successful reply. -/
def programs (fallback : Data → Option PV_STX2_SliceSyntax.Program) :=
  PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve
    (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve
    (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve
    (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve
    (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve
    (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback)))))))))))

/-- Entry-selected valid registered allocation headers. Initialization and
source type encodings are additionally the row's provider entry predicates. -/
abbrev RegisteredValidity := PV_LIB_SPEC_F361Contract.RegisteredValidity

#print axioms FullStoreActionTable
#print axioms Machine
#print axioms step
#print axioms TableAdequacy
#print axioms AwayAgreement
#print axioms ConsumedPending
#print axioms Boundary
#print axioms First
#print axioms Diverges
#print axioms Behavior
#print axioms programs
end PV_LIB_SPEC_D984

namespace PV_LIB_SPEC_F361Whole
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_FN_THREAD_f361
open PV_LIB_SPEC_D984
abbrev State := PV_LIB_SPEC_D984.State
abbrev Representation := PV_LIB_SPEC_F361Entry.Representation

/-- Source model parameters, including the FULL completed table. Input's old
sourceStep and changes are NOT executed by this machine. -/
def source (table : FullStoreActionTable) (x : Input) : Machine :=
  ⟨base x,x.K,programs x.P,handler x,x.resources,x.encode,table⟩

/-- An arbitrary machine, fixed before the entry/candidate quantifiers, meets
exact carrier/control/emitted table/native/resource bindings. No store-write,
callee-success, decoder-success, future read or desired Post hypothesis. -/
def MachineSpec (table : FullStoreActionTable) (x : Input) (m : Machine) : Prop :=
  m.carrier = base x ∧ m.control = x.K ∧ m.programs = programs x.P ∧
  m.handler = handler x ∧ @m.resources = @x.resources ∧ @m.encode = @x.encode ∧
  m.storeActions = table

/-- Both name Option arms and source Scope shape, actual capture registration,
initialized byte predicates, saved waiting action, lower/suspended numbering,
OWNER bounds and reference-valid allocation headers. No Some iteration premise. -/
def Pre (R : Representation) (x : Input) : Prop :=
  PV_LIB_SPEC_F361Contract.Pre R x

/-- Full f361 boundary (NOT the14756 milestone). Source execution retains
Thread/CString creation, Packet/Scope Arc counts, callback Box13923, casts,
registration14320, bridged ThreadInit14756, spawn/Result and both cleanup arms.
Exact source values and every resource reply are in Behavior's independent
emitted-body reference. Frame is exempt only after process abort. -/
def Post (table : FullStoreActionTable) (x : Input) (candidate : Nat → State) : Prop :=
  Behavior (source table x) (entry x) candidate ∧
  ∀ k, First (source table x) (entry x) candidate k →
    match (candidate k).current.status with
    | .fault .abort _ => True
    | _ => Frame x (candidate k) ∧ Numbered (candidate k)

/-- WHOLE correctness statement; deliberately a Prop, never a row theorem.
Candidate is independent of the frozen source reference. -/
def Contract (table : FullStoreActionTable) (R : Representation)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m x, MachineSpec table x m → Pre R x → Post table x (implementation m x)

/-- Explicit literal package comparison. Neither implication from the old
Post nor transport from its sourceStep/changes is presumed. -/
def Comparison (table : FullStoreActionTable) (R : Representation) : Prop :=
  (∀ x, Pre R x ↔ PV_FN_THREAD_f361.Pre x ∧
    PV_FN_THREAD_f361NameEntryValidity.EntryName R x ∧
    PV_FN_THREAD_f361ScopeEntryValidity.Shape x.scope ∧
    PV_LIB_SPEC_F361Entry.Numbered x ∧ RegisteredValidity x.w) ∧
  (∀ x, PV_FN_THREAD_f361.Post x →
    Post table x (fun n => run (source table x) n (entry x)))

/-- Separate actual source/binary adequacy obligation, including table binding,
operator/cast, name/Scope representation and allBridged at SAME-history14756.
No old-decode or bare-Box Shape antecedent is used. -/
def SourceAdequacy (table : FullStoreActionTable) (R : Representation)
    (actualSource : Input → Nat → State) : Prop :=
  ∀ x, Pre R x → Post table x (actualSource x)

#print axioms source
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
#print axioms SourceAdequacy
end PV_LIB_SPEC_F361Whole
