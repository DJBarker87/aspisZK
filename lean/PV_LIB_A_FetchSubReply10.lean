import PV_LIB_A_WeakFreePoll10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_FetchSubReply10
open scoped Classical
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable

/-- Exact emitted581, AtomicUsize::fetch_sub, returns the value BEFORE the
subtraction (pinned core atomic_int! fetch_sub; alloc/sync.rs Arc::drop consumes
it at21732). This is one named library value interpretation, not a T field.
Failure/divergence/fault/pending and all world/events remain the same answer. -/
def PV_THR2_LibrarySemantics_FetchSubValue581 (old : Nat)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  ⟨match r.answer with
    | .returned (.ok _) => .returned (.ok (.number old))
    | .returned (.fail e) => .returned (.fail e)
    | .returned .div => .returned .div
    | .fault f => .fault f
    | .pending => .pending,r.world,r.events⟩

/-- Read the atomic's actual source v.UnsafeCell.value BEFORE sourceStart.
The returned old value is not obtained from the decremented source on retry. -/
def readOld (C : Carrier OWNER Data) (c : Config) (w : OWNER) (site : SourceSite) : Option Nat := do
  let [reference,.number _,_] := site.arguments | none
  let p ← PV_LIB_A_StorePrimitiveV2.atReference C c.store w reference [0,0]
  PV_LIB_A_StorePrimitiveV2.numberAt C c.store p

/-- Read selection is by exact function identity, not by a count or branch
supplied by a caller. SourceSelect already excludes emitted inline bodies. -/
def selected (P : Data → Option PV_STX2_SliceSyntax.Program) (c : Config) : Option SourceSite := do
  let site ← sourceSelect (v2ProvenancePrograms P) c
  if PV_THR2_OffPath.functionId site.callee = some 581 then some site else none

/-- An ephemeral source-control snapshot, not another allocation or source
cell. The original wait is retained to prevent applying it to a different call. -/
structure Saved where
  waiting : PV_STX2_Native.Waiting Data
  old : Nat

/-- Only the exact selected request receives the documented value. All other
requests, including the payload's nested calls, retain the original handler. -/
def handler (H : Handler) (saved : Saved) : Handler := fun request w =>
  if request = saved.waiting.request then
    PV_THR2_LibrarySemantics_FetchSubValue581 saved.old (H request w)
  else H request w

theorem returned (old : Nat) (v : Data) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) :
    PV_THR2_LibrarySemantics_FetchSubValue581 old ⟨.returned (.ok v),w,es⟩ =
      ⟨.returned (.ok (.number old)),w,es⟩ := rfl

theorem pending (old : Nat) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) :
    PV_THR2_LibrarySemantics_FetchSubValue581 old ⟨.pending,w,es⟩ = ⟨.pending,w,es⟩ := rfl

theorem non_success (old : Nat) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (notReturned : ∀ v, r.answer ≠ .returned (.ok v)) :
    PV_THR2_LibrarySemantics_FetchSubValue581 old r = r := by
  cases r with
  | mk answer w es =>
    cases answer with
    | pending => rfl
    | fault f => rfl
    | returned result =>
      cases result with
      | fail e => rfl
      | div => rfl
      | ok v => exact False.elim (notReturned v rfl)

theorem effects (old : Nat) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    (PV_THR2_LibrarySemantics_FetchSubValue581 old r).world = r.world ∧
    (PV_THR2_LibrarySemantics_FetchSubValue581 old r).events = r.events := ⟨rfl,rfl⟩

theorem at_request (H : Handler) (saved : Saved) (w : OWNER) :
    handler H saved saved.waiting.request w =
      PV_THR2_LibrarySemantics_FetchSubValue581 saved.old (H saved.waiting.request w) := by
  simp [handler]

theorem away (H : Handler) (saved : Saved) (request : PV_STX2_Native.Request Data) (w : OWNER)
    (other : request ≠ saved.waiting.request) : handler H saved request w = H request w := by
  simp only [handler,if_neg other]

#print axioms PV_THR2_LibrarySemantics_FetchSubValue581
#print axioms readOld
#print axioms selected
#print axioms handler
#print axioms returned
#print axioms pending
#print axioms non_success
#print axioms effects
#print axioms at_request
#print axioms away
end PV_LIB_A_FetchSubReply10
