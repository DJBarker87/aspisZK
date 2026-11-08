import PV_LIB_A_ExactDestructMethods
import PV_LIB_A_TypedDropSource
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CellDestruct504
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_TypedDestruct PV_LIB_A_CellSetBegin

/-- A private semantic site, not an alleged instruction from the binary. -/
def site (n : Nat) : PV_STX2_Syntax.Site := ⟨504,n,.atom "documented Cell::set old-value destruction"⟩

/-- Cell::set's documented suffix after replacement. Destruction is of saved
OLD T, in its own source slot, before the unit result returns. Successful
Drop invalidates that slot using the ordinary dropped return action. -/
def suffix (d : Resolution) : List PV_STX2_SliceSyntax.Node :=
  (match d with
   | .noop => [.leaf (.storage (site 0) false 3)]
   | .call fn => [.leaf (.drop (site 0) (.local 3) fn false [])]) ++
  [.leaf (.ret (site 1) (.local 0))]

structure Site where
  waiting : PV_STX2_Native.Waiting Data
  activation : Nat
  prepared : Prepared
  destructor : Resolution

def select (C : Carrier OWNER Data) (P : Data → Option PV_STX2_SliceSyntax.Program)
    (c : Config) (w : OWNER) : Option Site := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request with
    | .child fn a args =>
      if PV_THR2_OffPath.functionId fn = some 504 ∧ (P fn).isNone = true then
        let normalized ← normalize 64 fn
        let prepared ← PV_THR2_LibrarySemantics_CellSetBegin504 C normalized args c.store w
        let d ← PV_LIB_A_ExactDestructMethods.resolve prepared.destructor.type prepared.destructor.witness
        pure ⟨wait,a,prepared,d⟩
      else none
    | _ => none

/-- Reuse the already reserved504 activation. The old T is local3; local0 is
unit. The selected glue later receives a reference to local3 in a fresh frame,
so its own temporary locals cannot clobber the saved old T. -/
def enter (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (selected : Site) (unit : Data) : PV_LIB_StoreActionTable.SourceState :=
  let a := selected.activation
  let store := write (write selected.prepared.store ⟨a,3,[]⟩ (some selected.prepared.old))
    ⟨a,0,[]⟩ (some unit)
  ⟨⟨⟨.running ⟨{activation := a,remaining := suffix selected.destructor},
    c.frame :: c.callers,store⟩,w,es⟩,stack⟩,none⟩

/-- No additional activation is reserved by the replacement/suffix transition.
No equality of counters is required at a later row boundary. -/
theorem enter_frame (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (selected : Site) (unit : Data) :
    ∃ next, (enter c w es stack selected unit).base.current.status = .running next ∧
      next.frame.activation = selected.activation ∧
      next.frame.remaining = suffix selected.destructor ∧
      next.callers = c.frame :: c.callers ∧
      next.store.nextActivation = selected.prepared.store.nextActivation ∧
      (enter c w es stack selected unit).base.current.world = w ∧
      (enter c w es stack selected unit).base.current.events = es ∧
      (enter c w es stack selected unit).base.suspended = stack :=
  ⟨_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- No successful outcome is asserted: the nontrivial suffix issues the actual
selected Drop, whose failure, divergence, panic/unwind and pending stay live. -/
theorem call_suffix (fn : Data) :
    suffix (.call fn) = [.leaf (.drop (site 0) (.local 3) fn false []),
      .leaf (.ret (site 1) (.local 0))] := rfl

theorem noop_invalidates :
    suffix .noop = [.leaf (.storage (site 0) false 3),
      .leaf (.ret (site 1) (.local 0))] := rfl

#print axioms site
#print axioms suffix
#print axioms select
#print axioms enter
#print axioms enter_frame
#print axioms call_suffix
#print axioms noop_invalidates
end PV_LIB_A_CellDestruct504
