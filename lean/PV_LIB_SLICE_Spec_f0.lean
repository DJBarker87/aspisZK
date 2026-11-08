import PV_LIB_SLICE_Spec_f1
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_Spec_f0
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_LIB_SLICE_Statements
structure Entry extends ArrayEntry where
  foundationAddress : Address
  foundation : PV_STX2_Source7EntryOwned.Foundation
abbrev MachineSpec := PV_LIB_SLICE_Statements.MachineSpec
abbrev start (e : Entry) := PV_LIB_SLICE_Statements.start PV_STX2_SliceF0.program
  [PV_STX2_TypedReferences.reference e.foundationAddress .null] e.toArrayEntry.toEntry

/-- Typed call-entry domain; no successful child, future read or callee Post. -/
def Pre (m : Machine) (e : Entry) : Prop := ArrayPre m (start e) e.toArrayEntry ∧
  ∃ entry : PV_STX2_Source7EntryReferenceValid.Source7EntryOwned''''' e.owner e.foundation,
  (∀ i : Fin 16, let j : Fin e.foundation.c1.val.length := ⟨i.val, by simpa using i.isLt⟩
    (e.columns i).identity = PV_STX2_Source7EntrySelection.identity entry.previous.previous.owned j ∧
    (e.columns i).header = PV_STX2_Source7EntrySelection.header entry.previous.previous.owned j ∧
    (e.columns i).region.place = PV_STX2_Source7EntrySelection.place entry.previous.previous.owned j) ∧
  e.arrayAddress = {e.foundationAddress with fields := e.foundationAddress.fields ++ [0]} ∧
  readAddress m.carrier (start e).store e.foundationAddress =
    some (PV_STX2_Aggregates.pack PV_STX2_AggregateKinds.source7Kind
      [.array (List.ofFn (fun i => vector (e.columns i).header))]) ∧
  (∀ i : Fin 16, (e.columns i).region.values =
    PV_STX2_Source7EntryOwned.values e.foundation ⟨i.val, by simpa using i.isLt⟩)

/-- Exact first boundary on every arm, plus the row's source value clause. -/
def Post (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (m : Machine) (e : Entry) (impl : Outcome) : Prop :=
  PV_LIB_SLICE_Statements.Post r enc m (start e) e.toArrayEntry.toEntry (sources e.toArrayEntry) []
    (fun out v => ∃ values, v = PV_STX2_Aggregates.pack PV_STX2_AggregateKinds.source7Kind [values] ∧
      ArrayClone r enc g e.toArrayEntry out values) impl

/-- A statement to be proved later, not an axiom or an instance. -/
def Contract (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (env : Environment) (impl : Machine → Entry → Outcome) : Prop :=
  ∀ m, MachineSpec m base ctrl external backend r enc env → ∀ e, Pre m e → Post r enc g m e (impl m e)
#print axioms Pre
#print axioms MachineSpec
#print axioms Post
#print axioms Contract
end PV_LIB_SLICE_Spec_f0
