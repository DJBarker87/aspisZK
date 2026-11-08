import PV_LIB_SLICE_Spec_f9
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_Spec_f4
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_LIB_SLICE_Statements
abbrev Entry := ArrayEntry
abbrev MachineSpec := PV_LIB_SLICE_Statements.MachineSpec
abbrev start (e : Entry) := PV_LIB_SLICE_Statements.start PV_STX2_SliceF4.program
  [wrapper e.arrayAddress 0] e.toEntry

/-- Typed call-entry domain; no successful child, future read or callee Post. -/
def Pre (m : Machine) (e : Entry) : Prop := ArrayPre m (start e) e

/-- Exact first boundary on every arm, plus the row's source value clause. -/
def Post (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (m : Machine) (e : Entry) (impl : Outcome) : Prop :=
  PV_LIB_SLICE_Statements.Post r enc m (start e) e.toEntry (sources e) []
    (fun out v => ∃ values, v = wrappedValue values ∧ ArrayClone r enc g e out values) impl

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
end PV_LIB_SLICE_Spec_f4
