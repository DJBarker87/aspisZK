import PV_LIB_SLICE_Spec_f5
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_Spec_f8
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_LIB_SLICE_Statements
abbrev Entry := ArrayEntry
abbrev MachineSpec := PV_LIB_SLICE_Statements.MachineSpec
abbrev start (e : Entry) := PV_LIB_SLICE_Statements.start PV_STX2_SliceF8.program
  [PV_STX2_TypedReferences.reference e.capture .null,PV_STX2_SliceLoopCallback.indexTuple e.index.val] e.toEntry

/-- Typed call-entry domain; no successful child, future read or callee Post. -/
def Pre (m : Machine) (e : Entry) : Prop := CapturePre m (start e) e true

/-- Exact first boundary on every arm, plus the row's source value clause. -/
def Post (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (m : Machine) (e : Entry) (impl : Outcome) : Prop :=
  PV_LIB_SLICE_Statements.Post r enc m (start e) e.toEntry (sources e) [e.capture]
    (fun out v => ∃ value, v = wrappedValue value ∧ Clone r enc g e.toEntry (e.columns e.index) out value ∧
      readAddress m.carrier (PV_STX2_ToVecCallCallerPost.statusStore out.status) e.capture =
        some (wrapper e.arrayAddress (e.index.val+1))) impl

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
end PV_LIB_SLICE_Spec_f8
