import PV_LIB_SLICE_Spec_f7
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_Spec_f9
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_LIB_SLICE_Statements
abbrev Entry := ArrayEntry
abbrev MachineSpec := PV_LIB_SLICE_Statements.MachineSpec
abbrev start (e : Entry) := PV_LIB_SLICE_Statements.start PV_STX2_SliceF9.program
  [PV_STX2_TypedReferences.reference e.buffer (.number 16),wrapper e.arrayAddress 0] e.toEntry

/-- Typed call-entry domain; no successful child, future read or callee Post. -/
def Pre (m : Machine) (e : Entry) : Prop := ArrayPre m (start e) e ∧ e.buffer.activation < (start e).frame.activation ∧
  ¬ inRoot e.buffer e.arrayAddress ∧
  readAddress m.carrier (start e).store e.buffer =
    some (.array (List.replicate 16 PV_STX2_SliceUninit.uninitValue))

/-- Initialized UNION slots, with the exact emitted nested constructors. -/
def initialized (v : Data) : Data :=
  PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF9.node110)
    [PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF9.node108)
      [PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF9.node107) [v]]]
/-- Exact first boundary on every arm, plus the row's source value clause. -/
def Post (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (m : Machine) (e : Entry) (impl : Outcome) : Prop :=
  PV_LIB_SLICE_Statements.Post r enc m (start e) e.toEntry (sources e) [e.buffer]
    (fun out v => ∃ values : Fin 16 → Data,
      v = PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF9.node146) [.null] ∧
      readAddress m.carrier (PV_STX2_ToVecCallCallerPost.statusStore out.status) e.buffer =
        some (.array (List.ofFn (fun i => initialized (values i)))) ∧
      ArrayClone r enc g e out (.array (List.ofFn values))) impl

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
end PV_LIB_SLICE_Spec_f9
