import PV_B3P_ClosureLinks14227
namespace PV_B3Q_MetadataActual
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Value interpretation of Rust ptr::metadata on a slice reference. The
intrinsic's machine realization remains V370; the wrapper changes no storage. -/
def source_len {α : Type} (slice : Slice α) : Usize :=
 Usize.ofNatCore slice.val.length (by have h := slice.property; scalar_tac)

theorem length_value {α : Type} (slice : Slice α) :
 (source_len slice).val = slice.val.length := rfl

theorem binding {α : Type} (slice : Slice α) : source_len slice = slice.len := rfl

theorem actual_metadata_link (α : Type) : PV_B3P_Link_std_dependency_closure14
 (fun _ : Unit => Slice α → Usize) (fun _ => @source_len α) (fun _ => Slice.len) := by
 intro _
 funext s
 exact binding s
#print axioms length_value
#print axioms binding
#print axioms actual_metadata_link
end PV_B3Q_MetadataActual
