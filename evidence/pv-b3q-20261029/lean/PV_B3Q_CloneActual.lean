import PV_B3P_ClosureLinks14227
namespace PV_B3Q_CloneActual
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
inductive Body where | usize_clone | bool_clone | usize_clone_from | bool_clone_from
def Signature : Body → Type
 | .usize_clone => Usize → Usize
 | .bool_clone => Bool → Bool
 | .usize_clone_from => Usize → Usize → Usize
 | .bool_clone_from => Bool → Bool → Result Bool
/-- Exact primitive carriers, including the caller-visible updated self for
clone_from. Copy scalar old values have no destructor. -/
def source : (body : Body) → Signature body
 | .usize_clone => fun borrowed => borrowed
 | .bool_clone => fun borrowed => borrowed
 | .usize_clone_from => fun _ source => source
 | .bool_clone_from => fun _ source => .ok source
def model : (body : Body) → Signature body
 | .usize_clone => core.clone.impls.CloneUsize.clone
 | .bool_clone => core.clone.impls.CloneBool.clone
 | .usize_clone_from => core.clone.impls.CloneUsize.clone_from
 | .bool_clone_from => core.clone.Clone.clone_from core.clone.CloneBool
theorem primitive_clone_links : PV_B3P_Link_std_dependency_closure14 Signature source model := by
 intro body
 cases body <;> rfl
#print axioms primitive_clone_links
#print core.cmp.impls.PartialEqU32.eq
#print core.cmp.impls.PartialEqU32.ne
#print core.cmp.impls.PartialEqU64.eq
#print core.cmp.impls.PartialEqUsize.eq
#print core.slice.cmp.PartialEqSlice.eq
end PV_B3Q_CloneActual
