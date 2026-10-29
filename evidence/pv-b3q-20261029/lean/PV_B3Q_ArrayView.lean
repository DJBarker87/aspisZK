import PV_B3P_ClosureLinks14227
namespace PV_B3Q_ArrayView
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Deployed array::as_slice/as_mut_slice are unsizings of self, not copies.
The view's native base pointer is unchanged; pointer realization is V370. -/
def source_view {α : Type} {n : Usize} (xs : Array α n) : Slice α := Array.to_slice xs
theorem view_contents {α : Type} {n : Usize} (xs : Array α n) :
    (source_view xs).val = xs.val := rfl
theorem view_length {α : Type} {n : Usize} (xs : Array α n) :
    (source_view xs).val.length = n.val := xs.property
/-- The shared array wrapper delegates to the slice body after unsizing.
All out-of-bounds and success tags must agree with the standing array model. -/
def source_read {α : Type} {n : Usize} (xs : Array α n) (index : Usize) : Result α :=
 Slice.index_usize (source_view xs) index
theorem read_binding {α : Type} {n : Usize} (xs : Array α n) (index : Usize) :
    source_read xs index = Array.index_usize xs index := by
 rfl
/-- The logical restoration associated with a mutable slice unsizing retains
exactly the same list update on the original fixed-size array. -/
theorem restore_view {α : Type} {n : Usize} (xs : Array α n) (index : Usize) (value : α) :
    source_view (Array.set xs index value) = Slice.set (source_view xs) index value := by
 apply Subtype.ext
 rfl
/-- Concrete standard family for both shared/mutable unsizing bodies. -/
theorem unsizing_link (α : Type) (n : Usize) : PV_B3P_Link_std_dependency_closure14
    (fun _ : Bool => Array α n → Slice α) (fun _ => @source_view α n)
    (fun _ => Array.to_slice) := by
 intro _
 rfl
#print axioms view_contents
#print axioms view_length
#print axioms read_binding
#print axioms restore_view
#print axioms unsizing_link
end PV_B3Q_ArrayView
