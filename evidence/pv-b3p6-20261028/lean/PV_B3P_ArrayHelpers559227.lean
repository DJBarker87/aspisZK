import PV_B3P_DependencyClosure557227
namespace PV_B3P_ArrayHelpers559227
open Aeneas Aeneas.Std core.ops.range
set_option autoImplicit false
/-- Source array Index forwards the shared slice to its SliceIndex instance.
The existing range source law supplies the two checks. Raw-pointer realization
of the array/slice cast remains a separate source obligation. -/
def read_source {α : Type} {n : Usize} (a : Array α n) (r : Range Usize) :
    Result (Slice α) := PV_B3Q_RangeIndexSource.source a.to_slice r

theorem read_binding {α : Type} {n : Usize} (a : Array α n) (r : Range Usize) :
    read_source a r = core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice α)) a r :=
  PV_B3Q_RangeIndexSource.binding a.to_slice r

/-- Source array IndexMut delegates the range borrow and composes its back
continuation with the array cast's back continuation. Neither is discarded. -/
def write_source {α : Type} {n : Usize} (a : Array α n) (r : RangeTo Usize) :
    Result (Slice α × (Slice α → Array α n)) := do
  let (s,back) ← core.slice.index.SliceIndexRangeToUsizeSlice.index_mut r a.to_slice
  .ok (s,fun out => Array.from_slice a (back out))

theorem write_binding {α : Type} {n : Usize} (a : Array α n) (r : RangeTo Usize) :
    write_source a r = core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice α)) a r := rfl

/-- Exact helper 318 instantiation: shared range read of the sixteen-QM31 array. -/
theorem read16_binding {α : Type} (a : Array α 16#usize) (r : Range Usize) :
    read_source a r = core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice α)) a r :=
  read_binding a r

/-- Exact helper 422 const/index specialization: mutable prefix of four cells. -/
theorem write4_binding {α : Type} (a : Array α 4#usize) (r : RangeTo Usize) :
    write_source a r = core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice α)) a r :=
  write_binding a r

/-- A source copy under the non-overlap/valid-reference primitive contract:
length mismatch panics; equal lengths replace all destination values. The
ptr::copy_nonoverlapping association is not inferred from this control law. -/
def copy_source {α : Type} (dest src : Slice α) : Result (Slice α) :=
  if dest.len = src.len then .ok src else .fail .panic

theorem copy_binding {α : Type} (inst : core.marker.Copy α) (dest src : Slice α) :
    copy_source dest src = core.slice.Slice.copy_from_slice inst dest src := rfl

/-- The copy's panic formatter is unreachable when the borrowed destination
and source lengths agree. This is a local event guard, not whole-cone safety. -/
theorem copy_no_panic {α : Type} (dest src : Slice α) (same : dest.len = src.len) :
    copy_source dest src = .ok src := by
  exact if_pos same

#print axioms read_binding
#print axioms write_binding
#print axioms read16_binding
#print axioms write4_binding
#print axioms copy_binding
#print axioms copy_no_panic
end PV_B3P_ArrayHelpers559227
