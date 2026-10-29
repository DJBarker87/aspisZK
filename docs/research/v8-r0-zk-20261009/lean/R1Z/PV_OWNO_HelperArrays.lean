import R1Z.PV_OWNO_HelperResult
set_option autoImplicit false
namespace R1Z.PV_OWNO_HelperArrays
open Aeneas Aeneas.Std PV_OWNK_TowerCanon PV_OWNL_HelperSlots PV_OWNO_HelperResult

/-- The deployed CopyLogUpRow carrier: four fixed two-element arrays. -/
structure CopyRow where
 producer_values : Aeneas.Std.Array Q 2#usize
 producer_weights : Aeneas.Std.Array U32 2#usize
 consumer_values : Aeneas.Std.Array Q 2#usize
 consumer_weights : Aeneas.Std.Array U32 2#usize

def slotsView (values : Aeneas.Std.Array Q 2#usize)
 (weights : Aeneas.Std.Array U32 2#usize) : List Slot :=
 (values.val.zip weights.val).map fun x => ⟨x.2,x.1⟩

def view (r : CopyRow) : Row :=
 ⟨slotsView r.producer_values r.producer_weights,
 slotsView r.consumer_values r.consumer_weights⟩

theorem slotsView_length (values : Aeneas.Std.Array Q 2#usize)
 (weights : Aeneas.Std.Array U32 2#usize) : (slotsView values weights).length = 2 := by
 simp only [slotsView,List.length_map,List.length_zip,values.property,weights.property]
 rfl

/-- All raw field values and weights are admitted by the invariant. -/
theorem row_canonical (inverse : Q → Option Q) (chi : Q) (index : Nat)
 (r : CopyRow) (out : Q)
 (h : rowResult inverse chi index (view r) = .ok out) : Canon out :=
 successful_row inverse chi index (view r) out h

#print axioms slotsView_length
#print axioms row_canonical
end R1Z.PV_OWNO_HelperArrays
