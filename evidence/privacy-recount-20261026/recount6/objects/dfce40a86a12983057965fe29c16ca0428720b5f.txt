import PV_B1_Orig258_PoleIndex
import PV_B1_MaskShift
import PV_B1_OriginalEqualTotal
import PV_B1_ReadTotal
set_option autoImplicit false
noncomputable section
namespace PV_B1_Orig258_Op258Step
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258

/-- Every indexed read and all four raw-word comparisons succeed on one valid row.
No numerical canonicality premise is imposed on the QM31 payloads. -/
theorem total
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (clear : Bool) (row : Usize) (hrow : row < Slice.len values) (hmask : row.val < 1024) :
    ∃ next, PV_B1_PoleOriginal.reference.all_slots_clear_loop.body values masks chi clear row =
      ok (cont (next,Usize.wrapping_add row 1#usize)) := by
  obtain ⟨mask,hm⟩ := PV_B1_ReadTotal.read_total masks (Usize.wrapping_shr row 4#u32)
    ((PV_B1_MaskShift.in_bounds row).mpr hmask)
  obtain ⟨r,hr⟩ : ∃ r, Slice.index_usize values row = ok r :=
    ⟨_,PV_B1_Orig258_PoleIndex.slice_read values row hrow⟩
  obtain ⟨left,hl⟩ := PV_B1_ReadTotal.read_total r 0#usize (by decide)
  obtain ⟨right,hri⟩ := PV_B1_ReadTotal.read_total r 1#usize (by decide)
  obtain ⟨a,ha⟩ := PV_B1_ReadTotal.read_total left 0#usize (by decide)
  obtain ⟨b,hb⟩ := PV_B1_ReadTotal.read_total left 1#usize (by decide)
  obtain ⟨c,hc⟩ := PV_B1_ReadTotal.read_total right 0#usize (by decide)
  obtain ⟨d,hd⟩ := PV_B1_ReadTotal.read_total right 1#usize (by decide)
  obtain ⟨e0,he0⟩ := PV_B1_OriginalEqualTotal.total chi a
  obtain ⟨e1,he1⟩ := PV_B1_OriginalEqualTotal.total chi b
  obtain ⟨e2,he2⟩ := PV_B1_OriginalEqualTotal.total chi c
  obtain ⟨e3,he3⟩ := PV_B1_OriginalEqualTotal.total chi d
  simp only [PV_B1_PoleOriginal.reference.all_slots_clear_loop.body,if_pos hrow,lift,bind_tc_ok,
    hm,hr,hl,hri,ha,hb,hc,hd,he0,he1,he2,he3]
  exact ⟨_,rfl⟩
#print axioms total
end PV_B1_Orig258_Op258Step
