import R1Z.PV_CB3_PoleIndex
import R1Z.PV_CB3_MaskShift
import R1Z.PV_CB3_Op258Equal
import R1Z.PV_CB3_StagedComposition
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258Step
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull

/-- Every indexed read and all four raw-word comparisons succeed on one valid row.
No numerical canonicality premise is imposed on the QM31 payloads. -/
theorem total
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (clear : Bool) (row : Usize) (hrow : row < Slice.len values) (hmask : row.val < 1024) :
    ∃ next, PV_CB3_Op258Ref.reference.all_slots_clear_loop.body values masks chi clear row =
      ok (cont (next,Usize.wrapping_add row 1#usize)) := by
  obtain ⟨mask,hm⟩ := PV_CB3_StagedComposition.read_total masks (Usize.wrapping_shr row 4#u32)
    ((PV_CB3_MaskShift.in_bounds row).mpr hmask)
  obtain ⟨r,hr⟩ : ∃ r, Slice.index_usize values row = ok r :=
    ⟨_,PV_CB3_PoleIndex.slice_read values row hrow⟩
  obtain ⟨left,hl⟩ := PV_CB3_StagedComposition.read_total r 0#usize (by decide)
  obtain ⟨right,hri⟩ := PV_CB3_StagedComposition.read_total r 1#usize (by decide)
  obtain ⟨a,ha⟩ := PV_CB3_StagedComposition.read_total left 0#usize (by decide)
  obtain ⟨b,hb⟩ := PV_CB3_StagedComposition.read_total left 1#usize (by decide)
  obtain ⟨c,hc⟩ := PV_CB3_StagedComposition.read_total right 0#usize (by decide)
  obtain ⟨d,hd⟩ := PV_CB3_StagedComposition.read_total right 1#usize (by decide)
  obtain ⟨e0,he0⟩ := PV_CB3_Op258Equal.total chi a
  obtain ⟨e1,he1⟩ := PV_CB3_Op258Equal.total chi b
  obtain ⟨e2,he2⟩ := PV_CB3_Op258Equal.total chi c
  obtain ⟨e3,he3⟩ := PV_CB3_Op258Equal.total chi d
  simp only [PV_CB3_Op258Ref.reference.all_slots_clear_loop.body,if_pos hrow,lift,bind_tc_ok,
    hm,hr,hl,hri,ha,hb,hc,hd,he0,he1,he2,he3]
  exact ⟨_,rfl⟩
#print axioms total
end R1Z.PV_CB3_Op258Step
