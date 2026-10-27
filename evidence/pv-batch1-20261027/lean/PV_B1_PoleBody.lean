import PV_B1_PoleRow
import PV_B1_PoleOriginalEqual
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleBody
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258
abbrev Q := aspis_core.field.QM31
abbrev Rows := PV_B1_PoleInner.Rows

def active (mask : U16) (row : Usize) : Bool :=
  (mask &&& U16.wrapping_shl 1#u16 (UScalar.cast .U32 (row &&& 15#usize))) != 0#u16

def verdictBody (values : Rows) (masks : Array U16 64#usize) (chi : Q)
    (clear : Bool) (row : Usize) : Result (ControlFlow (Bool × Usize) Bool) := do
  if row < Slice.len values then
    let mask ← Array.index_usize masks (Usize.wrapping_shr row 4#u32)
    let r ← Slice.index_usize values row
    ok (cont (clear && PV_B1_PoleRow.rowTest (active mask row) chi r,
      Usize.wrapping_add row 1#usize))
  else ok (done clear)

theorem source (values : Rows) (masks : Array U16 64#usize) (chi : Q)
    (clear : Bool) (row : Usize) :
    all_slots_clear_loop0.body values masks chi clear row = verdictBody values masks chi clear row := by
  unfold all_slots_clear_loop0.body verdictBody
  dsimp only
  by_cases h : row < Slice.len values
  · simp only [h,if_true,lift,bind_tc_ok,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro mask hm
    have hv : row.val < values.val.length := h
    let r := values.val[row.val]'hv
    have hr : Slice.index_usize values row = ok r := PV_B1_ArrayRead.slice_read values row hv
    rw [PV_B1_PoleMiddle.source]
    rw [PV_B1_PoleRow.source values chi clear row _ r hr]
    simp only [hr,bind_tc_ok,active] <;> rfl
  · simp only [h,if_false,bind_tc_ok]

theorem original (values : Rows) (masks : Array U16 64#usize) (chi : Q)
    (clear : Bool) (row : Usize) :
    PV_B1_PoleOriginal.reference.all_slots_clear_loop.body values masks chi clear row =
      verdictBody values masks chi clear row := by
  unfold PV_B1_PoleOriginal.reference.all_slots_clear_loop.body verdictBody
  dsimp only
  by_cases h : row < Slice.len values
  · simp only [h,if_true,lift,bind_tc_ok,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro mask hm
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro r hr
    simp only [PV_B1_ArrayRead.first,PV_B1_ArrayRead.second,bind_tc_ok,
      PV_B1_PoleOriginalEqual.source,PV_B1_PoleRow.rowTest,PV_B1_PoleRow.sideTest,
      active,decide_not,Bool.decide_eq_true,Bool.and_assoc] <;> rfl
  · simp only [h,if_false,bind_tc_ok]
#print axioms source
#print axioms original
end PV_B1_PoleBody
