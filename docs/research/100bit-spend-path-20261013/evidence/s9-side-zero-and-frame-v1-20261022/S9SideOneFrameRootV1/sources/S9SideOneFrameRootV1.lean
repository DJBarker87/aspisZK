import S9SideOneTailRootV1
import S9ArrayWriteScheduleRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S9SideOneFrameRootV1
open AspisR1S9HelperP6
abbrev W := field.WideExact
abbrev Q := field.QM31
abbrev A := Array W (4#usize)
local notation "cell" => S9ArrayWriteScheduleRootV1.cells

theorem sideOneTail_preserves_cell_zero
    (old ap1 out : A) (low all first2 : W) (q4 q16 : Q)
    (h : S9SideOneTailRootV1.sideOneTail old ap1 low all first2 q4 q16 = .ok out) :
    cell out 0 = cell old 0 := by
  obtain ⟨vold,i,last,scaled,prod,added,a,pall,v2,b,pfirst,q3,v3,
      hread,hi,hlast,hscaled,hprod,hadded,ha,hpall,hv2,hb,hpfirst,hq3,hv3,hout⟩ :=
    S9SideOneTailRootV1.sideOneTail_success_children
      old ap1 low all first2 q4 q16 out h
  rw [S9ArrayWriteScheduleRootV1.update_cells b out 3#usize v3 (by decide) hout 0,
      S9ArrayWriteScheduleRootV1.update_cells a b 2#usize v2 (by decide) hb 0,
      S9ArrayWriteScheduleRootV1.update_cells old a 1#usize added (by decide) ha 0]
  rfl

#print axioms sideOneTail_preserves_cell_zero
end AspisR1.S9SideOneFrameRootV1
