import PV_B1_PoleMiddle
import PV_B1_ArrayRead
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleRow
open Aeneas Aeneas.Std Result PV_B1_258 PV_B1_PoleInner
local instance : DecidableEq Q := Classical.decEq _
abbrev Pair := Array Q 2#usize
abbrev Row := Array Pair 2#usize

def sideTest (active : Bool) (chi : Q) (pair : Pair) : Bool :=
  !(active && decide (chi=PV_B1_ArrayRead.get2 pair 0)) &&
  !(active && decide (chi=PV_B1_ArrayRead.get2 pair 1))

def rowTest (active : Bool) (chi : Q) (r : Row) : Bool :=
  sideTest active chi (PV_B1_ArrayRead.get2 r 0) &&
  sideTest active chi (PV_B1_ArrayRead.get2 r 1)

theorem side_value (values : Rows) (chi : Q) (clear : Bool) (row side : Usize)
    (active : Bool) (r : Row) (pair : Pair)
    (hr : Slice.index_usize values row = ok r)
    (hs : Array.index_usize r side = ok pair) :
    two values chi clear row active side = ok (clear && sideTest active chi pair) := by
  simp only [two,read,hr,hs,PV_B1_ArrayRead.first,PV_B1_ArrayRead.second,
    bind_tc_ok,PV_B1_PoleKeep.source,sideTest,Bool.and_assoc] <;> rfl

theorem source (values : Rows) (chi : Q) (clear : Bool) (row : Usize)
    (active : Bool) (r : Row) (hr : Slice.index_usize values row = ok r) :
    PV_B1_PoleMiddle.twoSides values chi clear row active = ok (clear && rowTest active chi r) := by
  unfold PV_B1_PoleMiddle.twoSides
  rw [side_value values chi clear row 0#usize active r _ hr (PV_B1_ArrayRead.first r)]
  simp only [bind_tc_ok]
  rw [side_value values chi _ row 1#usize active r _ hr (PV_B1_ArrayRead.second r)]
  simp only [rowTest,Bool.and_assoc]
#print axioms side_value
#print axioms source
end PV_B1_PoleRow
