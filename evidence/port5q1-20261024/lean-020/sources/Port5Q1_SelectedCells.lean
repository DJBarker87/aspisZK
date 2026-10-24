import Port5Q1_ListCells
set_option autoImplicit false
namespace AspisR1.Port5Q1_SelectedCells
open Aeneas Aeneas.Std

def selected (queries : Array U32 22#usize) (start end1 : Usize) :=
  (queries.val.drop start.val).take (end1.val-start.val)

theorem length (queries : Array U32 22#usize) (start end1 : Usize)
    (order : start.val≤end1.val) (bound : end1.val≤22) :
    (selected queries start end1).length=end1.val-start.val := by
  unfold selected
  rw [List.length_take,List.length_drop]
  have size : queries.val.length=22 := queries.property
  rw [size]
  omega

theorem get (queries : Array U32 22#usize) (start end1 : Usize) (i : Nat)
    (hi : i<end1.val-start.val) :
    (selected queries start end1)[i]?=queries.val[start.val+i]? := by
  unfold selected
  rw [List.getElem?_take]
  rw [if_pos hi,List.getElem?_drop]

#print axioms length
#print axioms get
end AspisR1.Port5Q1_SelectedCells
