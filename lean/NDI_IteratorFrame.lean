import Aeneas
set_option autoImplicit false
namespace NDI_IteratorFrame
open Aeneas Aeneas.Std

theorem remainder {α : Type} (xs : List α) (start count : Nat)
    (fit : start+count≤xs.length) :
    ((xs.drop start).take count).length=count := by simp;omega

theorem next_remainder {α : Type} (xs : List α) (start count : Nat)
    (active : 0<count) :
    ((xs.drop start).take count).drop 1=(xs.drop (start+1)).take (count-1) := by
  rw [List.drop_take,List.drop_drop]

theorem selected {α : Type} (xs : List α) (start count j : Nat) (active : j<count) :
    ((xs.drop start).take count)[j]?=xs[start+j]? := by
  rw [List.getElem?_take,if_pos active,List.getElem?_drop]

theorem shape_tail (j : Nat) (active : j<7) : 9+j<16 ∧ 9+(j+1)≤16 := by omega

theorem query_prefix (i j : Nat) (indexBound : i < 22) (prefixBound : j < i) :
    j<22 ∧ j+1 ≤ i ∧ i+1≤22 := by omega

#print axioms remainder
#print axioms next_remainder
#print axioms selected
#print axioms shape_tail
#print axioms query_prefix
end NDI_IteratorFrame
