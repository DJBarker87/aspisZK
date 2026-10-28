import Aeneas.Std
namespace PV_B3P_LayoutIndex226
set_option autoImplicit false

theorem at_segment {α : Type} (pre body post : List α) (i start : Nat)
    (hp : pre.length = start) (lo : start ≤ i) (hi : i < start+body.length) :
    (pre++body++post)[i]? = body[i-start]? := by
  rw [List.append_assoc,List.getElem?_append_right (by omega),hp]
  rw [List.getElem?_append_left (by omega)]

#print axioms at_segment
end PV_B3P_LayoutIndex226
