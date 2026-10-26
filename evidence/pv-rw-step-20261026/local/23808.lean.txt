import Std
set_option autoImplicit false
namespace R1Z.PV_RW_IteratorMeasure

def remaining {T : Type} (values : List T) (cursor : Nat) : Nat := values.length-cursor

theorem positive {T : Type} (values : List T) (cursor : Nat) :
    0 < remaining values cursor ↔ cursor < values.length := by
  unfold remaining
  omega

theorem successor {T : Type} (values : List T) (cursor : Nat)
    (h : cursor < values.length) :
    remaining values (cursor+1)+1=remaining values cursor := by
  unfold remaining
  omega

theorem exhausted {T : Type} (values : List T) (cursor : Nat) :
    remaining values cursor=0 ↔ values.length≤cursor := by
  unfold remaining
  omega

theorem suffix_length {T : Type} (values : List T) (cursor : Nat) :
    (values.drop cursor).length=remaining values cursor := by
  simp only [List.length_drop,remaining]

theorem cursor_unique {T : Type} (values : List T) (left right : Nat)
    (hl : left ≤ values.length) (hr : right ≤ values.length)
    (same : remaining values left=remaining values right) : left=right := by
  unfold remaining at same
  omega

theorem exact_fuel {T : Type} (values : List T) (cursor : Nat)
    (h : cursor≤values.length) : cursor+remaining values cursor=values.length := by
  unfold remaining
  omega
#print axioms positive
#print axioms successor
#print axioms exhausted
#print axioms suffix_length
#print axioms cursor_unique
#print axioms exact_fuel
end R1Z.PV_RW_IteratorMeasure
