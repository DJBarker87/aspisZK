import Aeneas.Std
namespace PV_B3P_ArrayEight226
open Aeneas Aeneas.Std
set_option autoImplicit false

def readEight {α : Type} (a : Array α 8#usize) : List α := [
  a.val[0]'(by rw [a.property]; scalar_tac),
  a.val[1]'(by rw [a.property]; scalar_tac),
  a.val[2]'(by rw [a.property]; scalar_tac),
  a.val[3]'(by rw [a.property]; scalar_tac),
  a.val[4]'(by rw [a.property]; scalar_tac),
  a.val[5]'(by rw [a.property]; scalar_tac),
  a.val[6]'(by rw [a.property]; scalar_tac),
  a.val[7]'(by rw [a.property]; scalar_tac) ]
theorem values {α : Type} (a : Array α 8#usize) : readEight a = a.val := by
  apply List.ext_getElem
  · simp only [readEight,List.length_cons,List.length_nil,a.property]
    rfl
  · intro i hi hj
    have hb : i < 8 := by simpa only [a.property] using hj
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

#print axioms values
end PV_B3P_ArrayEight226
