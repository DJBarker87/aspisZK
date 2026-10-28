import Aeneas.Std
namespace PV_B3P_ReadTwenty226
open Aeneas Aeneas.Std
set_option autoImplicit false
def values {α : Type} (a : Array α 20#usize) : List α := [
  a.val[0]'(by rw [a.property]; scalar_tac),
  a.val[1]'(by rw [a.property]; scalar_tac),
  a.val[2]'(by rw [a.property]; scalar_tac),
  a.val[3]'(by rw [a.property]; scalar_tac),
  a.val[4]'(by rw [a.property]; scalar_tac),
  a.val[5]'(by rw [a.property]; scalar_tac),
  a.val[6]'(by rw [a.property]; scalar_tac),
  a.val[7]'(by rw [a.property]; scalar_tac),
  a.val[8]'(by rw [a.property]; scalar_tac),
  a.val[9]'(by rw [a.property]; scalar_tac),
  a.val[10]'(by rw [a.property]; scalar_tac),
  a.val[11]'(by rw [a.property]; scalar_tac),
  a.val[12]'(by rw [a.property]; scalar_tac),
  a.val[13]'(by rw [a.property]; scalar_tac),
  a.val[14]'(by rw [a.property]; scalar_tac),
  a.val[15]'(by rw [a.property]; scalar_tac),
  a.val[16]'(by rw [a.property]; scalar_tac),
  a.val[17]'(by rw [a.property]; scalar_tac),
  a.val[18]'(by rw [a.property]; scalar_tac),
  a.val[19]'(by rw [a.property]; scalar_tac) ]
theorem same {α : Type} (a : Array α 20#usize) : values a = a.val := by
  apply List.ext_getElem
  · simp only [values,List.length_cons,List.length_nil,a.property]; rfl
  · intro i hi hj
    have hb : i < 20 := by simpa only [a.property,show (20#usize).val = 20 from rfl] using hj
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
#print axioms same
end PV_B3P_ReadTwenty226
