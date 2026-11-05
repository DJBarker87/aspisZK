import NHF_SegmentedFrame
set_option autoImplicit false
namespace AspisR1.NHF_ScalarWindow
open Aeneas Aeneas.Std
/-- Physical field layout's value interpretation: one native typed u8 read
from the SAME complete arbitrary proof. No sparse/zero outside bytes. -/
theorem read (prefix field suffix : List U8) (i : Nat) (inside : i<field.length) :
 (prefix++field++suffix)[prefix.length+i]?=field[i]? := by
 have middle : ((prefix++field++suffix).drop prefix.length).take field.length=field := by
   rw [List.append_assoc,List.drop_left,List.take_left]
 have same:=congrArg (fun xs : List U8=>xs[i]?) middle
 simpa only [List.getElem?_take,if_pos inside,List.getElem?_drop] using same
/-- Every proof admits a segmented representation at every checked row window. -/
theorem represent (bytes : List U8) (start width : Nat) (bound : start+width≤bytes.length) :
 (bytes.take start).length=start ∧ ((bytes.drop start).take width).length=width ∧
 (bytes.drop (start+width)).length=bytes.length-start-width ∧
 bytes.take start ++ (bytes.drop start).take width ++ bytes.drop (start+width)=bytes := by
 refine ⟨?_,?_,?_,?_⟩
 · simp only [List.length_take];omega
 · simp only [List.length_take,List.length_drop];omega
 · simp only [List.length_drop];omega
 · rw [List.append_assoc,←List.drop_drop, List.take_append_drop,List.take_append_drop]
#print axioms read
#print axioms represent
end AspisR1.NHF_ScalarWindow
