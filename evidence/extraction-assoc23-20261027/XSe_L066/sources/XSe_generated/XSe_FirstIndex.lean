import XSe_BooleanScan
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_FirstIndex
/-- A chronological first-stop list scan is exactly find? over the matching
stage indices. No accepted-prefix or independently chosen first error. -/
theorem source {I : Type} (good : I → Bool) (fallback : I) (bad : Nat → Bool)
 (items : List I) (start : Nat)
 (agree : ∀ j, j<items.length → bad (start+j)= !good (items[j]?.getD fallback)) :
 XSe_BooleanScan.first good items start=(List.range' start items.length).find? bad := by
 induction items generalizing start with
 | nil => rfl
 | cons item rest ih =>
   have head := agree 0 (by simp)
   simp only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] at head
   simp only [XSe_BooleanScan.first,List.length_cons,List.range'_succ,List.find?_cons,head]
   cases hg : good item with
   | false => rfl
   | true =>
     simp only [hg,Bool.not_true,if_true,Bool.false_eq_true,if_false]
     apply ih (start+1)
     intro j hj
     have h := agree (j+1) (by simp only [List.length_cons];omega)
     simpa only [List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
#print axioms source
end XSe_FirstIndex
