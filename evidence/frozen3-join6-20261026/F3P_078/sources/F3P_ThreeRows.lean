import F3P_ArrayIndex
set_option autoImplicit false
namespace AspisR1.F3P_ThreeRows
open Aeneas Aeneas.Std Result

theorem selected {A : Type} (a b c : A) (point : Usize) (hp : point.val<3)
    (row : A) (read : Array.index_usize (Array.make 3#usize [a,b,c]) point=ok row) :
    (point.val=0 ∧ row=a) ∨ (point.val=1 ∧ row=b) ∨ (point.val=2 ∧ row=c) := by
  obtain ⟨bound,same⟩ := F3P_ArrayIndex.cell _ point row read
  have choices : point.val=0 ∨ point.val=1 ∨ point.val=2 := by omega
  rcases choices with h|h|h
  · exact Or.inl ⟨h,by simpa only [h,List.getElem_cons_zero] using same.symm⟩
  · exact Or.inr (Or.inl ⟨h,by simpa only [h,List.getElem_cons_succ,List.getElem_cons_zero] using same.symm⟩)
  · exact Or.inr (Or.inr ⟨h,by simpa only [h,List.getElem_cons_succ,List.getElem_cons_zero] using same.symm⟩)

#print axioms selected
end AspisR1.F3P_ThreeRows
