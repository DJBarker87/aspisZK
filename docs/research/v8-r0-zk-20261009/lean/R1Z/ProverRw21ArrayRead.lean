import R1Z.ProverRwP6ArrayRead
set_option autoImplicit false
namespace R1Z.ProverRw21ArrayRead
open Aeneas Aeneas.Std Result

def element {α : Type} {n : Usize} (a : Array α n) (i : Fin n.val) : α :=
  a.val[i.val]'(by rw [a.property]; exact i.isLt)

theorem exact_read {α : Type} {n : Usize} (a : Array α n) (i : Usize) (h : i.val<n.val) :
    Array.index_usize a i=ok (element a ⟨i.val,h⟩) := by
  have bound : i.val<a.val.length := by rw [a.property];exact h
  simp only [Array.index_usize,Array.getElem?_Usize_eq,List.getElem?_eq_getElem bound,element]

theorem values {α : Type} {n : Usize} (a : Array α n) : List.ofFn (element a)=a.val := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,a.property]
  · intro i hi hj
    simp only [List.getElem_ofFn,element]

theorem four {α : Type} (a : Array α 4#usize) :
    a.val=[element a ⟨0,by decide⟩,element a ⟨1,by decide⟩,element a ⟨2,by decide⟩,element a ⟨3,by decide⟩] := by
  rw [← values a]
  rfl

#print axioms element
#print axioms exact_read
#print axioms values
#print axioms four
end R1Z.ProverRw21ArrayRead
