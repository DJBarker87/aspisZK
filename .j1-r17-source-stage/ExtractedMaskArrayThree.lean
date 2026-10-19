import AspisR1SelectedMaskProbe.Funs

/-! Three-cell reads in the actual Aeneas array runtime. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskArrayThree
open Aeneas.Std
universe u
variable {α : Type u}
@[simp] theorem index0 (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 0#usize = .ok a := rfl
@[simp] theorem index1 (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 1#usize = .ok b := rfl
@[simp] theorem index2 (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 2#usize = .ok c := rfl
#print axioms index0
#print axioms index1
#print axioms index2
end AspisR1.ExtractedMaskArrayThree
