import NGM_ReferenceErrors
set_option autoImplicit false
noncomputable section
namespace NGM_ReferenceResult
open Aeneas Aeneas.Std Result NGM_FinishRef
attribute [local instance] Classical.propDecidable
theorem dot_error (next : Usize) (rhs first claim : Word) (error : U8) :
 project true next rhs ⟨.Ok first,.Ok claim,.Ok (),.Ok claim,.Err error⟩=ok (.Err error) := by
 simp [project,finish_ref,event,Array.update,Array.repeat,lift,Usize.wrapping_add,NGM_WordArrayEquality.arrays_ne]

theorem counter_mismatch (next : Usize) (rhs first claim actual : Word) (different : next≠22#usize) :
 project true next rhs ⟨.Ok first,.Ok claim,.Ok (),.Ok claim,.Ok actual⟩=ok (.Err 5#u8) := by
 simp [project,finish_ref,event,Array.update,Array.repeat,lift,Usize.wrapping_add,NGM_WordArrayEquality.arrays_ne,different]

theorem value_mismatch (rhs first claim actual : Word) (different : actual≠rhs) :
 project true 22#usize rhs ⟨.Ok first,.Ok claim,.Ok (),.Ok claim,.Ok actual⟩=ok (.Err 5#u8) := by
 simp [project,finish_ref,event,Array.update,Array.repeat,lift,Usize.wrapping_add,NGM_WordArrayEquality.arrays_ne,different]

theorem accepted (rhs first claim : Word) :
 project true 22#usize rhs ⟨.Ok first,.Ok claim,.Ok (),.Ok claim,.Ok rhs⟩=ok (.Ok ()) := by
 simp [project,finish_ref,event,Array.update,Array.repeat,lift,Usize.wrapping_add,NGM_WordArrayEquality.arrays_ne]

#print axioms dot_error
#print axioms counter_mismatch
#print axioms value_mismatch
#print axioms accepted
end NGM_ReferenceResult
end
