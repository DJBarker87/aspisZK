import AspisR1QueryGeometryActual.Funs
set_option autoImplicit false
namespace NEA_TableA07
open Aeneas Aeneas.Std

theorem canonical (p : U32 × U32) (member : p ∈ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07) :
    p.1.val < 2147483647 ∧ p.2.val < 2147483647 := by
  simp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor <;> decide

#print axioms canonical
end NEA_TableA07
