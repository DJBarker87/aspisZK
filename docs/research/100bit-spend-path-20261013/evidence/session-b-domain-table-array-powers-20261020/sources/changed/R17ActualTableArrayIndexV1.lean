import AspisR1QueryGeometryActual.Funs
import R17ArrayIndexMake
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace R17ActualTableArrayIndexV1

 theorem tableA_index_entries (i : Usize) (hi : i.val < 512) :
    Array.index_usize AspisR1QueryGeometryActual.fast_domain.TABLE_A i =
      .ok (AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[i.val]'(by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries_length]; exact hi)) := by
  rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A]
  exact R17ArrayIndexMake.index_make_get 512#usize
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries
    (by simpa using AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries_length)
    i hi

 theorem tableB_index_entries (i : Usize) (hi : i.val < 512) :
    Array.index_usize AspisR1QueryGeometryActual.fast_domain.TABLE_B i =
      .ok (AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[i.val]'(by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries_length]; exact hi)) := by
  rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B]
  exact R17ArrayIndexMake.index_make_get 512#usize
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries
    (by simpa using AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries_length)
    i hi

#print axioms tableA_index_entries
#print axioms tableB_index_entries
end R17ActualTableArrayIndexV1
