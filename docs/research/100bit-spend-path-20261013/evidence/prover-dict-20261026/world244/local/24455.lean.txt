import R1Z.PDict_RowChunk244_0
import R1Z.PDict_RowChunk244_1
import R1Z.PDict_RowChunk244_2
import R1Z.PDict_RowChunk244_3
import R1Z.PDict_RowChunk244_4
import R1Z.PDict_RowChunk244_5
import R1Z.PDict_RowChunk244_6
import R1Z.PDict_RowChunk244_7
set_option autoImplicit false
namespace R1Z.PDict_RowTable244
open Aeneas Aeneas.Std Result
def values : List U16 := PDict_RowChunk244_0.values ++ PDict_RowChunk244_1.values ++ PDict_RowChunk244_2.values ++ PDict_RowChunk244_3.values ++ PDict_RowChunk244_4.values ++ PDict_RowChunk244_5.values ++ PDict_RowChunk244_6.values ++ PDict_RowChunk244_7.values
theorem length : values.length = 1024 := by
  simp only [values,List.length_append,PDict_RowChunk244_0.length, PDict_RowChunk244_1.length, PDict_RowChunk244_2.length, PDict_RowChunk244_3.length, PDict_RowChunk244_4.length, PDict_RowChunk244_5.length, PDict_RowChunk244_6.length, PDict_RowChunk244_7.length]
theorem bounds : ∀ x ∈ values, x.val < 1024 :=
  (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ PDict_RowChunk244_0.bound PDict_RowChunk244_1.bound) PDict_RowChunk244_2.bound) PDict_RowChunk244_3.bound) PDict_RowChunk244_4.bound) PDict_RowChunk244_5.bound) PDict_RowChunk244_6.bound) PDict_RowChunk244_7.bound)
def table : Array U16 1024#usize :=
  Array.make 1024#usize values (hl := by rw [length]; scalar_tac)

theorem table_val : table.val = values := rfl

theorem index_bound (index : Usize) (small : index.val < 1024) :
    ∃ value : U16, Array.index_usize table index = .ok value ∧ value.val < 1024 := by
  have bound : index.val < table.length := by scalar_tac
  obtain ⟨value,run,atIndex⟩ := WP.spec_imp_exists (Array.index_usize_spec table index bound)
  refine ⟨value,run,bounds value ?_⟩
  rw [atIndex,←table_val]
  exact List.getElem_mem ..

#print axioms length
#print axioms bounds
#print axioms table_val
#print axioms index_bound
end R1Z.PDict_RowTable244
