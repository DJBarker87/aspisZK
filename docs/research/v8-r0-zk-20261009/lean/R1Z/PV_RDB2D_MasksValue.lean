import R1Z.PV_RDB2D_MaskChunk13
namespace R1Z.PV_RDB2D_MasksValue
open PV_RDB2D_MasksLoop
set_option autoImplicit false
def initial : Masks := PV_RDB2D_MaskChunk00.before
def value : Masks := PV_RDB2D_MaskChunk13.after
theorem rows_split : PV_B3P_Sorted133.expected = PV_RDB2D_MaskChunk00.rows ++ (PV_RDB2D_MaskChunk01.rows ++ (PV_RDB2D_MaskChunk02.rows ++ (PV_RDB2D_MaskChunk03.rows ++ (PV_RDB2D_MaskChunk04.rows ++ (PV_RDB2D_MaskChunk05.rows ++ (PV_RDB2D_MaskChunk06.rows ++ (PV_RDB2D_MaskChunk07.rows ++ (PV_RDB2D_MaskChunk08.rows ++ (PV_RDB2D_MaskChunk09.rows ++ (PV_RDB2D_MaskChunk10.rows ++ (PV_RDB2D_MaskChunk11.rows ++ (PV_RDB2D_MaskChunk12.rows ++ (PV_RDB2D_MaskChunk13.rows))))))))))))) := by
  simp only [PV_B3P_Sorted133.expected,PV_RDB2D_MaskChunk00.rows,PV_RDB2D_MaskChunk01.rows,PV_RDB2D_MaskChunk02.rows,PV_RDB2D_MaskChunk03.rows,PV_RDB2D_MaskChunk04.rows,PV_RDB2D_MaskChunk05.rows,PV_RDB2D_MaskChunk06.rows,PV_RDB2D_MaskChunk07.rows,PV_RDB2D_MaskChunk08.rows,PV_RDB2D_MaskChunk09.rows,PV_RDB2D_MaskChunk10.rows,PV_RDB2D_MaskChunk11.rows,PV_RDB2D_MaskChunk12.rows,PV_RDB2D_MaskChunk13.rows,List.cons_append,List.nil_append]
  rfl
theorem concrete : run PV_B3P_Sorted133.expected initial=value := by
  rw [rows_split]
  unfold initial value
  rw [append,PV_RDB2D_MaskChunk00.value]
  rw [append,PV_RDB2D_MaskChunk01.value]
  rw [append,PV_RDB2D_MaskChunk02.value]
  rw [append,PV_RDB2D_MaskChunk03.value]
  rw [append,PV_RDB2D_MaskChunk04.value]
  rw [append,PV_RDB2D_MaskChunk05.value]
  rw [append,PV_RDB2D_MaskChunk06.value]
  rw [append,PV_RDB2D_MaskChunk07.value]
  rw [append,PV_RDB2D_MaskChunk08.value]
  rw [append,PV_RDB2D_MaskChunk09.value]
  rw [append,PV_RDB2D_MaskChunk10.value]
  rw [append,PV_RDB2D_MaskChunk11.value]
  rw [append,PV_RDB2D_MaskChunk12.value]
  exact PV_RDB2D_MaskChunk13.value
theorem length : value.length=64 := rfl
theorem native_rows : run (PV_B3P_Install133.value.val.map (fun x => x.val)) initial=value := by
  rw [PV_B3P_Closure133.value_nat,concrete]

#print axioms rows_split
#print axioms concrete
#print axioms length
#print axioms native_rows
end R1Z.PV_RDB2D_MasksValue
