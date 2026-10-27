import FJj_TensorCellValue
import FJj_TensorIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorCellLanes
open Aeneas Aeneas.Std
open FIo_FieldBridge (NQ)

theorem written (input : Slice NQ) (digit : Array NQ 4#usize) (j n : Usize)
    (hn : n.val≤16) (hj : j.val < n.val) (s : Fin 4) :
    FJj_TensorCellValue.model input digit j n (j.val+s.val*n.val)=
      FJj_QMSlice.value input j.val*FJf_QMArray.value digit s.val := by
  have o0 := FJj_TensorIndex.value j n 0#usize hn hj (by decide)
  have o1 := FJj_TensorIndex.value j n 1#usize hn hj (by decide)
  have o2 := FJj_TensorIndex.value j n 2#usize hn hj (by decide)
  have o3 := FJj_TensorIndex.value j n 3#usize hn hj (by decide)
  change (FJj_TensorCell.index j n 0#usize).val=j.val+0*n.val at o0
  change (FJj_TensorCell.index j n 1#usize).val=j.val+1*n.val at o1
  change (FJj_TensorCell.index j n 2#usize).val=j.val+2*n.val at o2
  change (FJj_TensorCell.index j n 3#usize).val=j.val+3*n.val at o3
  unfold FJj_TensorCellValue.model
  rw [o0,o1,o2,o3]
  fin_cases s <;> split_ifs <;> first | rfl | omega
#print axioms written
end AspisR1.FJj_TensorCellLanes
end
