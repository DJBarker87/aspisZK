import PV_B3P_MaskStep132
import PV_B3P_Offset226V3
namespace PV_B3P_MaskLoopBounds132
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem row_next (r : Usize) (hr : r.val < 1024) :
    (Usize.wrapping_add r 1#usize).val = r.val + 1 ∧
    1024 - (Usize.wrapping_add r 1#usize).val < 1024-r.val := by
  have hb : r.val + (1#usize).val < UScalar.size .Usize := by
    have hm := Usize.cMax_bound_concrete.1
    rw [UScalar.size_def]
    scalar_tac
  rw [PV_B3P_Offset226V3.add_value r 1#usize hb]
  change r.val+1 = r.val+1 ∧ 1024-(r.val+1) < 1024-r.val
  omega

theorem column_next (c : Usize) (hc : c.val < 16) :
    (Usize.wrapping_add c 1#usize).val = c.val + 1 ∧
    16 - (Usize.wrapping_add c 1#usize).val < 16-c.val := by
  have hb : c.val + (1#usize).val < UScalar.size .Usize := by
    have hm := Usize.cMax_bound_concrete.1
    rw [UScalar.size_def]
    scalar_tac
  rw [PV_B3P_Offset226V3.add_value c 1#usize hb]
  change c.val+1 = c.val+1 ∧ 16-(c.val+1) < 16-c.val
  omega

theorem count_next (n : Usize) (hn : n.val < 3803) :
    (Usize.wrapping_add n 1#usize).val = n.val + 1 ∧
    (Usize.wrapping_add n 1#usize).val ≤ 3803 := by
  have hb : n.val + (1#usize).val < UScalar.size .Usize := by
    have hm := Usize.cMax_bound_concrete.1
    rw [UScalar.size_def]
    scalar_tac
  rw [PV_B3P_Offset226V3.add_value n 1#usize hb]
  change n.val+1 = n.val+1 ∧ n.val+1 ≤ 3803
  omega
#print axioms row_next
#print axioms column_next
#print axioms count_next
end PV_B3P_MaskLoopBounds132
