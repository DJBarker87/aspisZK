import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard355
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (mask : Aeneas.Std.U16) (h : mask ≠ 0#u16) :
 (Aeneas.Std.UScalar.cast .Usize (PV_B3Q_BitCounts.word (PV_B3Q_BitCounts.bits mask).ctz)).val < 16 := by
  exact PV_B3Q_PanicGuards.mask_read_bound mask h
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard355
