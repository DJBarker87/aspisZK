import PV_B3P_Offset226V3
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem next_exact (i j : Usize) (h : i.val+1=j.val) :
    Usize.wrapping_add i 1#usize = j := by
  apply UScalar.eq_of_val_eq
  rw [PV_B3P_Offset226V3.add_value i 1#usize (by
    have hj : j.val < UScalar.size .Usize := by
      simpa only [UScalar.size] using j.hBounds
    change i.val+1 < _
    omega)]
  exact h

theorem previous_exact (i j : Usize) (h : i.val=j.val+1) :
    Usize.wrapping_sub i 1#usize = j := by
  apply UScalar.eq_of_val_eq
  rw [PV_B3P_Offset226V3.sub_value i 1#usize (by change (1 : Nat) ≤ i.val; omega)]
  change i.val-1=j.val
  omega

#print axioms next_exact
#print axioms previous_exact
