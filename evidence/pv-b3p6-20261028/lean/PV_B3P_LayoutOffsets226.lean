import PV_B3P_Offset226V3
namespace PV_B3P_LayoutOffsets226
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem fixed_add (a b c : Usize) (hv : a.val + b.val = c.val)
    (hb : a.val + b.val < UScalar.size .Usize) : Usize.wrapping_add a b = c := by
  apply UScalar.eq_of_val_eq
  rw [PV_B3P_Offset226V3.add_value a b hb]
  exact hv
#print axioms fixed_add
theorem c0 : Usize.wrapping_add 70#usize 32#usize = 102#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c0
theorem c1 : Usize.wrapping_add 102#usize 32#usize = 134#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c1
theorem c2 : Usize.wrapping_add 70#usize 33#usize = 103#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c2
theorem c3 : Usize.wrapping_add 102#usize 33#usize = 135#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c3
theorem c4 : Usize.wrapping_add 107#usize 8#usize = 115#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c4
theorem c5 : Usize.wrapping_add 135#usize 8#usize = 143#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c5
theorem c6 : Usize.wrapping_add 115#usize 640#usize = 755#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c6
theorem c7 : Usize.wrapping_add 143#usize 640#usize = 783#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c7
theorem c8 : Usize.wrapping_add 115#usize 672#usize = 787#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c8
theorem c9 : Usize.wrapping_add 143#usize 672#usize = 815#usize := by
  apply fixed_add _ _ _ (by rfl)
  have hb := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac
#print axioms c9
end PV_B3P_LayoutOffsets226
