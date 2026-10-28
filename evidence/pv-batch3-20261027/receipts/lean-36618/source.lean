import PV_B3_MaskSparseStep
namespace PV_B3_MaskSparseScalar
open Aeneas Aeneas.Std PV_B3_MaskSparseStep
set_option autoImplicit false
#print Usize.wrapping_shr
#print Usize.wrapping_add
#print UScalar.cast_val_eq

theorem block_value (p : Usize) : (block p).val = p.val / 16 := by
  unfold block Usize.wrapping_shr
  simp_scalar

#print axioms block_value
end PV_B3_MaskSparseScalar
