import NBL_SlicePort
set_option autoImplicit false
namespace AspisR1.NBR_RangeGeometry
open Aeneas Aeneas.Std Result

/-- Keep large concrete offset subtraction behind a symbolic theorem. -/
theorem difference (lo hi : Usize) (size : Nat) (delta : hi.val=lo.val+size) :
    hi.val-lo.val=size := by omega

theorem length (input : Slice U8) (lo hi : Usize) (size : Nat)
    (delta : hi.val=lo.val+size) (within : hi.val≤input.val.length) :
    (NBL_SlicePort.segment input lo hi).val.length=size := by
  exact (NBL_SlicePort.length input lo hi (by omega) within).trans (difference lo hi size delta)

#print axioms difference
#print axioms length
end AspisR1.NBR_RangeGeometry
