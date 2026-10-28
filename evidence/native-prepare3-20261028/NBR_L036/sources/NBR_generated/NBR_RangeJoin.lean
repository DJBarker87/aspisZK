import NBR_RangeGeometry
set_option autoImplicit false
namespace AspisR1.NBR_RangeJoin
open Aeneas Aeneas.Std Result

theorem first (left right both : Slice U8) (hi : Usize)
    (bytes : both.val=left.val++right.val) (size : hi.val=left.val.length) :
    NBL_SlicePort.segment both 0#usize hi=left := by
  apply Subtype.ext
  change (both.val.drop 0).take (hi.val-0)=left.val
  rw [List.drop_zero,Nat.sub_zero,bytes,size,List.take_left]

theorem suffix (left right both : Slice U8) (lo hi : Usize)
    (bytes : both.val=left.val++right.val) (start : lo.val=left.val.length)
    (size : hi.val=lo.val+right.val.length) :
    NBL_SlicePort.segment both lo hi=right := by
  apply Subtype.ext
  change (both.val.drop lo.val).take (hi.val-lo.val)=right.val
  rw [NBR_RangeGeometry.difference lo hi right.val.length size,bytes,start,List.drop_left,List.take_length]

#print axioms first
#print axioms suffix
end AspisR1.NBR_RangeJoin
