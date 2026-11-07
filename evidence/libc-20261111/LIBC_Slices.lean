import LIBC_Bytes
import MultiproofConeSlices
set_option autoImplicit false
noncomputable section
namespace LIBC_Slices
open Aeneas Aeneas.Std
/-- End-index slices commute with the byte embedding on every source carrier. -/
theorem bytes_sub (b : Slice U8) (lo hi : Usize) :
 LIB_Carriers.bytes (AspisR1.MultiproofConeSlices.sub b lo hi) =
 RSL.slice (LIB_Carriers.bytes b) lo.val hi.val := by
 change List.map _ ((b.val.drop lo.val).take (hi.val-lo.val)) =
  ((List.map _ b.val).drop lo.val).take (hi.val-lo.val)
 rw [List.map_take,List.map_drop]
theorem raw_sub (b : RSL.Bytes) (bound : b.length ≤ Usize.max) (lo hi : Usize) :
 LIBC_Bytes.raw (RSL.slice b lo.val hi.val) =
 AspisR1.MultiproofConeSlices.sub (LIBC_Bytes.raw b) lo hi := by
 have h := bytes_sub (LIBC_Bytes.raw b) lo hi
 rw [LIBC_Bytes.to_native b bound] at h
 rw [←h,LIBC_Bytes.from_native]
#print axioms bytes_sub
#print axioms raw_sub
end LIBC_Slices
