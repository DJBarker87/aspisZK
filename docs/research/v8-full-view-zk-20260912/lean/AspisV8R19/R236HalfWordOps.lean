import AspisV8R19.R228HalfEncoding
set_option autoImplicit false
namespace AspisV8R19.R236HalfWordOps
open Aeneas Aeneas.Std

theorem unsigned_ops (w : U32) :
    UScalar.or (U32.wrapping_shr w 1#u32)
      (U32.wrapping_shl (UScalar.and w 1#u32) 30#u32) =
      R228HalfEncoding.halfScalar w := by
  apply UScalar.eq_of_val_eq
  change (UScalar.or (U32.wrapping_shr w 1#u32)
    (U32.wrapping_shl (UScalar.and w 1#u32) 30#u32)).bv.toNat =
    (R228HalfEncoding.halfScalar w).bv.toNat
  congr 1
#print axioms unsigned_ops
end AspisV8R19.R236HalfWordOps
