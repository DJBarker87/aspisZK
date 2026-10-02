import AspisV8R19.R228HalfEncoding
set_option autoImplicit false
namespace AspisV8R19.R236HalfWordOps
open Aeneas Aeneas.Std

theorem unsigned_ops (w : U32) :
    UScalar.or (U32.wrapping_shr w 1#u32)
      (U32.wrapping_shl (UScalar.and w 1#u32) 30#u32) =
      R228HalfEncoding.halfScalar w := by
  apply UScalar.eq_of_bv_eq
  simp only [UScalar.bv_or,U32.wrapping_shr_bv_eq,U32.wrapping_shl_bv_eq,
    UScalar.bv_and,R228HalfEncoding.halfScalar,R224HalfWordBounds.halfWord]
  rfl
#print axioms unsigned_ops
end AspisV8R19.R236HalfWordOps
