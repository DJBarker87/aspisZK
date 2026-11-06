import NJS_Extract.Funs
set_option autoImplicit false
namespace NJS_KeyWord
open Aeneas Aeneas.Std Result
def pack (u : U32) (j : Usize) : U64 :=
 (U64.wrapping_shl (core.convert.num.FromU64U32.from u) 8#u32) ||| UScalar.cast .U64 j

theorem value (u : U32) (j : Usize) (bound : j.val<16) :
 (pack u j).val=256*u.val+j.val := by
 change (((u.bv.setWidth 64) <<< (8:Nat)) ||| j.bv.setWidth 64).toNat = _
 rw [BitVec.toNat_or,BitVec.toNat_shiftLeft]
 have wu : (u.bv.setWidth 64).toNat=u.val := BitVec.toNat_setWidth_of_le (by decide)
 have wj : (j.bv.setWidth 64).toNat=j.val := by
   rw [BitVec.toNat_setWidth]
   change j.val % 18446744073709551616=j.val
   exact Nat.mod_eq_of_lt (by omega)
 rw [wu,wj]
 have ub : u.val<4294967296 := by scalar_tac
 have shift : u.val <<< 8 < 2^64 := by
   rw [Nat.shiftLeft_eq]
   change u.val*256<18446744073709551616
   omega
 rw [Nat.mod_eq_of_lt shift,←Nat.shiftLeft_add_eq_or_of_lt (by omega : j.val<2^8)]
 rw [Nat.shiftLeft_eq]
 change u.val*256+j.val=256*u.val+j.val
 omega
#print axioms value
end NJS_KeyWord
