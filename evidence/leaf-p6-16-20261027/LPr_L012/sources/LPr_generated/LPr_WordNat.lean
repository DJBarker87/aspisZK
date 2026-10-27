import LPr_WordValue
set_option autoImplicit false
namespace AspisR1.LPr_WordNat
open Aeneas Aeneas.Std

theorem append_value {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2^n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- Natural little-endian formula for the exact native library decoder. -/
theorem value (a b c d : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).val =
      a.val + 256*b.val + 65536*c.val + 16777216*d.val := by
  change ((core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).bv).toNat = _
  rw [LPr_WordValue.bits, append_value, append_value, append_value]
  change ((d.val * 256 + c.val) * 256 + b.val) * 256 + a.val = _
  omega

#print axioms append_value
#print axioms value
end AspisR1.LPr_WordNat
