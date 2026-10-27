import LPl_Kit_FunsExternal
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace LPn.Bytes

def decode (bs : List U8) : Nat := bs.foldr (fun b n => b.val+256*n) 0

theorem decode_bound (bs : List U8) : decode bs < 256^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    have byteBound : b.val ≤ 255 := U8.le_max b
    simp only [decode, List.foldr_cons, List.length_cons, Nat.pow_succ] at *
    omega

theorem le32_eq_decode (bs : List U8) : LPl_Kit_Bytes.le32 bs = decode (bs.take 4) := by rfl

theorem le32_bound (bs : List U8) : LPl_Kit_Bytes.le32 bs < 4294967296 := by
  have bound := decode_bound (bs.take 4)
  have len : (bs.take 4).length ≤ 4 := List.length_take_le _ _
  have powers : 256^(bs.take 4).length ≤ 256^4 := Nat.pow_le_pow_right (by decide) len
  change LPl_Kit_Bytes.le32 bs < 256^4
  exact Nat.lt_of_lt_of_le bound powers

#print axioms decode_bound
#print axioms le32_eq_decode
#print axioms le32_bound
end LPn.Bytes
