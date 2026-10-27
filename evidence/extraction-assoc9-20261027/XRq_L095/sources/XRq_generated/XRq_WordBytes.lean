import XRq_ByteEquation
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRq_WordBytes

theorem word (x : U32) : XRn_Join_wordBytes x =
 AspisR1WideToBytesIndexedCandidate.limbBytes x := by
 unfold XRn_Join_wordBytes AspisR1WideToBytesIndexedCandidate.limbBytes
 change [UScalar.ofNat (x.val/256^0%256) _,UScalar.ofNat (x.val/256^1%256) _,
   UScalar.ofNat (x.val/256^2%256) _,UScalar.ofNat (x.val/256^3%256) _] = _
 congr 1 <;> apply UScalar.eq_of_val_eq
 all_goals simp [BitVec.toLEBytes.eq_1,BitVec.toNat_setWidth,
   BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
#print axioms word
end XRq_WordBytes
