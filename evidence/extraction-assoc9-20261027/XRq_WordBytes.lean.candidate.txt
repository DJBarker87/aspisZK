import XRq_ByteCarrier
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRq_WordBytes

theorem word (x : U32) : XRn_Join_wordBytes x =
 AspisR1WideToBytesIndexedCandidate.limbBytes x := by
 unfold XRn_Join_wordBytes AspisR1WideToBytesIndexedCandidate.limbBytes
 change [UScalar.ofNat (x.val/256^0%256) _,UScalar.ofNat (x.val/256^1%256) _,
   UScalar.ofNat (x.val/256^2%256) _,UScalar.ofNat (x.val/256^3%256) _] = _
 refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl)))
 all_goals apply UScalar.eq_of_val_eq
 all_goals simp only [BitVec.toLEBytes.eq_1, show 32>0 from by decide,
   show 24>0 from by decide,show 16>0 from by decide,show 8>0 from by decide,
   show ¬(0>0) from by decide,ite_true,ite_false,
   List.getElem_cons_zero,List.getElem_cons_succ]
 all_goals simp only [XRq_ByteCarrier.val,BitVec.toNat_setWidth,
   BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
 all_goals
   have hx : x.val < 4294967296 := by scalar_tac
   change x.bv.toNat < 4294967296 at hx
   omega
#print axioms word
end XRq_WordBytes
