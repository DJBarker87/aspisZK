import XRs_ByteSteps
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRs_WordBytes

theorem byte_val (b : BitVec 8) : (b#uscalar : U8).val = b.toNat := rfl

theorem ofNat_val (n : Nat) (h : n ≤ U8.max) : (UScalar.ofNat n h : U8).val = n := rfl

theorem word (x : U32) : XRn_Join_wordBytes x =
 AspisR1WideToBytesIndexedCandidate.limbBytes x := by
 unfold XRn_Join_wordBytes AspisR1WideToBytesIndexedCandidate.limbBytes
 simp only [XRs_ByteSteps.bytes32,List.getElem_cons_zero,List.getElem_cons_succ]
 change [UScalar.ofNat (x.val/256^0%256) _,UScalar.ofNat (x.val/256^1%256) _,
   UScalar.ofNat (x.val/256^2%256) _,UScalar.ofNat (x.val/256^3%256) _] = _
 refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl)))
 all_goals apply UScalar.eq_of_val_eq
 all_goals simp only [ofNat_val,byte_val,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
 all_goals
   have hx : x.val < 4294967296 := by scalar_tac
   change x.bv.toNat < 4294967296 at hx
   change _ = _
   omega
#print axioms byte_val
#print axioms ofNat_val
#print axioms word
end XRs_WordBytes
