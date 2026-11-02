import R1Z.PV_RunJoin_MultilinearWeight69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MultilinearBits69
open Aeneas Aeneas.Std

theorem shift_val (x : Usize) (b : U32) (hb : b.val<32) :
    (Usize.wrapping_shl x b).val=(x.val*2^b.val)%UScalar.size .Usize := by
  unfold Usize.wrapping_shl UScalar.wrapping_shl
  simp only [UScalar.val,BitVec.shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,UScalar.size]
  have h : b.bv.toNat< UScalarTy.Usize.numBits :=
    lt_of_lt_of_le hb System.Platform.le_numBits
  rw [Nat.mod_eq_of_lt h]

theorem append_bound (suffix : Usize) (b : Bool) (k : Nat) (small : suffix.val<2^k) :
    ((Usize.wrapping_shl suffix 1#u32) ||| core.convert.num.FromUsizeBool.from b).val<2^(k+1) := by
  change ((Usize.wrapping_shl suffix 1#u32) ||| core.convert.num.FromUsizeBool.from b).bv.toNat<2^(k+1)
  rw [UScalar.bv_or,BitVec.toNat_or]
  apply Nat.or_lt_two_pow
  · change (Usize.wrapping_shl suffix 1#u32).val<2^(k+1)
    rw [shift_val _ _ (by decide)]
    have modle := Nat.mod_le (suffix.val*2) (UScalar.size .Usize)
    rw [Nat.pow_succ]
    change (suffix.val*2)%UScalar.size .Usize<2^k*2
    omega
  · cases b <;> change _<2^(k+1) <;> simp only [Nat.pow_succ] <;>
      have positive := Nat.two_pow_pos k <;> omega

#print axioms shift_val
#print axioms append_bound
end R1Z.PV_RunJoin_MultilinearBits69
