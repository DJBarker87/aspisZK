import R1Z.PV_RunJoin_WeightSquare46
import R1Z.ProverCommitPowerStep49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPowerBits46
open Aeneas Aeneas.Std

theorem bit64 (e : U64) : (e &&& 1#u64).val=e.val%2 := by
  change (e.bv &&& (1#u64).bv).toNat=_
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

theorem condition64 (e : U64) : (e &&& 1#u64)=1#u64 ↔ e.val%2≠0 := by
  constructor
  · intro h
    have hv := congrArg (fun x : U64 => x.val) h
    rw [bit64] at hv
    change e.val%2=1 at hv
    omega
  · intro h
    apply UScalar.eq_of_val_eq
    rw [bit64]
    change e.val%2=1
    have hb := Nat.mod_lt e.val (by decide : 0<2)
    omega

theorem shift64 (e : U64) : (U64.wrapping_shr e 1#u32).val=e.val/2 := by
  change (e.val >>> 1)=_
  rw [Nat.shiftRight_eq_div_pow]
#print axioms bit64
#print axioms condition64
#print axioms shift64
end R1Z.PV_RunJoin_WeightPowerBits46
