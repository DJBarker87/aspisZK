import R1Z.PV_RunJoin_CircleNeutralWide53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralWideMix53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralCast53 PV_RunJoin_CircleNeutralWide53

def pad (a : U32 × U32) : U64 :=
  U64.wrapping_add (UScalar.cast .U64 a.1) (UScalar.cast .U64 2147483647#u32)

theorem pad_val (a : U32 × U32) (ha : CC a) : (pad a).val = a.1.val+2147483647 := by
  unfold pad
  rw [PV_RunJoin_CircleNeutralWord53.add64]
  · rw [up_val,up_val];rfl
  · rw [up_val,up_val];have h0 := ha.1;unfold Canon at h0;change a.1.val+2147483647 < 18446744073709551616;omega

theorem pad_checked (a : U32 × U32) (ha : CC a) :
    UScalar.cast .U64 a.1 + UScalar.cast .U64 2147483647#u32 = ok (pad a) := by
  apply PV_RunJoin_CircleNeutralChecked64_53.add
  rw [up_val,up_val]
  have h0 := ha.1;unfold Canon at h0
  change a.1.val+2147483647 < 18446744073709551616;omega

theorem mix_sub (a : U32 × U32) (ha : CC a) :
    pad a - UScalar.cast .U64 a.2 = ok (mix a) := by
  apply PV_RunJoin_CircleNeutralChecked64_53.sub
  rw [up_val,pad_val _ ha]
  have h1 := ha.2;unfold Canon at h1;omega

theorem product_bound (x y : U64) (hx : x.val<4294967294) (hy : y.val<4294967294) :
    x.val*y.val < 18446744073709551616 := by
  have h := Nat.mul_lt_mul_of_lt_of_lt hx hy
  omega

#print axioms pad
#print axioms pad_val
#print axioms pad_checked
#print axioms mix_sub
#print axioms product_bound
end R1Z.PV_RunJoin_CircleNeutralWideMix53
