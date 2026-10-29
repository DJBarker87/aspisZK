import R1Z.PV_RunJoin_NeutralTowerValue54
import R1Z.PV_RunJoin_CircleNeutralCast53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralCMulWord54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_NeutralTowerValue54
open PV_RunJoin_CircleNeutralWord53 PV_RunJoin_CircleNeutralCast53

def word (a b : C) : U64 := U64.wrapping_mul
  (U64.wrapping_add (UScalar.cast .U64 a.1) (UScalar.cast .U64 a.2))
  (U64.wrapping_add (UScalar.cast .U64 b.1) (UScalar.cast .U64 b.2))
theorem value (a b : C) (ha : CC a) (hb : CC b) :
    (word a b).val=(a.1.val+a.2.val)*(b.1.val+b.2.val) := by
  have h0 : a.1.val<2147483647 := ha.1
  have h1 : a.2.val<2147483647 := ha.2
  have h2 : b.1.val<2147483647 := hb.1
  have h3 : b.2.val<2147483647 := hb.2
  have hprod : (a.1.val+a.2.val)*(b.1.val+b.2.val)<18446744073709551616 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt (show a.1.val+a.2.val<4294967294 by omega)
      (show b.1.val+b.2.val<4294967294 by omega)
    omega
  have s0 : (U64.wrapping_add (UScalar.cast .U64 a.1) (UScalar.cast .U64 a.2)).val=a.1.val+a.2.val := by
    rw [add64 _ _ (by rw [up_val,up_val];omega),up_val,up_val]
  have s1 : (U64.wrapping_add (UScalar.cast .U64 b.1) (UScalar.cast .U64 b.2)).val=b.1.val+b.2.val := by
    rw [add64 _ _ (by rw [up_val,up_val];omega),up_val,up_val]
  unfold word
  rw [mul64 _ _ (by rw [s0,s1];exact hprod),s0,s1]
#print axioms word
#print axioms value
end R1Z.PV_RunJoin_NeutralCMulWord54
