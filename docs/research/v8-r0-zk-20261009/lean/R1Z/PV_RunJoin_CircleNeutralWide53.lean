import R1Z.PV_RunJoin_CircleNeutralCast53
import R1Z.PV_RunJoin_CircleNeutralChecked64_53
import R1Z.PV_RunJoin_CircleNeutralShape53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralWide53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralCast53

def sum (a : U32 × U32) : U64 :=
  U64.wrapping_add (UScalar.cast .U64 a.1) (UScalar.cast .U64 a.2)
def mix (a : U32 × U32) : U64 :=
  U64.wrapping_sub (U64.wrapping_add (UScalar.cast .U64 a.1) (UScalar.cast .U64 2147483647#u32))
    (UScalar.cast .U64 a.2)

theorem sum_val (a : U32 × U32) (ha : CC a) : (sum a).val = a.1.val+a.2.val := by
  unfold sum
  rw [PV_RunJoin_CircleNeutralWord53.add64]
  · rw [up_val,up_val]
  · rw [up_val,up_val]; have h0 := ha.1;have h1 := ha.2;unfold Canon at h0 h1;omega

theorem sum_bound (a : U32 × U32) (ha : CC a) : (sum a).val < 4294967294 := by
  rw [sum_val _ ha]
  have h0 := ha.1;have h1 := ha.2;unfold Canon at h0 h1;omega

theorem mix_val (a : U32 × U32) (ha : CC a) :
    (mix a).val = a.1.val+2147483647-a.2.val := by
  have hv : (U64.wrapping_add (UScalar.cast .U64 a.1) (UScalar.cast .U64 2147483647#u32)).val =
      a.1.val+2147483647 := by
    rw [PV_RunJoin_CircleNeutralWord53.add64]
    · rw [up_val,up_val];rfl
    · rw [up_val,up_val];have h0 := ha.1;unfold Canon at h0;change a.1.val+2147483647 < 18446744073709551616;omega
  unfold mix
  rw [PV_RunJoin_CircleNeutralWord53.sub64]
  · rw [hv,up_val]
  · rw [hv,up_val];have h1 := ha.2;unfold Canon at h1;omega

theorem mix_bound (a : U32 × U32) (ha : CC a) : (mix a).val < 4294967294 := by
  rw [mix_val _ ha]
  have h0 := ha.1;have h1 := ha.2;unfold Canon at h0 h1;omega

theorem sum_checked (a : U32 × U32) (ha : CC a) :
    UScalar.cast .U64 a.1 + UScalar.cast .U64 a.2 = ok (sum a) := by
  apply PV_RunJoin_CircleNeutralChecked64_53.add
  rw [up_val,up_val]
  have h0 := ha.1;have h1 := ha.2;unfold Canon at h0 h1;omega

theorem mix_checked (a : U32 × U32) (ha : CC a) :
    (do let s ← UScalar.cast .U64 a.1 + UScalar.cast .U64 2147483647#u32
        s - UScalar.cast .U64 a.2) = ok (mix a) := by
  have h0 := ha.1;have h1 := ha.2;unfold Canon at h0 h1
  rw [PV_RunJoin_CircleNeutralChecked64_53.add _ _ (by rw [up_val,up_val];change a.1.val+2147483647 < 18446744073709551616;omega),bind_tc_ok]
  apply PV_RunJoin_CircleNeutralChecked64_53.sub
  rw [up_val,PV_RunJoin_CircleNeutralWord53.add64]
  · rw [up_val,up_val];change a.2.val ≤ a.1.val+2147483647;omega
  · rw [up_val,up_val];change a.1.val+2147483647 < 18446744073709551616;omega

#print axioms sum
#print axioms mix
#print axioms sum_val
#print axioms sum_bound
#print axioms mix_val
#print axioms mix_bound
#print axioms sum_checked
#print axioms mix_checked
end R1Z.PV_RunJoin_CircleNeutralWide53
