import R1Z.PV_RunJoin_CircleNeutralShift53
import R1Z.PV_RunJoin_CircleNeutralChecked64_53
import R1Z.PV_RunJoin_CircleNeutralCast53
import R1Z.PV_RunJoin_CircleNeutralWide53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralR24Leaf53
open PV_RunJoin_CircleNeutralCast53 PV_RunJoin_CircleNeutralShift53 PV_RunJoin_CircleNeutralFold53

def prime : U64 := UScalar.cast .U64 PV_RunJoin_CircleR72Raw52.field.P
def square : U64 := U64.wrapping_mul prime prime

theorem prime_val : prime.val = 2147483647 := by rw [prime,up_val];rfl

theorem square_val : square.val = 4611686014132420609 := by
  unfold square
  rw [PV_RunJoin_CircleNeutralWord53.mul64]
  · rw [prime_val]
  · rw [prime_val];decide

theorem pp : PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.PP = ok square := by
  unfold PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.PP
  simp only [lift,bind_tc_ok]
  apply PV_RunJoin_CircleNeutralChecked64_53.mul
  change prime.val*prime.val < 18446744073709551616
  rw [prime_val]
  decide

theorem fold_call (x : U64) :
    PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call () x =
      ok (fold x) := by
  unfold PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
  simp only [lift,bind_tc_ok,PV_RunJoin_CircleNeutralWide53.from32,low_mask,shr31i]
  rfl

#print axioms prime
#print axioms square
#print axioms prime_val
#print axioms square_val
#print axioms pp
#print axioms fold_call
end R1Z.PV_RunJoin_CircleNeutralR24Leaf53
