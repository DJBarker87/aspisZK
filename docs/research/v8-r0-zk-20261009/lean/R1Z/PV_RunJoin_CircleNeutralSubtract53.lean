import R1Z.PV_RunJoin_CircleNeutralWord53
import R1Z.PV_RunJoin_CircleNeutralShape53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralSubtract53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralWord53

def output (x : U32) : U32 :=
  if x ≥ 2147483647#u32 then U32.wrapping_sub x 2147483647#u32 else x

theorem source (x : U32) : PV_RunJoin_CircleRawScalar52.field.ct.subtract_p x = ok (output x) :=
  PV_RunJoin_CircleNeutralScalar52.subtract_shape x

theorem value (x : U32) : (output x).val =
    if 2147483647 ≤ x.val then x.val-2147483647 else x.val := by
  unfold output
  by_cases h : x ≥ 2147483647#u32
  · rw [if_pos h,sub32 _ _ h]
    exact (if_pos h).symm
  · rw [if_neg h]
    exact (if_neg h).symm

theorem canonical (x : U32) (hx : x.val < 4294967294) : Canon (output x) := by
  unfold Canon
  rw [value]
  split <;> omega

theorem total (x : U32) (hx : x.val < 4294967294) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.ct.subtract_p x = ok y ∧ Canon y :=
  ⟨output x,source x,canonical x hx⟩

#print axioms output
#print axioms source
#print axioms value
#print axioms canonical
#print axioms total
end R1Z.PV_RunJoin_CircleNeutralSubtract53
