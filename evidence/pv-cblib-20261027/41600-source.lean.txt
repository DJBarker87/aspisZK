import R1Z.PV_CBL_BlockArrayEta
import R1Z.PV_CBL_FallbackScheduleRecurrence
import R1Z.PV_CBL_FallbackBlockLinks
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockScheduleValue
open PV_CBL_FallbackArray4 PV_CBL_FallbackScheduleRecurrence
set_option autoImplicit false
def value (a b c d : A4) : A4 :=
  let x0 := next a.val[3]! a.val[2]! c.val[2]! d.val[1]!
  let x1 := next a.val[2]! a.val[1]! c.val[1]! d.val[0]!
  let x2 := next a.val[1]! a.val[0]! c.val[0]! x0
  let x3 := next a.val[0]! b.val[3]! d.val[3]! x1
  pack x3 x2 x1 x0
theorem source (a b c d : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.schedule a b c d = ok (value a b c d) := by
  rw [PV_CBL_FallbackBlockLinks.schedule_eq]
  conv_lhs => rw [← PV_CBL_BlockArrayEta.eta a, ← PV_CBL_BlockArrayEta.eta b,
    ← PV_CBL_BlockArrayEta.eta c, ← PV_CBL_BlockArrayEta.eta d]
  exact PV_CBL_FallbackScheduleRecurrence.four _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
#print axioms value
#print axioms source
end R1Z.PV_CBL_BlockScheduleValue
