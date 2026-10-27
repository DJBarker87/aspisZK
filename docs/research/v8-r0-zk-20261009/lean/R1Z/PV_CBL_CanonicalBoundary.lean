import R1Z.PV_CBL_BlockValueBoundary
import R1Z.PV_CBL_FallbackCanonicalStep
import R1Z.PV_CBL_FallbackCanonicalRecurrence
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_CanonicalBoundary
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
@[irreducible] def four (s : State) (w k : A4) : State :=
  let step := PV_CBL_FallbackCanonicalStep.step
  step (step (step (step s (U32.wrapping_add w.val[3]! k.val[3]!))
    (U32.wrapping_add w.val[2]! k.val[2]!))
    (U32.wrapping_add w.val[1]! k.val[1]!)) (U32.wrapping_add w.val[0]! k.val[0]!)
@[irreducible] def schedule (a b c d : A4) : A4 :=
  let next := PV_CBL_FallbackCanonicalRecurrence.next
  let x0 := next a.val[3]! a.val[2]! c.val[2]! d.val[1]!
  let x1 := next a.val[2]! a.val[1]! c.val[1]! d.val[0]!
  let x2 := next a.val[1]! a.val[0]! c.val[0]! x0
  let x3 := next a.val[0]! b.val[3]! d.val[3]! x1
  pack x3 x2 x1 x0
theorem four_eq (s : State) (w k : A4) : PV_CBL_BlockValueBoundary.four s w k = four s w k := by
  unfold PV_CBL_BlockValueBoundary.four four PV_CBL_BlockFourValue.value PV_CBL_FallbackFourModel.run4
  simp only [PV_CBL_FallbackRoundsModel.run_four,PV_CBL_FallbackCanonicalStep.source]
theorem schedule_eq (a b c d : A4) :
    PV_CBL_BlockValueBoundary.schedule a b c d = schedule a b c d := by
  unfold PV_CBL_BlockValueBoundary.schedule schedule PV_CBL_BlockScheduleValue.value
  simp only [PV_CBL_FallbackCanonicalRecurrence.source_next]
#print axioms four
#print axioms schedule
#print axioms four_eq
#print axioms schedule_eq
end R1Z.PV_CBL_CanonicalBoundary
