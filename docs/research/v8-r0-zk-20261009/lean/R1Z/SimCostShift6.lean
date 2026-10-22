import R1Z.SimCostWide5
import R1Z.SimCostSparse6

/-! Concrete WideExact specialization of the symbolic sparse-update loop.
Supplied materialized payload: two random-access reads and two writes.
The original terminal read is an input to this suffix, not a free callback.
This does not instantiate SimCostView.Stages.shifted. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostShift6
open AspisWideTower R1Z.SimCostWriter R0Z.HonestView R1Z.Batched

abbrev suffix := suffixRun SimCostWide5.add SimCostWide5.mul SimCostWide5.inv

theorem suffix_bound (a original : WideExact) (v : Payload WideExact R1Bat) :
    (suffix a original v).2 ≤ 85439 :=
  suffixRun_bound SimCostWide5.add SimCostWide5.mul SimCostWide5.inv a original v

theorem suffix_shift {F : Subfield WideExact} (pub : R0P.Public WideExact)
    (B : R0P.PackBasis F) (ch : Challenges WideExact) (v : Payload WideExact R1Bat) :
    (suffix (alpha ch 9) (R0Z.Shift.originalOf pub B ch v) v).1 =
      R0Z.Shift.shift pub B ch v :=
  suffixRun_shift SimCostWide5.add SimCostWide5.mul SimCostWide5.inv pub B ch v

#print axioms suffix_bound
#print axioms suffix_shift
end R1Z.SimCostShift6
