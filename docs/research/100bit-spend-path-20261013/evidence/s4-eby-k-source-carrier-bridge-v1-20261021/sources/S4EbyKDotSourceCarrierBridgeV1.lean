import AspisR1EbyKFinish.Types
import EbyKPushExplicitTypesV1
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1EbyKDotSourceCarrierBridgeV1

abbrev SourceDot := AspisR1EbyKFinish.canonical.Dot
abbrev PairDot := AspisR1EbyKPushCutV3.fast_pairing.canonical.Dot
abbrev SourceState := AspisR1EbyKFinish.EbyKDot
abbrev PairState := AspisR1EbyKPushCutV3.fast_pairing.EbyKDot

def dotToPair (d : SourceDot) : PairDot := { sums := d.sums }
def dotFromPair (d : PairDot) : SourceDot := { sums := d.sums }
def stateToPair (s : SourceState) : PairState :=
  { c0 := dotToPair s.c0, c1 := dotToPair s.c1, count := s.count }
def stateFromPair (s : PairState) : SourceState :=
  { c0 := dotFromPair s.c0, c1 := dotFromPair s.c1, count := s.count }

@[simp] theorem dot_from_to (d : SourceDot) : dotFromPair (dotToPair d) = d := by
  cases d; rfl
@[simp] theorem dot_to_from (d : PairDot) : dotToPair (dotFromPair d) = d := by
  cases d; rfl
@[simp] theorem state_from_to (s : SourceState) : stateFromPair (stateToPair s) = s := by
  cases s with | mk c0 c1 count => cases c0; cases c1; rfl
@[simp] theorem state_to_from (s : PairState) : stateToPair (stateFromPair s) = s := by
  cases s with | mk c0 c1 count => cases c0; cases c1; rfl

#print axioms state_to_from
#print axioms state_from_to

end AspisR1EbyKDotSourceCarrierBridgeV1
