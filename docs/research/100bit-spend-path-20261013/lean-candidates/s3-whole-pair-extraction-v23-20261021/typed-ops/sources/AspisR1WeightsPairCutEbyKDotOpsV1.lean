import Aeneas
import AspisR1WeightsPairCut.Types
import EbyKPushExplicitTypesV1
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1WeightsPairCutEbyKDotOpsV1

def dotToSource (d : AspisR1WeightsPairCut.fast_pairing.canonical.Dot) :
    AspisR1EbyKPushCutV3.fast_pairing.canonical.Dot := { sums := d.sums }
def dotFromSource (d : AspisR1EbyKPushCutV3.fast_pairing.canonical.Dot) :
    AspisR1WeightsPairCut.fast_pairing.canonical.Dot := { sums := d.sums }
def stateToSource (s : AspisR1WeightsPairCut.fast_pairing.EbyKDot) :
    AspisR1EbyKPushCutV3.fast_pairing.EbyKDot :=
  { c0 := dotToSource s.c0, c1 := dotToSource s.c1, count := s.count }
def stateFromSource (s : AspisR1EbyKPushCutV3.fast_pairing.EbyKDot) :
    AspisR1WeightsPairCut.fast_pairing.EbyKDot :=
  { c0 := dotFromSource s.c0, c1 := dotFromSource s.c1, count := s.count }
def qToSource (q : AspisR1WeightsPairCut.field.QM31) : AspisR1EbyKPushCutV3.field.QM31 :=
  { c0 := { a := q.c0.a, b := q.c0.b }, c1 := { a := q.c1.a, b := q.c1.b } }
def qFromSource (q : AspisR1EbyKPushCutV3.field.QM31) : AspisR1WeightsPairCut.field.QM31 :=
  { c0 := { a := q.c0.a, b := q.c0.b }, c1 := { a := q.c1.a, b := q.c1.b } }
def wideToSource (w : AspisR1WeightsPairCut.field.WideExact) :
    AspisR1EbyKPushCutV3.field.wide_exact.WideExact :=
  { c0 := qToSource w.c0, c1 := qToSource w.c1 }
def wideFromSource (w : AspisR1EbyKPushCutV3.field.wide_exact.WideExact) :
    AspisR1WeightsPairCut.field.WideExact :=
  { c0 := qFromSource w.c0, c1 := qFromSource w.c1 }

@[simp] theorem stateFromTo (s : AspisR1WeightsPairCut.fast_pairing.EbyKDot) :
    stateFromSource (stateToSource s) = s := by
  cases s with | mk c0 c1 count => cases c0; cases c1; rfl
@[simp] theorem stateToFrom (s : AspisR1EbyKPushCutV3.fast_pairing.EbyKDot) :
    stateToSource (stateFromSource s) = s := by
  cases s with | mk c0 c1 count => cases c0; cases c1; rfl
@[simp] theorem wideFromTo (w : AspisR1WeightsPairCut.field.WideExact) :
    wideFromSource (wideToSource w) = w := by
  cases w with | mk c0 c1 => cases c0 with | mk x0 x1 => cases x0; cases x1; cases c1 with | mk x0 x1 => cases x0; cases x1; rfl
@[simp] theorem wideToFrom (w : AspisR1EbyKPushCutV3.field.wide_exact.WideExact) :
    wideToSource (wideFromSource w) = w := by
  cases w with | mk c0 c1 => cases c0 with | mk x0 x1 => cases x0; cases x1; cases c1 with | mk x0 x1 => cases x0; cases x1; rfl

end AspisR1WeightsPairCutEbyKDotOpsV1

namespace AspisR1WeightsPairCut
/-- Actual source-operation boundary, typed on the retained EbyK carrier. -/
class fast_pairing.EbyKDotOps where
  new : Result AspisR1EbyKPushCutV3.fast_pairing.EbyKDot
  push : AspisR1EbyKPushCutV3.fast_pairing.EbyKDot →
    AspisR1EbyKPushCutV3.field.wide_exact.WideExact →
    AspisR1EbyKPushCutV3.field.QM31 →
    Result ((core.result.Result Unit Unit) × AspisR1EbyKPushCutV3.fast_pairing.EbyKDot)
  finish : AspisR1EbyKPushCutV3.fast_pairing.EbyKDot →
    Result AspisR1EbyKPushCutV3.field.wide_exact.WideExact

/-- Explicitly map actual source operations back to the extracted carrier. -/
def fast_pairing.EbyKDot.new [ops : fast_pairing.EbyKDotOps] : Result fast_pairing.EbyKDot := do
  let s ← ops.new
  ok (AspisR1WeightsPairCutEbyKDotOpsV1.stateFromSource s)

def fast_pairing.EbyKDot.push [ops : fast_pairing.EbyKDotOps]
    (self : fast_pairing.EbyKDot) (value : field.WideExact) (scalar : field.QM31) :
    Result ((core.result.Result Unit Unit) × fast_pairing.EbyKDot) := do
  let (r, s) ← ops.push
    (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource self)
    (AspisR1WeightsPairCutEbyKDotOpsV1.wideToSource value)
    (AspisR1WeightsPairCutEbyKDotOpsV1.qToSource scalar)
  ok (r, AspisR1WeightsPairCutEbyKDotOpsV1.stateFromSource s)

def fast_pairing.EbyKDot.finish [ops : fast_pairing.EbyKDotOps]
    (self : fast_pairing.EbyKDot) : Result field.WideExact := do
  let w ← ops.finish (AspisR1WeightsPairCutEbyKDotOpsV1.stateToSource self)
  ok (AspisR1WeightsPairCutEbyKDotOpsV1.wideFromSource w)
end AspisR1WeightsPairCut

#print axioms AspisR1WeightsPairCutEbyKDotOpsV1.stateFromTo
#print axioms AspisR1WeightsPairCutEbyKDotOpsV1.stateToFrom
#print axioms AspisR1WeightsPairCutEbyKDotOpsV1.wideFromTo
#print axioms AspisR1WeightsPairCutEbyKDotOpsV1.wideToFrom
