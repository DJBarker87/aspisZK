import PV_B3P_InclusiveFormatting569227
namespace PV_B3P_InclusiveFoldFormatting569227
open Aeneas Aeneas.Std core.ops.range PV_B3P_NthFormattingFinal559227
set_option autoImplicit false
/-- Middle while of default inclusive spec_try_fold. The cursor advances before
calling f, and early residual, failure and divergence keep that order. -/
def body {α β : Type} (handler : Str → Result Never)
    (step : α → Usize → Result (ControlFlow α β))
    (s : RangeInclusive Usize × α) :
    Result (ControlFlow (RangeInclusive Usize × α)
      (RangeInclusive Usize × ControlFlow α β)) :=
  if s.1.start.val < s.1.end.val then do
    let next ← PV_B3P_NthFinalGuard559227.increment_with handler s.1.start
    let answer ← step s.2 s.1.start
    let r := {s.1 with start := next}
    match answer with
    | .cont accum => .ok (.cont (r,accum))
    | .done residual => .ok (.done (r,.done residual))
  else .ok (.done (s.1,.cont s.2))

theorem body_independent {α β : Type} (first second : Str → Result Never)
    (step : α → Usize → Result (ControlFlow α β)) (s : RangeInclusive Usize × α) :
    body first step s = body second step s := by
  by_cases guard : s.1.start.val < s.1.end.val
  · simp only [body,guard,if_true,increment_value first s.1.start s.1.end guard,
      increment_value second s.1.start s.1.end guard]
  · simp only [body,guard,if_false]

theorem loop_independent {α β : Type} (first second : Str → Result Never)
    (step : α → Usize → Result (ControlFlow α β)) (s : RangeInclusive Usize × α) :
    loop (body first step) s = loop (body second step) s := by
  have same := funext (body_independent first second step)
  rw [same]

/-- Complete source-control fold, including initial emptiness, mid-loop residual,
exhausted write, final equality test and possible final callback. -/
def source {α β : Type} (handler : Str → Result Never)
    (step : α → Usize → Result (ControlFlow α β))
    (r : RangeInclusive Usize) (init : α) :
    Result (ControlFlow α β × RangeInclusive Usize) :=
  if r.exhausted = true ∨ r.end.val < r.start.val then .ok (.cont init,r)
  else do
    let (rest,answer) ← loop (body handler step) (r,init)
    match answer with
    | .done residual => .ok (.done residual,rest)
    | .cont accum => do
      let exhausted := {rest with exhausted := true}
      if rest.start = rest.end then do
        let final ← step accum rest.start
        .ok (final,exhausted)
      else .ok (.cont accum,exhausted)

theorem handler_independent {α β : Type} (first second : Str → Result Never)
    (step : α → Usize → Result (ControlFlow α β))
    (r : RangeInclusive Usize) (init : α) :
    source first step r init = source second step r init := by
  unfold source
  rw [loop_independent first second step]
#print axioms body_independent
#print axioms loop_independent
#print axioms handler_independent
end PV_B3P_InclusiveFoldFormatting569227
