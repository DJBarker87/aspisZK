import PV_B3P_RangeEvents578227
import PV_B3P_ArithmeticEvents583227
namespace PV_B3P_RangeComputedEvents592227
open Aeneas Aeneas.Std core.ops.range PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Retain the actual source next call before observing its scalar expression.
The expression carries its own checked arithmetic observation, with no guard
hypothesis introduced at the wrapper endpoint. -/
def sourceEvent (handler : Str → Result Never) (r : Range Usize)
    (expr : Usize → PV_B3P_ArithmeticEvents583227.Expr) (slack : Nat)
    (effects : List (Result Unit)) : Result (Option IndexState) := do
  let (item,_) ← PV_B3P_NextFormatting569227.source handler r
  match item with
  | none => .ok none
  | some i => PV_B3P_ArithmeticEvents583227.sourceEvent (expr i) slack effects

theorem event_certificate {α : Type} (handler : Str → Result Never) (r : Range Usize)
    (expr : Usize → PV_B3P_ArithmeticEvents583227.Expr) (slack : Nat)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent handler r expr slack effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second := by
  cases h : PV_B3P_NextFormatting569227.source handler r with
  | fail error => simp only [sourceEvent,h,bind_tc_fail] at ran; cases ran
  | div => simp only [sourceEvent,h,bind_tc_div] at ran; cases ran
  | ok pair =>
    rcases pair with ⟨item,next⟩
    cases item with
    | none => simp only [sourceEvent,h,bind_tc_ok] at ran; cases ran
    | some i =>
      simp only [sourceEvent,h,bind_tc_ok] at ran
      exact PV_B3P_ArithmeticEvents583227.event_certificate (expr i) slack effects observed ran normal first second
#print axioms event_certificate
end PV_B3P_RangeComputedEvents592227
