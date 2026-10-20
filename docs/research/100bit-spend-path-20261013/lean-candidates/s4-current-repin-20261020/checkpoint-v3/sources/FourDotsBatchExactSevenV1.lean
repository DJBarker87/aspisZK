import FourDotsBatchLoopScheduleV1
import StepByScheduleV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsBatchExactSeven
open AspisR1FastDotsBatchLoopSchedule

def expectedStartsFrom (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => 4 * n :: expectedStartsFrom (n + 1) k

theorem trace_shape_from (k n : Nat) (it : StepBy) (starts : List Nat)
    (hnk : n + k = 7) (hn : n ≤ 6)
    (hstart : it.iter.start.val = 4 * n)
    (hend : it.iter.end.val = 26)
    (hstep : it.step_by.val = 4)
    (ht : BatchTrace it starts) : starts = expectedStartsFrom n k := by
  induction k generalizing n it starts with
  | zero => omega
  | succ k ih =>
      have hlt : it.iter.start.val < it.iter.end.val := by omega
      cases ht with
      | stop it hstop => omega
      | @step _ it' tail hs hc he hk htail =>
          have htailEnd : it'.iter.end.val = 26 := by rw [he]; exact hend
          have htailStep : it'.step_by.val = 4 := by rw [hk]; exact hstep
          have hcursor : it'.iter.start.val = min (4*n + 4) 26 := by
            simpa [hstart, hstep, hend] using hc
          cases k with
          | zero =>
              have hn6 : n = 6 := by omega
              have hcursor26 : it'.iter.start.val = 26 := by
                rw [hcursor, hn6]
                norm_num [Nat.min_def]
              have htailNil : tail = [] := by
                cases htail with
                | stop _ _ => rfl
                | @step _ _ _ hmore _ _ _ _ => omega
              simp [expectedStartsFrom, hn6, hstart, htailNil]
          | succ j =>
              have hn5 : n ≤ 5 := by omega
              have hcursorNext : it'.iter.start.val = 4 * (n + 1) := by
                rw [hcursor]
                rw [Nat.min_eq_left (show 4 * n + 4 ≤ 26 by omega)]
                omega
              have hnkNext : (n + 1) + (j + 1) = 7 := by omega
              have hnNext : n + 1 ≤ 6 := by omega
              have htailShape := ih (n + 1) it' tail hnkNext hnNext
                hcursorNext htailEnd htailStep htail
              simp [expectedStartsFrom, hstart, htailShape]
#print axioms trace_shape_from

theorem actual_outer_exact_seven (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (limbs out : Array U64 8#usize)
    (h : Outer ops AspisR1FastDotsStepSchedule.startBy a a1 slot limbs = .ok out) :
    ∃ starts, BatchTrace AspisR1FastDotsStepSchedule.startBy starts ∧ starts.length = 7 := by
  obtain ⟨starts, htrace⟩ := outer_success_trace ops AspisR1FastDotsStepSchedule.startBy a a1 slot limbs out rfl h
  have hshape := trace_shape_from 7 0 AspisR1FastDotsStepSchedule.startBy starts rfl (by omega)
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy]) htrace
  refine ⟨starts, htrace, ?_⟩
  rw [hshape]
  rfl
#print axioms actual_outer_exact_seven
end AspisR1FastDotsBatchExactSeven
