import PV_B3P_IndexCounter579227
import PV_B3P_RangeEvents578227
import PV_B3P_Offset226V3
namespace PV_B3P_PositiveRangeEvents587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- Private Range1..16, including exhausted stutters. n counts successful
source next edges, with the old start observed before each increment. -/
def sourceCounter : Nat → Usize
  | 0 => 1#usize
  | n+1 => PV_B3P_IndexCounter579227.advance 16#usize (sourceCounter n)

theorem counter_bounds (n : Nat) :
    1 ≤ (sourceCounter n).val ∧ (sourceCounter n).val ≤ 16 := by
  induction n with
  | zero => change 1 ≤ (1#usize).val ∧ (1#usize).val ≤ 16; scalar_tac
  | succ n ih =>
    by_cases done : sourceCounter n = 16#usize
    · simp only [sourceCounter,PV_B3P_IndexCounter579227.advance,done,if_true]
      scalar_tac
    · have order : (sourceCounter n).val ≤ (16#usize).val := ih.2
      have safe := PV_B3P_PreconditionFormatting569227.index_range_conditions
        (sourceCounter n) 16#usize order done
      have nowrap : (sourceCounter n).val+(1#usize).val < UScalar.size .Usize := by
        have hm := Usize.cMax_bound_concrete.1
        rw [UScalar.size_def]
        scalar_tac
      simp only [sourceCounter,PV_B3P_IndexCounter579227.advance,if_neg done]
      rw [PV_B3P_Offset226V3.add_value _ _ nowrap]
      constructor
      · omega
      · have next := safe.2.2
        rw [PV_B3P_Offset226V3.add_value _ _ nowrap] at next
        exact next

/-- Bind the symbolic counter to the actual source next operation, including
its exhausted branch, rather than assuming a positive current index. -/
theorem source_next (handler : Str → Result Never) (n : Nat) :
    PV_B3P_NextFormatting569227.source handler ⟨sourceCounter n,16#usize⟩ =
      .ok ((if sourceCounter n = 16#usize then none else some (sourceCounter n)),
        ⟨sourceCounter (n+1),16#usize⟩) := by
  change PV_B3P_NextFormatting569227.source handler ⟨sourceCounter n,16#usize⟩ =
    .ok ((if sourceCounter n = 16#usize then none else some (sourceCounter n)),
      ⟨PV_B3P_IndexCounter579227.advance 16#usize (sourceCounter n),16#usize⟩)
  by_cases done : sourceCounter n = 16#usize
  · have inactive : ¬ (sourceCounter n).val < (16#usize).val := by
      rw [done]
      exact Nat.lt_irrefl _
    simp only [PV_B3P_NextFormatting569227.source,if_neg inactive,
      PV_B3P_IndexCounter579227.advance,if_pos done]
  · have safe := PV_B3P_PreconditionFormatting569227.index_range_conditions
      (sourceCounter n) 16#usize (counter_bounds n).2 done
    simp only [PV_B3P_NextFormatting569227.source,if_pos safe.1,
      PV_B3P_NthFormattingFinal559227.increment_value handler (sourceCounter n) 16#usize safe.1,
      bind_tc_ok,PV_B3P_IndexCounter579227.advance,if_neg done]

def sourceEvent (n : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  if sourceCounter n = 16#usize then .ok none
  else through effects (some ⟨(Usize.wrapping_sub (sourceCounter n) 1#usize).val,15⟩)

theorem event_guard (n : Nat) (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent n effects = .ok (some observed)) : indexGuard observed := by
  by_cases done : sourceCounter n = 16#usize
  · simp only [sourceEvent,if_pos done] at ran
    cases ran
  · simp only [sourceEvent,if_neg done] at ran
    have frame := through_value _ _ _ ran
    cases frame
    have bounds := counter_bounds n
    have low : (1#usize).val ≤ (sourceCounter n).val := bounds.1
    have safe := PV_B3P_PreconditionFormatting569227.index_range_conditions
      (sourceCounter n) 16#usize bounds.2 done
    change (Usize.wrapping_sub (sourceCounter n) 1#usize).val < 15
    rw [PV_B3P_Offset226V3.sub_value _ _ low]
    change (sourceCounter n).val - 1 < 15
    have high : (sourceCounter n).val < 16 := safe.1
    omega

theorem event_certificate {α : Type} (n : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent n effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  (index_out_of_bounds observed normal first second).2 (event_guard n effects observed ran)
#print axioms counter_bounds
#print axioms source_next
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_PositiveRangeEvents587227
