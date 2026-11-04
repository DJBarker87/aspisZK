import NFG_QueryLoopDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_QueryLoopReplay
open Aeneas Aeneas.Std Result ControlFlow NFG_QueryLoopDefs
/-- Finite induction retains the full Result on arbitrary states, including
semantic Err, machine failure and divergence. -/
theorem complete (query : Query) (progress : Progress query) (finish : Usize)
 (fuel : Nat) (state : State) (budget : Budget finish fuel state) :
 run query finish fuel state = loop (step query finish) state := by
 induction fuel generalizing state with
 | zero =>
  cases state with
  | Err error =>
   rw [Aeneas.Std.loop.eq_def]
   simp only [run,step,bind_tc_ok]
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   have halt : a.next >= finish := by change a.next.val≥finish.val; exact budget
   rw [Aeneas.Std.loop.eq_def]
   simp only [run,step,if_pos halt,bind_tc_ok]
 | succ fuel ih =>
  cases state with
  | Err error =>
   rw [Aeneas.Std.loop.eq_def]
   simp only [run,step,bind_tc_ok]
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases halt : a.next >= finish
   · rw [Aeneas.Std.loop.eq_def]
     simp only [run,step,if_pos halt,bind_tc_ok]
   · rw [Aeneas.Std.loop.eq_def]
     simp only [run,step,if_neg halt]
     cases returned : query a b with
     | fail error => simp only [returned,bind_tc_fail]
     | div => simp only [returned,bind_tc_div]
     | ok next =>
      simp only [returned,bind_tc_ok]
      apply ih next
      cases next with
      | Err error => trivial
      | Ok pair =>
       rcases pair with ⟨after,pending⟩
       have advance := progress a b after pending returned
       change finish.val≤after.next.val+fuel
       change finish.val≤a.next.val+(fuel+1) at budget
       omega
#print axioms complete
end AspisR1.NFG_QueryLoopReplay
end
