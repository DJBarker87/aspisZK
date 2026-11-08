import NFS_QueryLoopRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_QueryInduction
open Aeneas Aeneas.Std Result AspisR1Stage2 NFG_QueryLoopDefs

theorem finite (q1 q2 : Query) (Valid : State → Prop) (finish : Usize)
 (same : ∀ a b,Valid (.Ok (a,b)) → q1 a b=q2 a b)
 (preserve : ∀ a b after pending,Valid (.Ok (a,b)) → a.next.val<finish.val →
  q2 a b=.ok (.Ok (after,pending)) → Valid (.Ok (after,pending)))
 (fuel : Nat) (state : State) (valid : Valid state) :
 run q1 finish fuel state = run q2 finish fuel state := by
 induction fuel generalizing state with
 | zero => cases state with | Err e=>rfl | Ok pair=>cases pair;rfl
 | succ fuel ih =>
  cases state with
  | Err e => rfl
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases stopped : a.next≥finish
   · simp only [run,stopped,if_true]
   · have inside : a.next.val<finish.val := Nat.lt_of_not_ge stopped
     simp only [run,stopped,if_false,same a b valid]
     cases step : q2 a b with
     | fail e => rfl
     | div => rfl
     | ok next =>
      simp only [bind_tc_ok]
      cases next with
      | Err e => rfl
      | Ok pair =>
       rcases pair with ⟨after,pending⟩
       exact ih (.Ok (after,pending)) (preserve a b after pending valid inside step)
#print axioms finite
end AspisR1.NNU_QueryInduction
end
