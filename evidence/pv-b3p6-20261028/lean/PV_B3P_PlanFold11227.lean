import PV_B3P_UsizeLoop9227
import PV_B3P_Ordered227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_Binding9227
set_option autoImplicit false

def usize_indices11 : Nat → Usize → List Usize
  | 0, _ => []
  | n+1, i => i :: usize_indices11 n (Usize.wrapping_add i 1#usize)

theorem plan_as_fold11 {α : Type} (step : α → Usize → Result α)
    (n : Nat) (i : Usize) (state : α) :
    usize_plan step n i state = PV_B3P_Ordered227.fold step (usize_indices11 n i) state := by
  induction n generalizing i state with
  | zero => exact Eq.refl _
  | succ n ih =>
    simp only [usize_plan,usize_indices11,PV_B3P_Ordered227.fold]
    exact congrArg (fun k => step state i >>= k) (funext fun next => ih _ next)

theorem loop_as_fold11 {α : Type} (step : α → Usize → Result α)
    (stop i : Usize) (n : Nat) (state : α) (h : i.val+n=stop.val) :
    loop (usize_body step stop) (state,i) =
      PV_B3P_Ordered227.fold step (usize_indices11 n i) state :=
  (usize_loop_plan step stop i n state h).trans (plan_as_fold11 step n i state)
#print axioms plan_as_fold11
#print axioms loop_as_fold11
end PV_B3P_Binding11227
