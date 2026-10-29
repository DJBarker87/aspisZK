import PV_B3P_Offset226V3
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

def reverse_plan {α : Type} (step : α → Usize → Result α) :
    Nat → Usize → α → Result α
  | 0, _, state => .ok state
  | n+1, i, state => do
    let j ← lift (Usize.wrapping_sub i 1#usize)
    let next ← step state j
    reverse_plan step n j next

def reverse_body {α : Type} (step : α → Usize → Result α)
    (state : α × Usize) : Result (ControlFlow (α × Usize) α) := do
  if state.2 > 0#usize then
    let j ← lift (Usize.wrapping_sub state.2 1#usize)
    let next ← step state.1 j
    .ok (.cont (next,j))
  else .ok (.done state.1)

theorem reverse_loop_plan {α : Type} (step : α → Usize → Result α)
    (i : Usize) (n : Nat) (state : α) (h : i.val=n) :
    loop (reverse_body step) (state,i) = reverse_plan step n i state := by
  induction n generalizing i state with
  | zero =>
    have hp : ¬i>0#usize := by scalar_tac
    rw [loop.eq_1]
    simp only [reverse_body,hp,↓reduceIte,bind_tc_ok,reverse_plan]
  | succ n ih =>
    have hp : i>0#usize := by scalar_tac
    have hn : (Usize.wrapping_sub i 1#usize).val=n := by
      rw [PV_B3P_Offset226V3.sub_value i 1#usize (by scalar_tac)]
      change i.val-1=n
      omega
    rw [loop.eq_1]
    simp only [reverse_body,hp,↓reduceIte,reverse_plan,lift,bind_tc_ok]
    cases hs : step state (Usize.wrapping_sub i 1#usize) with
    | fail e => rfl
    | div => rfl
    | ok next =>
      simp only [bind_tc_ok]
      exact ih _ next hn

#print axioms reverse_loop_plan
end PV_B3P_Binding9227
