import PV_B3P_Ordered227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_Ordered227
set_option autoImplicit false

/-- Source-shaped increasing loop, with every step's Result retained. -/
def count_body {α : Type} (step : α → Nat → Result α) (stop : Nat)
    (state : α × Nat) : Result (ControlFlow (α × Nat) α) := do
  if state.2 < stop then
    let next ← step state.1 state.2
    .ok (.cont (next,state.2+1))
  else .ok (.done state.1)

def count_loop {α : Type} (step : α → Nat → Result α) (stop : Nat)
    (initial : α) (start : Nat) : Result α :=
  loop (count_body step stop) (initial,start)

theorem count_loop_fold {α : Type} (step : α → Nat → Result α)
    (start count : Nat) (initial : α) :
    count_loop step (start+count) initial start =
      fold step (List.range' start count) initial := by
  induction count generalizing start initial with
  | zero =>
    unfold count_loop
    rw [loop.eq_1]
    simp only [count_body,Nat.add_zero,lt_self_iff_false,↓reduceIte,bind_tc_ok,fold,List.range'_zero]
  | succ count ih =>
    unfold count_loop
    rw [loop.eq_1]
    have hp : start < start + (count+1) := by omega
    simp only [count_body,hp,↓reduceIte,List.range'_succ,fold]
    cases hs : step initial start with
    | fail e => rfl
    | div => rfl
    | ok next =>
      change count_loop step (start+(count+1)) next (start+1) =
        fold step (List.range' (start+1) count) next
      have he : start+(count+1)=(start+1)+count := by omega
      rw [he]
      exact ih (start+1) next

#print axioms count_loop_fold
end PV_B3P_Binding9227
