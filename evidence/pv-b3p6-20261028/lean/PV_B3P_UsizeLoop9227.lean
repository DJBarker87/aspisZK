import PV_B3P_Offset226V3
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

def usize_plan {α : Type} (step : α → Usize → Result α) :
    Nat → Usize → α → Result α
  | 0, _, state => .ok state
  | n+1, i, state => do
    let next ← step state i
    usize_plan step n (Usize.wrapping_add i 1#usize) next

def usize_body {α : Type} (step : α → Usize → Result α) (stop : Usize)
    (state : α × Usize) : Result (ControlFlow (α × Usize) α) := do
  if state.2 < stop then
    let next ← step state.1 state.2
    let i ← lift (Usize.wrapping_add state.2 1#usize)
    .ok (.cont (next,i))
  else .ok (.done state.1)

theorem usize_loop_plan {α : Type} (step : α → Usize → Result α)
    (stop i : Usize) (n : Nat) (state : α) (h : i.val+n=stop.val) :
    loop (usize_body step stop) (state,i) = usize_plan step n i state := by
  induction n generalizing i state with
  | zero =>
    have hp : ¬i<stop := by scalar_tac
    rw [loop.eq_1]
    simp only [usize_body,hp,↓reduceIte,bind_tc_ok,usize_plan]
  | succ n ih =>
    have hp : i<stop := by scalar_tac
    have hn : (Usize.wrapping_add i 1#usize).val=i.val+1 :=
      PV_B3P_Offset226V3.add_value i 1#usize (by
        have hb := stop.hBounds
        change i.val+1 < _
        simpa only [UScalar.size] using (show i.val+1 < 2^UScalarTy.Usize.numBits from by omega))
    rw [loop.eq_1]
    simp only [usize_body,hp,↓reduceIte,usize_plan]
    cases hs : step state i with
    | fail e => rfl
    | div => rfl
    | ok next =>
      simp only [lift,bind_tc_ok]
      exact ih _ next (by omega)

#print axioms usize_loop_plan
end PV_B3P_Binding9227
