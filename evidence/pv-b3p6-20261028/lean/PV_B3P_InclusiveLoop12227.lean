import PV_B3P_PlanFold11227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_Binding9227 PV_B3P_Binding11227
set_option autoImplicit false

def inclusive_body12 {α : Type} (step : α → Usize → Result α) (last : Usize)
    (state : α × Usize) : Result (ControlFlow (α × Usize) α) :=
  if state.2 <= last then do
    let next ← step state.1 state.2
    .ok (.cont (next,Usize.wrapping_add state.2 1#usize))
  else .ok (.done state.1)

theorem inclusive_body_binding12 {α : Type} (step : α → Usize → Result α)
    (last : Usize) (hl : last.val < 24) (state : α × Usize) :
    inclusive_body12 step last state =
      usize_body step (Usize.wrapping_add last 1#usize) state := by
  have hv : (Usize.wrapping_add last 1#usize).val = last.val+1 :=
    PV_B3P_Offset226V3.add_value last 1#usize (by
      rw [UScalar.size_def]
      scalar_tac)
  have hg : (state.2 <= last) = (state.2 < Usize.wrapping_add last 1#usize) := by
    apply propext
    scalar_tac
  unfold inclusive_body12 usize_body
  rw [hg]
  simp only [lift,bind_tc_ok]

theorem inclusive_loop_fold12 {α : Type} (step : α → Usize → Result α)
    (last i : Usize) (hl : last.val < 24) (n : Nat) (state : α)
    (hn : i.val+n=last.val+1) :
    loop (inclusive_body12 step last) (state,i) =
      PV_B3P_Ordered227.fold step (usize_indices11 n i) state := by
  have hv : (Usize.wrapping_add last 1#usize).val = last.val+1 :=
    PV_B3P_Offset226V3.add_value last 1#usize (by
      rw [UScalar.size_def]
      scalar_tac)
  have hb : inclusive_body12 step last = usize_body step (Usize.wrapping_add last 1#usize) :=
    funext (inclusive_body_binding12 step last hl)
  rw [hb]
  exact loop_as_fold11 step _ i n state (by omega)

#print axioms inclusive_body_binding12
#print axioms inclusive_loop_fold12
end PV_B3P_Binding12227
