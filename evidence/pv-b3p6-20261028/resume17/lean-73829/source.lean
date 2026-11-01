import PV_B3P_DirectInclusive17227
import PV_B3P_InclusiveLoop12227
namespace PV_B3P_Direct540227
open Aeneas Aeneas.Std PV_B3P_Direct17227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result ControlFlow
set_option autoImplicit false

/-- The standard inclusive iterator fold does not require last < 24.
Its own exhausted flag handles the final index without wrapping it. -/
theorem inclusive_std_fold540 {α : Type} (step : α → Usize → Result α)
    (last first : Usize) (n : Nat) (state : α)
    (count : first.val+n=last.val+1) :
    inclusive_std_loop17 step first last state =
      PV_B3P_Ordered227.fold step (usize_indices11 n first) state := by
  induction n generalizing first state with
  | zero =>
    have empty : last.val < first.val := by omega
    unfold inclusive_std_loop17
    rw [loop.eq_1]
    simp only [inclusive_std_body17,inclusive_next_extraction17,empty,or_true,if_true,
      bind_tc_ok,usize_indices11,PV_B3P_Ordered227.fold]
  | succ n ih =>
    by_cases final : first = last
    · subst first
      have zero : n=0 := by omega
      subst n
      unfold inclusive_std_loop17
      rw [loop.eq_1]
      simp only [inclusive_std_body17,inclusive_final17,bind_tc_ok,inclusive_exhausted17,
        usize_indices11,PV_B3P_Ordered227.fold]
      cases operation : step state last with
      | fail e => rfl
      | div => rfl
      | ok next => simp only [bind_tc_ok,inclusive_exhausted17]
    · have inside : first.val < last.val := by scalar_tac
      have inc := PV_B3P_Offset226V3.add_value first 1#usize
        (range_increment_safe13 first last (by scalar_tac))
      change (Usize.wrapping_add first 1#usize).val = first.val+1 at inc
      have rest : (Usize.wrapping_add first 1#usize).val+n=last.val+1 := by rw [inc]; omega
      unfold inclusive_std_loop17
      rw [loop.eq_1]
      simp only [inclusive_std_body17,inclusive_more17 first last inside,bind_tc_ok,
        usize_indices11,PV_B3P_Ordered227.fold]
      cases operation : step state first with
      | fail e => rfl
      | div => rfl
      | ok next =>
        simpa only [inclusive_std_loop17,bind_tc_ok] using
          (ih (Usize.wrapping_add first 1#usize) next rest)

/-- The reference while loop only needs a nonwrapping successor of last. -/
theorem inclusive_body_general540 {α : Type} (step : α → Usize → Result α)
    (last : Usize) (safe : last.val+1 < UScalar.size .Usize) (state : α × Usize) :
    inclusive_body12 step last state =
      usize_body step (Usize.wrapping_add last 1#usize) state := by
  have hv : (Usize.wrapping_add last 1#usize).val = last.val+1 :=
    PV_B3P_Offset226V3.add_value last 1#usize safe
  have hg : (state.2 <= last) = (state.2 < Usize.wrapping_add last 1#usize) := by
    apply propext
    scalar_tac
  unfold inclusive_body12 usize_body
  simp only [hg,lift,bind_tc_ok]

theorem inclusive_while_fold540 {α : Type} (step : α → Usize → Result α)
    (last first : Usize) (safe : last.val+1 < UScalar.size .Usize)
    (n : Nat) (state : α) (count : first.val+n=last.val+1) :
    loop (inclusive_body12 step last) (state,first) =
      PV_B3P_Ordered227.fold step (usize_indices11 n first) state := by
  have hv : (Usize.wrapping_add last 1#usize).val = last.val+1 :=
    PV_B3P_Offset226V3.add_value last 1#usize safe
  have body := funext (inclusive_body_general540 step last safe)
  rw [body]
  exact loop_as_fold11 step _ first n state (by omega)

/-- Both loops agree on empty/reversed ranges and every nonwrapping endpoint.
The step may fail or diverge; neither is hidden by a success hypothesis. -/
theorem inclusive_std_while540 {α : Type} (step : α → Usize → Result α)
    (first last : Usize) (safe : last.val+1 < UScalar.size .Usize) (state : α) :
    inclusive_std_loop17 step first last state =
      loop (inclusive_body12 step last) (state,first) := by
  by_cases order : first <= last
  · have count : first.val+(last.val+1-first.val)=last.val+1 := by scalar_tac
    exact (inclusive_std_fold540 step last first _ state count).trans
      (inclusive_while_fold540 step last first safe _ state count).symm
  · have empty : last.val < first.val := by scalar_tac
    have left : inclusive_std_loop17 step first last state = .ok state := by
      unfold inclusive_std_loop17
      rw [loop.eq_1]
      simp only [inclusive_std_body17,inclusive_next_extraction17,empty,or_true,if_true,bind_tc_ok]
    have right : loop (inclusive_body12 step last) (state,first) = .ok state := by
      rw [loop.eq_1]
      simp only [inclusive_body12,order,if_false]
    exact left.trans right.symm

#print axioms inclusive_std_fold540
#print axioms inclusive_body_general540
#print axioms inclusive_while_fold540
#print axioms inclusive_std_while540
end PV_B3P_Direct540227
