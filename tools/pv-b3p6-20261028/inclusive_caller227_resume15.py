from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean');h='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding12227 Result ControlFlow
set_option autoImplicit false
'''
s='import PV_B3P_InclusiveLoop12227\n'+h+'''
/-- Ordered caller semantics of a finite inclusive interval: the final yielded
index executes once, and then iteration completes. This is NOT an association
of the std RangeInclusive implementation, whose catalogue belongs to pv-b3q. -/
def inclusive_caller_body15 {α : Type} (step : α → Usize → Result α) (last : Usize)
    (state : α × Usize) : Result (ControlFlow (α × Usize) α) :=
  if state.2 ≤ last then do
    let next ← step state.1 state.2
    if state.2 = last then .ok (.done next)
    else .ok (.cont (next,Usize.wrapping_add state.2 1#usize))
  else .ok (.done state.1)

def inclusive_caller_loop15 {α : Type} (step : α → Usize → Result α)
    (last first : Usize) (state : α) : Result α :=
  loop (inclusive_caller_body15 step last) (state,first)

theorem inclusive_caller_fold15 {α : Type} (step : α → Usize → Result α)
    (last first : Usize) (limit : last.val < 24) (n : Nat) (state : α)
    (count : first.val+n=last.val+1) :
    inclusive_caller_loop15 step last first state =
      PV_B3P_Ordered227.fold step (usize_indices11 n first) state := by
  induction n generalizing first state with
  | zero =>
    have outside : ¬ first ≤ last := by scalar_tac
    unfold inclusive_caller_loop15
    rw [loop.eq_1]
    simp only [inclusive_caller_body15,outside,if_false,usize_indices11,PV_B3P_Ordered227.fold]
  | succ n ih =>
    have inside : first ≤ last := by scalar_tac
    by_cases final : first = last
    · subst first
      have zero : n = 0 := by omega
      subst n
      unfold inclusive_caller_loop15
      rw [loop.eq_1]
      simp only [inclusive_caller_body15,le_refl,if_true,usize_indices11,
        PV_B3P_Ordered227.fold]
      cases operation : step state last <;> rfl
    · have increment : (Usize.wrapping_add first 1#usize).val = first.val+1 :=
        PV_B3P_Offset226V3.add_value first 1#usize (by
          rw [UScalar.size_def]
          scalar_tac)
      have rest : (Usize.wrapping_add first 1#usize).val+n=last.val+1 := by omega
      unfold inclusive_caller_loop15
      rw [loop.eq_1]
      simp only [inclusive_caller_body15,inside,if_true,final,if_false,usize_indices11,
        PV_B3P_Ordered227.fold]
      cases operation : step state first with
      | fail error => rfl
      | div => rfl
      | ok next =>
        simpa only [inclusive_caller_loop15,bind_tc_ok] using ih (Usize.wrapping_add first 1#usize) next rest
#print axioms inclusive_caller_fold15
end PV_B3P_Native15227
''';(L/'PV_B3P_InclusiveCaller15227.lean').write_text(s)
s='import PV_B3P_InclusiveCaller15227\nimport PV_B3P_NativePreweighted15227\n'+h+'''
open PV_B3P_227
/-- The actual preweighted caller's bounded inclusive iteration is joined to
its owned loop. Macro and packed stores stay in their source order. -/
theorem preweighted_inclusive_caller15 {N : Usize}
    (start : Usize) (values : Array aspis_core.field.QM31 N)
    (last first : Usize) (limit : last.val < 24) (n : Nat)
    (packed : Array aspis_core.field.QM31 24#usize) (count : first.val+n=last.val+1) :
    inclusive_caller_loop15 (source_preweighted_macro_step12 start values) last first packed =
      reference_terminal.add_preweighted_loop packed start values last first := by
  rw [inclusive_caller_fold15 _ last first limit n packed count,preweighted_loop_binding12]
  have steps : source_preweighted_macro_step12 start values = preweighted_source_step12 start values := by
    funext state group
    exact preweighted_macro_step_binding12 start values state group
  rw [steps]
  exact (inclusive_loop_fold12 _ last first limit n packed count).symm
#print axioms preweighted_inclusive_caller15
end PV_B3P_Native15227
''';(L/'PV_B3P_PreweightedInclusive15227.lean').write_text(s)
