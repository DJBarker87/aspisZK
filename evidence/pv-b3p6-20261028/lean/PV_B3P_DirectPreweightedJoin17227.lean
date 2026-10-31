import PV_B3P_DirectPreweighted17227
import PV_B3P_DirectInclusive17227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Native15227 Result ControlFlow
set_option autoImplicit false
attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.add host_terminal_field.qm31_pack_base4

theorem preweighted_outer_body17 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N)
    (iter : core.ops.range.RangeInclusive Usize)
    (packed : Array aspis_core.field.QM31 24#usize) :
    host_terminal.add_preweighted_loop0.body start values iter packed =
      inclusive_std_body17 (source_preweighted_macro_step12 start values) (iter,packed) := by
  unfold host_terminal.add_preweighted_loop0.body inclusive_std_body17
  cases execution : core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨item,rest⟩
    cases item with
    | none => rfl
    | some group =>
      simp only [bind_tc_ok,preweighted_four17,source_preweighted_macro_step12,
        PV_B3P_Ordered227.bind_assoc]

theorem preweighted_outer_loop17 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (first last : Usize)
    (packed : Array aspis_core.field.QM31 24#usize) :
    host_terminal.add_preweighted_loop0 ⟨first,last,false⟩ packed start values =
      inclusive_std_loop17 (source_preweighted_macro_step12 start values) first last packed := by
  unfold host_terminal.add_preweighted_loop0 inclusive_std_loop17
  apply congrArg (fun body => loop body
    ((⟨first,last,false⟩ : core.ops.range.RangeInclusive Usize),packed))
  funext state
  exact preweighted_outer_body17 start values state.1 state.2

theorem preweighted_loop_reference17 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (first last : Usize)
    (packed : Array aspis_core.field.QM31 24#usize)
    (limit : last.val < 24) (n : Nat) (count : first.val+n=last.val+1) :
    host_terminal.add_preweighted_loop0 ⟨first,last,false⟩ packed start values =
      reference_terminal.add_preweighted_loop packed start values last first := by
  rw [preweighted_outer_loop17,inclusive_std_fold17 _ last first limit n packed count,
    preweighted_loop_binding12]
  have steps : source_preweighted_macro_step12 start values = preweighted_source_step12 start values := by
    funext state group
    exact preweighted_macro_step_binding12 start values state group
  rw [steps]
  exact (inclusive_loop_fold12 _ last first limit n packed count).symm

#print axioms preweighted_outer_body17
#print axioms preweighted_outer_loop17
#print axioms preweighted_loop_reference17
end PV_B3P_Direct17227
