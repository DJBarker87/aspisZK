import PV_B3P_InclusiveGeneral540227
import PV_B3P_DirectPreweightedJoin17227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Direct540227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Direct17227 PV_B3P_Binding12227 PV_B3P_Links13227 Result
set_option autoImplicit false

/-- No buffer bound is needed for loop equality: both sides preserve the
same failing array operation, as well as divergence and success. -/
theorem preweighted_loop_total540 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (first last : Usize)
    (packed : Array aspis_core.field.QM31 24#usize)
    (safe : last.val+1 < UScalar.size .Usize) :
    host_terminal.add_preweighted_loop0 ⟨first,last,false⟩ packed start values =
      reference_terminal.add_preweighted_loop packed start values last first := by
  rw [preweighted_outer_loop17,inclusive_std_while540 _ first last safe,
    preweighted_loop_binding12]
  have steps : source_preweighted_macro_step12 start values = preweighted_source_step12 start values := by
    funext state group
    exact preweighted_macro_step_binding12 start values state group
  rw [steps]

/-- The final inclusive endpoint is divided by four, even when start+N or
start+N-1 wraps. Thus its successor cannot wrap. No huge range is evaluated. -/
theorem preweighted_extraction_total540 {N : Usize}
    (packed : Array aspis_core.field.QM31 24#usize) (start : Usize)
    (values : Array aspis_core.field.QM31 N) :
    host_terminal.add_preweighted packed start values =
      reference_terminal.add_preweighted packed start values := by
  obtain ⟨first,hfirst,_⟩ := UScalar.div_spec (x:=start) (y:=4#usize) (by scalar_tac)
  let stop := Usize.wrapping_add start N
  let before := Usize.wrapping_sub stop 1#usize
  obtain ⟨last,hlast,hlastval⟩ := UScalar.div_spec (x:=before) (y:=4#usize) (by scalar_tac)
  have upper : before.val < UScalar.size .Usize := by
    simpa only [UScalar.size] using before.hBounds
  have divvalue : last.val = before.val/4 := by scalar_tac
  have big : 4 < UScalar.size .Usize := by
    rw [UScalar.size_def]
    scalar_tac
  have safe : last.val+1 < UScalar.size .Usize := by omega
  unfold host_terminal.add_preweighted reference_terminal.add_preweighted
  rw [hfirst]
  simp only [lift,bind_tc_ok]
  simp only [before,stop] at hlast
  rw [hlast]
  simp only [bind_tc_ok,core.ops.range.RangeInclusive.new]
  exact preweighted_loop_total540 start values first last packed safe

/-- This discharges the old total Link3 for the direct extraction, without
replacing its quantifiers by an actual-call guard. -/
theorem extracted_preweighted_total_link540 :
    PV_B3P_Link_terminal_add_preweighted (@host_terminal.add_preweighted) := by
  funext N packed start values
  exact preweighted_extraction_total540 packed start values

#print axioms preweighted_loop_total540
#print axioms preweighted_extraction_total540
#print axioms extracted_preweighted_total_link540
end PV_B3P_Direct540227
