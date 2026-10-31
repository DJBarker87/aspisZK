import PV_B3P_DirectPreweightedJoin17227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Native15227 Result
set_option autoImplicit false

theorem preweighted_extraction_reference17 {N : Usize}
    (packed : Array aspis_core.field.QM31 24#usize) (start : Usize)
    (values : Array aspis_core.field.QM31 N)
    (positive : 0 < N.val) (bounded : start.val+N.val ≤ 96) :
    host_terminal.add_preweighted packed start values =
      reference_terminal.add_preweighted packed start values := by
  obtain ⟨first,hfirst,hfirstval⟩ := UScalar.div_spec (x:=start) (y:=4#usize) (by scalar_tac)
  let stop := Usize.wrapping_add start N
  have hstop : stop.val=start.val+N.val := PV_B3P_Offset226V3.add_value start N (by
    have hsize := Usize.cMax_bound_concrete.1
    rw [UScalar.size_def]
    scalar_tac)
  let finish := Usize.wrapping_sub stop 1#usize
  have hfinish : finish.val=stop.val-1 := PV_B3P_Offset226V3.sub_value stop 1#usize (by scalar_tac)
  obtain ⟨last,hlast,hlastval⟩ := UScalar.div_spec (x:=finish) (y:=4#usize) (by scalar_tac)
  have limit : last.val < 24 := by
    have hf : finish.val < 96 := by omega
    scalar_tac
  have ordered : first.val ≤ last.val := by
    have hle : start.val ≤ finish.val := by omega
    have hdiv : start.val/4 ≤ finish.val/4 := Nat.div_le_div_right hle
    scalar_tac
  have count : first.val+(last.val+1-first.val)=last.val+1 := by omega
  unfold host_terminal.add_preweighted reference_terminal.add_preweighted
  rw [hfirst]
  simp only [lift,bind_tc_ok]
  simp only [finish,stop] at hlast
  rw [hlast]
  simp only [bind_tc_ok,core.ops.range.RangeInclusive.new]
  exact preweighted_loop_reference17 start values first last packed limit _ count

#print axioms preweighted_extraction_reference17
end PV_B3P_Direct17227
