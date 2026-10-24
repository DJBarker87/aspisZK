import S1WideViewFinalFrameV1
import S1FrameArithmeticV1
set_option autoImplicit false
namespace AspisR1SelectedWideViewV1
open Aeneas Aeneas.Std Result

/-- Exact source width multiplication, TOTAL at every supported usize width. -/
theorem final_width_total : (compact.FINAL_LEN*32#usize : Result Usize)=ok 2048#usize := by
  simp only [compact.FINAL_LEN]
  exact AspisS1FrameArithmetic.mul_exact _ _ _ (by scalar_tac)

/-- The actual accepted View supplies its final-message length. No separate
parser, slice, source-offset or arithmetic success hypothesis is added. -/
theorem wide_view_final_length (proof semantic y1 : Slice U8) (out : verifier.View)
    (accepted : verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) :
    out.final_message.length=2048 := by
  obtain ⟨start,stop,hstart,hstop,hframe,horder,hbound,hlength⟩ :=
    wide_view_final_frame proof semantic y1 out accepted
  unfold compact.OFF_OPENINGS at hstop
  rw [final_width_total,bind_tc_ok,hstart,bind_tc_ok] at hstop
  have exactSum := AspisS1FrameArithmetic.add_value start 2048#usize stop hstop
  have width : (2048#usize : Usize).val=2048 := by scalar_tac
  rw [width] at exactSum
  omega

#print axioms final_width_total
#print axioms wide_view_final_length
end AspisR1SelectedWideViewV1
