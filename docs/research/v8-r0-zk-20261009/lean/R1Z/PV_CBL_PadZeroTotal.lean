import R1Z.PV_CBL_PadZeroStep
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_PadZeroTotal
set_option autoImplicit false
theorem loop_total (out : Array U8 64#usize) (i : Usize) :
    ∃ a, PV_CBL_ShaPadFixed.sha_pad_zero_loop out i=ok a := by
  generalize he : 64-i.val=fuel
  induction fuel using Nat.strong_induction_on generalizing out i with
  | h fuel ih =>
    rw [PV_CBL_PadZeroStep.unfold_loop]
    by_cases hi : i.val<64
    · rw [PV_CBL_PadZeroStep.continuing out i hi,bind_tc_ok]
      have hs := PV_CBL_ArrayStep.increment i 64#usize hi
      obtain ⟨a,ha⟩ := ih _ (by omega) (out.set i 0#u8) (Usize.wrapping_add i 1#usize) rfl
      exact ⟨a,ha⟩
    · rw [PV_CBL_PadZeroStep.done out i (by omega),bind_tc_ok]
      exact ⟨out,rfl⟩
theorem total (out : Array U8 64#usize) (pos : Usize) (h : pos.val<64) :
    ∃ a, PV_CBL_ShaPadFixed.sha_pad_zero out pos=ok a := by
  unfold PV_CBL_ShaPadFixed.sha_pad_zero
  rw [PV_CBL_ArrayStep.write out pos 128#u8 h]
  simp only [bind_tc_ok,lift]
  exact loop_total _ _
#print axioms loop_total
#print axioms total
end R1Z.PV_CBL_PadZeroTotal
