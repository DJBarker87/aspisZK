import R1Z.PV_CBL_PadDelimitedSource
import R1Z.PV_CBL_PadSuffixList
import R1Z.PV_CBL_PadBranchValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadTwoSource
set_option autoImplicit false
theorem source (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<64) (h56 : 56≤pos.val) :
    ∃ first second, PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos suffix =
      ok (first,some second,first,0#usize) ∧
      first.val = PV_CBL_PaddingModel.first buffer.val pos.val suffix.val ∧
      some second.val = PV_CBL_PaddingModel.second pos.val suffix.val := by
  obtain ⟨head,hh,hv⟩ := PV_CBL_PadDelimitedSource.source buffer pos hp
  have hc := (PV_CBL_PadBranchValue.branch pos hp).mpr h56
  refine ⟨head,PV_CBL_PadSuffixValue.value (Array.repeat 64#usize 0#u8) suffix,?_,?_,?_⟩
  · unfold PV_CBL_ShaPadFixed.sha_pad_owned_split8
    rw [hh]
    simp only [lift,bind_tc_ok,if_pos hc,PV_CBL_PadSuffixValue.source]
  · simp only [PV_CBL_PaddingModel.first,if_neg (show ¬pos.val<56 by omega)]
    exact hv
  · rw [PV_CBL_PadSuffixList.value]
    simp [PV_CBL_PaddingModel.second,show ¬pos.val<56 by omega,Array.repeat]
#print axioms source
end R1Z.PV_CBL_PadTwoSource
