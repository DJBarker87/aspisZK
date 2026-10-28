import R1Z.PV_CBL_PadDelimitedSource
import R1Z.PV_CBL_PadSuffixList
import R1Z.PV_CBL_PadBranchValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadOneSource
set_option autoImplicit false
theorem source (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<56) :
    ∃ first, PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos suffix =
      ok (first,none,first,0#usize) ∧
      first.val = PV_CBL_PaddingModel.first buffer.val pos.val suffix.val := by
  obtain ⟨head,hh,hv⟩ := PV_CBL_PadDelimitedSource.source buffer pos (by omega)
  have hn : ¬(Usize.wrapping_sub (Usize.wrapping_sub 64#usize pos) 1#usize < 8#usize) := by
    rw [PV_CBL_PadBranchValue.branch pos (by omega)]; omega
  refine ⟨PV_CBL_PadSuffixValue.value head suffix,?_,?_⟩
  · unfold PV_CBL_ShaPadFixed.sha_pad_owned_split8
    rw [hh]
    simp only [lift,bind_tc_ok,if_neg hn,PV_CBL_PadSuffixValue.source]
  · rw [PV_CBL_PadSuffixList.value,hv]
    simp only [PV_CBL_PaddingModel.first,if_pos hp]
#print axioms source
end R1Z.PV_CBL_PadOneSource
