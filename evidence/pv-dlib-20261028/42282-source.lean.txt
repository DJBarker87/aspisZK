import R1Z.PV_CBL_PadOneSource
import R1Z.PV_CBL_PadTwoSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadContentSource
set_option autoImplicit false
/-- Full content, retained-buffer and reset-position law of the extracted owned
reference. The native loan/callback/destructor link is a separate obligation. -/
theorem source (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<64) :
    ∃ first second, PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos suffix =
      ok (first,second,first,0#usize) ∧
      first.val = PV_CBL_PaddingModel.first buffer.val pos.val suffix.val ∧
      second.map (fun a => a.val) = PV_CBL_PaddingModel.second pos.val suffix.val := by
  by_cases h : pos.val<56
  · obtain ⟨first,hf,hv⟩ := PV_CBL_PadOneSource.source buffer pos suffix h
    exact ⟨first,none,hf,hv,by simp [PV_CBL_PaddingModel.second,h]⟩
  · obtain ⟨first,second,hf,hv,hs⟩ := PV_CBL_PadTwoSource.source buffer pos suffix hp (by omega)
    exact ⟨first,some second,hf,hv,hs⟩
#print axioms source
end R1Z.PV_CBL_PadContentSource
