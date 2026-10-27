import R1Z.PV_CBL_PadZeroTotal
import R1Z.PV_CBL_PadSuffixTotal
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadComplete
set_option autoImplicit false
/-- Full Result totality and exact retained-buffer/reset shape of the safe
padding reference; no shipped wrapper/loan/callback association is inferred. -/
theorem complete (buffer : Array U8 64#usize) (pos : Usize)
    (suffix : Array U8 8#usize) (h : pos.val<64) :
    ∃ first second, PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos suffix =
      ok (first,second,first,0#usize) := by
  obtain ⟨head,hh⟩ := PV_CBL_PadZeroTotal.total buffer pos h
  unfold PV_CBL_ShaPadFixed.sha_pad_owned_split8
  rw [hh]
  simp only [lift,bind_tc_ok]
  split
  · obtain ⟨second,hs⟩ := PV_CBL_PadSuffixTotal.total (Array.repeat 64#usize 0#u8) suffix
    rw [hs,bind_tc_ok]
    exact ⟨head,some second,rfl⟩
  · obtain ⟨first,hs⟩ := PV_CBL_PadSuffixTotal.total head suffix
    rw [hs,bind_tc_ok]
    exact ⟨first,none,rfl⟩
#print axioms complete
end R1Z.PV_CBL_PadComplete
