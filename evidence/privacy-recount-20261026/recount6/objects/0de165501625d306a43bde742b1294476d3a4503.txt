import R1Z.PV_CBL_PadZeroContent
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadDelimitedBytes
set_option autoImplicit false
/-- Exact byte contents, retaining the delimiter and all bytes preceding it. -/
theorem source (out : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) :
    ∃ a, PV_CBL_ShaPadFixed.sha_pad_zero out pos = ok a ∧
      ∀ (j : Nat), j<64 → a.val[j]! =
        if j < pos.val then out.val[j]! else if j=pos.val then 128#u8 else 0#u8 := by
  obtain ⟨a,ha,hc⟩ := PV_CBL_PadZeroContent.loop_content
    (out.set pos 128#u8) (Usize.wrapping_add pos 1#usize)
  refine ⟨a,?_,?_⟩
  · unfold PV_CBL_ShaPadFixed.sha_pad_zero
    rw [PV_CBL_ArrayStep.write out pos 128#u8 hp]
    exact ha
  · intro j hj
    rw [hc j hj,PV_CBL_ArrayStep.increment pos 64#usize hp,
      PV_CBL_ArrayPrefix.set_get out pos 128#u8 j hp]
    by_cases hlt : j < pos.val
    · rw [if_pos (by omega),if_neg (by omega),if_pos hlt]
    · by_cases he : j=pos.val
      · rw [if_pos (by omega),if_pos he,if_neg hlt,if_pos he]
      · rw [if_neg (by omega),if_neg hlt,if_neg he]
#print axioms source
end R1Z.PV_CBL_PadDelimitedBytes
