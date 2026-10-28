import R1Z.PV_AL_RangeInvariant
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_AL_RangeLoop
set_option autoImplicit false

theorem source (v : Slice U8) (out : alloc.vec.Vec U8) (lo : Nat) (last i : Usize)
    (hl : last.val ≤ v.val.length) (hi : i.val ≤ last.val) (hlo : lo ≤ i.val)
    (hp : out.val=PV_AL_RangeLists.segment v.val lo i.val) :
    ∃ a, PV_AL_SplitFlat.copy_range_loop v last out i=ok a ∧
      a.val=PV_AL_RangeLists.segment v.val lo last.val := by
  generalize he : last.val-i.val=fuel
  induction fuel using Nat.strong_induction_on generalizing out i with
  | h fuel ih =>
    rw [PV_AL_RangeUnfold.unfold_loop]
    by_cases hs : i.val < last.val
    · obtain ⟨next,hn,hv⟩ := PV_AL_RangeStep.continuing v out last i hs hl
        (PV_AL_RangeInvariant.capacity v out lo i last hl hs hlo hp)
      rw [hn,bind_tc_ok]
      have inc := PV_CBL_ArrayStep.increment i last hs
      have nextp := PV_AL_RangeInvariant.advance v out next lo i hlo (by omega) hp hv
      obtain ⟨a,ha,hcopy⟩ := ih _ (by omega) next
        (Usize.wrapping_add i 1#usize) (by omega) (by omega)
        (by simpa only [inc] using nextp) rfl
      exact ⟨a,ha,hcopy⟩
    · rw [PV_AL_RangeStep.done v out last i (by omega),bind_tc_ok]
      have eq : i.val=last.val := by omega
      exact ⟨out,rfl,by simpa only [eq] using hp⟩

#print axioms source
end R1Z.PV_AL_RangeLoop
