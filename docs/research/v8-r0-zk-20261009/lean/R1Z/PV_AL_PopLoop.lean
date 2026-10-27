import R1Z.PV_AL_PopPrefix
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_AL_PopLoop
set_option autoImplicit false

theorem source {T : Type} (v : Slice T) (out : alloc.vec.Vec T) (last i : Usize)
    (hl : last.val≤v.val.length) (hi : i.val≤last.val)
    (hp : out.val=v.val.take i.val) :
    ∃ a, PV_CBL_PopSlices.pop_slices_reference_loop v out last i=ok a ∧
      a.val=v.val.take last.val := by
  generalize he : last.val-i.val=fuel
  induction fuel using Nat.strong_induction_on generalizing out i with
  | h fuel ih =>
    rw [PV_AL_PopUnfold.unfold_loop]
    by_cases hs : i.val<last.val
    · obtain ⟨next,hn,hv⟩ := PV_AL_PopStep.continuing v out last i hs hl
        (PV_AL_PopPrefix.length v out i last hs hl hp)
      rw [hn,bind_tc_ok]
      have inc := PV_CBL_ArrayStep.increment i last hs
      have nextp := PV_AL_PopPrefix.advance v out next i (by omega) hp hv
      obtain ⟨a,ha,hcopy⟩ := ih _ (by omega) next
        (Usize.wrapping_add i 1#usize) (by omega)
        (by simpa only [inc] using nextp) rfl
      exact ⟨a,ha,hcopy⟩
    · rw [PV_AL_PopStep.done v out last i (by omega),bind_tc_ok]
      have eq : i.val=last.val := by omega
      exact ⟨out,rfl,by simpa only [eq] using hp⟩
#print axioms source
end R1Z.PV_AL_PopLoop
