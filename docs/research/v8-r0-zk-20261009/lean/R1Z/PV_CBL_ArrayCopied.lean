import R1Z.PV_CBL_ArrayPrefix
import R1Z.PV_CBL_ArrayStep
import R1Z.PV_CBL_ArrayUnfold
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_ArrayCopied
set_option autoImplicit false

theorem total_copied {T : Type} [Inhabited T] {N : Usize} (v : Slice T)
    (hv : N.val≤v.val.length) (out : Array T N) (i : Usize)
    (hi : i.val≤N.val) (hp : PV_CBL_ArrayPrefix.copied out v i.val) :
    ∃ a, PV_CBL_ArrayKernel.array_reference_loop v out i = ok a ∧
      PV_CBL_ArrayPrefix.copied a v N.val := by
  generalize he : N.val-i.val=fuel
  induction fuel using Nat.strong_induction_on generalizing out i with
  | h fuel ih =>
    rw [PV_CBL_ArrayUnfold.unfold_loop]
    by_cases hs : i.val<N.val
    · rw [PV_CBL_ArrayStep.continuing v out i hs (by omega),bind_tc_ok]
      have inc := PV_CBL_ArrayStep.increment i N hs
      have next := PV_CBL_ArrayPrefix.advance out v i hs (by omega) hp
      obtain ⟨a,ha,hcopy⟩ := ih _ (by omega) (out.set i v.val[i.val])
        (Usize.wrapping_add i 1#usize) (by omega) (by simpa only [inc] using next) rfl
      exact ⟨a,ha,hcopy⟩
    · rw [PV_CBL_ArrayStep.done v out i (by omega),bind_tc_ok]
      have eq : i.val=N.val := by omega
      exact ⟨out,rfl,by simpa only [eq] using hp⟩
#print axioms total_copied
end R1Z.PV_CBL_ArrayCopied
