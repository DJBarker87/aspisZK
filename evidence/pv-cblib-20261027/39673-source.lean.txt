import R1Z.PV_CBL_ArrayStep
import R1Z.PV_CBL_ArrayUnfold
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_ArrayTotal
set_option autoImplicit false

/-- Totality follows from the decreasing number of uncopied cells, for all N. -/
theorem total {T : Type} {N : Usize} (v : Slice T) (hv : N.val≤v.val.length)
    (out : Array T N) (i : Usize) :
    ∃ a, PV_CBL_ArrayKernel.array_reference_loop v out i = ok a := by
  generalize he : N.val-i.val = fuel
  induction fuel using Nat.strong_induction_on generalizing out i with
  | h fuel ih =>
    rw [PV_CBL_ArrayUnfold.unfold_loop]
    by_cases hi : i.val<N.val
    · rw [PV_CBL_ArrayStep.continuing v out i hi (by omega),bind_tc_ok]
      have hs := PV_CBL_ArrayStep.increment i N hi
      have less : N.val-(Usize.wrapping_add i 1#usize).val<fuel := by omega
      obtain ⟨a,ha⟩ := ih _ less (out.set i v.val[i.val])
        (Usize.wrapping_add i 1#usize) rfl
      exact ⟨a,ha⟩
    · rw [PV_CBL_ArrayStep.done v out i (by omega),bind_tc_ok]
      exact ⟨out,rfl⟩
#print axioms total
end R1Z.PV_CBL_ArrayTotal
