import R1Z.PV_CBL_ArrayReferenceTotal
import R1Z.PV_CBL_ArrayExt
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArraySuccess
set_option autoImplicit false

theorem success {T : Type} (N : Usize) (copy : core.marker.Copy T)
    (v : Slice T) (zero : T) (h : Slice.len v=N) :
    ∃ a, PV_CBL_ArrayKernel.array_reference N copy v zero = ok (some a) ∧ a.val=v.val := by
  letI : Inhabited T := ⟨zero⟩
  have hlen : v.val.length=N.val := congrArg UScalar.val h
  let target : Array T N := ⟨v.val,hlen⟩
  have ht : PV_CBL_ArrayPrefix.copied target v N.val := by intro j _ _; rfl
  obtain ⟨a,ha,hcopy⟩ := PV_CBL_ArrayCopied.total_copied v (by omega)
    (Array.repeat N zero) 0#usize (by simp) (PV_CBL_ArrayPrefix.initial _ _)
  have eq : a=target := PV_CBL_ArrayExt.copied_unique a target v hcopy ht
  refine ⟨a,?_,?_⟩
  · rw [PV_CBL_ArrayGuard.correct_length N copy v zero h,ha,bind_tc_ok]
  · rw [eq]; rfl

#print axioms success
end R1Z.PV_CBL_ArraySuccess
