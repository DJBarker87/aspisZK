import NDL_IterRef.Funs
import NDL_FieldAssociation
import NCJ_ForwardRange
import NCJ_Reverse
set_option autoImplicit false
namespace NDL_IterAssociation
open Aeneas Aeneas.Std Result

theorem forward_active (iter : NCJ_ForwardRange.Range) (last : iter.end.val=4)
    (more : iter.start.val  <  iter.end.val) :
    ∃ rest,NCJ_ForwardRange.next iter=ok (some iter.start,rest) ∧
      NDL_IterRef.forward_ref iter.start iter.end=ok (true,iter.start,rest.start,rest.end) := by
  obtain ⟨rest,next,inc,ending⟩ := NCJ_ForwardRange.active iter more
  have bound : iter.start.val+(1#usize).val  <  2^UScalarTy.Usize.numBits := by scalar_tac
  have add := NDL_FieldAssociation.checked_add iter.start 1#usize bound
  have hs : Usize.wrapping_add iter.start 1#usize=rest.start := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq,UScalar.size_def,Nat.mod_eq_of_lt bound,inc]
    rfl
  exact ⟨rest,next,by simp [NDL_IterRef.forward_ref,show iter.start < iter.end from more,add,hs,ending]⟩

theorem forward_done (iter : NCJ_ForwardRange.Range) (stop : iter.end.val ≤ iter.start.val) :
    NCJ_ForwardRange.next iter=ok (none,iter) ∧
    NDL_IterRef.forward_ref iter.start iter.end=ok (false,0#usize,iter.start,iter.end) := by
  exact ⟨NCJ_ForwardRange.done iter stop,by simp [NDL_IterRef.forward_ref,show ¬iter.start < iter.end by exact Nat.not_lt.mpr stop]⟩

theorem quarter : NDL_IterRef.quarter_ref=ok FIo_Native.weights.QUARTER := by
  simp [NDL_IterRef.quarter_ref,FIo_Native.weights.QUARTER]
theorem perm (s : Usize) : NDL_IterRef.perm_ref s=Array.index_usize FIo_Native.weights.PERM s := by
  simp [NDL_IterRef.perm_ref,FIo_Native.weights.PERM]
theorem finish (a : Array U32 8#usize) : NDL_IterRef.finish_ref a=ok a := rfl
#print axioms forward_active
#print axioms forward_done
#print axioms quarter
#print axioms perm
#print axioms finish
end NDL_IterAssociation
