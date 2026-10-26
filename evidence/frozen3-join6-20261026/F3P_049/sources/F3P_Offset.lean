import F3P_TraceArithmetic
set_option autoImplicit false
namespace AspisR1.F3P_Offset
open Aeneas Aeneas.Std Result

theorem value (offset bytes : Usize)
    (h : lift (Usize.checked_mul offset 32#usize)=ok (some bytes)) :
    bytes.val=32*offset.val := by
  unfold lift Usize.checked_mul core.num.checked_mul_UScalar at h
  simp only [Result.ok.injEq] at h
  split at h
  · have same := Option.some.inj h
    exact (congrArg UScalar.val same).symm.trans (Nat.mul_comm _ _)
  · cases h


#print axioms value
end AspisR1.F3P_Offset
