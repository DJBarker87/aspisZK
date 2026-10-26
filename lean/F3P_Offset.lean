import F3P_TraceArithmetic
set_option autoImplicit false
namespace AspisR1.F3P_Offset
open Aeneas Aeneas.Std Result

theorem value (offset bytes : Usize)
    (h : lift (Usize.checked_mul offset 32#usize)=ok (some bytes)) :
    bytes.val=32*offset.val := by
  unfold lift Usize.checked_mul core.num.checked_mul_UScalar at h
  simp only [Result.ok.injEq] at h
  cases hm : UScalar.mul offset 32#usize with
  | fail e => simp only [hm,Option.ofResult] at h;cases h
  | div => simp only [hm,Option.ofResult] at h;cases h
  | ok value =>
    simp only [hm,Option.ofResult,Option.some.injEq] at h
    subst value
    have numeric := F3P_TraceArithmetic.checked_mul offset 32#usize bytes hm
    change bytes.val=offset.val*32 at numeric
    exact numeric.trans (Nat.mul_comm _ _)


#print axioms value
end AspisR1.F3P_Offset
