import AspisR1DecodeKFullSuccessIndexedParser
set_option autoImplicit false
namespace AspisR1.F3P_TraceArithmetic
open Aeneas Aeneas.Std Result

theorem checked_add (x y z : Usize) (h : x+y=ok z) : z.val=x.val+y.val := by
  change UScalar.tryMk .Usize (x.val+y.val)=ok z at h
  unfold UScalar.tryMk UScalar.tryMkOpt at h
  split at h
  · exact congrArg UScalar.val (Result.ok.inj h).symm
  · cases h


theorem checked_mul (x y z : Usize) (h : x*y=ok z) : z.val=x.val*y.val := by
  change UScalar.tryMk .Usize (x.val*y.val)=ok z at h
  unfold UScalar.tryMk UScalar.tryMkOpt at h
  split at h
  · exact congrArg UScalar.val (Result.ok.inj h).symm
  · cases h


#print axioms checked_add
#print axioms checked_mul
end AspisR1.F3P_TraceArithmetic
