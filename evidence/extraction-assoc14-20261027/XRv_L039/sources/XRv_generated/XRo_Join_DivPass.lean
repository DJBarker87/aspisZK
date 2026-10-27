import XRo_Join_OrdinaryDigits
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRo_Join_DivPass

theorem pass (rank : Array U32 8#usize) :
 XRn_Join_Release.sampler.qm31_div_pass rank =
 AspisR1Post25Sampler.sampler.qm31_div_pass rank := by
 have h := XRo_Join_OrdinaryDigits.div_loop rank 0#u64 8#usize
 exact congrArg (fun r : Result (Array U32 8#usize × U64) => do
   let (a,b) ← r
   let b ← lift (UScalar.cast .U32 b)
   ok (a,b)) h

#print axioms pass
end XRo_Join_DivPass
