import NNG_Filled087
set_option autoImplicit false
namespace AspisR1.NNG_FilledReturned087
open Aeneas Aeneas.Std Result NMP_prepare

theorem length (env : RSL.Env) (n : Usize) (logical : alloc.vec.Vec U8)
 (returned : NNG_Filled087.call env core.marker.CopyU8 n 0#u8=.ok (.Ok logical)) : logical.val.length=n.val := by
 unfold NNG_Filled087.call at returned
 cases h : env.reservation with
 | false=>simp only [h,Bool.false_eq_true,if_false] at returned;cases returned
 | true=>
   simp only [h,if_true] at returned
   have same := core.result.Result.Ok.inj (Result.ok.inj returned)
   have len := congrArg (fun v : alloc.vec.Vec U8=>v.val.length) same
   rw [List.length_replicate] at len
   exact len.symm
#print axioms length
end AspisR1.NNG_FilledReturned087
