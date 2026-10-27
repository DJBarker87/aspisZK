import RPt_FIo_ReduceValues
set_option autoImplicit false
namespace AspisR1.FJm_BaseCast
open Aeneas Aeneas.Std

theorem value (x : U32) : (x.val : ZMod 2147483647)=AspisR1CurrentWide.Proof.decodeM x := rfl
#print axioms value
end AspisR1.FJm_BaseCast
