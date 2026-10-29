import R1Z.PV_RDB2E_FallbackBlockLinks

section
-- Unchanged source component R1Z.PV_CBL_FallbackBlockSwap
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackBlockSwap
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a b c d : U32) :
    PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap (pack a b c d) =
      ok (pack c d a b) := by
  simp only [PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap,
    index0,index1,index2,index3,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackBlockSwap

end
