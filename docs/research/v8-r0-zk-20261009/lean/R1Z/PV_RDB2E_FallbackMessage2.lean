import R1Z.PV_RDB2E_FallbackLanes

section
-- Unchanged source component R1Z.PV_CBL_FallbackMessage2
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackMessage2
open PV_CBL_FallbackArray4 PV_CBL_FallbackSmallSigma
set_option autoImplicit false
theorem shape (x3 x2 x1 x0 w15 w14 u v : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg2
      (pack x3 x2 x1 x0) (pack w15 w14 u v) =
      let w16 := U32.wrapping_add x0 (small1 w14)
      let w17 := U32.wrapping_add x1 (small1 w15)
      let w18 := U32.wrapping_add x2 (small1 w16)
      let w19 := U32.wrapping_add x3 (small1 w17)
      ok (pack w19 w18 w17 w16) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg2,
    index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackMessage2

end
