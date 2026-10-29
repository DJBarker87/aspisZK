import R1Z.PV_RDB2E_FallbackCanonical
import R1Z.PV_RDB2E_FallbackFourShape

section
-- Unchanged source component R1Z.PV_CBL_FallbackFourCanonical
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackFourCanonical
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
set_option autoImplicit false
theorem source (s : State) (w0 w1 w2 w3 k0 k1 k2 k3 : U32) :
    PV_CBL_FallbackFourModel.source (pack s.a s.b s.e s.f) (pack s.c s.d s.g s.h)
      (pack w3 w2 w1 w0) (pack k3 k2 k1 k0) =
      let r := PV_CBL_FallbackCanonicalStep.step
        (PV_CBL_FallbackCanonicalStep.step
        (PV_CBL_FallbackCanonicalStep.step
        (PV_CBL_FallbackCanonicalStep.step s (U32.wrapping_add w0 k0)) (U32.wrapping_add w1 k1))
        (U32.wrapping_add w2 k2)) (U32.wrapping_add w3 k3)
      ok (packed r) := by
  simpa only [PV_CBL_FallbackFourModel.run4,run_four,PV_CBL_FallbackCanonicalStep.source] using
    PV_CBL_FallbackFourShape.shape s w0 w1 w2 w3 k0 k1 k2 k3
#print axioms source
end R1Z.PV_CBL_FallbackFourCanonical

end
