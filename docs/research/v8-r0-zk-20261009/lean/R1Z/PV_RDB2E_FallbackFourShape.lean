import R1Z.PV_RDB2E_FallbackFourModel

section
-- Unchanged source component R1Z.PV_CBL_FallbackFourShape
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackFourShape
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
open PV_CBL_FallbackFourModel PV_CBL_FallbackStateShift
set_option autoImplicit false
theorem shape (s : State) (w0 w1 w2 w3 k0 k1 k2 k3 : U32) :
    source (pack s.a s.b s.e s.f) (pack s.c s.d s.g s.h)
      (pack w3 w2 w1 w0) (pack k3 k2 k1 k0) =
    ok (packed (run4 s w0 w1 w2 w3 k0 k1 k2 k3)) := by
  let t0 := U32.wrapping_add w0 k0
  let t1 := U32.wrapping_add w1 k1
  let t2 := U32.wrapping_add w2 k2
  let t3 := U32.wrapping_add w3 k3
  have h1 := PV_CBL_FallbackRoundShape.shape s t0 t1 t3 t2
  have h2 := PV_CBL_FallbackRoundShape.shape (step (step s t0) t1) t2 t3 t1 t0
  simp only [two_c,two_d,two_g,two_h] at h2
  simp only [source,PV_CBL_FallbackBlockLinks.add_eq,PV_CBL_FallbackLaneAdd.shape,
    PV_CBL_FallbackBlockLinks.round_eq,h1,h2,PV_CBL_FallbackBlockSwap.shape,bind_tc_ok]
  simp only [run4,run_four,packed,two_c,two_d,two_g,two_h] <;> rfl
#print axioms shape
end R1Z.PV_CBL_FallbackFourShape

end
