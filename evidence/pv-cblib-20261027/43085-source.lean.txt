import R1Z.PV_CBL_FallbackCanonicalT1
import R1Z.PV_CBL_FallbackCanonicalT2
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackCanonicalStep
open PV_CBL_FallbackScalar
set_option autoImplicit false
/-- Conventional SHA scalar state transition over wrapping 32-bit words. -/
def step (s : State) (w : U32) : State :=
  let x := PV_CBL_FallbackCanonicalT1.value s.e s.f s.g s.h w
  let y := PV_CBL_FallbackCanonicalT2.value s.a s.b s.c
  ⟨U32.wrapping_add x y,s.a,s.b,s.c,U32.wrapping_add x s.d,s.e,s.f,s.g⟩
theorem source (s : State) (w : U32) : PV_CBL_FallbackScalar.step s w = step s w := by
  simp only [PV_CBL_FallbackScalar.step,step,
    PV_CBL_FallbackCanonicalT1.source,PV_CBL_FallbackCanonicalT2.source]
#print axioms step
#print axioms source
end R1Z.PV_CBL_FallbackCanonicalStep
