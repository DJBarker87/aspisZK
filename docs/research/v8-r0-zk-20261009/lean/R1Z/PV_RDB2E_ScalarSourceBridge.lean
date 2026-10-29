import R1Z.PV_RDB2E_ScalarTransport
import R1Z.PV_RDB2E_FallbackScalar
namespace R1Z.PV_RDB2E_ScalarSourceBridge
open Aeneas Aeneas.Std PV_RDB2E_ScalarTransport
set_option autoImplicit false
abbrev S := PV_RDB2E_ShaScalar.S
abbrev W := PV_RDB2E_ShaScalar.W

def encode (s : S) : PV_CBL_FallbackScalar.State :=
  ⟨toWord s.a,toWord s.b,toWord s.c,toWord s.d,toWord s.e,toWord s.f,toWord s.g,toWord s.h⟩

theorem big0 (x : W) :
    PV_CBL_FallbackScalar.big0 (toWord x)=toWord (PV_RDB2E_ShaScalar.big0 x) := rfl

theorem big1 (x : W) :
    PV_CBL_FallbackScalar.big1 (toWord x)=toWord (PV_RDB2E_ShaScalar.big1 x) := rfl

theorem round (s : S) (wk : W) :
    PV_CBL_FallbackScalar.step (encode s) (toWord wk)=encode (PV_RDB2E_ShaScalar.round s wk) := rfl

/-- Only the explicit literal shift-count port is proved here. This does not
replace the native compiler/intrinsic adequacy boundary with an assumption. -/
theorem shift_literal_port (x : W) :
    x >>> Int.toNat (10 : Int) = x >>> (10#u32).val := rfl

#print axioms big0
#print axioms big1
#print axioms round
#print axioms shift_literal_port
end R1Z.PV_RDB2E_ScalarSourceBridge
