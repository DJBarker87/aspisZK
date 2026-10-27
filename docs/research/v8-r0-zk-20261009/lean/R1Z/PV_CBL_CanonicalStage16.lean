import R1Z.PV_CBL_BlockStage16
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_CanonicalStage16
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
def value (original current : State) (_w0 _w1 _w2 _w3 : A4) : State :=
  PV_CBL_FallbackFeedForward.value original current
theorem source_value (original current : State) (w0 w1 w2 w3 : A4) :
    PV_CBL_BlockStage16.value original current w0 w1 w2 w3 = value original current w0 w1 w2 w3 := rfl
#print axioms value
#print axioms source_value
end R1Z.PV_CBL_CanonicalStage16
