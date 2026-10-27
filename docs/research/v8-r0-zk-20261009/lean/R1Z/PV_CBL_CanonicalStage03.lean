import R1Z.PV_CBL_CanonicalStage04
import R1Z.PV_CBL_BlockStage03
import R1Z.PV_CBL_CanonicalBoundary
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_CanonicalStage03
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
def value (original current : State) (w0 w1 w2 w3 : A4) : State :=
  let current := PV_CBL_CanonicalBoundary.four current w3 PV_CBL_FallbackConstantMatrix.q3
  PV_CBL_CanonicalStage04.value original current w0 w1 w2 w3
theorem source_value (original current : State) (w0 w1 w2 w3 : A4) :
    PV_CBL_BlockStage03.value original current w0 w1 w2 w3 = value original current w0 w1 w2 w3 := by
  simp only [PV_CBL_BlockStage03.value,value,PV_CBL_CanonicalBoundary.four_eq,
    PV_CBL_CanonicalBoundary.schedule_eq,PV_CBL_CanonicalStage04.source_value]
#print axioms value
#print axioms source_value
end R1Z.PV_CBL_CanonicalStage03
