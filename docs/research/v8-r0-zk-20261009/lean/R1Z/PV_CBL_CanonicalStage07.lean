import R1Z.PV_CBL_CanonicalStage08
import R1Z.PV_CBL_BlockStage07
import R1Z.PV_CBL_CanonicalBoundary
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_CanonicalStage07
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
def value (original current : State) (w0 w1 w2 w3 : A4) : State :=
  let w := PV_CBL_CanonicalBoundary.schedule w0 w1 w2 w3
  let current := PV_CBL_CanonicalBoundary.four current w PV_CBL_FallbackConstantMatrix.q7
  PV_CBL_CanonicalStage08.value original current w1 w2 w3 w
theorem source_value (original current : State) (w0 w1 w2 w3 : A4) :
    PV_CBL_BlockStage07.value original current w0 w1 w2 w3 = value original current w0 w1 w2 w3 := by
  simp only [PV_CBL_BlockStage07.value,value,PV_CBL_CanonicalBoundary.four_eq,
    PV_CBL_CanonicalBoundary.schedule_eq,PV_CBL_CanonicalStage08.source_value]
#print axioms value
#print axioms source_value
end R1Z.PV_CBL_CanonicalStage07
