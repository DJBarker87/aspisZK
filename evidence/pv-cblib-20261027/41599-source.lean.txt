import R1Z.PV_CBL_BlockArrayEta
import R1Z.PV_CBL_FallbackFourShape
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockFourValue
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundsModel
set_option autoImplicit false
def value (s : State) (w k : A4) : State :=
  PV_CBL_FallbackFourModel.run4 s w.val[3]! w.val[2]! w.val[1]! w.val[0]!
    k.val[3]! k.val[2]! k.val[1]! k.val[0]!
theorem source (s : State) (w k : A4) :
    PV_CBL_FallbackFourModel.source (pack s.a s.b s.e s.f) (pack s.c s.d s.g s.h) w k =
      ok (packed (value s w k)) := by
  conv_lhs => rw [← PV_CBL_BlockArrayEta.eta w, ← PV_CBL_BlockArrayEta.eta k]
  exact PV_CBL_FallbackFourShape.shape s _ _ _ _ _ _ _ _
#print axioms value
#print axioms source
end R1Z.PV_CBL_BlockFourValue
