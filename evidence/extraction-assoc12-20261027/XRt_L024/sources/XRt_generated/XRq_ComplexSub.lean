import XRq_ScalarSub
import XRp_PowersComplex
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRp_PowersComplex
set_option autoImplicit false
noncomputable section
namespace XRq_ComplexSub

theorem sub (a b : EC) (ha : Canonical a) (hb : Canonical b) :
 mapR toC (XRn_Join_Field.field.CM31.sub a b) =
 AspisR1Qm31ArithmeticProbe.field.CM31.sub (toC a) (toC b) := by
 unfold XRn_Join_Field.field.CM31.sub AspisR1Qm31ArithmeticProbe.field.CM31.sub
 rw [XRq_ScalarSub.sub a.a b.a ha.1 hb.1,XRq_ScalarSub.sub a.b b.b ha.2 hb.2]
 simp only [mapR_bind]
 rfl
#print axioms sub
end XRq_ComplexSub
