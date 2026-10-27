import XRp_PowersScalar
import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_PowersComplex
open XRo_Join_Carriers
abbrev EC := XRn_Join_Field.field.CM31
abbrev TC := AspisR1Qm31ArithmeticProbe.field.CM31
def toC (a : EC) : TC := ⟨a.a,a.b⟩
def Canonical (a : EC) := a.a.val < 2147483647 ∧ a.b.val < 2147483647

theorem add (a b : EC) (ha : Canonical a) (hb : Canonical b) :
    mapR toC (XRn_Join_Field.field.CM31.add a b) =
      AspisR1Qm31ArithmeticProbe.field.CM31.add (toC a) (toC b) := by
  unfold XRn_Join_Field.field.CM31.add AspisR1Qm31ArithmeticProbe.field.CM31.add
  rw [XRp_PowersScalar.add a.a b.a ha.1 hb.1,XRp_PowersScalar.add a.b b.b ha.2 hb.2]
  simp only [mapR_bind]
  rfl

#print axioms add
end XRp_PowersComplex
