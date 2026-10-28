import R1Z.ProverRwDictionaryDigest
import AspisR1Qm31ArithmeticProbe.Funs

/-! Exact retained extracted M31 arithmetic, including every machine error.
No canonicality or successful-result premise is supplied to these equations. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryBaseField
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwDictionaryDigest.selected {ops with
    op57 := AspisR1Qm31ArithmeticProbe.field.M31.mul
    op58 := AspisR1Qm31ArithmeticProbe.field.M31.double
    op73 := AspisR1Qm31ArithmeticProbe.field.M31.add
    op74 := AspisR1Qm31ArithmeticProbe.field.M31.sub}

theorem entry57 (ops : ExternalFuns) (a b : U32) :
    (selected ops).op57 a b = AspisR1Qm31ArithmeticProbe.field.M31.mul a b := rfl

theorem entry58 (ops : ExternalFuns) (a : U32) :
    (selected ops).op58 a = AspisR1Qm31ArithmeticProbe.field.M31.double a := rfl

theorem entry73 (ops : ExternalFuns) (a b : U32) :
    (selected ops).op73 a b = AspisR1Qm31ArithmeticProbe.field.M31.add a b := rfl

theorem entry74 (ops : ExternalFuns) (a b : U32) :
    (selected ops).op74 a b = AspisR1Qm31ArithmeticProbe.field.M31.sub a b := rfl

#print axioms entry57
#print axioms entry58
#print axioms entry73
#print axioms entry74
end R1Z.ProverRwDictionaryBaseField
