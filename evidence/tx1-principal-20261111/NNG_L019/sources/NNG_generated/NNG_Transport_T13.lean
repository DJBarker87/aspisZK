import NNG_Transport_T12
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT13 : NNG_verify_finish.r1_wire.Error → AspisR1PublicPreparation.r1_wire.Error
 | .Allocation => .Allocation
 | .RowOrder x0 x1 => .RowOrder (x0) (x1)
 | .InvalidRow => .InvalidRow
 | .Tag x0 => .Tag (x0)
 | .Length x0 => .Length (x0)
 | .NonCanonical x0 x1 => .NonCanonical (x0) (x1)
 | .Boundary x0 => .Boundary (x0)
 | .Terminal => .Terminal
 | .EqualCirclePoints => .EqualCirclePoints
 | .TrailingBytes => .TrailingBytes
 | .Public => .Public
def fromT13 : AspisR1PublicPreparation.r1_wire.Error → NNG_verify_finish.r1_wire.Error
 | .Allocation => .Allocation
 | .RowOrder x0 x1 => .RowOrder (x0) (x1)
 | .InvalidRow => .InvalidRow
 | .Tag x0 => .Tag (x0)
 | .Length x0 => .Length (x0)
 | .NonCanonical x0 x1 => .NonCanonical (x0) (x1)
 | .Boundary x0 => .Boundary (x0)
 | .Terminal => .Terminal
 | .EqualCirclePoints => .EqualCirclePoints
 | .TrailingBytes => .TrailingBytes
 | .Public => .Public
@[simp] theorem toT13_inverse (x : NNG_verify_finish.r1_wire.Error) : fromT13 (toT13 x)=x := by
 cases x <;> simp [toT13,fromT13]
#print axioms toT13_inverse
@[simp] theorem fromT13_inverse (x : AspisR1PublicPreparation.r1_wire.Error) : toT13 (fromT13 x)=x := by
 cases x <;> simp [fromT13,toT13]
#print axioms fromT13_inverse
end AspisR1.NNG_Transport
