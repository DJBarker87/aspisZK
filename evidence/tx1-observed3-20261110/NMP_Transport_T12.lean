import NMP_Transport_T11
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT12 : NMP_prepare.r1_wire.Error → AspisR1PublicPreparation.r1_wire.Error
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
def fromT12 : AspisR1PublicPreparation.r1_wire.Error → NMP_prepare.r1_wire.Error
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
@[simp] theorem toT12_inverse (x : NMP_prepare.r1_wire.Error) : fromT12 (toT12 x)=x := by
 cases x <;> simp [toT12,fromT12]
#print axioms toT12_inverse
@[simp] theorem fromT12_inverse (x : AspisR1PublicPreparation.r1_wire.Error) : toT12 (fromT12 x)=x := by
 cases x <;> simp [fromT12,toT12]
#print axioms fromT12_inverse
end AspisR1.NMP_Transport
