import NNG_InstallBase
set_option autoImplicit false
namespace AspisR1.NNG_TransportCoreError
open Aeneas Aeneas.Std NNG_verify_finish
abbrev Old := AspisR1PublicPreparation.aspis_core.state_only_prefix.r0.Error
abbrev Fresh := aspis_core.state_only_prefix.r0.Error
def raise : Old → Fresh
 | .Allocation => .Allocation
 | .RowOrder a b => .RowOrder a b
 | .InvalidRow => .InvalidRow
 | .Tag a => .Tag a
 | .Length a => .Length a
 | .NonCanonical a b => .NonCanonical a b
 | .Boundary a => .Boundary a
 | .Terminal => .Terminal
 | .EqualCirclePoints => .EqualCirclePoints
 | .TrailingBytes => .TrailingBytes
 | .Public => .Public
def lower : Fresh → Old
 | .Allocation => .Allocation
 | .RowOrder a b => .RowOrder a b
 | .InvalidRow => .InvalidRow
 | .Tag a => .Tag a
 | .Length a => .Length a
 | .NonCanonical a b => .NonCanonical a b
 | .Boundary a => .Boundary a
 | .Terminal => .Terminal
 | .EqualCirclePoints => .EqualCirclePoints
 | .TrailingBytes => .TrailingBytes
 | .Public => .Public
theorem raise_inverse (x : Old) : lower (raise x)=x := by cases x <;> rfl
theorem lower_inverse (x : Fresh) : raise (lower x)=x := by cases x <;> rfl
#print axioms raise_inverse
#print axioms lower_inverse
end AspisR1.NNG_TransportCoreError
