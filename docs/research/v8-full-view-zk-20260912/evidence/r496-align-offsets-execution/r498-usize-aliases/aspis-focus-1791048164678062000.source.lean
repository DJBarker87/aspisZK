import Aeneas.Std

set_option autoImplicit false

/-! Names used by the current extractor for the existing supplied unsigned
scalar operations. These definitions add no behavior or assumptions. -/
namespace Aeneas.Std.Usize

def div (n d : Usize) : Result Usize := UScalar.div n d
def rem (n d : Usize) : Result Usize := UScalar.rem n d

theorem div_eq (n d : Usize) : div n d = UScalar.div n d := rfl
theorem rem_eq (n d : Usize) : rem n d = UScalar.rem n d := rfl

#print axioms div
#print axioms rem
#print axioms div_eq
#print axioms rem_eq

end Aeneas.Std.Usize
