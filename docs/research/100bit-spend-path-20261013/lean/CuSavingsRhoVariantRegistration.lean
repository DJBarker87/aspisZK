import AspisR1RhoPowerTail.Types

/-! Pin the generated enum-numbering reader before changing only its colliding
instance registration name. This module is a focused metadata audit, not a
constructor or optimization equivalence theorem. -/
namespace AspisR1.CuSavingsRhoVariantRegistration
open Aeneas Aeneas.Std AspisR1RhoPowerTail

theorem s1 : read_discriminant transport.Variant.S1 = 0#isize := rfl
theorem s2 : read_discriminant transport.Variant.S2 = 1#isize := rfl
theorem d : read_discriminant transport.Variant.D = 2#isize := rfl
#print AspisR1RhoPowerTail.transport.Variant.read_discriminant
#print AspisR1RhoPowerTail.transport.Variant.instDiscriminant
#print axioms s1
#print axioms s2
#print axioms d
end AspisR1.CuSavingsRhoVariantRegistration
