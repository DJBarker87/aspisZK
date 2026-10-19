import AspisR1RhoBasis.Types
import AspisR1Qm31ArithmeticProbe.Funs

/-! Bind unchanged base-field methods to the existing checked source bodies.
The generated external template is not imported. -/
namespace AspisR1RhoBasis
abbrev field.M31.mul := AspisR1Qm31ArithmeticProbe.field.M31.mul
abbrev field.M31.add := AspisR1Qm31ArithmeticProbe.field.M31.add
abbrev field.M31.sub := AspisR1Qm31ArithmeticProbe.field.M31.sub
end AspisR1RhoBasis
