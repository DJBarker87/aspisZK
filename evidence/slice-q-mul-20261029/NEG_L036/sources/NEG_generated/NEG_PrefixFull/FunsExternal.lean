import NEG_PrefixFull.Types
import Port4C_NativePrefix
import AspisR1Qm31ArithmeticProbe.Funs
namespace NEG_PrefixFull
open Aeneas Aeneas.Std Result
abbrev aspis_core.field.M31.mul := AspisR1Qm31ArithmeticProbe.field.M31.mul
def aspis_core.field.M31.ONE : Result U32 := ok 1#u32
#print axioms aspis_core.field.M31.ONE
end NEG_PrefixFull
