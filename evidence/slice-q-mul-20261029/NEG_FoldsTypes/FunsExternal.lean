import NEG_FoldsTypes.Types
namespace NEG_FoldsTypes
open Aeneas Aeneas.Std Result
abbrev aspis_core.field.wide_exact.WideExact.add := AspisR1CurrentWide.field.wide_exact.WideExact.add
abbrev aspis_core.field.wide_exact.WideExact.sub := AspisR1CurrentWide.field.wide_exact.WideExact.sub
abbrev aspis_core.field.wide_exact.WideExact.mul := AspisR1CurrentWide.field.wide_exact.WideExact.mul
abbrev aspis_core.field.wide_exact.WideExact.mul_m31 := AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31
abbrev aspis_core.field.M31.mul := AspisR1CurrentWide.field.M31.mul
def aspis_core.field.M31.ONE : Result U32 := ok 1#u32
#print axioms aspis_core.field.M31.ONE
end NEG_FoldsTypes
