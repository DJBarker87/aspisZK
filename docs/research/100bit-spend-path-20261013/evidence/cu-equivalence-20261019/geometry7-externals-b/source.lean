import AspisR1GeometryCandidate7.Types
import AspisR1WideArithmetic.Funs
import AspisR1ViewParseProbe.CallerStdModels
set_option autoImplicit false
namespace AspisR1GeometryCandidate7
open Aeneas Aeneas.Std Result
abbrev field.M31.mul := AspisR1WideArithmetic.field.M31.mul
abbrev field.M31.double := AspisR1WideArithmetic.field.M31.double
abbrev field.M31.sub := AspisR1WideArithmetic.field.M31.sub
/-- Coordinate-only transport into the existing exact source CM31 multiplication. -/
def field.CM31.mul (x y : field.CM31) : Result field.CM31 := do
  let z ← AspisR1WideArithmetic.field.CM31.mul ⟨x.a,x.b⟩ ⟨y.a,y.b⟩
  .ok ⟨z.a,z.b⟩
abbrev core.result.Result.map_err := @AspisR1ViewParseProbe.core.result.Result.map_err
abbrev core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any :=
  @AspisR1ViewParseProbe.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
#print axioms field.M31.mul
#print axioms field.M31.double
#print axioms field.M31.sub
#print axioms field.CM31.mul
#print axioms core.result.Result.map_err
#print axioms core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
end AspisR1GeometryCandidate7
