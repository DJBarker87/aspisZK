import Aeneas.Std
import AspisR249R110Raw
import AspisR156FullFreeze.FunsCore
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR249R110Raw AspisR156FullFreeze
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR278PrivateInverseRaw

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::ZERO]
    Source: '../r110_norm.rs', lines 7:4-7:28 -/
@[global_simps, irreducible]
def circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO
  : circle_norm.joined_inverse.line_norm.r110_norm.B :=
  0#u32

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::neg]:
    Source: '../r110_norm.rs', lines 12:21-12:61 -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.neg
  (self : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.B
  := do
  circle_norm.joined_inverse.line_norm.r110_norm.B.sub
    circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO self

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::inv]:
    Source: '../r110_norm.rs', lines 20:4-20:49 -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.inv
  (self : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.B
  := do
  let m ← aspis_core.field.M31.inv self
  ok m

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.neg
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.inv

end AspisR278PrivateInverseRaw
