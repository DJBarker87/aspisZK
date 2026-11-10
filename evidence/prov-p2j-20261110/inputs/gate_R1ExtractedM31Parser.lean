import Aeneas.Std.Primitives
import Aeneas.Std.Scalar.CoreConvertNum
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- Generated M31 parser declarations retained from the pinned M31-only Aeneas
   translation. Declaration bodies below are checked against its source files. -/
namespace AspisR1M31Parser

/-- [aspis_core::field::M31]
    Source: 'field.rs', lines 23:0-23:24
    Visibility: public -/
@[reducible]
def field.M31 := Std.U32


/-- [aspis_core::field::P]
    Source: 'field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::M31}::from_le_bytes]:
    Source: 'field.rs', lines 239:4-246:5
    Visibility: public -/
def field.M31.from_le_bytes
  (bytes : Array Std.U8 4#usize) : Result (Option field.M31) := do
  let v ← lift (core.num.U32.from_le_bytes bytes)
  if v >= field.P
  then ok none
  else ok (some v)

/-- [aspis_core::parse_m31_probe]:
    Source: 'lib.rs', lines 7:0-9:1
    Visibility: public -/
def parse_m31_probe
  (base : Array Std.U8 4#usize) : Result (Option field.M31) := do
  field.M31.from_le_bytes base

#print axioms field.P
#print axioms field.M31.from_le_bytes
#print axioms parse_m31_probe

end AspisR1M31Parser
