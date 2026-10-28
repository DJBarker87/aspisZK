import PV_B3P_BytesTypes226
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
namespace PV_B3P_226
def aspis_core.field.M31.ZERO : aspis_core.field.M31 := 0#u32

/-- [pv_b3p6_reference::reference226::canonical]:
    Source: 'reference226.rs', lines 29:0-35:1 -/
def reference226.canonical (v : Std.U32) : Result (Option Std.U32) := do
  if v < 2147483647#u32
  then ok (some v)
  else ok none

/-- [pv_b3p6_reference::reference226::field_byte]:
    Source: 'reference226.rs', lines 37:0-43:1 -/
def reference226.field_byte
  (v : Std.U32) (j : Std.Usize) :
  Result (core.result.Result Std.U8 aspis_core.state_only_prefix.r0.Error)
  := do
  let o ← reference226.canonical v
  match o with
  | none =>
    ok (core.result.Result.Err aspis_core.state_only_prefix.r0.Error.Public)
  | some v1 =>
    let i ← lift (UScalar.cast .U32 j)
    let i1 ← lift (Std.U32.wrapping_mul 8#u32 i)
    let i2 ← lift (Std.U32.wrapping_shr v1 i1)
    let i3 ← lift (UScalar.cast .U8 i2)
    ok (core.result.Result.Ok i3)

/-- [pv_b3p6_reference::reference226::byte_at]:
    Source: 'reference226.rs', lines 45:0-91:1 -/

end PV_B3P_226
#print axioms PV_B3P_226.aspis_core.field.M31.ZERO
#print axioms PV_B3P_226.reference226.canonical
#print axioms PV_B3P_226.reference226.field_byte
