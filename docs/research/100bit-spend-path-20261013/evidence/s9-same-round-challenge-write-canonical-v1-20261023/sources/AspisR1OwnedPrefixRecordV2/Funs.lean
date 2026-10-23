import Aeneas
import AspisR1ActualSemanticRoundCutV1.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1ActualSemanticRoundCutV1
/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::Prefix<'a>}::record]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 338:4-343:5
    Visibility: public -/
def r1_wire.Prefix.record
  (self : r1_wire.Prefix) (row : Std.U8) :
  Result (core.result.Result (Slice Std.U8) r1_wire.Error)
  := do
  if row >= 27#u8
  then ok (core.result.Result.Err r1_wire.Error.InvalidRow)
  else
    let i ← lift (UScalar.cast .Usize row)
    let s ← Array.index_usize self.records i
    ok (core.result.Result.Ok s)

/-- [aspis_r1_cost_probe::r1_wire::{aspis_r1_cost_probe::r1_wire::Prefix<'a>}::validated_record]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 348:4-353:5 -/
def r1_wire.Prefix.validated_record
  (self : r1_wire.Prefix) (row : Std.U8) :
  Result (core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.record self row
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok { row, framed := val })
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_wire.ValidatedRecord (core.convert.FromSame r1_wire.Error) residual

end AspisR1ActualSemanticRoundCutV1
