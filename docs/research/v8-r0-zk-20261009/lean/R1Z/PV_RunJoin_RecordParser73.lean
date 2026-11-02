import R1Z.PV_RunJoin_FourReader73
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RecordParser73
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def parse
  (row : Std.U8) (record1 : Slice Std.U8) :
  Result (core.result.Result (Slice Std.U8) r1_wire.Error)
  := do
  let o ← r1_wire.row_shape row
  let r ← core.option.Option.ok_or o r1_wire.Error.InvalidRow
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (tag, size) := val
    let i := Slice.len record1
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add 5#usize size)
    if i != i1
    then ok (core.result.Result.Err (r1_wire.Error.Length row))
    else
      let i2 ← Slice.index_usize record1 0#usize
      if i2 != tag
      then ok (core.result.Result.Err (r1_wire.Error.Tag row))
      else
        let i7 ← PV_RunJoin_FourReader73.read record1 1#usize 2#usize 3#usize 4#usize
        let i8 ← Aeneas.Std.lift (UScalar.cast .Usize i7)
        if i8 != size
        then ok (core.result.Result.Err (r1_wire.Error.Length row))
        else
          let payload ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) record1
              { start := 5#usize }
          if row >= 14#u8
          then
            let r1 ← host_wire.validate_record_fields row payload
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (core.result.Result.Ok payload)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (Slice Std.U8) (core.convert.FromSame r1_wire.Error) residual
          else ok (core.result.Result.Ok payload)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Slice Std.U8) (core.convert.FromSame r1_wire.Error) residual


theorem source (row : U8) (s : Slice U8) :
    host_wire.parse_record row s=parse row s := by
  simp only [host_wire.parse_record,parse,PV_RunJoin_FourReader73.read,bind_assoc_eq,bind_tc_ok,lift]
  rfl

attribute [irreducible] parse
#print axioms parse
#print axioms source
end R1Z.PV_RunJoin_RecordParser73
