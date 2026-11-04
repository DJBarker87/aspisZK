import NGD_QDecodeLaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_DecodeGuards
open AspisR1DecodeKFullV10
abbrev Record := r1_wire.ValidatedRecord
abbrev Q := aspis_core.field.QM31

theorem invalid_row (N off : Usize) (r : Record) (bad : r.row < 14#u8) :
    r1_wire.ValidatedRecord.decode_k N r off = ok (.Err .InvalidRow) := by
  simp [r1_wire.ValidatedRecord.decode_k,bad]

theorem offset_overflow (N off : Usize) (r : Record) (row : ¬r.row < 14#u8)
    (overflow : Usize.checked_mul off 32#usize = none) :
    r1_wire.ValidatedRecord.decode_k N r off = ok (.Err (.Length r.row)) := by
  simp [r1_wire.ValidatedRecord.decode_k,row,overflow,lift,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem length_overflow (N off start : Usize) (r : Record) (row : ¬r.row < 14#u8)
    (offset : Usize.checked_mul off 32#usize = some start)
    (overflow : Usize.checked_mul N 32#usize = none) :
    r1_wire.ValidatedRecord.decode_k N r off = ok (.Err (.Length r.row)) := by
  simp [r1_wire.ValidatedRecord.decode_k,row,offset,overflow,lift,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem end_overflow (N off start size : Usize) (r : Record) (row : ¬r.row < 14#u8)
    (offset : Usize.checked_mul off 32#usize = some start)
    (length : Usize.checked_mul N 32#usize = some size)
    (overflow : Usize.checked_add start size = none) :
    r1_wire.ValidatedRecord.decode_k N r off = ok (.Err (.Length r.row)) := by
  simp [r1_wire.ValidatedRecord.decode_k,row,offset,length,overflow,lift,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem range_error (N off start size finish : Usize) (r : Record) (payload : Slice U8)
    (row : ¬r.row < 14#u8) (offset : Usize.checked_mul off 32#usize = some start)
    (length : Usize.checked_mul N 32#usize = some size)
    (addition : Usize.checked_add start size = some finish)
    (original : r1_wire.ValidatedRecord.payload r = ok payload)
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      payload {start, «end»:=finish} = ok none) :
    r1_wire.ValidatedRecord.decode_k N r off = ok (.Err (.Length r.row)) := by
  simp [r1_wire.ValidatedRecord.decode_k,row,offset,length,addition,original,get,lift,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
#print axioms invalid_row
#print axioms offset_overflow
#print axioms length_overflow
#print axioms end_overflow
#print axioms range_error
end NGD_DecodeGuards
