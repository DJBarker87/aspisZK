import NDF_ChunkCheck
import ExtractedPrefixRecordAgreement
set_option autoImplicit false
noncomputable section
namespace NDF_ValidatorStep
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1RecordParser AspisR1RecordParser.field
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8)

theorem split_step (row : U8) (iter : Iter) (chunk : Slice U8) (chunks : List (Slice U8))
    (count : Usize) (head : iter.iter.chunks=chunk::chunks) (advance : iter.count+1#usize=ok count) :
    r1_wire.validate_record_fields_loop.body row iter =
      (do let status ← NDF_ChunkCheck.check row iter.count chunk
          match status with
          | .Ok _ => ok (cont ({iter:={chunks:=chunks,remainder:=iter.iter.remainder},count:=count} : Iter))
          | .Err error => ok (done (.Err error))) := by
  simp only [r1_wire.validate_record_fields_loop.body,
    core.iter.adapters.enumerate.IteratorEnumerate.next,core.slice.iter.IteratorChunksExact.next,
    head,advance,bind_tc_ok,uncurry]
  unfold NDF_ChunkCheck.check
  generalize decodeCall : wide_exact.WideExact.from_le_bytes chunk = decoded
  cases decoded with
  | fail e => rfl
  | div => rfl
  | ok decoded =>
    cases decoded with
    | none => rfl
    | some w =>
      simp only [AspisR1RecordParser.core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        wide_exact.WideExact.impl.c1,bind_tc_ok]
      generalize compareCall : core.cmp.PartialEq.ne.trait_default QM31.Insts.CoreCmpPartialEqQM31 w.c1 QM31.ZERO = compared
      cases compared with
      | fail e => rfl
      | div => rfl
      | ok b => cases b <;> rfl

theorem value (row : U8) (iter : Iter) (arr : Array U8 32#usize) (chunks : List (Slice U8))
    (count : Usize) (head : iter.iter.chunks=Array.to_slice arr::chunks) (advance : iter.count+1#usize=ok count) :
    r1_wire.validate_record_fields_loop.body row iter =
      if LPl_Kit_Bytes.validChunk 8 true arr.val then
        ok (cont ({iter:={chunks:=chunks,remainder:=iter.iter.remainder},count:=count} : Iter))
      else ok (done (.Err (.NonCanonical row iter.count))) := by
  rw [split_step row iter (Array.to_slice arr) chunks count head advance,NDF_ChunkCheck.value]
  cases LPl_Kit_Bytes.validChunk 8 true arr.val <;> rfl

#print axioms split_step
#print axioms value
end NDF_ValidatorStep
