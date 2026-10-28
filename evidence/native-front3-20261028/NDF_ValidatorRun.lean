import NDF_ValidatorStep
import ExtractedRecordValidator
set_option autoImplicit false
noncomputable section
namespace NDF_ValidatorRun
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1RecordParser
open NDF_ValidatorStep (Iter)

def scan (row : U8) (count : Usize) : List (Slice U8) → Result (core.result.Result Unit r1_wire.Error)
  | [] => ok (.Ok ())
  | chunk::chunks => do
    let next ← count+1#usize
    if LPl_Kit_Bytes.validChunk 8 true chunk.val then scan row next chunks
    else ok (.Err (.NonCanonical row count))

theorem source (row : U8) (iter : Iter)
    (widths : ∀ chunk∈iter.iter.chunks, chunk.val.length=32) :
    r1_wire.validate_record_fields_loop iter row=scan row iter.count iter.iter.chunks := by
  generalize equal : iter.iter.chunks=chunks at *
  induction chunks generalizing iter with
  | nil =>
    rw [AspisR1.ExtractedRecordValidator.loop_unroll]
    simp only [r1_wire.validate_record_fields_loop.body,
      core.iter.adapters.enumerate.IteratorEnumerate.next,core.slice.iter.IteratorChunksExact.next,
      equal,bind_tc_ok,scan,uncurry]
  | cons chunk chunks ih =>
    rw [AspisR1.ExtractedRecordValidator.loop_unroll]
    cases increment : iter.count+1#usize with
    | fail error =>
      simp only [r1_wire.validate_record_fields_loop.body,
        core.iter.adapters.enumerate.IteratorEnumerate.next,core.slice.iter.IteratorChunksExact.next,
        equal,increment,bind_tc_ok,bind_tc_fail,scan,uncurry]
    | div =>
      simp only [r1_wire.validate_record_fields_loop.body,
        core.iter.adapters.enumerate.IteratorEnumerate.next,core.slice.iter.IteratorChunksExact.next,
        equal,increment,bind_tc_ok,bind_tc_div,scan,uncurry]
    | ok count =>
      have width : chunk.val.length=32 := widths chunk (by simp [equal])
      let arr : Array U8 32#usize := ⟨chunk.val,by simpa using width⟩
      have same : Array.to_slice arr=chunk := by cases chunk; rfl
      have step := NDF_ValidatorStep.value row iter arr chunks count (by rw [same];exact equal) increment
      rw [step]
      simp only [equal,scan,increment,bind_tc_ok]
      by_cases valid : LPl_Kit_Bytes.validChunk 8 true chunk.val=true
      · have validArr : LPl_Kit_Bytes.validChunk 8 true arr.val=true := valid
        rw [if_pos validArr,bind_tc_ok,if_pos valid]
        apply ih
        · rfl
        · intro c member
          exact widths c (List.mem_cons_of_mem chunk member)
      · have invalidArr : ¬ LPl_Kit_Bytes.validChunk 8 true arr.val=true := valid
        rw [if_neg invalidArr,bind_tc_ok,if_neg valid]

#print axioms source
end NDF_ValidatorRun
