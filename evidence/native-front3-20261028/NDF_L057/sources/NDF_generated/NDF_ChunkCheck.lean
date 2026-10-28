import NDF_CodecTotal
set_option autoImplicit false
noncomputable section
namespace NDF_ChunkCheck
open Aeneas Aeneas.Std Result
open AspisR1RecordParser AspisR1RecordParser.field
attribute [local instance] Classical.propDecidable

def check (row : U8) (index : Usize) (bytes : Slice U8) : Result (core.result.Result Unit r1_wire.Error) := do
  let decoded ← wide_exact.WideExact.from_le_bytes bytes
  match decoded with
  | none => ok (.Err (.NonCanonical row index))
  | some w =>
    let bad ← core.cmp.PartialEq.ne.trait_default QM31.Insts.CoreCmpPartialEqQM31 w.c1 QM31.ZERO
    if bad then ok (.Err (.NonCanonical row index)) else ok (.Ok ())

theorem value (row : U8) (index : Usize) (arr : Array U8 32#usize) :
    check row index (Array.to_slice arr) = ok (if LPl_Kit_Bytes.validChunk 8 true arr.val
      then .Ok () else .Err (.NonCanonical row index)) := by
  obtain ⟨decoded,call⟩ := NDF_CodecTotal.decode arr
  cases decoded with
  | none =>
    have bad : LPl_Kit_Bytes.validChunk 8 true arr.val=false := by
      cases h : LPl_Kit_Bytes.validChunk 8 true arr.val with
      | false => rfl
      | true =>
        obtain ⟨w,other,_⟩ := (NDF_ChunkCodec.valid_iff arr).mp h
        rw [call] at other
        cases other
    simp only [check,call,bind_tc_ok,bad,Bool.false_eq_true,if_false]
  | some w =>
    have valid : LPl_Kit_Bytes.validChunk 8 true arr.val=true ↔ w.c1=QM31.ZERO := by
      rw [NDF_ChunkCodec.valid_iff]
      constructor
      · rintro ⟨v,other,zero⟩
        rw [call] at other
        have same := Option.some.inj (Result.ok.inj other)
        subst v
        exact zero
      · intro zero
        exact ⟨w,call,zero⟩
    simp only [check,call,bind_tc_ok]
    rw [NDF_CodecTotal.compare]
    by_cases zero : w.c1=QM31.ZERO
    · simp only [zero,ne_eq,not_true_eq_false,decide_false,bind_tc_ok,Bool.false_eq_true,if_false,valid.mpr zero,if_true]
    · have bad : LPl_Kit_Bytes.validChunk 8 true arr.val=false := by
        cases h : LPl_Kit_Bytes.validChunk 8 true arr.val with
        | false => rfl
        | true => exact False.elim (zero (valid.mp h))
      simp only [zero,ne_eq,not_false_eq_true,decide_true,bind_tc_ok,if_true,bad,Bool.false_eq_true,if_false]

#print axioms value
end NDF_ChunkCheck
