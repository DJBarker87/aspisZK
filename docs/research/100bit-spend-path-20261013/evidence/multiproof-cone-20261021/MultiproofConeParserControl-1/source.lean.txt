import MultiproofConeHeader
import MultiproofConeStrictScan

/-! Complete top-level parser control composition. The remaining row-loop
refinement is deliberately a named, uninstantiated hypothesis. This module
does not assert a complete parser source join. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeParserControl
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft MultiproofConeCanonical MultiproofConeSlices
attribute [local instance] Classical.propDecidable

def decodedRows (rows : alloc.vec.Vec (alloc.vec.Vec U8)) : List Bytes :=
  rows.val.map (fun row => bytesOf row.val)

def RowsJoin : Prop := ∀ bytes : Slice U8, bytes.val.length=6983 →
  (do let result ← MultiproofParserRef.parser_reference.semantic_rows 0#u8 bytes
        (alloc.vec.Vec.new (alloc.vec.Vec U8))
      ok (result.map decodedRows)) =
    ok (semanticRows 27 0 (bytesOf bytes.val))

private theorem parse_semantic (wire : Bytes) :
    (parse wire).map Parsed.semantic =
      if OraclePortHeader.accepts wire = true then
        if scan wire then semanticRows 27 0 (slice wire 48 6983) else none
      else none := by
  unfold parse
  cases ha : OraclePortHeader.accepts wire <;> simp only [ha]
  · rfl
  · by_cases hs : scan wire
    · simp only [hs,not_true_eq_false,if_false]
      cases semanticRows 27 0 (slice wire 48 6983) <;> rfl
    · simp only [hs,not_false_eq_true,if_true]
      rfl

theorem parse_of_rows (rows : RowsJoin) (bytes : Slice U8) :
    (do let result ← MultiproofParserRef.parser_reference.parse bytes
        ok (result.map decodedRows)) =
      ok ((parse (bytesOf bytes.val)).map Parsed.semantic) := by
  have hh : MultiproofParserRef.parser_reference.header bytes =
      ok (OraclePortHeader.accepts (bytesOf bytes.val)) :=
    MultiproofConeHeader.header_total bytes
  rw [MultiproofParserRef.parser_reference.parse,hh,parse_semantic]
  simp only [bind_tc_ok]
  cases ha : OraclePortHeader.accepts (bytesOf bytes.val) with
  | false => simp only [ha,Bool.false_eq_true,if_false,bind_tc_ok,Option.map_none]
  | true =>
    have length : bytes.val.length=57607 := by
      have h := (OraclePortHeader.accepts_iff _).mp ha
      simpa only [bytesOf,List.length_map] using h.1
    rw [MultiproofConeStrictScan.scan_total bytes length]
    simp only [ha,if_true,bind_tc_ok,decide_eq_true_eq]
    by_cases hs : scan (bytesOf bytes.val)
    · simp only [hs,if_true]
      have bound : (7031#usize).val≤bytes.val.length := by change 7031≤bytes.val.length;omega
      rw [range_total bytes 48#usize 7031#usize (by scalar_tac) bound]
      simp only [bind_tc_ok]
      have hl : (sub bytes 48#usize 7031#usize).val.length=6983 := by
        rw [sub_length bytes 48#usize 7031#usize (by scalar_tac) bound]
        rfl
      rw [rows _ hl,bytes_sub]
      rfl
    · simp only [hs,if_false,bind_tc_ok,Option.map_none]

#print axioms parse_semantic
#print axioms parse_of_rows
end AspisR1.MultiproofConeParserControl
end
