import ExtractedPrefixRowPayload
import R1SemanticPrefixCodec

/-! Successful actual Prefix parsing supplies typed decoding of the exact
first 25 returned records. No selected transcript or challenge is assumed. -/
set_option autoImplicit false
namespace AspisR1.ExtractedPrefixTypedFull
open Aeneas Aeneas.Std Result
open ExtractedRecordByteValue ExtractedPrefixTrace
open SemanticPrefixCodec

def completedRecords (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix) : List Bytes :=
  (parsed.records.val.take 25).map (fun frame => frame.val.map rawByte)

theorem rowOrder_values : rowOrder.map UScalar.val = List.range 27 := by rfl

theorem full_of_slots (raws : List Bytes) (hlen : raws.length = 25)
    (hslot : ∀ i : Fin 25, ∃ value : SemanticRecordCodec.RowPayload i,
      SemanticRecordCodec.decode i (raws[i.val]'(by omega)) = some value) :
    ∃ values : Full, decodeFull raws = some values ∧ encodeFull values = raws ∧
      decodeFrom 0 raws = some (entriesOf values) := by
  classical
  choose values hv using hslot
  have he : encodeFull values = raws := by
    apply List.ext_getElem
    · rw [encodeFull_length, hlen]
    · intro i hi hj
      have hi25 : i < 25 := by simpa only [encodeFull_length] using hi
      simp only [encodeFull, List.getElem_map]
      rw [entriesOf_getElem values ⟨i, hi25⟩]
      exact SemanticRecordCodec.encode_of_decode _ _ _ (hv ⟨i, hi25⟩)
  refine ⟨values, ?_, he, ?_⟩
  · rw [← he]; exact decodeFull_encodeFull values
  · rw [← he]; exact decode_encodeFull values

theorem parse_decodeFull (bytes : Slice U8)
    (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix)
    (h : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes =
      ok (core.result.Result.Ok parsed)) :
    ∃ values : Full,
      decodeFull (completedRecords parsed) = some values ∧
      encodeFull values = completedRecords parsed ∧
      decodeFrom 0 (completedRecords parsed) = some (entriesOf values) := by
  obtain ⟨_, finish, hc, _⟩ := ExtractedPrefixParse.parse_success bytes parsed h
  have hrows : rowOrder.length = 27 := rfl
  have hframes : parsed.records.val.length = 27 := hc.length.trans hrows
  have hlen : (completedRecords parsed).length = 25 := by
    simp only [completedRecords, List.length_map, List.length_take, hframes]
    decide
  apply full_of_slots _ hlen
  intro i
  have hir : i.val < rowOrder.length := by omega
  have hif : i.val < parsed.records.val.length := by omega
  let row := rowOrder[i.val]'hir
  let frame := parsed.records.val[i.val]'hif
  have hrow : row.val = i.val := by
    have hh := congrArg (fun xs : List Nat => xs[i.val]?) rowOrder_values
    rw [List.getElem?_map, List.getElem?_eq_getElem hir,
      List.getElem?_range (by omega)] at hh
    exact Option.some.inj hh
  have hm : (row, frame) ∈ rowOrder.zip parsed.records.val := by
    have hi : i.val < (rowOrder.zip parsed.records.val).length := by
      simp only [List.length_zip]; omega
    exact List.mem_of_getElem (List.getElem_zip (h := hi))
  obtain ⟨payload, hp⟩ :=
    ExtractedPrefixParse.parse_record_of_success bytes parsed h row frame hm
  obtain ⟨value, hd, _⟩ :=
    ExtractedPrefixRowPayload.parse_record_decode i row hrow frame payload hp
  refine ⟨value, ?_⟩
  simpa only [completedRecords, List.getElem_map, List.getElem_take] using hd

#print axioms rowOrder_values
#print axioms full_of_slots
#print axioms parse_decodeFull
end AspisR1.ExtractedPrefixTypedFull
