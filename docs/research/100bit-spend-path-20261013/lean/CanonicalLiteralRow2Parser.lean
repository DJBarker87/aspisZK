import ExtractedPrefixRowPayload

/-! Small adapter from the checked Aeneas prefix-parser success theorem to the
strict typed row-2 semantic decoder used by the literal model. The surrounding
Rust-to-run/wire linkage remains an explicit integration obligation. -/
set_option autoImplicit false
namespace AspisR1.CanonicalLiteralRow2Parser

open Aeneas Aeneas.Std Result
open AspisR1.SemanticRecordCodec
open AspisR1.ExtractedRecordByteValue

abbrev Bytes := AspisR1.SemanticRecordCodec.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State

theorem decode_c2Root_of_r1_wire_parse_success
    (frame payload : Slice U8)
    (hparse : AspisR1PrefixAggregateParser.r1_wire.parse_record (2#u8) frame =
      ok (core.result.Result.Ok payload)) :
    ∃ root : State,
      SemanticRecordCodec.decode ⟨2, by decide⟩
        (frame.val.map rawByte) = some ⟨.c2Root root, by rfl⟩ := by
  let i : Fin 25 := ⟨2, by decide⟩
  obtain ⟨typed, hdecode, _hencode⟩ :=
    ExtractedPrefixRowPayload.parse_record_decode i (2#u8) (by rfl) frame payload hparse
  rcases typed with ⟨p, hp⟩
  cases p with
  | c2Root root =>
      exact ⟨root, by simpa [i] using hdecode⟩
  | empty => simp [SemanticRecordCodec.validRow, i] at hp
  | maskSum value => simp [SemanticRecordCodec.validRow, i] at hp
  | polynomial coeff => simp [SemanticRecordCodec.validRow, i] at hp

#print axioms decode_c2Root_of_r1_wire_parse_success

end AspisR1.CanonicalLiteralRow2Parser
