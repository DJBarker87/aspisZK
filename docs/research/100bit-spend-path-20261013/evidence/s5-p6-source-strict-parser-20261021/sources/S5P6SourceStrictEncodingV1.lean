import ToBytesP6IndexedCarrierBridgeV1
import S5P6WordCodecBridgeV1
import S5P6ParserSuccessV1
import UnrolledWideParserRefinement
import R1WideParserArrayHalves

set_option autoImplicit false

namespace AspisR1S5P6SourceStrictEncodingV1

open Aeneas Aeneas.Std
open AspisR1.RetainedFieldByteCodec
open AspisR1.StrictWideByteCodec

abbrev SourceWide := P6ToBytes.IndexedCarrierBridge.SourceWide
abbrev IndexedWide := P6ToBytes.IndexedCarrierBridge.IndexedWide

def wordAt (x : SourceWide) : Fin 8 → Std.U32 := fun i =>
  match i.val with
  | 0 => x.c0.c0.a
  | 1 => x.c0.c0.b
  | 2 => x.c0.c1.a
  | 3 => x.c0.c1.b
  | 4 => x.c1.c0.a
  | 5 => x.c1.c0.b
  | 6 => x.c1.c1.a
  | _ => x.c1.c1.b

def sourceWideLimbs (x : SourceWide) (h : ∀ i, (wordAt x i).val < m31Modulus) : WideLimbs :=
  (fun i : Fin 4 => ⟨(wordAt x ⟨i.val, by omega⟩).val, h ⟨i.val, by omega⟩⟩,
   fun i : Fin 4 => ⟨(wordAt x ⟨i.val + 4, by omega⟩).val, h ⟨i.val + 4, by omega⟩⟩)

private theorem word_byte (w : Std.U32) (hw : w.val < m31Modulus) (k : Fin 4) :
    AspisV8R19.SqueezeOracleBridge.decodeByte
      ((core.num.U32.to_le_bytes w).val[k.val]'(by
        have hlen := (core.num.U32.to_le_bytes w).property
        change (core.num.U32.to_le_bytes w).val.length = 4 at hlen
        omega)) = encodeM31LE ⟨w.val, hw⟩ k := by
  change AspisR1S5P6WordCodecBridgeV1.u32WordBytes w k = _
  exact congrFun (AspisR1S5P6WordCodecBridgeV1.u32WordBytes_eq_encodeM31 w hw) k

@[simp] private theorem generated_word_byte (w : Std.U32) (hw : w.val < m31Modulus) (k : Fin 4) :
    AspisV8R19.SqueezeOracleBridge.decodeByte ((U32.bv w).toLEBytes[k.val]#uscalar) =
      encodeM31LE ⟨w.val, hw⟩ k := by
  have h := word_byte w hw k
  change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((core.num.U32.to_le_bytes w).val[k.val]'(by
        have hl := (core.num.U32.to_le_bytes w).property
        change (core.num.U32.to_le_bytes w).val.length = 4 at hl
        omega)) = _ at h
  simpa [core.num.U32.to_le_bytes] using h

theorem indexed_expected_array_strict
    (x : SourceWide) (h : ∀ i, (wordAt x i).val < m31Modulus) :
    AspisR1.WideParserArrayHalves.arrayBytes32
      (AspisR1WideToBytesIndexedCandidate.expectedBytes
        (P6ToBytes.IndexedCarrierBridge.toIndexed x)) =
      encodeWideLE (sourceWideLimbs x h) := by
  funext j
  fin_cases j
  case «0» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c0.a).toLEBytes[0]#uscalar) =
      encodeM31LE ⟨x.c0.c0.a.val, by simpa [wordAt] using h (⟨0, by omega⟩ : Fin 8)⟩ 0
    exact generated_word_byte x.c0.c0.a (by simpa [wordAt] using h (⟨0, by omega⟩ : Fin 8)) (⟨0, by omega⟩ : Fin 4)
  case «1» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c0.a).toLEBytes[1]#uscalar) =
      encodeM31LE ⟨x.c0.c0.a.val, by simpa [wordAt] using h (⟨0, by omega⟩ : Fin 8)⟩ 1
    exact generated_word_byte x.c0.c0.a (by simpa [wordAt] using h (⟨0, by omega⟩ : Fin 8)) (⟨1, by omega⟩ : Fin 4)
  case «2» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c0.a).toLEBytes[2]#uscalar) =
      encodeM31LE ⟨x.c0.c0.a.val, by simpa [wordAt] using h (⟨0, by omega⟩ : Fin 8)⟩ 2
    exact generated_word_byte x.c0.c0.a (by simpa [wordAt] using h (⟨0, by omega⟩ : Fin 8)) (⟨2, by omega⟩ : Fin 4)
  case «3» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c0.a).toLEBytes[3]#uscalar) =
      encodeM31LE ⟨x.c0.c0.a.val, by simpa [wordAt] using h (⟨0, by omega⟩ : Fin 8)⟩ 3
    exact generated_word_byte x.c0.c0.a (by simpa [wordAt] using h (⟨0, by omega⟩ : Fin 8)) (⟨3, by omega⟩ : Fin 4)
  case «4» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c0.b).toLEBytes[0]#uscalar) =
      encodeM31LE ⟨x.c0.c0.b.val, by simpa [wordAt] using h (⟨1, by omega⟩ : Fin 8)⟩ 0
    exact generated_word_byte x.c0.c0.b (by simpa [wordAt] using h (⟨1, by omega⟩ : Fin 8)) (⟨0, by omega⟩ : Fin 4)
  case «5» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c0.b).toLEBytes[1]#uscalar) =
      encodeM31LE ⟨x.c0.c0.b.val, by simpa [wordAt] using h (⟨1, by omega⟩ : Fin 8)⟩ 1
    exact generated_word_byte x.c0.c0.b (by simpa [wordAt] using h (⟨1, by omega⟩ : Fin 8)) (⟨1, by omega⟩ : Fin 4)
  case «6» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c0.b).toLEBytes[2]#uscalar) =
      encodeM31LE ⟨x.c0.c0.b.val, by simpa [wordAt] using h (⟨1, by omega⟩ : Fin 8)⟩ 2
    exact generated_word_byte x.c0.c0.b (by simpa [wordAt] using h (⟨1, by omega⟩ : Fin 8)) (⟨2, by omega⟩ : Fin 4)
  case «7» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c0.b).toLEBytes[3]#uscalar) =
      encodeM31LE ⟨x.c0.c0.b.val, by simpa [wordAt] using h (⟨1, by omega⟩ : Fin 8)⟩ 3
    exact generated_word_byte x.c0.c0.b (by simpa [wordAt] using h (⟨1, by omega⟩ : Fin 8)) (⟨3, by omega⟩ : Fin 4)
  case «8» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c1.a).toLEBytes[0]#uscalar) =
      encodeM31LE ⟨x.c0.c1.a.val, by simpa [wordAt] using h (⟨2, by omega⟩ : Fin 8)⟩ 0
    exact generated_word_byte x.c0.c1.a (by simpa [wordAt] using h (⟨2, by omega⟩ : Fin 8)) (⟨0, by omega⟩ : Fin 4)
  case «9» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c1.a).toLEBytes[1]#uscalar) =
      encodeM31LE ⟨x.c0.c1.a.val, by simpa [wordAt] using h (⟨2, by omega⟩ : Fin 8)⟩ 1
    exact generated_word_byte x.c0.c1.a (by simpa [wordAt] using h (⟨2, by omega⟩ : Fin 8)) (⟨1, by omega⟩ : Fin 4)
  case «10» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c1.a).toLEBytes[2]#uscalar) =
      encodeM31LE ⟨x.c0.c1.a.val, by simpa [wordAt] using h (⟨2, by omega⟩ : Fin 8)⟩ 2
    exact generated_word_byte x.c0.c1.a (by simpa [wordAt] using h (⟨2, by omega⟩ : Fin 8)) (⟨2, by omega⟩ : Fin 4)
  case «11» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c1.a).toLEBytes[3]#uscalar) =
      encodeM31LE ⟨x.c0.c1.a.val, by simpa [wordAt] using h (⟨2, by omega⟩ : Fin 8)⟩ 3
    exact generated_word_byte x.c0.c1.a (by simpa [wordAt] using h (⟨2, by omega⟩ : Fin 8)) (⟨3, by omega⟩ : Fin 4)
  case «12» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c1.b).toLEBytes[0]#uscalar) =
      encodeM31LE ⟨x.c0.c1.b.val, by simpa [wordAt] using h (⟨3, by omega⟩ : Fin 8)⟩ 0
    exact generated_word_byte x.c0.c1.b (by simpa [wordAt] using h (⟨3, by omega⟩ : Fin 8)) (⟨0, by omega⟩ : Fin 4)
  case «13» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c1.b).toLEBytes[1]#uscalar) =
      encodeM31LE ⟨x.c0.c1.b.val, by simpa [wordAt] using h (⟨3, by omega⟩ : Fin 8)⟩ 1
    exact generated_word_byte x.c0.c1.b (by simpa [wordAt] using h (⟨3, by omega⟩ : Fin 8)) (⟨1, by omega⟩ : Fin 4)
  case «14» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c1.b).toLEBytes[2]#uscalar) =
      encodeM31LE ⟨x.c0.c1.b.val, by simpa [wordAt] using h (⟨3, by omega⟩ : Fin 8)⟩ 2
    exact generated_word_byte x.c0.c1.b (by simpa [wordAt] using h (⟨3, by omega⟩ : Fin 8)) (⟨2, by omega⟩ : Fin 4)
  case «15» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c0.c1.b).toLEBytes[3]#uscalar) =
      encodeM31LE ⟨x.c0.c1.b.val, by simpa [wordAt] using h (⟨3, by omega⟩ : Fin 8)⟩ 3
    exact generated_word_byte x.c0.c1.b (by simpa [wordAt] using h (⟨3, by omega⟩ : Fin 8)) (⟨3, by omega⟩ : Fin 4)
  case «16» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c0.a).toLEBytes[0]#uscalar) =
      encodeM31LE ⟨x.c1.c0.a.val, by simpa [wordAt] using h (⟨4, by omega⟩ : Fin 8)⟩ 0
    exact generated_word_byte x.c1.c0.a (by simpa [wordAt] using h (⟨4, by omega⟩ : Fin 8)) (⟨0, by omega⟩ : Fin 4)
  case «17» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c0.a).toLEBytes[1]#uscalar) =
      encodeM31LE ⟨x.c1.c0.a.val, by simpa [wordAt] using h (⟨4, by omega⟩ : Fin 8)⟩ 1
    exact generated_word_byte x.c1.c0.a (by simpa [wordAt] using h (⟨4, by omega⟩ : Fin 8)) (⟨1, by omega⟩ : Fin 4)
  case «18» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c0.a).toLEBytes[2]#uscalar) =
      encodeM31LE ⟨x.c1.c0.a.val, by simpa [wordAt] using h (⟨4, by omega⟩ : Fin 8)⟩ 2
    exact generated_word_byte x.c1.c0.a (by simpa [wordAt] using h (⟨4, by omega⟩ : Fin 8)) (⟨2, by omega⟩ : Fin 4)
  case «19» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c0.a).toLEBytes[3]#uscalar) =
      encodeM31LE ⟨x.c1.c0.a.val, by simpa [wordAt] using h (⟨4, by omega⟩ : Fin 8)⟩ 3
    exact generated_word_byte x.c1.c0.a (by simpa [wordAt] using h (⟨4, by omega⟩ : Fin 8)) (⟨3, by omega⟩ : Fin 4)
  case «20» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c0.b).toLEBytes[0]#uscalar) =
      encodeM31LE ⟨x.c1.c0.b.val, by simpa [wordAt] using h (⟨5, by omega⟩ : Fin 8)⟩ 0
    exact generated_word_byte x.c1.c0.b (by simpa [wordAt] using h (⟨5, by omega⟩ : Fin 8)) (⟨0, by omega⟩ : Fin 4)
  case «21» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c0.b).toLEBytes[1]#uscalar) =
      encodeM31LE ⟨x.c1.c0.b.val, by simpa [wordAt] using h (⟨5, by omega⟩ : Fin 8)⟩ 1
    exact generated_word_byte x.c1.c0.b (by simpa [wordAt] using h (⟨5, by omega⟩ : Fin 8)) (⟨1, by omega⟩ : Fin 4)
  case «22» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c0.b).toLEBytes[2]#uscalar) =
      encodeM31LE ⟨x.c1.c0.b.val, by simpa [wordAt] using h (⟨5, by omega⟩ : Fin 8)⟩ 2
    exact generated_word_byte x.c1.c0.b (by simpa [wordAt] using h (⟨5, by omega⟩ : Fin 8)) (⟨2, by omega⟩ : Fin 4)
  case «23» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c0.b).toLEBytes[3]#uscalar) =
      encodeM31LE ⟨x.c1.c0.b.val, by simpa [wordAt] using h (⟨5, by omega⟩ : Fin 8)⟩ 3
    exact generated_word_byte x.c1.c0.b (by simpa [wordAt] using h (⟨5, by omega⟩ : Fin 8)) (⟨3, by omega⟩ : Fin 4)
  case «24» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c1.a).toLEBytes[0]#uscalar) =
      encodeM31LE ⟨x.c1.c1.a.val, by simpa [wordAt] using h (⟨6, by omega⟩ : Fin 8)⟩ 0
    exact generated_word_byte x.c1.c1.a (by simpa [wordAt] using h (⟨6, by omega⟩ : Fin 8)) (⟨0, by omega⟩ : Fin 4)
  case «25» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c1.a).toLEBytes[1]#uscalar) =
      encodeM31LE ⟨x.c1.c1.a.val, by simpa [wordAt] using h (⟨6, by omega⟩ : Fin 8)⟩ 1
    exact generated_word_byte x.c1.c1.a (by simpa [wordAt] using h (⟨6, by omega⟩ : Fin 8)) (⟨1, by omega⟩ : Fin 4)
  case «26» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c1.a).toLEBytes[2]#uscalar) =
      encodeM31LE ⟨x.c1.c1.a.val, by simpa [wordAt] using h (⟨6, by omega⟩ : Fin 8)⟩ 2
    exact generated_word_byte x.c1.c1.a (by simpa [wordAt] using h (⟨6, by omega⟩ : Fin 8)) (⟨2, by omega⟩ : Fin 4)
  case «27» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c1.a).toLEBytes[3]#uscalar) =
      encodeM31LE ⟨x.c1.c1.a.val, by simpa [wordAt] using h (⟨6, by omega⟩ : Fin 8)⟩ 3
    exact generated_word_byte x.c1.c1.a (by simpa [wordAt] using h (⟨6, by omega⟩ : Fin 8)) (⟨3, by omega⟩ : Fin 4)
  case «28» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c1.b).toLEBytes[0]#uscalar) =
      encodeM31LE ⟨x.c1.c1.b.val, by simpa [wordAt] using h (⟨7, by omega⟩ : Fin 8)⟩ 0
    exact generated_word_byte x.c1.c1.b (by simpa [wordAt] using h (⟨7, by omega⟩ : Fin 8)) (⟨0, by omega⟩ : Fin 4)
  case «29» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c1.b).toLEBytes[1]#uscalar) =
      encodeM31LE ⟨x.c1.c1.b.val, by simpa [wordAt] using h (⟨7, by omega⟩ : Fin 8)⟩ 1
    exact generated_word_byte x.c1.c1.b (by simpa [wordAt] using h (⟨7, by omega⟩ : Fin 8)) (⟨1, by omega⟩ : Fin 4)
  case «30» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c1.b).toLEBytes[2]#uscalar) =
      encodeM31LE ⟨x.c1.c1.b.val, by simpa [wordAt] using h (⟨7, by omega⟩ : Fin 8)⟩ 2
    exact generated_word_byte x.c1.c1.b (by simpa [wordAt] using h (⟨7, by omega⟩ : Fin 8)) (⟨2, by omega⟩ : Fin 4)
  case «31» =>
    change AspisV8R19.SqueezeOracleBridge.decodeByte
      ((U32.bv x.c1.c1.b).toLEBytes[3]#uscalar) =
      encodeM31LE ⟨x.c1.c1.b.val, by simpa [wordAt] using h (⟨7, by omega⟩ : Fin 8)⟩ 3
    exact generated_word_byte x.c1.c1.b (by simpa [wordAt] using h (⟨7, by omega⟩ : Fin 8)) (⟨3, by omega⟩ : Fin 4)

theorem source_serializer_strict_parser_success
    (x : SourceWide) (h : ∀ i, (wordAt x i).val < m31Modulus) :
    ∃ out : Array U8 32#usize,
      AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes x = .ok out ∧
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
        (Array.to_slice out) =
        .ok (some (AspisR1.CandidateWideParserRefinement.limbsToCandidate
          (sourceWideLimbs x h))) := by
  obtain ⟨out, hout, hlist, hindexed⟩ :=
    P6ToBytes.IndexedCarrierBridge.source_output_matches_indexed_encoding x
  refine ⟨out, hout, ?_⟩
  have hbytes : AspisR1.WideParserArrayHalves.arrayBytes32 out =
      encodeWideLE (sourceWideLimbs x h) := by
    have harr : out = AspisR1WideToBytesIndexedCandidate.expectedBytes
        (P6ToBytes.IndexedCarrierBridge.toIndexed x) := Subtype.ext hlist
    rw [harr]
    exact indexed_expected_array_strict x h
  exact AspisR1S5P6ParserSuccessV1.parser_success_of_strict_encoding out
    (sourceWideLimbs x h) hbytes

/-- The strict-parser value recovers the source's eight field coordinates. -/
theorem parsed_candidate_coordinates_eq_source
    (x : SourceWide) (h : ∀ i, (wordAt x i).val < m31Modulus) :
    let y := AspisR1.CandidateWideParserRefinement.limbsToCandidate
      (sourceWideLimbs x h)
    y.c0.c0.a.val = x.c0.c0.a.val ∧
    y.c0.c0.b.val = x.c0.c0.b.val ∧
    y.c0.c1.a.val = x.c0.c1.a.val ∧
    y.c0.c1.b.val = x.c0.c1.b.val ∧
    y.c1.c0.a.val = x.c1.c0.a.val ∧
    y.c1.c0.b.val = x.c1.c0.b.val ∧
    y.c1.c1.a.val = x.c1.c1.a.val ∧
    y.c1.c1.b.val = x.c1.c1.b.val := by
  dsimp
  simp [AspisR1.CandidateWideParserRefinement.limbsToCandidate,
    AspisR1.CandidateStrictQM31Parser.limbsToCandidate,
    sourceWideLimbs, wordAt, AspisR1.M31ParserRefinement.valueToU32_val]

theorem source_serializer_parser_roundtrip_fieldwise
    (x : SourceWide) (h : ∀ i, (wordAt x i).val < m31Modulus) :
    ∃ out : Array U8 32#usize,
      AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes x = .ok out ∧
      ∃ y : AspisR1CandidateParser.field.wide_exact.WideExact,
        AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
          (Array.to_slice out) = .ok (some y) ∧
        y.c0.c0.a.val = x.c0.c0.a.val ∧
        y.c0.c0.b.val = x.c0.c0.b.val ∧
        y.c0.c1.a.val = x.c0.c1.a.val ∧
        y.c0.c1.b.val = x.c0.c1.b.val ∧
        y.c1.c0.a.val = x.c1.c0.a.val ∧
        y.c1.c0.b.val = x.c1.c0.b.val ∧
        y.c1.c1.a.val = x.c1.c1.a.val ∧
        y.c1.c1.b.val = x.c1.c1.b.val := by
  obtain ⟨out, hout, hparse⟩ := source_serializer_strict_parser_success x h
  refine ⟨out, hout, _, hparse, ?_⟩
  simpa using parsed_candidate_coordinates_eq_source x h

#print axioms indexed_expected_array_strict
#print axioms source_serializer_strict_parser_success
#print axioms parsed_candidate_coordinates_eq_source
#print axioms source_serializer_parser_roundtrip_fieldwise

end AspisR1S5P6SourceStrictEncodingV1
