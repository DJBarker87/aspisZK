import CanonicalLiteralEcheckSevenChunks
import CanonicalLiteralRow30WideSecond
import R1SourceWideExactCodec
import R1WideParserArrayHalves
import CanonicalLiteralChunkFacts

/-! Compose the actual echeck success facts with the checked strict logical
`.second` codec. The 224-byte source slice is interpreted byte-for-byte through
the explicit U8→Byte map. This is not yet a claim that View::parse selects or
passes that slice to echeck. -/
set_option autoImplicit false

namespace AspisR1.CanonicalLiteralEcheckStrictSecond
open Aeneas Aeneas.Std Result
open AspisR1.CanonicalLiteralEcheckSevenChunks
open AspisR1.CanonicalLiteralRow30WideSecond
open AspisR1.SourceWideExactCodec
open AspisR1.WideParserArrayHalves

abbrev CandidateWide := AspisR1CandidateParser.field.wide_exact.WideExact
abbrev ExactWide := AspisR1.SourceWideExactCodec.Wide
abbrev State := AspisR1.OpeningRecordCodec.State
abbrev Bytes := AspisR1.OpeningRecordCodec.Bytes

def sectionByteList (arrays : Fin 7 → Array Aeneas.Std.U8 32#usize) : Bytes :=
  (List.ofFn (fun i : Fin 7 =>
    List.ofFn (arrayBytes32 (arrays i)))).flatten

def decodedValues (values : Fin 7 → CandidateWide) : Fin 7 → ExactWide :=
  fun i => candidateWideToExact (values i)

theorem arrayBytes32_list (arr : Array Aeneas.Std.U8 32#usize) :
    List.ofFn (arrayBytes32 arr) =
      arr.val.map AspisV8R19.SqueezeOracleBridge.decodeByte := by
  apply List.ext_getElem
  · simp [arrayBytes32]
  · intro i hi hj
    simp only [List.getElem_ofFn, arrayBytes32, List.getElem_map]

theorem sectionByteList_eq_flatten
    (arrays : Fin 7 → Array Aeneas.Std.U8 32#usize)
    (chunks : List (List Aeneas.Std.U8))
    (hchunks : chunks.length = 7)
    (hvalues : ∀ i : Fin 7, (arrays i).val = chunks[i.val]'(by omega)) :
    sectionByteList arrays =
      chunks.flatten.map AspisV8R19.SqueezeOracleBridge.decodeByte := by
  have hlists :
      List.ofFn (fun i : Fin 7 => List.ofFn (arrayBytes32 (arrays i))) =
        chunks.map (fun raw => raw.map AspisV8R19.SqueezeOracleBridge.decodeByte) := by
    apply List.ext_getElem
    · simp [hchunks, List.length_map, List.length_ofFn]
    · intro i hi hj
      have hi7 : i < 7 := by simpa using hi
      have hj7 : i < 7 := by simpa [hchunks] using hj
      let j : Fin 7 := ⟨i, hi7⟩
      simp only [List.getElem_ofFn, List.getElem_map, arrayBytes32_list]
      congr 1
      exact hvalues j
  unfold sectionByteList
  rw [hlists, List.map_flatten]

theorem echeck_success_strict_second_decode
    (root : State) (rootBytes : Bytes) (bytes : Slice Aeneas.Std.U8)
    (hroot : rootBytes = AspisR1.OpeningRecordCodec.stateBytes root)
    (hlen : bytes.val.length = 224)
    (hcheck : AspisR1EcheckCut.verifier.echeck_round1 bytes =
      ok (core.result.Result.Ok ())) :
    ∃ values : Fin 7 → CandidateWide,
      AspisR1.OpeningRecordCodec.decode .second
        (AspisR1.LengthFrameCodec.frame
          (rootBytes ++ bytes.val.map AspisV8R19.SqueezeOracleBridge.decodeByte)) =
        some (root, decodedValues values) := by
  obtain ⟨arrays, values, hvalues, hparsed⟩ :=
    seven_chunks_parsed bytes hlen hcheck
  have hchunks := AspisR1.CanonicalLiteralChunkFacts.chunks32_exact_seven_of_length224 bytes.val hlen
  have hsection := sectionByteList_eq_flatten arrays
    (List.toChunksExact 32 (by decide) bytes.val).1 hchunks.1 hvalues
  have hflat : (List.toChunksExact 32 (by decide) bytes.val).1.flatten = bytes.val :=
    hchunks.2.2.1
  have hsectionInput : sectionByteList arrays =
      bytes.val.map AspisV8R19.SqueezeOracleBridge.decodeByte := by
    rw [hsection, hflat]
  have hparsedHalf : ∀ i : Fin 7,
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
        (Array.to_slice (arrays i)) = ok (some (values i)) := by
    intro i
    have hsourceEq := AspisR1.UnrolledWideParserRefinement.source_eq_half_parser
      (Array.to_slice (arrays i))
    exact hsourceEq.symm.trans (hparsed i)
  have hsecond := AspisR1.CanonicalLiteralRow30WideSecond.source_wide_success_implies_strict_second_decode
    root rootBytes arrays values hroot hparsedHalf
  refine ⟨values, ?_⟩
  rw [← hsectionInput]
  exact hsecond

#print axioms arrayBytes32_list
#print axioms sectionByteList_eq_flatten
#print axioms echeck_success_strict_second_decode

end AspisR1.CanonicalLiteralEcheckStrictSecond
