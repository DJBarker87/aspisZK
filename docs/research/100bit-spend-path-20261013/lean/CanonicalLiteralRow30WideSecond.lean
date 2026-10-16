import R1SourceWideExactCodec
import R1OpeningRecordCodec
import R1SelectedFieldSequenceCodec
import R1LengthFrameCodec

/-! Source-success to strict row-30 logical-record bridge.

This theorem treats the seven 32-byte wide values as the payload of the
logical `.second` record. It does not identify this length-framed record with
the separate `Transcript.absorb` sampler framing, and it does not claim that
`View::parse` supplies the seven arrays or these parser-success facts. -/
set_option autoImplicit false

namespace AspisR1.CanonicalLiteralRow30WideSecond

open AspisR1.SourceWideExactCodec
open AspisR1.SelectedFieldSequenceCodec
open AspisR1.OpeningRecordCodec
open AspisR1.SemanticCoefficientCodec
open Aeneas Aeneas.Std

abbrev U8 := Aeneas.Std.U8
abbrev CandidateWide := AspisR1.SourceWideExactCodec.CandidateWide
abbrev Wide := AspisR1.SourceWideExactCodec.Wide
abbrev State := AspisR1.OpeningRecordCodec.State
abbrev Bytes := AspisR1.OpeningRecordCodec.Bytes

private def sectionBytes (chunks : Fin 7 → Array U8 32#usize) : Bytes :=
  (List.ofFn (fun i : Fin 7 =>
    List.ofFn (AspisR1.WideParserArrayHalves.arrayBytes32 (chunks i)))).flatten

private def decodedValues (values : Fin 7 → CandidateWide) : Fin 7 → Wide :=
  fun i => AspisR1.SourceWideExactCodec.candidateWideToExact (values i)

private theorem sectionBytes_eq_encode
    (chunks : Fin 7 → Array U8 32#usize)
    (values : Fin 7 → CandidateWide)
    (hparsed : ∀ i : Fin 7,
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
        (Array.to_slice (chunks i)) = .ok (some (values i))) :
    sectionBytes chunks = SelectedFieldSequenceCodec.encodeWide (decodedValues values) := by
  have hone : ∀ i : Fin 7,
      AspisR1.FoldedLeafCodec.encodeWide (decodedValues values i) =
        List.ofFn (AspisR1.WideParserArrayHalves.arrayBytes32 (chunks i)) := by
    intro i
    have hsourceEq := AspisR1.UnrolledWideParserRefinement.source_eq_half_parser
      (Array.to_slice (chunks i))
    have hunrolled :
        AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
          (Array.to_slice (chunks i)) = .ok (some (values i)) :=
      hsourceEq.trans (hparsed i)
    have hdecode := AspisR1.SourceWideExactCodec.successful_parse_decodes
      (chunks i) (values i) hunrolled
    exact AspisR1.FoldedLeafCodec.encodeWide_of_decode _ _ hdecode
  unfold sectionBytes SelectedFieldSequenceCodec.encodeWide
    AspisR1.FixedWidthDecoder.encode
  simp only [List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact (hone i).symm

theorem source_wide_success_implies_strict_second_decode
    (root : State) (rootBytes : Bytes)
    (chunks : Fin 7 → Array U8 32#usize)
    (values : Fin 7 → CandidateWide)
    (hroot : rootBytes = AspisR1.OpeningRecordCodec.stateBytes root)
    (hparsed : ∀ i : Fin 7,
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
        (Array.to_slice (chunks i)) = .ok (some (values i))) :
    AspisR1.OpeningRecordCodec.decode .second
      (AspisR1.LengthFrameCodec.frame (rootBytes ++ sectionBytes chunks)) =
      some (root, decodedValues values) := by
  have hsection := sectionBytes_eq_encode chunks values hparsed
  rw [hroot, hsection]
  exact AspisR1.OpeningRecordCodec.decode_encode
    (row := .second) (root, decodedValues values)

#print axioms sectionBytes_eq_encode
#print axioms source_wide_success_implies_strict_second_decode

end AspisR1.CanonicalLiteralRow30WideSecond
