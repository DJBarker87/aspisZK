import ExtractedRecordStrictCodec
import StrictLowChunkCodec

/-! Zero high-coordinate transport for the unchanged strict limb codec.
This remains below WideExact algebra and the semantic-prefix import chain. -/
namespace AspisR1.ExtractedRecordStrictLow
open Aeneas Aeneas.Std
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality
open ExtractedRecordStrictCodec

theorem canonical_high_zero (arr : Array U8 32#usize)
    (canonical : ∀ i : Fin 8, (wordLE arr i).val < 2147483647)
    (hz : (packed (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
      (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7)).c1 =
      AspisR1RecordParser.field.QM31.ZERO) :
    (canonicalLimbs arr canonical).2 = fun _ => zeroLimb := by
  funext i
  fin_cases i
  · apply Fin.ext
    change (wordLE arr 4).val = 0
    simpa only [packed, AspisR1RecordParser.field.QM31.ZERO,
      show (0#u32).val = 0 from by decide] using
      congrArg (fun q : AspisR1RecordParser.field.QM31 => q.c0.a.val) hz
  · apply Fin.ext
    change (wordLE arr 5).val = 0
    simpa only [packed, AspisR1RecordParser.field.QM31.ZERO,
      show (0#u32).val = 0 from by decide] using
      congrArg (fun q : AspisR1RecordParser.field.QM31 => q.c0.b.val) hz
  · apply Fin.ext
    change (wordLE arr 6).val = 0
    simpa only [packed, AspisR1RecordParser.field.QM31.ZERO,
      show (0#u32).val = 0 from by decide] using
      congrArg (fun q : AspisR1RecordParser.field.QM31 => q.c1.a.val) hz
  · apply Fin.ext
    change (wordLE arr 7).val = 0
    simpa only [packed, AspisR1RecordParser.field.QM31.ZERO,
      show (0#u32).val = 0 from by decide] using
      congrArg (fun q : AspisR1RecordParser.field.QM31 => q.c1.b.val) hz

theorem actual_decode_low (bytes : Slice U8)
    (w : AspisR1PrefixAggregateParser.field.wide_exact.WideExact)
    (h : AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes bytes =
      Result.ok (some w))
    (hz : w.c1 = AspisR1PrefixAggregateParser.field.QM31.ZERO) :
    ∃ arr : Array U8 32#usize, arr.val = bytes.val ∧
      ∃ canonical : ∀ i : Fin 8, (wordLE arr i).val < 2147483647,
        StrictWideByteCodec.decodeWideLE (arrayBytes arr) =
          some (canonicalLimbs arr canonical) ∧
        (canonicalLimbs arr canonical).2 = fun _ => zeroLimb := by
  obtain ⟨arr, hb, hc, hd, hp⟩ := actual_decode_strict bytes w h
  refine ⟨arr, hb, hc, hd, canonical_high_zero arr hc ?_⟩
  rw [← hp]
  change ExtractedPrefixFieldAgreement.qmToRecord w.c1 = _
  rw [hz, ExtractedPrefixFieldAgreement.qm_zero_agreement]

end AspisR1.ExtractedRecordStrictLow

#print axioms AspisR1.ExtractedRecordStrictLow.canonical_high_zero
#print axioms AspisR1.ExtractedRecordStrictLow.actual_decode_low
