import S9NativeWideDecoderRecordMapV1
import S5PairCutTransparentReaderAdapterV1
import R22Stage2ControlBounds
import R22TotalUnsignedPrimitives
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9NativeFieldS5BoundedReaderV1
open AspisR1S9NativeWideDecoderRecordMapV1
open AspisR1S9OwnedFromLimbsMapV1 (mapResult mapOptionResult)
abbrev S5W := AspisR1S5PairCutTransparentReaderV1.PairWide

def toS5 (w : NativeW) : S5W := AspisR1S5PairCutTransparentReaderV1.recordToPair (toRecord w)
def SafeIndex (i : Usize) : Prop := (i.val+1)*32 ≤ Usize.max

private theorem map_comp (r : Result (Option NativeW)) :
    mapResult (Option.map AspisR1S5PairCutTransparentReaderV1.recordToPair)
      (mapOptionResult toRecord r) = mapResult (Option.map toS5) r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok o => cases o <;> rfl

private theorem s5_decoder_record_map (bytes : Slice U8) :
    mapResult (Option.map AspisR1S5PairCutTransparentReaderV1.recordToPair)
      (AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes) =
      AspisR1S5PairCutTransparentReaderV1.actualPairDecoder bytes := by
  unfold AspisR1S5PairCutTransparentReaderV1.actualPairDecoder
    AspisR1S5PairCutTransparentReaderV1.mapDecodedRecord
  cases AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes <;> rfl

/-- Full decoderResult, matched to the EXISTING concrete S5 actual decoder. -/
theorem native_decoder_maps_s5 (bytes : Slice U8) :
    mapResult (Option.map toS5) (aspis_core.field.wide_exact.WideExact.from_le_bytes bytes) =
      AspisR1S5PairCutTransparentReaderV1.actualPairDecoder bytes := by
  rw [←map_comp,native_bytes_maps_record]
  exact s5_decoder_record_map bytes

private theorem mapResult_bind {A B C : Type} (f : B → C) (m : Result A) (next : A → Result B) :
    mapResult f (do let x ← m; next x) = (do let x ← m; mapResult f (next x)) := by
  cases m <;> rfl

private theorem map_unwrap {A B : Type} (f : A → B) (m : Result (Option A)) :
    mapResult f (do let o ← m; core.option.Option.unwrap o) =
      (do let o ← mapResult (Option.map f) m; core.option.Option.unwrap o) := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok o => cases o <;> rfl

private theorem native_decode_unwrap (bytes : Slice U8) :
    (do let o ← aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
        mapResult toS5 (core.option.Option.unwrap o)) =
      (do let o ← AspisR1S5PairCutTransparentReaderV1.actualPairDecoder bytes
          core.option.Option.unwrap o) := by
  have hm := map_unwrap toS5 (aspis_core.field.wide_exact.WideExact.from_le_bytes bytes)
  rw [mapResult_bind,native_decoder_maps_s5] at hm
  exact hm

/-- The actual index bound supplies successful CHECKED offsets equal to all
three source WRAPPING offsets. Reuses existing R22 totality/success laws. -/
theorem checked_offsets (i : Usize) (hi : SafeIndex i) :
    ∃ (start next finish : Usize),
      (i*32#usize : Result Usize)=.ok start ∧
      (i+1#usize : Result Usize)=.ok next ∧
      (next*32#usize : Result Usize)=.ok finish ∧
      Usize.wrapping_mul i 32#usize=start ∧
      Usize.wrapping_add i 1#usize=next ∧
      Usize.wrapping_mul next 32#usize=finish := by
  change (i.val+1)*32 ≤ Usize.max at hi
  obtain ⟨start,hs,hsv⟩ := AspisR1.R22Stage2ControlBounds.mul_total i 32#usize (by change i.val*32 ≤ Usize.max; omega)
  obtain ⟨next,hn,hnv⟩ := AspisR1.R22Stage2ControlBounds.add_total i 1#usize (by change i.val+1 ≤ Usize.max; omega)
  have hnval : next.val=i.val+1 := hnv
  obtain ⟨finish,hf,hfv⟩ := AspisR1.R22Stage2ControlBounds.mul_total next 32#usize (by change next.val*32 ≤ Usize.max; rw [hnval]; exact hi)
  exact ⟨start,next,finish,hs,hn,hf,
    (AspisR1.R22TotalUnsignedPrimitives.mul_success i 32#usize start hs).1,
    (AspisR1.R22TotalUnsignedPrimitives.add_success i 1#usize next hn).1,
    (AspisR1.R22TotalUnsignedPrimitives.mul_success next 32#usize finish hf).1⟩

/-- BOUNDED full reader equality against the EXISTING S5 checked reader.
All bytes, including malformed decoder/unwrap cases, are covered. -/
theorem native_field_maps_s5_reader (bytes : Slice U8) (i : Usize) (hi : SafeIndex i) :
    mapResult toS5 (weights.field bytes i) =
      AspisR1S5PairCutTransparentReaderV1.readerBody
        AspisR1S5PairCutTransparentReaderV1.actualPairDecoder bytes i := by
  obtain ⟨start,next,finish,hs,hn,hf,hws,hwn,hwf⟩ := checked_offsets i hi
  simp only [weights.field,AspisR1S5PairCutTransparentReaderV1.readerBody,
    lift,hws,hwn,hwf,hs,hn,hf,bind_tc_ok,mapResult_bind,native_decode_unwrap]

/-- A field window contained in the ACTUAL input gives the machine bound;
no separate architecture/minimum-word-size assumption is introduced. -/
theorem fitting_window_safe (bytes : Slice U8) (i : Usize)
    (hfit : (i.val+1)*32 ≤ bytes.val.length) : SafeIndex i := by
  have hlen := bytes.property
  change (i.val+1)*32 ≤ Usize.max
  omega

#print axioms native_decoder_maps_s5
#print axioms checked_offsets
#print axioms native_field_maps_s5_reader
#print axioms fitting_window_safe
end AspisR1S9NativeFieldS5BoundedReaderV1
