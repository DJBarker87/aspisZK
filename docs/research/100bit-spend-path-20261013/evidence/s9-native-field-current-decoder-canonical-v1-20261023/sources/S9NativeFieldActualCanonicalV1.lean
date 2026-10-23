import S9NativeWideDecoderRecordMapV1
import S4ReaderEActualWideCanonicalV1
import S9ActualPairWideCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9NativeFieldActualCanonicalV1
open AspisR1S9NativeWideDecoderRecordMapV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def FlatCanonical (w : NativeW) : Prop :=
  w.c0.c0.a.val < 2147483647 ∧ w.c0.c0.b.val < 2147483647 ∧
  w.c0.c1.a.val < 2147483647 ∧ w.c0.c1.b.val < 2147483647 ∧
  w.c1.c0.a.val < 2147483647 ∧ w.c1.c0.b.val < 2147483647 ∧
  w.c1.c1.a.val < 2147483647 ∧ w.c1.c1.b.val < 2147483647

/-- Current transparent decoder success reuses the checked retained32-byte
parser and ReaderE canonicality; no decoder/data correctness premise. -/
theorem native_decoder_success_canonical (bytes : Slice U8) (w : NativeW)
    (h : aspis_core.field.wide_exact.WideExact.from_le_bytes bytes=.ok (some w)) : FlatCanonical w := by
  have hm := native_bytes_maps_record bytes
  rw [h] at hm
  have hr : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes=.ok (some (toRecord w)) := hm.symm
  have hc : AspisR1S4ReaderEActualWideCanonicalV1.actualCurrentWideDecoder bytes =
      .ok (some (AspisR1S4ReaderEActualWideCanonicalV1.currentOfRecordWide (toRecord w))) := by
    unfold AspisR1S4ReaderEActualWideCanonicalV1.actualCurrentWideDecoder
    rw [hr]
    rfl
  have hcan := AspisR1S4ReaderEActualWideCanonicalV1.actualCurrentWideDecoder_success_canonical bytes _ hc
  simpa only [FlatCanonical,AspisR1S4ReaderEActualWideCanonicalV1.currentWideCanonical,
    AspisR1S4ReaderEActualWideCanonicalV1.currentOfRecordWide,
    AspisR1S4ReaderEActualWideCanonicalV1.currentOfRecordQM,toRecord,toOwned,toOwnedQM,toOwnedCM,
    AspisR1S9OwnedFromLimbsMapV1.wideToParser,AspisR1S9OwnedFromLimbsMapV1.qmToParser,
    AspisR1S9OwnedFromLimbsMapV1.cmToParser] using hcan

private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Actual field call supplies ALL its own offset/window/decoder witnesses.
Wrapping offsets are retained exactly; no index bound is silently assumed. -/
theorem field_success_source_decoder (bytes : Slice U8) (i : Usize) (w : NativeW)
    (h : weights.field bytes i=.ok w) :
    ∃ (start next finish : Usize) (selected : Slice U8),
      start=Usize.wrapping_mul i 32#usize ∧ next=Usize.wrapping_add i 1#usize ∧
      finish=Usize.wrapping_mul next 32#usize ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes {start:=start,«end»:=finish}=.ok selected ∧
      aspis_core.field.wide_exact.WideExact.from_le_bytes selected=.ok (some w) := by
  unfold weights.field at h
  obtain ⟨start,hs,h⟩ := bind_success _ _ _ h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  obtain ⟨finish,hf,h⟩ := bind_success _ _ _ h
  obtain ⟨selected,hselected,h⟩ := bind_success _ _ _ h
  obtain ⟨o,hdecoder,hunwrap⟩ := bind_success _ _ _ h
  cases o with
  | none => simp only [core.option.Option.unwrap] at hunwrap; cases hunwrap
  | some value =>
    have heq : value=w := Result.ok.inj hunwrap
    subst w
    exact ⟨start,next,finish,selected,(Result.ok.inj hs).symm,(Result.ok.inj hn).symm,
      (Result.ok.inj hf).symm,hselected,hdecoder⟩

/-- Canonicality for EVERY successful actual field call, including wrapping
index aliases. Whole checked-reader/index correspondence is separate. -/
theorem field_success_flat_canonical (bytes : Slice U8) (i : Usize) (w : NativeW)
    (h : weights.field bytes i=.ok w) : FlatCanonical w := by
  obtain ⟨start,next,finish,selected,hs,hn,hf,hselected,hdecoder⟩ := field_success_source_decoder bytes i w h
  exact native_decoder_success_canonical selected w hdecoder

theorem field_success_native_canonical (bytes : Slice U8) (i : Usize) (w : NativeW)
    (h : weights.field bytes i=.ok w) : AspisR1S9ActualPairWideCanonicalV1.Canonical w := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := field_success_flat_canonical bytes i w h
  change ((w.c0.c0.a.val < 2147483647 ∧ w.c0.c0.b.val < 2147483647) ∧
    (w.c0.c1.a.val < 2147483647 ∧ w.c0.c1.b.val < 2147483647)) ∧
    ((w.c1.c0.a.val < 2147483647 ∧ w.c1.c0.b.val < 2147483647) ∧
    (w.c1.c1.a.val < 2147483647 ∧ w.c1.c1.b.val < 2147483647))
  exact ⟨⟨⟨h0,h1⟩,h2,h3⟩,⟨⟨h4,h5⟩,h6,h7⟩⟩

/-- Every one of the32 actual source byte reads is in-bounds and succeeds,
derived from THIS field execution and the existing exact decoder provenance. -/
theorem field_success_all_byte_reads (bytes : Slice U8) (i : Usize) (w : NativeW)
    (h : weights.field bytes i=.ok w) :
    ∃ selected : Slice U8,
      aspis_core.field.wide_exact.WideExact.from_le_bytes selected=.ok (some w) ∧
      selected.val.length=32 ∧
      ∀ (j : Usize), j.val < 32 → ∃ b : U8, Slice.index_usize selected j=.ok b := by
  obtain ⟨start,next,finish,selected,hs,hn,hf,hselected,hdecoder⟩ := field_success_source_decoder bytes i w h
  have hm := native_bytes_maps_record selected
  rw [hdecoder] at hm
  have hr : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected=.ok (some (toRecord w)) := hm.symm
  have hlen := (AspisR1.ExtractedRecordByteCanonicality.slice_success selected (toRecord w) hr).1
  refine ⟨selected,hdecoder,hlen,?_⟩
  intro j hj
  have hb : j.val < selected.length := by simpa only [Slice.length,hlen] using hj
  obtain ⟨b,hread,hvalue⟩ := WP.spec_imp_exists (Slice.index_usize_spec selected j hb)
  exact ⟨b,hread⟩

#print axioms native_decoder_success_canonical
#print axioms field_success_source_decoder
#print axioms field_success_flat_canonical
#print axioms field_success_native_canonical
#print axioms field_success_all_byte_reads
end AspisR1S9NativeFieldActualCanonicalV1
