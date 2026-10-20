import Stage2ReaderSuccess
import ExtractedRecordByteCanonicality
import AspisR1DecodeKFullParserCanonicalityCMQ

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality

open AspisR1Stage2AdoptedReader
open AspisR1.ExtractedRecordByteCanonicality

abbrev ReaderQM := aspis_core.field.QM31
abbrev ReaderWide := aspis_core.field.WideExact
abbrev ActualQM := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev RecordQM := AspisR1RecordParser.field.QM31
abbrev ActualWide := AspisR1RecordParser.field.wide_exact.WideExact

def qmOfActual (q : ActualQM) : ReaderQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def qmOfRecord (q : RecordQM) : ReaderQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def wideOfActual (w : ActualWide) : ReaderWide :=
  ⟨qmOfRecord w.c0, qmOfRecord w.c1⟩

def readerQMCanonical (q : ReaderQM) : Prop :=
  q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
  q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

def readerWideCanonical (w : ReaderWide) : Prop :=
  readerQMCanonical w.c0 ∧ readerQMCanonical w.c1

private def mapDecodeResult {A B : Type} (f : A → B) (r : Result (Option A)) : Result (Option B) :=
  match r with
  | .ok o => .ok (o.map f)
  | .fail e => .fail e
  | .div => .div

def actualQMDecoder (bytes : Slice Std.U8) : Result (Option ReaderQM) :=
  mapDecodeResult qmOfActual
    (AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes)

def actualWideDecoder (bytes : Slice Std.U8) : Result (Option ReaderWide) :=
  mapDecodeResult wideOfActual
    (AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes)

def actualReaderDecoders
    (unwrap : {n : Usize} →
      core.result.Result (Array Std.U8 n) core.array.TryFromSliceError →
      Result (Array Std.U8 n)) : ReaderDecoders where
  unwrapArray := unwrap
  wide := actualWideDecoder
  qm := actualQMDecoder

theorem actualQMDecoder_success_canonical (bytes : Slice Std.U8) (q : ReaderQM)
    (h : actualQMDecoder bytes = .ok (some q)) : readerQMCanonical q := by
  unfold actualQMDecoder mapDecodeResult at h
  cases hs : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok o =>
      cases o with
      | none => simp [hs] at h
      | some q0 =>
          simp only [hs, Option.map_some, Result.ok.injEq, Option.some.injEq] at h
          cases h
          have hc := AspisR1DecodeKFullParserCanonicality.qm31_from_le_bytes_success_canonical
            bytes q0 hs
          rcases hc with ⟨h0,h1,h2,h3⟩
          have hP : AspisR1DecodeKFullV10.aspis_core.field.P.val = 2147483647 := by
            unfold AspisR1DecodeKFullV10.aspis_core.field.P
            rfl
          exact ⟨by simpa [qmOfActual, hP] using h0,
            by simpa [qmOfActual, hP] using h1,
            by simpa [qmOfActual, hP] using h2,
            by simpa [qmOfActual, hP] using h3⟩

theorem actualWideDecoder_success_canonical (bytes : Slice Std.U8) (w : ReaderWide)
    (h : actualWideDecoder bytes = .ok (some w)) : readerWideCanonical w := by
  unfold actualWideDecoder mapDecodeResult at h
  cases hs : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok o =>
      cases o with
      | none => simp [hs] at h
      | some w0 =>
          simp only [hs, Option.map_some, Result.ok.injEq, Option.some.injEq] at h
          subst w
          obtain ⟨_, arr, _, hlimbs, hw⟩ :=
            AspisR1.ExtractedRecordByteCanonicality.slice_success bytes w0 hs
          subst w0
          have h0 := hlimbs (⟨0, by decide⟩ : Fin 8)
          have h1 := hlimbs (⟨1, by decide⟩ : Fin 8)
          have h2 := hlimbs (⟨2, by decide⟩ : Fin 8)
          have h3 := hlimbs (⟨3, by decide⟩ : Fin 8)
          have h4 := hlimbs (⟨4, by decide⟩ : Fin 8)
          have h5 := hlimbs (⟨5, by decide⟩ : Fin 8)
          have h6 := hlimbs (⟨6, by decide⟩ : Fin 8)
          have h7 := hlimbs (⟨7, by decide⟩ : Fin 8)
          simpa [readerWideCanonical, readerQMCanonical, wideOfActual, qmOfRecord,
            AspisR1.ExtractedRecordLimbCanonicality.packed] using
            (show (wordLE arr 0).val < 2147483647 ∧ (wordLE arr 1).val < 2147483647 ∧
              (wordLE arr 2).val < 2147483647 ∧ (wordLE arr 3).val < 2147483647 ∧
              (wordLE arr 4).val < 2147483647 ∧ (wordLE arr 5).val < 2147483647 ∧
              (wordLE arr 6).val < 2147483647 ∧ (wordLE arr 7).val < 2147483647 from
              ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩)

#print axioms actualQMDecoder_success_canonical
#print axioms actualWideDecoder_success_canonical

end AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality
