import ClaimReadGeneratedSuccess
import Stage2GeneratedPrefixCallCanonicality

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2ResumeClaimReadCanonicality

abbrev SWide := AspisR1Stage2ResumeSuffix.aspis_core.field.WideExact
abbrev SQM := AspisR1Stage2ResumeSuffix.aspis_core.field.QM31
abbrev SReader := AspisR1Stage2ResumeSuffix.verifier.Reader
abbrev RWide := AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.ReaderWide
abbrev RQM := AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.ReaderQM

def suffixWideToReader (w : SWide) : RWide :=
  ⟨⟨⟨w.c0.c0.a, w.c0.c0.b⟩, ⟨w.c0.c1.a, w.c0.c1.b⟩⟩,
    ⟨⟨w.c1.c0.a, w.c1.c0.b⟩, ⟨w.c1.c1.a, w.c1.c1.b⟩⟩⟩

def suffixQMToReader (q : SQM) : RQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem suffix_wide_decode_canonical (bytes : Slice Std.U8) (w : SWide)
    (h : AspisR1Stage2ResumeSuffix.aspis_core.field.WideExact.from_le_bytes bytes = .ok (some w)) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
      (suffixWideToReader w) := by
  unfold AspisR1Stage2ResumeSuffix.aspis_core.field.WideExact.from_le_bytes
    AspisR1Stage2ResumeSuffix.mapDecoderOption at h
  cases hp : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes with
  | fail e => simp [hp] at h
  | div => simp [hp] at h
  | ok o =>
    cases o with
    | none => simp [hp] at h
    | some actual =>
      simp only [hp, Option.map_some, Result.ok.injEq, Option.some.injEq] at h
      subst w
      have hactual :
          AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualWideDecoder bytes =
            .ok (some (AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.wideOfActual actual)) := by
        rfl
      have hc := AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualWideDecoder_success_canonical
        bytes _ hactual
      simpa [suffixWideToReader, AspisR1Stage2ResumeSuffix.actualWideToGenerated,
        AspisR1Stage2ResumeSuffix.recordQMToGenerated,
        AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.wideOfActual,
        AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.qmOfRecord] using hc

theorem suffix_qm_decode_canonical (bytes : Slice Std.U8) (q : SQM)
    (h : AspisR1Stage2ResumeSuffix.aspis_core.field.QM31.from_le_bytes bytes = .ok (some q)) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerQMCanonical
      (suffixQMToReader q) := by
  unfold AspisR1Stage2ResumeSuffix.aspis_core.field.QM31.from_le_bytes
    AspisR1Stage2ResumeSuffix.mapDecoderOption at h
  cases hp : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes with
  | fail e => simp [hp] at h
  | div => simp [hp] at h
  | ok o =>
    cases o with
    | none => simp [hp] at h
    | some actual =>
      simp only [hp, Option.map_some, Result.ok.injEq, Option.some.injEq] at h
      subst q
      have hactual :
          AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualQMDecoder bytes =
            .ok (some (AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.qmOfActual actual)) := by
        rfl
      have hc := AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualQMDecoder_success_canonical
        bytes _ hactual
      simpa [suffixQMToReader, AspisR1Stage2ResumeSuffix.actualQMToGenerated,
        AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.qmOfActual] using hc

theorem successful_reader_e_has_canonical_output (r r' : SReader) (w : SWide)
    (h : AspisR1Stage2ResumeSuffix.verifier.Reader.e r = .ok (.Ok w, r')) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
      (suffixWideToReader w) := by
  unfold AspisR1Stage2ResumeSuffix.verifier.Reader.e at h
  obtain ⟨pair, hp, h⟩ := bind_success _ _ _ h
  rcases pair with ⟨bytes, rr⟩
  simp only [lift, bind_tc_ok] at h
  obtain ⟨o, ho, h⟩ := bind_success _ _ _ h
  cases o with
  | none => simp only [AspisR1Stage2ResumeSuffix.core.option.Option.ok_or, bind_tc_ok] at h; cases h
  | some v =>
    simp only [AspisR1Stage2ResumeSuffix.core.option.Option.ok_or, bind_tc_ok,
      Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨hv, hr⟩ := h
    subst v
    subst rr
    exact suffix_wide_decode_canonical bytes w ho

theorem successful_reader_k_has_canonical_output (r r' : SReader) (q : SQM)
    (h : AspisR1Stage2ResumeSuffix.verifier.Reader.k r = .ok (.Ok q, r')) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerQMCanonical
      (suffixQMToReader q) := by
  unfold AspisR1Stage2ResumeSuffix.verifier.Reader.k at h
  obtain ⟨pair, hp, h⟩ := bind_success _ _ _ h
  rcases pair with ⟨bytes, rr⟩
  simp only [lift, bind_tc_ok] at h
  obtain ⟨o, ho, h⟩ := bind_success _ _ _ h
  cases o with
  | none => simp only [AspisR1Stage2ResumeSuffix.core.option.Option.ok_or, bind_tc_ok] at h; cases h
  | some v =>
    simp only [AspisR1Stage2ResumeSuffix.core.option.Option.ok_or, bind_tc_ok,
      Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨hv, hr⟩ := h
    subst v
    subst rr
    exact suffix_qm_decode_canonical bytes q ho

#print axioms successful_reader_e_has_canonical_output
#print axioms successful_reader_k_has_canonical_output

end AspisR1Stage2ResumeClaimReadCanonicality
