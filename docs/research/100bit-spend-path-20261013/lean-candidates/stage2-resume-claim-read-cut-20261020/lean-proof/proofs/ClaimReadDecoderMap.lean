import Stage2GeneratedPrefixCallCanonicality
import AspisR1Stage2ResumeSuffix.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2ResumeClaimReadDecoderMap

abbrev PWide := AspisR1Stage2AdoptedResume.aspis_core.field.WideExact
abbrev PQM := AspisR1Stage2AdoptedResume.aspis_core.field.QM31
abbrev SWide := AspisR1Stage2ResumeSuffix.aspis_core.field.WideExact
abbrev SQM := AspisR1Stage2ResumeSuffix.aspis_core.field.QM31
abbrev SReader := AspisR1Stage2ResumeSuffix.verifier.Reader
abbrev PReader := AspisR1Stage2AdoptedResume.verifier.Reader

def suffixQMToPrefix (q : SQM) : PQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def suffixWideToPrefix (w : SWide) : PWide :=
  ⟨suffixQMToPrefix w.c0, suffixQMToPrefix w.c1⟩

def prefixQMToReader (q : PQM) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.ReaderQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def prefixWideToReader (w : PWide) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.ReaderWide :=
  ⟨prefixQMToReader w.c0, prefixQMToReader w.c1⟩

def suffixReaderToPrefix (r : SReader) : PReader :=
  ⟨r.bytes, r.«at»⟩

def suffixErrorToPrefix (e : AspisR1Stage2ResumeSuffix.verifier.Error) :
    AspisR1Stage2AdoptedResume.verifier.Error :=
  match e with
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

def mapOuter {A B : Type} (f : A → B) (r : Result A) : Result B :=
  match r with
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

def mapSuffixWideResult
    (r : AspisR1Stage2ResumeSuffix.core.result.Result SWide
      AspisR1Stage2ResumeSuffix.verifier.Error) :
    AspisR1Stage2AdoptedResume.core.result.Result PWide
      AspisR1Stage2AdoptedResume.verifier.Error :=
  match r with
  | .Ok w => .Ok (suffixWideToPrefix w)
  | .Err e => .Err (suffixErrorToPrefix e)

def mapSuffixQMResult
    (r : AspisR1Stage2ResumeSuffix.core.result.Result SQM
      AspisR1Stage2ResumeSuffix.verifier.Error) :
    AspisR1Stage2AdoptedResume.core.result.Result PQM
      AspisR1Stage2AdoptedResume.verifier.Error :=
  match r with
  | .Ok q => .Ok (suffixQMToPrefix q)
  | .Err e => .Err (suffixErrorToPrefix e)

theorem reader_e_map (r : SReader) :
    mapOuter (fun p => (mapSuffixWideResult p.1, suffixReaderToPrefix p.2))
      (AspisR1Stage2ResumeSuffix.verifier.Reader.e r) =
    AspisR1Stage2AdoptedResume.verifier.Reader.e (suffixReaderToPrefix r) := by
  rfl

theorem reader_k_map (r : SReader) :
    mapOuter (fun p => (mapSuffixQMResult p.1, suffixReaderToPrefix p.2))
      (AspisR1Stage2ResumeSuffix.verifier.Reader.k r) =
    AspisR1Stage2AdoptedResume.verifier.Reader.k (suffixReaderToPrefix r) := by
  rfl

theorem suffix_reader_e_success_canonical (r r' : SReader) (w : SWide)
    (h : AspisR1Stage2ResumeSuffix.verifier.Reader.e r = .ok (.Ok w, r')) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
      (prefixWideToReader (suffixWideToPrefix w)) := by
  have hp : AspisR1Stage2AdoptedResume.verifier.Reader.e (suffixReaderToPrefix r) =
      .ok (.Ok (suffixWideToPrefix w), suffixReaderToPrefix r') := by
    have hm := congrArg
      (mapOuter (fun p => (mapSuffixWideResult p.1, suffixReaderToPrefix p.2))) h
    rw [reader_e_map] at hm
    simpa [mapSuffixWideResult] using hm
  obtain ⟨raw, hraw, hdecode⟩ :=
    AspisR1Stage2AdoptedReader.GeneratedPrefixSuccessInversion.generated_wide_success
      (suffixReaderToPrefix r) (suffixReaderToPrefix r')
      (suffixWideToPrefix w) hp
  exact AspisR1Stage2AdoptedReader.GeneratedPrefixCallCanonicality.generated_wide_decode_canonical
    raw.to_slice (suffixWideToPrefix w) hdecode

theorem suffix_reader_k_success_canonical (r r' : SReader) (q : SQM)
    (h : AspisR1Stage2ResumeSuffix.verifier.Reader.k r = .ok (.Ok q, r')) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerQMCanonical
      (prefixQMToReader (suffixQMToPrefix q)) := by
  have hp : AspisR1Stage2AdoptedResume.verifier.Reader.k (suffixReaderToPrefix r) =
      .ok (.Ok (suffixQMToPrefix q), suffixReaderToPrefix r') := by
    have hm := congrArg
      (mapOuter (fun p => (mapSuffixQMResult p.1, suffixReaderToPrefix p.2))) h
    rw [reader_k_map] at hm
    simpa [mapSuffixQMResult] using hm
  obtain ⟨raw, hraw, hdecode⟩ :=
    AspisR1Stage2AdoptedReader.GeneratedPrefixSuccessInversion.generated_qm_success
      (suffixReaderToPrefix r) (suffixReaderToPrefix r')
      (suffixQMToPrefix q) hp
  exact AspisR1Stage2AdoptedReader.GeneratedPrefixCallCanonicality.generated_qm_decode_canonical
    raw.to_slice (suffixQMToPrefix q) hdecode

#print axioms reader_e_map
#print axioms reader_k_map
#print axioms suffix_reader_e_success_canonical
#print axioms suffix_reader_k_success_canonical

end AspisR1Stage2ResumeClaimReadCanonicality
