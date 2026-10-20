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
    (r : core.result.Result SWide
      AspisR1Stage2ResumeSuffix.verifier.Error) :
    core.result.Result PWide
      AspisR1Stage2AdoptedResume.verifier.Error :=
  match r with
  | .Ok w => .Ok (suffixWideToPrefix w)
  | .Err e => .Err (suffixErrorToPrefix e)

def mapSuffixQMResult
    (r : core.result.Result SQM
      AspisR1Stage2ResumeSuffix.verifier.Error) :
    core.result.Result PQM
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

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Successful return from the generated straight-line cut forces all three
    concrete Reader calls to return successful decodes, in source order. -/
theorem successful_claim_rhs_power_calls
    (bytes : Slice Std.U8) (startAt : Std.Usize)
    (claim rhs : SWide) (power : SQM) (endAt : Std.Usize)
    (h : AspisR1Stage2ResumeSuffix.verifier.resume_read_claim_rhs_power bytes startAt =
      .ok (.Ok (claim, rhs, power, endAt))) :
    ∃ r1 r2 r3,
      AspisR1Stage2ResumeSuffix.verifier.Reader.e
          ({ bytes := bytes, «at» := startAt } : SReader) = .ok (.Ok claim, r1) ∧
      AspisR1Stage2ResumeSuffix.verifier.Reader.e r1 = .ok (.Ok rhs, r2) ∧
      AspisR1Stage2ResumeSuffix.verifier.Reader.k r2 = .ok (.Ok power, r3) ∧
      r3.«at» = endAt := by
  unfold AspisR1Stage2ResumeSuffix.verifier.resume_read_claim_rhs_power at h
  obtain ⟨pair1, hread1, hrest1⟩ := bind_success _ _ _ h
  rcases pair1 with ⟨result1, r1⟩
  cases result1 with
  | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        at hrest1
  | Ok claimValue =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        bind_tc_ok] at hrest1
      obtain ⟨pair2, hread2, hrest2⟩ := bind_success _ _ _ hrest1
      rcases pair2 with ⟨result2, r2⟩
      cases result2 with
      | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at hrest2
      | Ok rhsValue =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            bind_tc_ok] at hrest2
          obtain ⟨pair3, hread3, hrest3⟩ := bind_success _ _ _ hrest2
          rcases pair3 with ⟨result3, r3⟩
          cases result3 with
          | Err e =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                at hrest3
          | Ok powerValue =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok, Result.ok.injEq,
                core.result.Result.Ok.injEq,
                Prod.mk.injEq] at hrest3
              rcases hrest3 with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨r1, r2, r3, hread1, hread2, hread3, rfl⟩

theorem successful_claim_rhs_power_outputs_canonical
    (bytes : Slice Std.U8) (startAt : Std.Usize)
    (claim rhs : SWide) (power : SQM) (endAt : Std.Usize)
    (h : AspisR1Stage2ResumeSuffix.verifier.resume_read_claim_rhs_power bytes startAt =
      .ok (.Ok (claim, rhs, power, endAt))) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
        (prefixWideToReader (suffixWideToPrefix claim)) ∧
      AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
        (prefixWideToReader (suffixWideToPrefix rhs)) ∧
      AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerQMCanonical
        (prefixQMToReader (suffixQMToPrefix power)) := by
  obtain ⟨r1, r2, r3, hclaim, hrhs, hpower, _⟩ :=
    successful_claim_rhs_power_calls bytes startAt claim rhs power endAt h
  exact ⟨suffix_reader_e_success_canonical _ _ _ hclaim,
    suffix_reader_e_success_canonical _ _ _ hrhs,
    suffix_reader_k_success_canonical _ _ _ hpower⟩

#print axioms reader_e_map
#print axioms reader_k_map
#print axioms suffix_reader_e_success_canonical
#print axioms suffix_reader_k_success_canonical
#print axioms successful_claim_rhs_power_calls
#print axioms successful_claim_rhs_power_outputs_canonical

end AspisR1Stage2ResumeClaimReadDecoderMap
