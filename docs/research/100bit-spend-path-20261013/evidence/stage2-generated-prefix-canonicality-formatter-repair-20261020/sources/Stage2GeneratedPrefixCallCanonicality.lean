import Stage2GeneratedPrefixCallSuccess
import Stage2ResumePrefixCanonicalOutputs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.GeneratedPrefixCallCanonicality

abbrev GenWide := AspisR1Stage2AdoptedResume.aspis_core.field.WideExact
abbrev GenQM := AspisR1Stage2AdoptedResume.aspis_core.field.QM31
abbrev ReadWide := AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.ReaderWide
abbrev ReadQM := AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.ReaderQM

private def genQMToRead (q : GenQM) : ReadQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

private def genWideToRead (w : GenWide) : ReadWide :=
  ⟨genQMToRead w.c0, genQMToRead w.c1⟩

private def mapGeneratedDecoderOption {A B : Type} (f : A → B)
    (r : Result (Option A)) : Result (Option B) := do
  match r with
  | .ok o => ok (o.map f)
  | .fail e => .fail e
  | .div => .div

private def mapConcreteDecoderOption {A B : Type} (f : A → B)
    (r : Result (Option A)) : Result (Option B) :=
  match r with
  | .ok o => .ok (o.map f)
  | .fail e => .fail e
  | .div => .div

private theorem generated_wide_decode_eq (bytes : Slice Std.U8) :
    AspisR1Stage2AdoptedResume.aspis_core.field.WideExact.from_le_bytes bytes =
      mapGeneratedDecoderOption AspisR1Stage2AdoptedResume.actualWideToGenerated
        (AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes) := rfl

private theorem generated_qm_decode_eq (bytes : Slice Std.U8) :
    AspisR1Stage2AdoptedResume.aspis_core.field.QM31.from_le_bytes bytes =
      mapGeneratedDecoderOption AspisR1Stage2AdoptedResume.actualQMToGenerated
        (AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes) := rfl

private theorem actual_wide_decode_eq (bytes : Slice Std.U8) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualWideDecoder bytes =
      mapConcreteDecoderOption AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.wideOfActual
        (AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes) := rfl

private theorem actual_qm_decode_eq (bytes : Slice Std.U8) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualQMDecoder bytes =
      mapConcreteDecoderOption AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.qmOfActual
        (AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes) := rfl

private theorem wide_decode_map_agrees
    (w : AspisR1RecordParser.field.wide_exact.WideExact) :
    genWideToRead (AspisR1Stage2AdoptedResume.actualWideToGenerated w) =
      AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.wideOfActual w := by
  rfl

private theorem qm_decode_map_agrees
    (q : AspisR1DecodeKFullV10.aspis_core.field.QM31) :
    genQMToRead (AspisR1Stage2AdoptedResume.actualQMToGenerated q) =
      AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.qmOfActual q := by
  rfl

theorem generated_wide_decode_canonical (bytes : Slice Std.U8) (value : GenWide)
    (h : AspisR1Stage2AdoptedResume.aspis_core.field.WideExact.from_le_bytes bytes =
      .ok (some value)) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
      (genWideToRead value) := by
  rw [generated_wide_decode_eq] at h
  cases hp : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes with
  | fail e => simp [mapGeneratedDecoderOption, hp] at h
  | div => simp [mapGeneratedDecoderOption, hp] at h
  | ok decoded =>
      cases decoded with
      | none => simp [mapGeneratedDecoderOption, hp] at h
      | some actual =>
          simp [mapGeneratedDecoderOption, hp] at h
          cases h
          have hactual :
              AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualWideDecoder bytes =
                .ok (some
                  (AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.wideOfActual actual)) := by
            rw [actual_wide_decode_eq, hp]
            rfl
          have hcanonical :=
            AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualWideDecoder_success_canonical
              bytes _ hactual
          rw [wide_decode_map_agrees]
          exact hcanonical

theorem generated_qm_decode_canonical (bytes : Slice Std.U8) (value : GenQM)
    (h : AspisR1Stage2AdoptedResume.aspis_core.field.QM31.from_le_bytes bytes =
      .ok (some value)) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerQMCanonical
      (genQMToRead value) := by
  rw [generated_qm_decode_eq] at h
  cases hp : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes with
  | fail e => simp [mapGeneratedDecoderOption, hp] at h
  | div => simp [mapGeneratedDecoderOption, hp] at h
  | ok decoded =>
      cases decoded with
      | none => simp [mapGeneratedDecoderOption, hp] at h
      | some actual =>
          simp [mapGeneratedDecoderOption, hp] at h
          cases h
          have hactual :
              AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualQMDecoder bytes =
                .ok (some
                  (AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.qmOfActual actual)) := by
            rw [actual_qm_decode_eq, hp]
            rfl
          have hcanonical :=
            AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.actualQMDecoder_success_canonical
              bytes _ hactual
          rw [qm_decode_map_agrees]
          exact hcanonical

theorem successful_generated_prefix_outputs_canonical
    (bytes : Slice Std.U8)
    (state root0 root1 : Array Std.U8 32#usize)
    (gamma kappa alpha0 alpha1 : GenWide) (rho : GenQM) (finalAt : Usize)
    (h : AspisR1Stage2AdoptedResume.verifier.resume_read_prefix bytes =
      ok (.Ok (state, Array.make 2#usize [root0, root1], gamma, kappa,
        Array.make 2#usize [alpha0, alpha1], rho, finalAt))) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
        (genWideToRead gamma) ∧
      AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
        (genWideToRead kappa) ∧
      AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
        (genWideToRead alpha0) ∧
      AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
        (genWideToRead alpha1) ∧
      AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerQMCanonical
        (genQMToRead rho) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8,
    _, _, _, hgamma, hkappa, halpha0, halpha1, hrho, _⟩ :=
      AspisR1Stage2AdoptedReader.GeneratedPrefixCallSuccess.generated_prefix_call_success
        bytes state root0 root1 gamma kappa alpha0 alpha1 rho finalAt h
  obtain ⟨gammaBytes, _, hgammaDecode⟩ :=
    AspisR1Stage2AdoptedReader.GeneratedPrefixSuccessInversion.generated_wide_success
      r3 r4 gamma hgamma
  obtain ⟨kappaBytes, _, hkappaDecode⟩ :=
    AspisR1Stage2AdoptedReader.GeneratedPrefixSuccessInversion.generated_wide_success
      r4 r5 kappa hkappa
  obtain ⟨alpha0Bytes, _, halpha0Decode⟩ :=
    AspisR1Stage2AdoptedReader.GeneratedPrefixSuccessInversion.generated_wide_success
      r5 r6 alpha0 halpha0
  obtain ⟨alpha1Bytes, _, halpha1Decode⟩ :=
    AspisR1Stage2AdoptedReader.GeneratedPrefixSuccessInversion.generated_wide_success
      r6 r7 alpha1 halpha1
  obtain ⟨rhoBytes, _, hrhoDecode⟩ :=
    AspisR1Stage2AdoptedReader.GeneratedPrefixSuccessInversion.generated_qm_success
      r7 r8 rho hrho
  exact ⟨generated_wide_decode_canonical gammaBytes.to_slice gamma hgammaDecode,
    generated_wide_decode_canonical kappaBytes.to_slice kappa hkappaDecode,
    generated_wide_decode_canonical alpha0Bytes.to_slice alpha0 halpha0Decode,
    generated_wide_decode_canonical alpha1Bytes.to_slice alpha1 halpha1Decode,
    generated_qm_decode_canonical rhoBytes.to_slice rho hrhoDecode⟩

#print axioms successful_generated_prefix_outputs_canonical

end AspisR1Stage2AdoptedReader.GeneratedPrefixCallCanonicality
