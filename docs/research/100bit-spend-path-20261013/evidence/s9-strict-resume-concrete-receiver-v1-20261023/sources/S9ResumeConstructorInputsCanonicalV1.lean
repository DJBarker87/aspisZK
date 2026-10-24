import S9ResumeSemanticAlphaCanonicalV1
import S9ResumeCircleReadsCanonicalV1
import S9ResumeFinishNativePairBindingV1
import S9FinishActualConstructorSlotV1
import S9ConstructorV3FactorsCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeConstructorInputsCanonicalV1
open AspisR1S9ResumeFinishNativePairBindingV1
abbrev mapArray := @AspisR1S9CandidateFoldMapPrimitivesV1.mapArray

def withConstructorReaders (ops : AspisR1Stage2.ResumeOps) : AspisR1Stage2.ResumeOps :=
  AspisR1S9ResumeSemanticAlphaCanonicalV1.withSemanticAlpha
    (AspisR1S9ResumeCircleReadsCanonicalV1.withStrictReaders ops)

def inputAlpha (p : AspisR1Stage2.verifier.Prepared) :=
  mapArray AspisR1S9FinishActualConstructorSlotV1.toCtorQM (stagePrepared p).semantic_alpha

def inputZ (p : AspisR1Stage2.verifier.Prepared) :=
  mapArray AspisR1S9FinishActualConstructorSlotV1.toCtorPoint (stagePrepared p).z

private theorem mapped_read_source {A B : Type} {n : Usize} (f : A → B)
    (a : Array A n) (i : Usize) (v : B)
    (h : Array.index_usize (mapArray f a) i = .ok v) :
    ∃ original, Array.index_usize a i = .ok original ∧ f original = v := by
  have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result f a i
  rw [h] at hm
  cases hr : Array.index_usize a i with
  | fail e => rw [hr] at hm; cases hm
  | div => rw [hr] at hm; cases hm
  | ok original =>
    rw [hr] at hm
    exact ⟨original,rfl,Result.ok.inj hm⟩

private theorem array_read_mem {A : Type} {n : Usize} (a : Array A n) (i : Usize) (v : A)
    (h : Array.index_usize a i = .ok v) : v ∈ a.val := by
  unfold Array.index_usize at h
  cases hr : a[i]? with
  | none => simp [hr] at h
  | some original =>
    have hi : a.val[i.val]? = some original := by simpa using hr
    have hm := List.mem_of_getElem? hi
    rw [hr] at h
    have he : original = v := Result.ok.inj h
    exact he ▸ hm

private theorem stage_ctor_qm_canonical (q : AspisR1Stage2.aspis_core.field.QM31)
    (h : AspisR1S9ReaderKActualQMCanonicalV1.Canonical q) :
    AspisR1S9ConstructorV3Loop2InnerCanonicalV1.CanQ
      (AspisR1S9ConstructorV3Loop2InnerCanonicalV1.toProbeQ
        (AspisR1S9FinishActualConstructorSlotV1.toCtorQM (stageQM q))) := by
  rcases h with ⟨h0,h1,h2,h3⟩
  exact ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩

/-- Both canonical input contracts required by the actual V3 constructor now
come from the SAME resume with strict16-byte K reads/helper installed. No
sampler law, independent semantic-alpha/z canonicality or successful child
reader is assumed. Domain/distribution and whole runtime remain separate. -/
theorem resume_success_constructor_inputs_canonical
    (ops : AspisR1Stage2.ResumeOps) {H : Type}
    (digest : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (variant : AspisR1Stage2.transport.Variant) (hash : H)
    (p : AspisR1Stage2.verifier.Prepared) (acc : AspisR1Stage2.verifier.Accumulator)
    (h : AspisR1Stage2.verifier.resumeWithOps (withConstructorReaders ops)
      digest bytes proof publicInput variant hash = .ok (.Ok (p,acc))) :
    AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1.VectorCanonical (inputAlpha p) ∧
      AspisR1S9ConstructorV3PointScanBodyCanonicalV1.PointsCanonical (inputZ p) := by
  have halpha : ∀ (i : Usize) (q : AspisR1Stage2.aspis_core.field.QM31),
      Array.index_usize p.semantic_alpha i = .ok q →
      AspisR1S9ReaderKActualQMCanonicalV1.Canonical q := by
    intro i q hread
    exact AspisR1S9ResumeSemanticAlphaCanonicalV1.successful_resume_semantic_alpha_canonical
      (AspisR1S9ResumeCircleReadsCanonicalV1.withStrictReaders ops) digest bytes proof publicInput
      variant hash p acc h i q hread
  have hcircle : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S9ResumeCircleReadsCanonicalV1.withReaderK
        (AspisR1S9ResumeSemanticAlphaCanonicalV1.withSemanticAlpha
          (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops)))
      digest bytes proof publicInput variant hash = .ok (.Ok (p,acc)) := h
  obtain ⟨x0,y0,x1,y1,hz,hx0,hy0,hx1,hy1⟩ :=
    AspisR1S9ResumeCircleReadsCanonicalV1.resume_success_circle_coordinates_canonical
      (AspisR1S9ResumeSemanticAlphaCanonicalV1.withSemanticAlpha
        (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops))
      digest bytes proof publicInput variant hash p acc hcircle
  constructor
  · intro i probe hread
    obtain ⟨cq,hcq,hprobe⟩ := mapped_read_source
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.toProbeQ (inputAlpha p) i probe hread
    obtain ⟨fq,hfq,hctor⟩ := mapped_read_source
      AspisR1S9FinishActualConstructorSlotV1.toCtorQM (stagePrepared p).semantic_alpha i cq hcq
    obtain ⟨sq,hsq,hfinish⟩ := mapped_read_source stageQM p.semantic_alpha i fq hfq
    rw [← hprobe,← hctor,← hfinish]
    exact stage_ctor_qm_canonical sq (halpha i sq hsq)
  · intro i point hread
    obtain ⟨fp,hfp,hpoint⟩ := mapped_read_source
      AspisR1S9FinishActualConstructorSlotV1.toCtorPoint (stagePrepared p).z i point hread
    obtain ⟨sp,hsp,hfinish⟩ := mapped_read_source stagePoint p.z i fp hfp
    have hm := array_read_mem p.z i sp hsp
    rw [hz] at hm
    change sp ∈ [⟨x0,y0⟩,⟨x1,y1⟩] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rw [← hpoint,← hfinish]
    rcases hm with rfl | rfl
    · exact ⟨stage_ctor_qm_canonical x0 hx0,stage_ctor_qm_canonical y0 hy0⟩
    · exact ⟨stage_ctor_qm_canonical x1 hx1,stage_ctor_qm_canonical y1 hy1⟩

#print axioms resume_success_constructor_inputs_canonical
end AspisR1S9ResumeConstructorInputsCanonicalV1
