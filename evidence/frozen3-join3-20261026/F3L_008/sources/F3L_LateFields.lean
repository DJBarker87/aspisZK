import F3L_InputDiscovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_LateFields
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Construct the instance carrier from actual public and late sampler rows.
Arithmetic data is deliberately arbitrary here: Fields does not observe it. -/
theorem exists_fields (tr : RawCutTranscriptRun.ErasedPrefix)
    (decoded : R0P.Public SemanticPublicWire.M31)
    (m31 m32 : LiteralTranscript.Message)
    (queries : List Nat) (rho : LiteralTranscript.E) (s31 s32 : State)
    (data : MatchingSupport.Data LiteralTranscript.E)
    (parsedPublic : SemanticPublicWire.parsePublic tr.statement.pubBytes=some decoded)
    (row31 : tr.rounds[31]?=some (LiteralTranscript.erase m31,
      (TranscriptView.Value.queries (.ok queries),s31)))
    (row32 : tr.rounds[32]?=some (LiteralTranscript.erase m32,
      (TranscriptView.Value.ordinary rho,s32)))
    (v31 : LiteralTranscript.valid 31 m31) (v32 : LiteralTranscript.valid 32 m32) :
    ∃ i, D0InstanceAdmission.Fields tr i := by
  refine ⟨{decoded:=decoded,data:=data,m31:=m31,queryBytes:=queries,state31:=s31,m32:=m32,rho:=rho,state32:=s32},?_⟩
  exact ⟨parsedPublic,row31,row32,v31,v32⟩

#print axioms exists_fields
#print RecordedBinaryExperimentBin.SourceInputs
end AspisR1.F3L_LateFields
end
