import F3L_LateFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_TypedFields
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem fields (Q : LiteralTranscript.Prefix)
    (decoded : R0P.Public SemanticPublicWire.M31)
    (m31 m32 : LiteralTranscript.Message)
    (queries : List Nat) (rho : LiteralTranscript.E) (s31 s32 : State)
    (data : MatchingSupport.Data LiteralTranscript.E)
    (parsedPublic : SemanticPublicWire.parsePublic Q.statement.pubBytes=some decoded)
    (row31 : Q.rounds[31]?=some (m31,(TranscriptView.Value.queries (.ok queries),s31)))
    (row32 : Q.rounds[32]?=some (m32,(TranscriptView.Value.ordinary rho,s32)))
    (v31 : LiteralTranscript.valid 31 m31) (v32 : LiteralTranscript.valid 32 m32) :
    ∃ i,D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix Q) i := by
  apply F3L_LateFields.exists_fields _ decoded m31 m32 queries rho s31 s32 data parsedPublic
  · simp only [LiteralTranscript.erasePrefix,List.getElem?_map,row31,Option.map_some]
  · simp only [LiteralTranscript.erasePrefix,List.getElem?_map,row32,Option.map_some]
  · exact v31
  · exact v32

#print axioms fields
end AspisR1.F3L_TypedFields
end
