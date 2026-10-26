import F3L_FieldsTransport
import F3L_ParsedSampler
import F3L_ModelRead
import F3L_OpeningFields
import F3K_OpeningQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_FullFields
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

theorem fields {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : F3K_OpeningCalls.Calls D B embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (pub : LiteralTranscript.Public) (data : MatchingSupport.Data LiteralTranscript.E)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (header : OraclePortHeader.accepts p.wire=true) (canonical : scan p.wire)
    (typed : ∃ decoded,SemanticPrefixCodec.decodeFrom 0 (p.semantic.take 25)=some decoded)
    (tag : pub.tag=p.wire[8]?.getD 0)
    (parsedPublic : ∃ decoded,SemanticPublicWire.parsePublic pub.pubBytes=some decoded)
    (rootBytes : bytes root=root0 p)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 0 27 (FS.emptyPrefix pub))).2)=decodeState c.t0.state) :
    let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program
      (F3J_InputRows.proof p root w bound) 0 33 (FS.emptyPrefix pub))).2
    ∃ i,D0InstanceAdmission.Fields tr i := by
  let pf := F3J_InputRows.proof p root w bound
  let P27 := (eval H (F3J_SamplerRun.program pf 0 27 (FS.emptyPrefix pub))).2
  have length := F3J_SamplerRun.length H pf 0 27 (FS.emptyPrefix pub)
  simp only [FS.emptyPrefix,List.length_nil,Nat.zero_add] at length
  have publicP := F3L_ParsedSampler.parsed H pf 27 pub parsedPublic
  have fields := F3L_OpeningFields.fields c H backend root w bound P27 length publicP data state
  have transported := F3L_FieldsTransport.fields H pf 0 27 6 (FS.emptyPrefix pub) fields
  simp only [Nat.zero_add,Nat.reduceAdd] at transported
  exact transported

#print axioms fields
end AspisR1.F3L_FullFields
end
