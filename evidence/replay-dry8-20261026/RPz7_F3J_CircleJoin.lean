import RPz7_F3J_CircleCode
import RPz7_F3J_BlockSampler
import RPz7_F3J_ReseedSampler
import RPz7_F3J_RecordPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_CircleJoin
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation PreparedHashCode OraclePortCompactDraft

theorem first {Hash : Type} (D : aspis_core.Digest32 Hash) (B : FinishModel.Boundaries)
    (pre : r1_wire.Prefix) (record : r1_wire.ValidatedRecord)
    (before after : r1_wire.SemanticTranscript Hash) (point : aspis_core.circle.SecureCirclePoint)
    (read : r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record))
    (success : FinishModel.circle_validated B D before record=ok (.Ok point,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (records : p.semantic=pre.records.val.map (fun s => MultiproofConeCanonical.bytesOf s.val))
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (LiteralByteSampler.samp 25 P (pf 25)).toProgram).1=
      observe (run (S1SemanticCode.circleValidated B D before record)).1 ∧
    (eval H (LiteralByteSampler.samp 25 P (pf 25)).toProgram).2.2=decodeState after.state := by
  have row := (SourceFull25.validated_record_bytes pre 25#u8 record read).1
  obtain ⟨block,sampled,circle⟩ := PAln_CircleCalls.circle25_success B D before after record point row success
  obtain ⟨c⟩ := F3J_BlockCalls.from_success D before after 25#u8 record.framed block (by decide) sampled
  have model := F3J_BlockSampler.payload c H backend (by decide) (by decide) (by decide) (by decide)
    P (F3J_InputRows.proof p root w bound 25) ⟨rowBytes p 25,bound 25⟩
    (by rw [F3J_InputRows.erased,if_neg (by decide)]) state
    (F3J_RecordPayload.row_bytes pre record 25#u8 p records (by decide) read)
  have source := F3J_CircleCode.first record c B point row circle
  exact ⟨(congrArg Prod.fst model).trans source.symm,congrArg (fun r => r.2.2) model⟩

theorem second {Hash : Type} (D : aspis_core.Digest32 Hash) (B : FinishModel.Boundaries)
    (pre : r1_wire.Prefix) (record : r1_wire.ValidatedRecord)
    (before after : r1_wire.SemanticTranscript Hash) (point : aspis_core.circle.SecureCirclePoint)
    (read : r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok record))
    (success : FinishModel.circle_validated B D before record=ok (.Ok point,after))
    (hash : Hash) (out : transcript.Transcript Hash)
    (reseed : transcript.Transcript.new D hash after.state .S2=ok out)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (records : p.semantic=pre.records.val.map (fun s => MultiproofConeCanonical.bytesOf s.val))
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (tag : P.statement.tag=2)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (LiteralByteSampler.samp 26 P (pf 26)).toProgram).1=
      observe (run (S1SemanticCode.circleValidated B D before record)).1 ++
      observe (run (PreparedHashEffects.new effects D hash after.state .S2)).1 ∧
    (eval H (LiteralByteSampler.samp 26 P (pf 26)).toProgram).2.2=decodeState out.state := by
  have row := (SourceFull25.validated_record_bytes pre 26#u8 record read).1
  obtain ⟨block,sampled,circle⟩ := PAln_CircleCalls.circle26_success B D before after record point row success
  obtain ⟨c⟩ := F3J_BlockCalls.from_success D before after 26#u8 record.framed block (by decide) sampled
  have model := F3J_ReseedSampler.payload c H backend hash out reseed
    P (F3J_InputRows.proof p root w bound 26) ⟨rowBytes p 26,bound 26⟩ tag
    (by rw [F3J_InputRows.erased,if_neg (by decide)]) state
    (F3J_RecordPayload.row_bytes pre record 26#u8 p records (by decide) read)
  have source := F3J_CircleCode.second record c B point row circle
  have seed := (F3J_ReseedSource.reached D hash after.state out reseed H backend).2
  exact ⟨by rw [model,source,seed],congrArg (fun r => r.2.2) model⟩

#print axioms first
#print axioms second
end AspisR1.F3J_CircleJoin
end
