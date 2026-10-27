import F3M_CircleValues
import F3K_SamplerIndex
import F3J_CircleCode
import F3J_BlockSampler
import F3J_ReseedSampler
import F3J_RecordPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CircleEntries
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
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state)
    (length : P.rounds.length=25) (tail : Nat) :
    let pf := F3J_InputRows.proof p root w bound
    ∃ block,B.circle block .First=ok point ∧
      (eval H (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 25 (tail+1) P)).2.rounds[25]?=
        some (F3J_InputRows.proof p root w bound 25,
          (TranscriptView.Value.ordinary (SelectedTranscriptParams.params.σ 25 (decodeState block)),
            (eval H (LiteralByteSampler.samp 25 P (F3J_InputRows.proof p root w bound 25)).toProgram).2.2)) := by
  obtain ⟨block,call,value⟩ := F3M_CircleValues.first D B pre record before after point read success H backend p records root w bound P state
  let pf := F3J_InputRows.proof p root w bound
  have entry := F3K_SamplerIndex.first_entry H pf 25 tail P
  rw [length] at entry
  have pair : (eval H (LiteralByteSampler.samp 25 P (pf 25)).toProgram).2=
      (TranscriptView.Value.ordinary (SelectedTranscriptParams.params.σ 25 (decodeState block)),
        (eval H (LiteralByteSampler.samp 25 P (pf 25)).toProgram).2.2) := Prod.ext value rfl
  exact ⟨block,call,entry.trans (congrArg (fun c=>some (pf 25,c)) pair)⟩

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
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state)
    (length : P.rounds.length=26) (tail : Nat) :
    let pf := F3J_InputRows.proof p root w bound
    ∃ block,B.circle block .Second=ok point ∧
      (eval H (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 26 (tail+1) P)).2.rounds[26]?=
        some (F3J_InputRows.proof p root w bound 26,
          (TranscriptView.Value.ordinary (SelectedTranscriptParams.params.σ 26 (decodeState block)),
            (eval H (LiteralByteSampler.samp 26 P (F3J_InputRows.proof p root w bound 26)).toProgram).2.2)) := by
  obtain ⟨block,call,value⟩ := F3M_CircleValues.second D B pre record before after point read success hash out reseed H backend p records root w bound P tag state
  let pf := F3J_InputRows.proof p root w bound
  have entry := F3K_SamplerIndex.first_entry H pf 26 tail P
  rw [length] at entry
  have pair : (eval H (LiteralByteSampler.samp 26 P (pf 26)).toProgram).2=
      (TranscriptView.Value.ordinary (SelectedTranscriptParams.params.σ 26 (decodeState block)),
        (eval H (LiteralByteSampler.samp 26 P (pf 26)).toProgram).2.2) := Prod.ext value rfl
  exact ⟨block,call,entry.trans (congrArg (fun c=>some (pf 26,c)) pair)⟩

#print axioms first
#print axioms second
end AspisR1.F3M_CircleEntries
end
