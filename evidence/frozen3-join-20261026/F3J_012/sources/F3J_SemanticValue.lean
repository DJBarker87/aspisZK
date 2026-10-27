import F3J_SemanticLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_SemanticValue
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog

theorem payload {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (row : Nat) (positive : row≠0) (below : row<25) (number : c.row.val=row)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.before.state)
    (payload : b.val=rawBytes c.record.framed) :
    eval H (LiteralByteSampler.samp row P m).toProgram=
      (callLog c,(TranscriptView.Value.ordinary (SourceLiteralTraceLift.sourceChallenge c),decodeState c.after.state)) := by
  have all : ∀ q ∈ sourceLog [c],q.2=H q.1 := by
    simpa only [sourceLog,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      F3J_SemanticLog.consistent c H backend
  have bound : ∀ d ∈ [c],(rawBytes d.record.framed).length≤SelectedTranscriptParams.D := by
    intro d hd
    have same : d=c := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hd
    subst d
    rw [← payload]
    exact b.property
  have value := SourceGlobalOracleCoupling.call_simulates_literal_payload [c] c
    (List.mem_cons_self) H (sourceLog [c]) (fun _ h => h) all bound
    row below positive number P m b erased state payload
  apply Prod.ext
  · exact F3J_SemanticLog.payload c H backend row positive below number P m b erased state payload
  · rw [LiteralByteSampler.eval_eq]
    exact Prod.ext value.1.symm value.2.symm

#print axioms payload
end AspisR1.F3J_SemanticValue
end
