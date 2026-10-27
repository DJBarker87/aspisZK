import F3J_InputRows
import RawTx1DigestLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_SemanticLog
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog

theorem consistent {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H) :
    ∀ q ∈ callLog c, q.2=H q.1 := by
  intro q hq
  obtain ⟨input,output,same,call⟩ := callLog_actual c q hq
  exact backend q ⟨c.before.hash,input,output,same,call⟩

theorem payload {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (row : Nat) (positive : row≠0) (below : row<25) (number : c.row.val=row)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.before.state)
    (payload : b.val=rawBytes c.record.framed) :
    (eval H (LiteralByteSampler.samp row P m).toProgram).1=callLog c := by
  let params := SelectedTranscriptParams.params
  have bound : (rawBytes c.record.framed).length≤params.D := by rw [← payload]; exact b.property
  have tag : params.lbl row=decodeByte c.tag := by
    apply Fin.ext
    change (SelectedTranscriptParams.label row).val=c.tag.val
    rw [SelectedTranscriptParams.label_val row (by omega),c.tag_code,c.record_row,number]
  have address : (UnifiedSampler.absorb params row (LiteralTranscript.erasePrefix P) b).toBytes=
      flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed) := by
    rw [absorb_address params _ _ _ bound]
    congr 1
    unfold UnifiedSampler.absorb
    rw [state,tag]
    congr 1
  have consistent := consistent c H backend
  have ha := consistent _ (List.mem_cons_self)
  have hb := consistent _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hs := consistent _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  change decodeState c.absorbed=H (flatten _) at ha
  change decodeState c.block=H (flatten _) at hb
  change decodeState c.state=H (flatten _) at hs
  rw [squeeze_address params] at hb
  rw [advance_address params] at hs
  rw [LiteralByteSampler.eval_eq]
  change (mapView Addr.toBytes (eval (fun a => H a.toBytes)
    (UnifiedSampler.samp params _ row (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)).toProgram)).1=_
  rw [erased,UnifiedSampler.row_ordinary params _ row positive (by omega) (by omega),DuplexSamplers.plain_eval]
  simp only [mapView,List.map_cons,List.map_nil]
  rw [address,← ha,← hb,← hs]
  unfold callLog
  rw [squeeze_address params,advance_address params]

#print axioms consistent
#print axioms payload
end AspisR1.F3J_SemanticLog
end
