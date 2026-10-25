import F3J_BlockCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_BlockSampler
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses

theorem payload {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : r1_wire.SemanticTranscript Hash} {row : U8} {framed : Slice U8}
    {block : Array U8 32#usize} (c : F3J_BlockCalls.Calls D before after row framed block)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (positive : row.val≠0) (notReseed : row.val≠26) (notQuery : row.val≠31) (below : row.val<33)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state)
    (payload : b.val=rawBytes framed) :
    eval H (LiteralByteSampler.samp row.val P m).toProgram=
      (F3J_BlockCalls.log c,
       (TranscriptView.Value.ordinary (SelectedTranscriptParams.params.σ row.val (decodeState block)),decodeState after.state)) := by
  let params := SelectedTranscriptParams.params
  have bound : (rawBytes framed).length≤params.D := by rw [← payload]; exact b.property
  have tag : params.lbl row.val=decodeByte c.tag := by
    apply Fin.ext
    change (SelectedTranscriptParams.label row.val).val=c.tag.val
    rw [SelectedTranscriptParams.label_val row.val (by omega),c.tag_value]
  have address : (UnifiedSampler.absorb params row.val (LiteralTranscript.erasePrefix P) b).toBytes=
      flatten (TranscriptStep.absorbParts before.state c.tag framed) := by
    rw [absorb_address params _ _ _ bound]
    congr 1
    unfold UnifiedSampler.absorb
    rw [state,tag]
    congr 1
  have consistent := F3J_BlockCalls.consistent c H backend
  have ha := consistent _ (List.mem_cons_self)
  have hb := consistent _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hs := consistent _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  change decodeState c.absorbed=H (flatten _) at ha
  change decodeState block=H (flatten _) at hb
  change decodeState c.state=H (flatten _) at hs
  rw [squeeze_address params] at hb
  rw [advance_address params] at hs
  rw [LiteralByteSampler.eval_eq]
  change mapView Addr.toBytes (eval (fun a => H a.toBytes)
    (UnifiedSampler.samp params _ row.val (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)).toProgram)=_
  rw [erased,UnifiedSampler.row_ordinary params _ row.val positive notReseed notQuery,DuplexSamplers.plain_eval]
  simp only [mapView,List.map_cons,List.map_nil]
  rw [address,← ha,← hb,← hs]
  unfold F3J_BlockCalls.log
  have afterState : after.state=c.state := congrArg (fun t => t.state) c.carried
  rw [squeeze_address params,advance_address params,afterState]
  rfl

#print axioms payload
end AspisR1.F3J_BlockSampler
end
