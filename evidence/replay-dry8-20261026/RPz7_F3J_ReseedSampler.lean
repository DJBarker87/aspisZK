import RPz7_F3J_ReseedSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_ReseedSampler
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses

theorem payload {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : r1_wire.SemanticTranscript Hash} {framed : Slice U8}
    {block : Array U8 32#usize} (c : F3J_BlockCalls.Calls D before after 26#u8 framed block)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (hash : Hash) (out : transcript.Transcript Hash)
    (reseed : transcript.Transcript.new D hash after.state .S2=ok out)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (pubTag : P.statement.tag=2)
    (erased : LiteralTranscript.erase m=.payload b)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state)
    (payload : b.val=rawBytes framed) :
    eval H (LiteralByteSampler.samp 26 P m).toProgram=
      (F3J_BlockCalls.log c++[(OpeningReseedFrame.frame 2 (decodeState after.state),decodeState out.state)],
       (TranscriptView.Value.ordinary (SelectedTranscriptParams.params.σ 26 (decodeState block)),decodeState out.state)) := by
  let params := SelectedTranscriptParams.params
  have bound : (rawBytes framed).length≤params.D := by rw [← payload]; exact b.property
  have tag : params.lbl 26=decodeByte c.tag := by
    apply Fin.ext
    change (SelectedTranscriptParams.label 26).val=c.tag.val
    rw [SelectedTranscriptParams.label_val 26 (by decide),c.tag_value]
    rfl
  have address : (UnifiedSampler.absorb params 26 (LiteralTranscript.erasePrefix P) b).toBytes=
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
    (UnifiedSampler.samp params _ 26 (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)).toProgram)=_
  rw [erased,UnifiedSampler.row_reseed,DuplexSamplers.reseeded_eval]
  simp only [mapView,List.map_cons,List.map_nil]
  rw [address,← ha,← hb,← hs]
  have seed := (F3J_ReseedSource.reached D hash after.state out reseed H backend).1
  unfold F3J_BlockCalls.log
  have afterState : after.state=c.state := congrArg (fun t => t.state) c.carried
  have seedAddr : (OpeningReseedFrame.addr P.statement.tag
      (by have := P.statement.initFits;omega) (decodeState c.state) : Addr SelectedTranscriptParams.L).toBytes=
        OpeningReseedFrame.frame 2 (decodeState after.state) := by
    rw [OpeningReseedFrame.addr_bytes,pubTag,afterState]
    rfl
  simp only [LiteralTranscript.erasePrefix]
  rw [seedAddr,← seed,squeeze_address params,advance_address params]
  rfl

#print axioms payload
end AspisR1.F3J_ReseedSampler
end
